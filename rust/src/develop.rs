//! Natural language -> ordinary Rust -> proof annotations -> real Verus verification.
use crate::{
    model::{Client, Usage},
    pipeline, process, syntax,
    verifier::Verifier,
};
use anyhow::{ensure, Context, Result};
use serde_json::{json, Value};
use std::{fs, path::PathBuf, process::Command};

const RUST_SYSTEM: &str = "Implement the user's requirements as a COMPLETE ordinary Rust source file. Return code only. Use safe standalone free functions, standard types (i32, i64, u32, u64, usize, bool, Vec, slices), and standard library imports only. Include fn main() {}. Do not include Verus syntax, specifications, proof blocks, unsafe, structs, impls, traits, build scripts or external dependencies. Standard demonstration printing in main is allowed; prefer an empty main. The requirements may show Verus-style named return bindings or spec fn declarations: translate executable signatures to ordinary Rust return types and leave spec functions to the later proof stage. Keep requested function names and integer types. Implement the exact requested behavior over its requested domain. Do not replace the task with a stub. The program will first be compiled with rustc and then proved by Verus without changing its executable AST.";
const PROOF_SYSTEM: &str = "Annotate the provided ordinary Rust implementation with Verus specifications and proofs. Return a COMPLETE Verus source file only. Use vstd::prelude::* and verus!. Preserve every executable statement, function signature, visibility, import (except adding vstd imports), and main. Keep the original demonstration main OUTSIDE verus!; functions being proved go inside verus!. Named return bindings are allowed. Add meaningful requires/ensures corresponding to the user's requirements, invariants, decreases, ghost blocks and proved helper functions. Explain the requirement-to-contract mapping in source comments. Do not use assume, admit, axioms, external_body, unsafe, opaque macros, or unverifiable external dependencies. Every non-main executable function must have a nontrivial ensures. Do not invent impossible preconditions or narrow the user-requested domain. All frozen contracts and spec definitions in the prompt must stay unchanged. If verification fails, repair proof annotations only; never change the supplied executable Rust implementation.";

pub struct Options {
    pub requirement: String,
    pub output: PathBuf,
    pub attempts: usize,
    pub max_requests: usize,
    pub max_verifications: usize,
    pub proof_config: pipeline::Config,
    pub verifier: Verifier,
    pub client: Option<Client>,
    pub replay: Vec<String>,
}
struct Session {
    options: Options,
    report: Value,
    usage: Usage,
    requests: usize,
    verifications: usize,
    empty_truncations: usize,
}
impl Session {
    fn save(&mut self) -> Result<()> {
        self.report["requests"] = json!(self.requests);
        self.report["verifications"] = json!(self.verifications);
        self.report["usage"] = json!(self.usage);
        fs::write(
            self.options.output.join("report.json"),
            serde_json::to_vec_pretty(&self.report)?,
        )?;
        Ok(())
    }
    fn event(&mut self, event: Value) -> Result<()> {
        self.report["attempts"].as_array_mut().unwrap().push(event);
        self.save()
    }
    fn request(
        &mut self,
        stage: &str,
        index: usize,
        system: &str,
        prompt: &str,
    ) -> Result<Option<String>> {
        if self.requests >= self.options.max_requests || self.report["status"] == "output_truncated"
        {
            return Ok(None);
        }
        if !self.options.replay.is_empty() && self.requests >= self.options.replay.len() {
            return Ok(None);
        }
        fs::write(
            self.options
                .output
                .join(stage)
                .join(format!("prompt-{index}.txt")),
            prompt,
        )?;
        self.report["stage"] = json!(stage);
        let request = self.requests;
        self.requests += 1;
        self.save()?;
        eprintln!(
            "  [{stage}] request {}/{}; attempt {}/{}",
            self.requests,
            self.options.max_requests,
            index + 1,
            self.options.attempts
        );
        if !self.options.replay.is_empty() {
            return Ok(Some(self.options.replay[request].clone()));
        }
        let response = self
            .options
            .client
            .as_ref()
            .context("model is unavailable")?
            .complete(system, prompt, 1)?;
        self.usage.add(&response.usage);
        let response = response
            .choices
            .into_iter()
            .next()
            .context("missing generated program")?;
        self.save()?;
        if response.truncated {
            self.empty_truncations = if response.code.is_empty() {
                self.empty_truncations + 1
            } else {
                0
            };
            fs::write(
                self.options
                    .output
                    .join(stage)
                    .join(format!("truncated-{index}.txt")),
                response.code,
            )?;
            if self.empty_truncations >= 3 {
                self.report["status"] = json!("output_truncated");
            }
            self.event(json!({"stage":stage,"index":index,"status":"truncated"}))?;
            return Ok(Some(String::new()));
        }
        self.empty_truncations = 0;
        Ok(Some(response.code))
    }
    fn compile(&self, source: &str) -> Result<process::Output> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("implementation.rs");
        fs::write(&path, source)?;
        process::run(
            Command::new("rustc")
                .args([
                    "--edition=2021",
                    "--crate-type=lib",
                    "--emit=metadata",
                    "--crate-name=verusseek_generated",
                ])
                .arg(path)
                .arg("-o")
                .arg(dir.path().join("implementation.rmeta")),
            self.options.verifier.timeout,
        )
    }
    fn generate_rust(&mut self) -> Result<Option<String>> {
        let mut previous = String::new();
        let mut feedback = String::new();
        for index in 0..self.options.attempts {
            let prompt = format!(
                "REQUIREMENTS:\n{}\nPREVIOUS RUST:\n{previous}\nCOMPILER FEEDBACK:\n{feedback}",
                self.options.requirement
            );
            let Some(code) = self.request("rust", index, RUST_SYSTEM, &prompt)? else {
                break;
            };
            if code.is_empty() {
                feedback =
                    "Previous response was truncated; return concise complete Rust code.".into();
                continue;
            }
            fs::write(
                self.options
                    .output
                    .join("rust")
                    .join(format!("candidate-{index}.rs")),
                &code,
            )?;
            previous = code.clone();
            if let Err(error) = syntax::plain_rust_structure(&code) {
                feedback = format!("Invalid ordinary Rust: {error:#}");
                eprintln!("  {feedback}");
                self.event(
                    json!({"stage":"rust","index":index,"status":"rejected","error":feedback}),
                )?;
                continue;
            }
            let result = self.compile(&code)?;
            let success = result.exit_code == Some(0) && !result.timed_out;
            fs::write(
                self.options
                    .output
                    .join("rust")
                    .join(format!("compile-{index}.json")),
                serde_json::to_vec_pretty(&result)?,
            )?;
            self.event(json!({"stage":"rust","index":index,"status":if success {"compiled"} else {"compile_failed"}}))?;
            if success {
                eprintln!("  rustc: compiled successfully; handing Rust to specification adapter");
                fs::write(self.options.output.join("implementation.rs"), &code)?;
                self.report["rust_compiled"] = json!(true);
                self.save()?;
                return Ok(Some(code));
            }
            feedback = result.stderr.chars().take(24_000).collect();
            eprintln!(
                "  rustc failed: {}",
                feedback.lines().take(8).collect::<Vec<_>>().join("\n")
            );
        }
        if !feedback.is_empty() {
            self.report["error"] = json!(feedback);
            self.save()?;
        }
        Ok(None)
    }
    fn prove_rust(&mut self, rust: &str) -> Result<()> {
        let executable = syntax::plain_rust_structure(rust)?;
        let mut previous = String::new();
        let mut feedback = String::new();
        for index in 0..self.options.attempts {
            let prompt = format!("REQUIREMENTS:\n{}\nIMMUTABLE RUST IMPLEMENTATION:\n{rust}\nPREVIOUS ANNOTATION:\n{previous}\nFEEDBACK:\n{feedback}\nAdd the specification adapter only; VerusSeek-RS will handle verification and proof repair.", self.options.requirement);
            let Some(code) = self.request("proof", index, PROOF_SYSTEM, &prompt)? else {
                break;
            };
            if code.is_empty() {
                feedback = "Return a concise complete specification adapter within the fixed output budget.".into();
                continue;
            }
            fs::write(
                self.options
                    .output
                    .join("proof")
                    .join(format!("candidate-{index}.rs")),
                &code,
            )?;
            previous = code.clone();
            let validation = syntax::generated_contracts(&code).and_then(|contracts| {
                let erased = syntax::executable_rust(&code)?;
                ensure!(syntax::plain_rust_structure(&erased)? == executable, "executable Rust changed; retain the supplied implementation and demonstration main");
                Ok(contracts)
            });
            let contracts = match validation {
                Ok(contracts) => contracts,
                Err(error) => {
                    feedback = format!("Rejected specification adapter: {error:#}");
                    eprintln!("  {feedback}");
                    self.event(
                        json!({"stage":"proof","index":index,"status":"rejected","error":feedback}),
                    )?;
                    continue;
                }
            };
            fs::write(
                self.options.output.join("contracts.json"),
                serde_json::to_vec_pretty(&contracts)?,
            )?;
            self.event(json!({"stage":"proof","index":index,"status":"handed_to_verusseek"}))?;
            let mut config = self.options.proof_config.clone();
            let remaining = self.options.max_requests.saturating_sub(self.requests);
            // Engine still checks the initial program when no further model requests remain.
            config.max_requests = remaining;
            config.max_verifications = self
                .options
                .max_verifications
                .saturating_sub(self.verifications);
            let replay = self
                .options
                .replay
                .get(self.requests..)
                .unwrap_or(&[])
                .to_vec();
            eprintln!("  Rust compiled. Handing specification adapter to VerusSeek-RS...");
            let proof_dir = self.options.output.join("proof").join("verusseek");
            let seed = syntax::specification_seed(&code)?;
            fs::write(self.options.output.join("proof").join("input.rs"), &seed)?;
            let report = pipeline::Engine::new(
                config,
                self.options.verifier.clone(),
                self.options.client.clone(),
                replay,
                proof_dir.clone(),
                seed,
            )?
            .run()?;
            self.requests += report["requests"].as_u64().unwrap_or(0) as usize;
            self.verifications += report["verifications"].as_u64().unwrap_or(0) as usize;
            let usage: Usage = serde_json::from_value(report["usage"].clone())?;
            self.usage.add(&usage);
            self.report["proof_engine"] = report.clone();
            self.report["final_verification"] = report["final_verification"].clone();
            let final_code = fs::read_to_string(proof_dir.join("final.rs"))?;
            ensure!(
                syntax::plain_rust_structure(&syntax::executable_rust(&final_code)?)? == executable,
                "proof engine changed the generated executable Rust"
            );
            fs::write(self.options.output.join("final.rs"), &final_code)?;
            self.report["executable_preserved"] = json!(true);
            if report["verified"] == true {
                fs::write(self.options.output.join("verified.rs"), &final_code)?;
                self.report["verified"] = json!(true);
                self.report["status"] = json!("verified");
            } else {
                self.report["status"] = json!("unproved");
                if report["error"].is_string() {
                    self.report["error"] = report["error"].clone();
                }
            }
            self.save()?;
            return Ok(());
        }
        if !feedback.is_empty() {
            self.report["error"] = json!(feedback);
            self.save()?;
        }
        Ok(())
    }
}

pub fn run(options: Options) -> Result<Value> {
    ensure!(
        !options.requirement.trim().is_empty() && options.requirement.len() <= 64_000,
        "requirements must contain 1..64000 bytes"
    );
    ensure!(
        options.client.is_some() || !options.replay.is_empty(),
        "development requires a model or explicit replay responses"
    );
    fs::create_dir(&options.output).context("output directory must be new")?;
    fs::create_dir(options.output.join("rust"))?;
    fs::create_dir(options.output.join("proof"))?;
    fs::write(options.output.join("requirements.md"), &options.requirement)?;
    let report = json!({"mode":if options.replay.is_empty() {"live"} else {"replay"},"status":"running","verified":false,"rust_compiled":false,"executable_preserved":false,"model":options.client.as_ref().map(|client| &client.model),"attempts":[],"pipeline":"natural_language_to_rust_to_verusseek","verification_scope":"specified_functions; ordinary demonstration main is retained outside verus!","specification_source":"generated_from_requirements","requirement_alignment":"requires_human_review"});
    let mut session = Session {
        options,
        report,
        usage: Usage::default(),
        requests: 0,
        verifications: 0,
        empty_truncations: 0,
    };
    session.save()?;
    let outcome = session.generate_rust().and_then(|rust| {
        if let Some(rust) = rust {
            session.prove_rust(&rust)
        } else {
            Ok(())
        }
    });
    if let Err(error) = outcome {
        session.report["status"] = json!("error");
        session.report["error"] = json!(format!("{error:#}"));
    } else if session.report["status"] == "running" {
        session.report["status"] = json!(if session.report["rust_compiled"] == true {
            "unproved"
        } else {
            "generation_failed"
        });
    }
    session.save()?;
    Ok(session.report)
}
