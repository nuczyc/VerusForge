use crate::{
    model::{Client, Completion, Usage},
    strategies, syntax,
    verifier::{Evaluation, Score, Verifier},
};
use anyhow::{ensure, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct Config {
    pub phases: usize,
    pub inference_retries: usize,
    pub candidates: usize,
    pub refinement_retries: usize,
    pub repair_steps: usize,
    pub houdini_steps: usize,
    pub max_requests: usize,
    pub max_verifications: usize,
    pub max_tokens: u32,
    pub max_empty_truncations: usize,
    pub temperature: f64,
    pub timeout: u64,
    pub profile: String,
    pub inheritance: bool,
    pub ranking: bool,
    pub enhanced: bool,
    pub examples: Option<PathBuf>,
    pub phase1_examples: Vec<String>,
    pub disabled_refinements: Vec<String>,
    pub repair_candidates: usize,
    pub loop_isolation: bool,
    pub repair_uniform: bool,
    pub generation_uniform: bool,
    pub baseline_retries: usize,
    pub lemmas: Option<PathBuf>,
}
impl Default for Config {
    fn default() -> Self {
        Self {
            phases: 3,
            inference_retries: 3,
            candidates: 5,
            refinement_retries: 3,
            repair_steps: 10,
            houdini_steps: 20,
            max_requests: 96,
            max_verifications: 512,
            max_tokens: 8192,
            max_empty_truncations: 3,
            temperature: 1.0,
            timeout: 60,
            profile: "standard".into(),
            inheritance: true,
            ranking: true,
            enhanced: true,
            examples: Some(PathBuf::from("examples")),
            phase1_examples: vec!["3".into(), "6".into(), "7".into()],
            disabled_refinements: Vec::new(),
            repair_candidates: 3,
            loop_isolation: true,
            repair_uniform: false,
            generation_uniform: false,
            baseline_retries: 25,
            lemmas: Some(PathBuf::from("lemmas")),
        }
    }
}
impl Config {
    pub fn load(path: Option<&Path>) -> Result<Self> {
        let config: Self = match path {
            Some(path) => serde_json::from_str(&fs::read_to_string(path)?)?,
            None => Self::default(),
        };
        ensure!(
            (1..=10).contains(&config.phases)
                && (1..=20).contains(&config.candidates)
                && config.inference_retries <= 10
                && config.refinement_retries <= 10,
            "invalid stage limits"
        );
        ensure!(
            config.max_requests > 0
                && config.max_requests <= 1000
                && config.max_verifications > 0
                && config.max_verifications <= 5000
                && config.houdini_steps <= 100
                && config.repair_steps <= 100,
            "invalid request/verification limits"
        );
        ensure!(
            config.timeout > 0
                && config.max_tokens > 0
                && (1..=10).contains(&config.max_empty_truncations)
                && (0.0..=2.0).contains(&config.temperature),
            "invalid timeout/model settings"
        );
        ensure!(
            ["standard", "baseline", "uniform", "direct-repair"].contains(&config.profile.as_str()),
            "unknown strategy profile"
        );
        ensure!(
            (1..=10).contains(&config.repair_candidates),
            "repair_candidates must be 1..10"
        );
        ensure!(
            (1..=100).contains(&config.baseline_retries),
            "baseline_retries must be 1..100"
        );
        Ok(config)
    }
}

#[derive(Clone)]
struct Candidate {
    code: String,
    evaluation: Evaluation,
}

pub fn annotated(code: &str, score: Option<Score>, safe: bool) -> String {
    let score = score.map(|s| s.legacy_text()).unwrap_or_else(|| {
        "Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 0".into()
    });
    format!(
        "{}\n\n// Score: {score}\n// Safe: {}\n",
        code.trim_end(),
        if safe { "True" } else { "False" }
    )
}

pub struct Engine {
    pub config: Config,
    pub verifier: Verifier,
    pub client: Option<Client>,
    pub replay: Vec<String>,
    pub dir: PathBuf,
    original: String,
    best: String,
    evaluation: Option<Evaluation>,
    report: Value,
    requests: usize,
    verifications: usize,
    usage: Usage,
    replay_index: usize,
    start: Instant,
    last_rejection: String,
    cache: std::collections::BTreeMap<String, Evaluation>,
    cache_hits: usize,
    last_candidate: Option<Candidate>,
    legacy_output: Option<PathBuf>,
    phase: usize,
    candidate_name: Option<String>,
    batch_size: usize,
    batch_loaded: bool,
    pending: std::collections::VecDeque<(usize, usize, Completion)>,
    empty_truncations: usize,
}
impl Engine {
    pub fn new(
        config: Config,
        verifier: Verifier,
        client: Option<Client>,
        replay: Vec<String>,
        dir: PathBuf,
        original: String,
    ) -> Result<Self> {
        fs::create_dir(&dir).context("run output directory must not already exist")?;
        fs::write(dir.join("input.rs"), &original)?;
        let mode = if !replay.is_empty() {
            "replay"
        } else if client.is_some() {
            "live"
        } else {
            "no-model"
        };
        let report = json!({"schema_version":2,"mode":mode,"status":"running","verified":false,"config":config,"model":client.as_ref().map(|c|&c.model),"api_base":client.as_ref().map(|c|&c.base),"events":[],"phases":[],"scope":"whole-program AST preservation; original specifications are trusted"});
        Ok(Self {
            config,
            verifier,
            client,
            replay,
            dir,
            original: original.clone(),
            best: original,
            evaluation: None,
            report,
            requests: 0,
            verifications: 0,
            usage: Usage::default(),
            replay_index: 0,
            start: Instant::now(),
            last_rejection: String::new(),
            cache: Default::default(),
            cache_hits: 0,
            last_candidate: None,
            legacy_output: None,
            phase: 1,
            candidate_name: None,
            batch_size: 1,
            batch_loaded: false,
            pending: Default::default(),
            empty_truncations: 0,
        })
    }
    pub fn with_legacy_output(mut self, output: PathBuf) -> Self {
        self.legacy_output = Some(output);
        self
    }
    fn phase_output(&self) -> Option<PathBuf> {
        self.legacy_output.as_ref().map(|output| {
            output.with_file_name(format!(
                "{}-{}",
                self.phase,
                output.file_name().unwrap().to_string_lossy()
            ))
        })
    }
    fn artifact_dir(&self) -> PathBuf {
        self.phase_output()
            .map(|output| {
                output.with_file_name(format!(
                    "intermediate-{}",
                    output.file_stem().unwrap().to_string_lossy()
                ))
            })
            .unwrap_or_else(|| self.dir.clone())
    }
    fn log(&self, message: String) -> Result<()> {
        eprintln!("{message}");
        if let Some(output) = self.phase_output() {
            let mut file = fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(output.with_extension("time"))?;
            writeln!(file, "{message}")?;
        }
        Ok(())
    }
    fn snapshot_phase(&mut self) -> Result<()> {
        if let Some(output) = self.phase_output() {
            let safe = syntax::check(&self.original, &self.best).is_ok();
            fs::write(
                &output,
                annotated(&self.best, self.evaluation.as_ref().map(|e| e.score), safe),
            )?;
            self.report["result_file"] = json!(output);
        }
        Ok(())
    }
    fn save(&mut self) -> Result<()> {
        self.report["requests"] = json!(self.requests);
        self.report["verifications"] = json!(self.verifications);
        self.report["usage"] = json!(self.usage);
        self.report["elapsed_ms"] = json!(self.start.elapsed().as_millis());
        self.report["verification_cache_hits"] = json!(self.cache_hits);
        self.report["best_score"] = json!(self.evaluation.as_ref().map(|e| e.score));
        fs::write(
            self.dir.join("report.json"),
            serde_json::to_vec_pretty(&self.report)?,
        )?;
        fs::write(
            self.artifact_dir().join("best.rs"),
            annotated(
                &self.best,
                self.evaluation.as_ref().map(|e| e.score),
                self.evaluation.is_some(),
            ),
        )?;
        Ok(())
    }
    fn finish(mut self) -> Result<Value> {
        let safe = syntax::check(&self.original, &self.best).is_ok();
        self.report["safe"] = json!(safe);
        self.report["final_file"] = json!(self.artifact_dir().join("final.rs"));
        self.snapshot_phase()?;
        self.save()?;
        let source = annotated(&self.best, self.evaluation.as_ref().map(|e| e.score), safe);
        fs::write(self.artifact_dir().join("final.rs"), &source)?;
        fs::write(self.artifact_dir().join("best.rs"), &source)?;
        if self.report["verified"] == true {
            fs::write(self.artifact_dir().join("verified.rs"), source)?;
        }
        Ok(self.report)
    }
    fn record(&mut self, event: Value) -> Result<()> {
        self.report["events"].as_array_mut().unwrap().push(event);
        self.save()
    }
    fn evaluate(&mut self, code: &str) -> Result<Evaluation> {
        if let Some(e) = self.cache.get(code) {
            self.cache_hits += 1;
            return Ok(e.clone());
        }
        ensure!(
            self.verifications < self.config.max_verifications,
            "verification budget exhausted"
        );
        self.verifications += 1;
        self.log(format!(
            "  Verus check {}/{} ...",
            self.verifications, self.config.max_verifications
        ))?;
        let evaluation = self.verifier.code(code)?;
        self.log(format!(
            "  {} ({:.2}s)",
            evaluation.score.legacy_text(),
            evaluation.process.elapsed_ms as f64 / 1000.0
        ))?;
        if !evaluation.process.timed_out {
            self.cache.insert(code.to_string(), evaluation.clone());
        }
        Ok(evaluation)
    }
    fn correct(&self) -> bool {
        self.evaluation.as_ref().is_some_and(|e| e.success)
    }
    fn score(&self) -> Score {
        self.evaluation.as_ref().expect("initial evaluation").score
    }
    fn feedback(&self) -> String {
        format!(
            "{}\n{}",
            self.evaluation
                .as_ref()
                .map(|e| e.feedback())
                .unwrap_or_default(),
            self.last_rejection
        )
    }
    fn consider(&mut self, candidate: &Candidate, loose: bool) -> bool {
        let old = self.evaluation.as_ref().map(|e| e.score);
        let score = candidate.evaluation.score;
        let accepted = candidate.evaluation.success
            || old.is_none()
            || !self.config.ranking && !score.compilation_error
            || old.is_some_and(|s| score.rank() > s.rank())
            || loose && old.is_some_and(|s| score.good_repair(&s));
        if accepted {
            self.best = candidate.code.clone();
            self.evaluation = Some(candidate.evaluation.clone());
        }
        accepted
    }
    fn attempt(&mut self, label: &str, code: String, loose: bool) -> Result<Option<Candidate>> {
        self.last_candidate = None;
        let mut code = code;
        let named = self.candidate_name.take();
        for fix in 0..=10 {
            let id = self.report["events"].as_array().unwrap().len();
            let stage = if fix == 0 { label } else { "type_fix" };
            let filename = named
                .clone()
                .unwrap_or_else(|| format!("candidate-{id}.rs"));
            let path = self.artifact_dir().join(&filename);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(&path, &code)?;
            if let Err(error) = syntax::check(&self.original, &code) {
                self.log(format!("  [{stage}] rejected: {error}"))?;
                self.last_rejection=format!("Rejected candidate: {error}. Preserve the original executable program and all original contracts.");
                fs::write(&path, annotated(&code, None, false))?;
                self.record(json!({"stage":stage,"candidate":filename,"phase":self.phase,"safe":false,"reason":error.to_string()}))?;
                return Ok(None);
            }
            let evaluation = self.evaluate(&code)?;
            let fixed = if evaluation.score.compilation_error && fix < 10 {
                evaluation.type_fix(&code)
            } else {
                None
            };
            let candidate = Candidate {
                code: code.clone(),
                evaluation,
            };
            let accepted = self.consider(&candidate, loose);
            self.log(format!(
                "  [{stage}] {}",
                if candidate.evaluation.success {
                    "verified"
                } else if accepted {
                    "selected"
                } else {
                    "not selected"
                }
            ))?;
            fs::write(
                &path,
                annotated(&code, Some(candidate.evaluation.score), true),
            )?;
            self.record(json!({"stage":stage,"candidate":filename,"phase":self.phase,"safe":true,"accepted":accepted,"evaluation":candidate.evaluation}))?;
            if let Some(fixed) = fixed {
                if fixed != code && syntax::check(&self.original, &fixed).is_ok() {
                    code = fixed;
                    continue;
                }
            }
            self.last_rejection = if accepted {
                String::new()
            } else {
                format!(
                    "Last candidate was not selected. Its verifier feedback:\n{}",
                    candidate.evaluation.feedback()
                )
            };
            self.last_candidate = Some(candidate.clone());
            return Ok(Some(candidate));
        }
        unreachable!()
    }
    fn consume_response(
        &mut self,
        id: usize,
        index: usize,
        response: Completion,
    ) -> Result<Option<String>> {
        if response.truncated {
            let empty = response.code.trim().is_empty();
            self.empty_truncations = if empty { self.empty_truncations + 1 } else { 0 };
            fs::write(
                self.artifact_dir()
                    .join(format!("response-{id}-{index}-truncated.txt")),
                response.code,
            )?;
            self.record(json!({"stage":"truncated_candidate","request":id,"index":index,"empty":empty,"consecutive_empty":self.empty_truncations}))?;
            ensure!(
                self.empty_truncations < self.config.max_empty_truncations,
                "consecutive empty truncated outputs; stopped task at fixed max_tokens={}",
                self.config.max_tokens
            );
            self.log(format!(
                "  truncated candidate discarded (empty={empty}); fixed max_tokens={}",
                self.config.max_tokens
            ))?;
            return Ok(Some(String::new()));
        }
        self.empty_truncations = 0;
        Ok(Some(response.code))
    }
    fn request(
        &mut self,
        strategy: &str,
        phase: &str,
        iteration: usize,
        source: &str,
    ) -> Result<Option<String>> {
        if let Some((id, index, response)) = self.pending.pop_front() {
            return self.consume_response(id, index, response);
        }
        if self.batch_loaded || self.requests >= self.config.max_requests {
            return Ok(None);
        }
        if !self.replay.is_empty() {
            let Some(code) = self.replay.get(self.replay_index).cloned() else {
                return Ok(None);
            };
            self.replay_index += 1;
            self.requests += 1;
            self.record(
                json!({"stage":"replay_response","strategy":strategy,"index":self.replay_index-1}),
            )?;
            return Ok(Some(code));
        }
        let Some(client) = self.client.clone() else {
            return Ok(None);
        };
        let analysis = syntax::analyze(source)?;
        let mut examples = self.examples(strategy)?;
        if source.contains("Seq") || source.contains("Vec") {
            examples.push_str(&self.reference("seq", true)?);
        }
        if strategy.contains("lemma_func") || strategy.contains("special_assertion") {
            examples.push_str(&self.reference("lemmas", false)?);
        }
        let prompt=format!("STRATEGY: {strategy}\n{}\nPHASE: {iteration} / {phase}\nSTATIC ANALYSIS:\n{}\nFEW-SHOT EXAMPLES:\n{examples}\nCURRENT PROGRAM:\n{source}\nVERIFIER FEEDBACK:\n{}\nReturn the complete program; preserve imports, executable statements and contracts.",strategies::prompt(strategy),serde_json::to_string(&analysis)?,self.feedback());
        let id = self.requests;
        fs::write(
            self.artifact_dir().join(format!("prompt-{id}.txt")),
            &prompt,
        )?;
        self.requests += 1;
        self.log(format!(
            "  [{strategy}] model request {}/{} (n={}, max_tokens={}) ...",
            self.requests, self.config.max_requests, self.batch_size, client.max_tokens
        ))?;
        let request_start = Instant::now();
        let response = client.complete(strategies::SYSTEM, &prompt, self.batch_size)?;
        let usage = response.usage;
        self.log(format!(
            "  model response ({:.2}s, {} input / {} output tokens)",
            request_start.elapsed().as_secs_f64(),
            usage.prompt_tokens,
            usage.completion_tokens
        ))?;
        self.usage.add(&usage);
        self.record(
            json!({"stage":"model_response","strategy":strategy,"request":id,"phase":self.phase,"usage":usage,"choices":response.choices.len(),"truncated":response.choices.iter().filter(|c| c.truncated).count(),"max_tokens":client.max_tokens}),
        )?;
        if self.batch_size > 1 {
            self.batch_loaded = true;
        }
        for (index, choice) in response.choices.into_iter().enumerate() {
            self.pending.push_back((id, index, choice));
        }
        let (id, index, choice) = self
            .pending
            .pop_front()
            .context("missing response choice")?;
        self.consume_response(id, index, choice)
    }

    fn examples(&self, strategy: &str) -> Result<String> {
        let Some(root) = &self.config.examples else {
            return Ok(String::new());
        };
        let kind = if strategy == "generation.direct_inference"
            || strategy == "generation.direct_inference_with_refinement"
        {
            ""
        } else if strategy == "generation.direct_full_inference" {
            "temp"
        } else if strategy.contains("proof_func") {
            "proof-func-middle"
        } else if strategy == "generation.proof_block_inference" {
            "proof"
        } else if strategy.contains("condloop") {
            "condinv"
        } else if strategy.contains("invfail_front") {
            "inv-front"
        } else if strategy.contains("invfail_end") {
            "inv-end"
        } else if strategy.contains("postcond") {
            "postcond"
        } else if strategy.contains("precond") {
            "precond"
        } else if strategy.contains("assertion") {
            "assert"
        } else if strategy.contains("arithmetic") {
            "aritherr"
        } else if strategy.contains("breakloop") {
            "loopbreak"
        } else {
            "default"
        };
        let suffix = if kind.is_empty() {
            String::new()
        } else {
            format!("-{kind}")
        };
        let input = root.join(format!("input{suffix}"));
        let output = root.join(format!("output{suffix}"));
        if !input.is_dir() {
            return Ok(String::new());
        }
        let mut files = fs::read_dir(input)?
            .map(|e| e.map(|e| e.path()))
            .collect::<std::io::Result<Vec<_>>>()?;
        files.sort();
        let mut result = String::new();
        for file in files
            .into_iter()
            .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        {
            if kind.is_empty()
                && !file.file_stem().and_then(|s| s.to_str()).is_some_and(|s| {
                    self.config
                        .phase1_examples
                        .iter()
                        .any(|id| s == format!("ex{id}"))
                })
            {
                continue;
            }
            let paired = output.join(file.file_name().unwrap());
            if paired.exists() {
                result.push_str(&format!(
                    "\nINPUT:\n{}\nANSWER:\n{}\n",
                    fs::read_to_string(file)?,
                    fs::read_to_string(paired)?
                ));
            }
        }
        Ok(result.chars().take(24_000).collect())
    }
    fn reference(&self, kind: &str, is_example: bool) -> Result<String> {
        let root = if is_example {
            self.config.examples.as_ref().map(|p| p.join(kind))
        } else {
            self.config.lemmas.clone()
        };
        let Some(root) = root.filter(|p| p.is_dir()) else {
            return Ok(String::new());
        };
        let mut files = fs::read_dir(root)?
            .map(|e| e.map(|e| e.path()))
            .collect::<std::io::Result<Vec<_>>>()?;
        files.sort();
        let mut text = String::new();
        for file in files
            .into_iter()
            .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        {
            text.push_str(&format!(
                "\nREFERENCE {}:\n{}",
                file.file_name().unwrap().to_string_lossy(),
                fs::read_to_string(&file)?
            ));
        }
        Ok(text.chars().take(24_000).collect())
    }
    fn houdini_candidate(&mut self, label: &str, mut candidate: Candidate) -> Result<Candidate> {
        for _ in 0..self.config.houdini_steps {
            if candidate.evaluation.success || candidate.evaluation.score.compilation_error {
                break;
            }
            let spans = candidate.evaluation.prune_spans();
            if spans.is_empty() {
                break;
            }
            let code = syntax::prune_at(&candidate.code, &spans)?;
            if code == candidate.code || syntax::check(&self.original, &code).is_err() {
                break;
            }
            let Some(next) = self.attempt(label, code, true)? else {
                break;
            };
            candidate = next;
        }
        Ok(candidate)
    }
    fn houdini(&mut self, label: &str) -> Result<()> {
        let candidate = Candidate {
            code: self.best.clone(),
            evaluation: self.evaluation.as_ref().unwrap().clone(),
        };
        self.houdini_candidate(label, candidate)?;
        Ok(())
    }
    fn generated(
        &mut self,
        strategy: &str,
        phase: &str,
        iteration: usize,
        source: &str,
        loose: bool,
    ) -> Result<bool> {
        let Some(code) = self.request(strategy, phase, iteration, source)? else {
            self.candidate_name = None;
            return Ok(false);
        };
        if code.is_empty() {
            self.last_candidate = None;
            self.candidate_name = None;
            return Ok(true);
        }
        if let Some(candidate) = self.attempt(strategy, code, loose)? {
            if self.config.profile != "baseline"
                && !candidate.evaluation.success
                && !candidate.evaluation.score.compilation_error
            {
                self.houdini_candidate("candidate_houdini", candidate)?;
            }
        }
        Ok(true)
    }
    fn run_inner(&mut self) -> Result<()> {
        syntax::check(&self.original, &self.original).context("unsupported or untrusted input")?;
        let original = self.original.clone();
        self.attempt("original", original, false)?;
        // Basic bounds and termination candidates before spending model requests.
        if self.config.enhanced && self.config.profile != "baseline" && !self.correct() {
            if let Ok(candidate) = syntax::augment(&self.best) {
                self.attempt("deterministic_loop_synthesis", candidate, true)?;
            }
        }
        for phase in 1..=self.config.phases {
            if self.correct() {
                break;
            }
            self.phase = phase;
            fs::create_dir_all(self.artifact_dir())?;
            self.log(format!("  Phase {phase}/{}", self.config.phases))?;
            if phase > 1 && !self.config.inheritance {
                self.best = self.original.clone();
                let code = self.best.clone();
                self.evaluation = Some(self.evaluate(&code)?);
            }
            let starting_score = self.score();
            let phase_input = format!("phase-{phase}-start.rs");
            fs::write(self.artifact_dir().join(&phase_input), &self.best)?;
            let phase_record = json!({"phase":phase,"starting_score":starting_score,"inheritance":self.config.inheritance,"input":phase_input,"directory":self.artifact_dir(),"output":self.phase_output()});
            self.report["phases"]
                .as_array_mut()
                .unwrap()
                .push(phase_record);
            let seed = self.best.clone();
            let mut pool = Vec::new();
            if self.config.profile != "direct-repair" {
                let strategy = if self.config.profile == "baseline" {
                    "generation.direct_full_inference"
                } else if self.config.profile == "uniform" || self.config.generation_uniform {
                    "generation.direct_inference_with_refinement"
                } else {
                    "generation.direct_inference"
                };
                let retries = if self.config.profile == "baseline" {
                    self.config.baseline_retries
                } else {
                    self.config.inference_retries
                };
                let candidates = self
                    .client
                    .as_ref()
                    .map(|client| client.candidate_count(self.config.candidates))
                    .unwrap_or(self.config.candidates);
                for round in 0..retries {
                    self.batch_size = candidates;
                    self.batch_loaded = false;
                    self.pending.clear();
                    self.log(format!(
                        "  Generation round {}/{} ({} candidates)",
                        round + 1,
                        retries,
                        candidates
                    ))?;
                    self.record(json!({"stage":"generation_round","phase":phase,"round":round,"candidates":candidates}))?;
                    let mut valid = false;
                    let mut unsafe_candidate = false;
                    for index in 0..candidates {
                        self.log(format!("  Checking candidate {round}-{index}"))?;
                        self.candidate_name = Some(format!("{round}-{index}.rs"));
                        if !self.generated(strategy, "inference", phase, &seed, false)? {
                            break;
                        }
                        if self.correct() {
                            return Ok(());
                        }
                        if self.last_candidate.is_none() {
                            unsafe_candidate = true;
                        }
                        if let Some(candidate) = &self.last_candidate {
                            if !candidate.evaluation.score.compilation_error {
                                valid = true;
                                if !pool.contains(&candidate.code) {
                                    pool.push(candidate.code.clone());
                                }
                            }
                        }
                        if self.config.profile != "baseline"
                            && pool.len() >= if self.config.ranking { 4 } else { 1 }
                        {
                            break;
                        }
                        if self.requests >= self.config.max_requests && self.pending.is_empty() {
                            break;
                        }
                    }
                    self.batch_size = 1;
                    self.batch_loaded = false;
                    self.pending.clear();
                    if self.config.profile != "baseline" && valid && !unsafe_candidate
                        || self.config.profile != "baseline"
                            && pool.len() >= if self.config.ranking { 4 } else { 1 }
                        || self.requests >= self.config.max_requests
                    {
                        break;
                    }
                }
                let mut all = self.best.clone();
                for (index, code) in pool.into_iter().enumerate() {
                    let best = self.best.clone();
                    if let Ok(merged) = syntax::merge(&best, &code) {
                        self.candidate_name = Some(format!("merged-{index}.rs"));
                        self.attempt("selective_merge", merged, true)?;
                        self.houdini("merge_houdini")?;
                    }
                    if self.correct() {
                        return Ok(());
                    }
                    if let Ok(merged) = syntax::merge(&all, &code) {
                        all = merged.clone();
                        self.candidate_name = Some(format!("allmerged-{index}.rs"));
                        self.attempt("all_merge", merged, true)?;
                        self.houdini("all_merge_houdini")?;
                    }
                    if self.correct() {
                        return Ok(());
                    }
                }
            }
            if self.config.profile == "standard" && !self.config.generation_uniform {
                let a = syntax::analyze(&self.best)?;
                for (refine_index, strategy) in strategies::refinements(&a).into_iter().enumerate()
                {
                    if self
                        .config
                        .disabled_refinements
                        .iter()
                        .any(|s| s == strategy)
                    {
                        continue;
                    }
                    if !self.config.enhanced
                        && ["loop_synthesis", "spec_decomposition", "array_write"]
                            .contains(&strategy)
                    {
                        continue;
                    }
                    let source = self.best.clone();
                    for refine_attempt in 0..self.config.refinement_retries {
                        self.candidate_name =
                            Some(format!("refine-{refine_index}-{refine_attempt}.rs"));
                        if !self.generated(
                            strategy,
                            "refinement",
                            phase,
                            &source,
                            strategy != "generation.condlooprefine_inference",
                        )? {
                            break;
                        }
                        if self.correct() {
                            return Ok(());
                        }
                        self.houdini("refinement_houdini")?;
                        if self.correct() {
                            return Ok(());
                        }
                        if self.best != source {
                            fs::write(
                                self.artifact_dir()
                                    .join(format!("refine-{refine_index}.rs")),
                                annotated(
                                    &self.best,
                                    self.evaluation.as_ref().map(|e| e.score),
                                    true,
                                ),
                            )?;
                            break;
                        }
                    }
                }
            }
            let mut stalled = 0;
            if self.config.profile != "baseline" {
                fs::write(
                    self.artifact_dir().join("before-repair.rs"),
                    annotated(&self.best, self.evaluation.as_ref().map(|e| e.score), true),
                )?;
                fs::create_dir_all(self.artifact_dir().join("repair"))?;
                if self.config.loop_isolation {
                    let code = syntax::loop_isolation(&self.best)?;
                    self.attempt("loop_isolation", code, true)?;
                    if self.correct() {
                        return Ok(());
                    }
                }
                for step in 0..self.config.repair_steps {
                    let before = self.score();
                    let source = self.best.clone();
                    let diagnostic = strategies::select_diagnostic(
                        &self.evaluation.as_ref().unwrap().diagnostics,
                    );
                    let strategy = if self.config.profile == "uniform" || self.config.repair_uniform
                    {
                        "refinement.repair_plain_text"
                    } else if self.config.enhanced && step % 3 == 0 {
                        "counterexample"
                    } else {
                        strategies::repair(diagnostic, stalled)
                    };
                    let old_kind = diagnostic.map(|d| d.kind);
                    let failure_name = old_kind.map(|kind| kind.legacy_name()).unwrap_or("Other");
                    let old_count = self
                        .evaluation
                        .as_ref()
                        .unwrap()
                        .diagnostics
                        .iter()
                        .filter(|d| Some(d.kind) == old_kind)
                        .count();
                    let mut responded = false;
                    let count = if stalled > 0 {
                        self.config.repair_candidates.max(5)
                    } else {
                        self.config.repair_candidates
                    };
                    for index in 0..count {
                        self.candidate_name = Some(
                            if self.config.repair_uniform || self.config.profile == "uniform" {
                                format!("repair/repair-{step}-{index}.rs")
                            } else {
                                format!("repair/repair-{step}-{index}-{failure_name}.rs")
                            },
                        );
                        if !self.generated(strategy, "repair", phase, &source, true)? {
                            break;
                        }
                        responded = true;
                        if self.correct() {
                            return Ok(());
                        }
                        if let Some(candidate) = self.last_candidate.clone() {
                            let new_count = candidate
                                .evaluation
                                .diagnostics
                                .iter()
                                .filter(|d| Some(d.kind) == old_kind)
                                .count();
                            if new_count < old_count
                                && candidate.evaluation.score.good_repair(&before)
                            {
                                self.consider(&candidate, true);
                                break;
                            }
                        }
                    }
                    if !responded {
                        break;
                    }
                    if self.correct() {
                        return Ok(());
                    }
                    if self.score().rank() > before.rank() {
                        stalled = 0;
                    } else {
                        stalled += 1;
                    }
                    if stalled >= 3 {
                        self.houdini("repair_houdini")?;
                    }
                    if self.correct() {
                        return Ok(());
                    }
                }
            }
            fs::write(
                self.artifact_dir().join("final.rs"),
                annotated(&self.best, self.evaluation.as_ref().map(|e| e.score), true),
            )?;
            self.houdini("final_houdini")?;
            fs::write(
                self.artifact_dir().join("final-hdn.rs"),
                annotated(&self.best, self.evaluation.as_ref().map(|e| e.score), true),
            )?;
            self.snapshot_phase()?;
        }
        Ok(())
    }
    pub fn run(mut self) -> Result<Value> {
        self.save()?;
        if let Err(error) = self.run_inner() {
            self.log(format!("  error: {error:#}"))?;
            self.report["status"] = json!(if error
                .to_string()
                .contains("consecutive empty truncated outputs")
            {
                "output_truncated"
            } else if error.to_string().contains("budget exhausted") {
                "budget_exhausted"
            } else {
                "error"
            });
            self.report["error"] = json!(format!("{error:#}"));
            self.save()?;
            return self.finish();
        }
        if self.correct() {
            // A second full guard + verifier evaluation at the acceptance boundary.
            syntax::check(&self.original, &self.best)?;
            if self.verifications >= self.config.max_verifications {
                self.report["status"] = json!("budget_exhausted");
                self.save()?;
                return self.finish();
            }
            let final_eval = match self.verifier.code(&self.best) {
                Ok(eval) => eval,
                Err(error) => {
                    self.report["status"] = json!("error");
                    self.report["error"] = json!(error.to_string());
                    self.save()?;
                    return self.finish();
                }
            };
            self.verifications += 1;
            if final_eval.success {
                fs::write(self.artifact_dir().join("verified.rs"), &self.best)?;
                self.report["verified"] = json!(true);
                self.report["status"] = json!("verified");
            } else {
                self.report["status"] = json!("final_recheck_failed");
            }
            self.report["final_verification"] = json!(final_eval);
            self.evaluation = Some(final_eval);
        } else {
            self.report["status"] = json!("exhausted");
        }
        self.save()?;
        self.finish()
    }
}
