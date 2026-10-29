use crate::{
    model::Client,
    pipeline::{Config, Engine},
    verifier::Verifier,
};
use anyhow::{ensure, Context, Result};
use serde_json::{json, Value};
use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

pub struct Options {
    pub root: PathBuf,
    pub name: String,
    pub output: PathBuf,
    pub limit: Option<usize>,
    pub verify_only: bool,
    pub config: Config,
    pub verifier: Verifier,
    pub client: Option<Client>,
    pub replay: Vec<String>,
    pub replay_manifest: Option<PathBuf>,
}

pub fn suite_directory(name: &str) -> Option<&'static str> {
    match name.to_ascii_lowercase().as_str() {
        "clover" | "cloverbench" => Some("CloverBench"),
        "diffy" => Some("Diffy"),
        "mbpp" => Some("MBPP"),
        "misc" => Some("Misc"),
        _ => None,
    }
}
pub fn dataset_name(root: &Path) -> String {
    let folder = if root.file_name().is_some_and(|n| n == "unverified") {
        root.parent().unwrap_or(root)
    } else {
        root
    };
    let name = folder
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("benchmark")
        .to_ascii_lowercase();
    if name == "cloverbench" {
        "clover".into()
    } else {
        name
    }
}

fn discover(root: &Path) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    let suites = ["CloverBench", "Diffy", "MBPP", "Misc"];
    if suites.iter().any(|s| root.join(s).is_dir()) {
        for suite in suites {
            let path = root.join(suite).join("unverified");
            if path.is_dir() {
                files.extend(discover(&path)?);
            }
        }
    } else {
        for entry in
            fs::read_dir(root).with_context(|| format!("read benchmark root {}", root.display()))?
        {
            let p = entry?.path();
            if p.is_file() && p.extension().is_some_and(|e| e == "rs") {
                files.push(p);
            }
        }
    }
    files.sort();
    ensure!(!files.is_empty(), "no .rs benchmark tasks found");
    Ok(files)
}
pub fn run(options: Options) -> Result<Value> {
    let mut files = discover(&options.root)?;
    if let Some(limit) = options.limit {
        ensure!(limit > 0, "limit must be positive");
        files.truncate(limit);
    }
    fs::create_dir(&options.output).context("benchmark output must be a new directory")?;
    let start = Instant::now();
    let manifest: std::collections::BTreeMap<String, Vec<PathBuf>> = match &options.replay_manifest
    {
        Some(p) => serde_json::from_str(&fs::read_to_string(p)?)?,
        None => Default::default(),
    };
    let mode = if options.verify_only {
        "verify-only"
    } else if !options.replay.is_empty() || options.replay_manifest.is_some() {
        "replay"
    } else if options.client.is_none() {
        "local-only"
    } else {
        "live"
    };
    let mut summary = json!({"schema_version":2,"benchmark":options.name,"mode":mode,"total":files.len(),"config":options.config,"verifier":options.verifier.path,"model":options.client.as_ref().map(|c|&c.model),"tasks":[],"completed":false});
    let mut transport_failure: Option<String> = None;
    for (index, file) in files.iter().enumerate() {
        let relative = file.strip_prefix(&options.root).unwrap_or(file);
        let task_start = Instant::now();
        eprintln!("[{}/{}] {}", index + 1, files.len(), relative.display());
        let source = fs::read_to_string(file)?;
        let output_file = options.output.join(relative);
        let parent = output_file.parent().unwrap();
        fs::create_dir_all(parent)?;
        let stem = output_file.file_stem().unwrap().to_string_lossy();
        let task_dir = parent.join(format!("intermediate-1-{stem}"));
        let mut task = json!({"input":relative,"directory":task_dir.strip_prefix(&options.output)?,"verified":false});
        if options.verify_only {
            fs::create_dir(&task_dir)?;
            fs::write(task_dir.join("input.rs"), &source)?;
            match options.verifier.code(&source) {
                Ok(evaluation) => {
                    fs::write(
                        task_dir.join("final.rs"),
                        crate::pipeline::annotated(&source, Some(evaluation.score), true),
                    )?;
                    task["verified"] = json!(evaluation.success);
                    task["status"] = json!(if evaluation.process.timed_out {
                        "verifier_timeout"
                    } else if evaluation.success {
                        "verified_original"
                    } else if evaluation.score.compilation_error {
                        "compilation_error"
                    } else {
                        "verification_failed"
                    });
                    fs::write(
                        task_dir.join("evaluation.json"),
                        serde_json::to_vec_pretty(&evaluation)?,
                    )?;
                }
                Err(error) => {
                    task["status"] = json!("verifier_error");
                    task["error"] = json!(error.to_string());
                }
            }
        } else if let Some(error) = &transport_failure {
            task["directory"] = Value::Null;
            task["status"] = json!("blocked_api");
            task["error"] = json!(error);
        } else {
            let replay_sources = manifest
                .get(relative.to_string_lossy().as_ref())
                .or_else(|| {
                    // Selecting a suite changes the discovery root, while the shared
                    // manifest retains paths relative to the complete benchmark set.
                    let directory = file.parent()?;
                    if directory.file_name()? != "unverified" {
                        return None;
                    }
                    let suite = suite_directory(directory.parent()?.file_name()?.to_str()?)?;
                    let filename = file.file_name()?.to_str()?;
                    manifest.get(&format!("{suite}/unverified/{filename}"))
                });
            let responses = if options.replay_manifest.is_some() {
                replay_sources
                    .map(|paths| {
                        paths
                            .iter()
                            .map(fs::read_to_string)
                            .collect::<std::io::Result<Vec<_>>>()
                    })
                    .transpose()?
                    .unwrap_or_default()
            } else {
                options.replay.clone()
            };
            task["replay_sources"] = json!(replay_sources);
            let missing_replay = mode == "replay" && responses.is_empty();
            let engine = Engine::new(
                options.config.clone(),
                options.verifier.clone(),
                options.client.clone(),
                responses,
                task_dir.clone(),
                source,
            )?;
            let report = engine.with_legacy_output(output_file.clone()).run()?;
            if let Some(result) = report["result_file"].as_str() {
                task["result"] = json!(Path::new(result).strip_prefix(&options.output)?);
            }
            task["phases"] = report["phases"].clone();
            task["verified"] = report["verified"].clone();
            task["status"] = report["status"].clone();
            task["requests"] = report["requests"].clone();
            task["usage"] = report["usage"].clone();
            if missing_replay && task["verified"] != true {
                task["status"] = json!("missing_replay");
            }
            if let Some(error) = report["error"].as_str() {
                task["error"] = json!(error);
                if error.contains("API transport failed") {
                    transport_failure = Some(error.to_string());
                    task["status"] = json!("blocked_api");
                }
            }
        }
        if options.verify_only && task_dir.join("final.rs").is_file() {
            let final_path = output_file.with_file_name(format!(
                "1-{}",
                output_file.file_name().unwrap().to_string_lossy()
            ));
            if let Some(parent) = final_path.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(task_dir.join("final.rs"), &final_path)?;
            task["result"] = json!(final_path.strip_prefix(&options.output)?);
        }
        eprintln!(
            "[{}/{}] {}: {} ({:.2}s)",
            index + 1,
            files.len(),
            relative.display(),
            task["status"].as_str().unwrap_or("unknown"),
            task_start.elapsed().as_secs_f64()
        );
        summary["tasks"].as_array_mut().unwrap().push(task);
        update(&mut summary, start.elapsed().as_millis());
        write_results(&options.output, &summary)?;
    }
    summary["completed"] = json!(true);
    update(&mut summary, start.elapsed().as_millis());
    write_results(&options.output, &summary)?;
    Ok(summary)
}
fn write_results(output: &Path, summary: &Value) -> Result<()> {
    fs::write(
        output.join("summary.json"),
        serde_json::to_vec_pretty(summary)?,
    )?;
    fn field(value: &str) -> String {
        format!("\"{}\"", value.replace('"', "\"\""))
    }
    let mut csv =
        String::from("task,status,verified,requests,prompt_tokens,completion_tokens,error\n");
    for task in summary["tasks"].as_array().unwrap() {
        csv.push_str(&format!(
            "{},{},{},{},{},{},{}\n",
            field(task["input"].as_str().unwrap_or("")),
            field(task["status"].as_str().unwrap_or("")),
            task["verified"].as_bool().unwrap_or(false),
            task["requests"].as_u64().unwrap_or(0),
            task["usage"]["prompt_tokens"].as_u64().unwrap_or(0),
            task["usage"]["completion_tokens"].as_u64().unwrap_or(0),
            field(task["error"].as_str().unwrap_or(""))
        ));
    }
    fs::write(output.join("results.csv"), csv)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn results_escape_csv_fields_and_preserve_json() {
        let dir = tempfile::tempdir().unwrap();
        let summary = json!({"tasks":[{"input":"a,b.rs","status":"error","verified":false,"requests":1,"error":"HTTP \"bad\"\nnext"}]});
        write_results(dir.path(), &summary).unwrap();
        let csv = fs::read_to_string(dir.path().join("results.csv")).unwrap();
        assert!(csv.contains("\"a,b.rs\",\"error\",false,1,0,0,\"HTTP \"\"bad\"\"\nnext\""));
        assert_eq!(
            serde_json::from_str::<Value>(
                &fs::read_to_string(dir.path().join("summary.json")).unwrap()
            )
            .unwrap(),
            summary
        );
    }
}
fn update(summary: &mut Value, elapsed: u128) {
    let tasks = summary["tasks"].as_array().unwrap();
    let mut counts = std::collections::BTreeMap::<String, usize>::new();
    let mut verified = 0;
    for task in tasks {
        *counts
            .entry(task["status"].as_str().unwrap_or("unknown").to_string())
            .or_default() += 1;
        if task["verified"] == true {
            verified += 1;
        }
    }
    summary["processed"] = json!(tasks.len());
    summary["verified"] = json!(verified);
    summary["counts"] = json!(counts);
    summary["elapsed_ms"] = json!(elapsed);
}
