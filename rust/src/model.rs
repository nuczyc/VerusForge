use anyhow::{ensure, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{fs, path::Path, process::Command};

#[derive(Clone)]
pub struct Client {
    pub base: String,
    pub model: String,
    key: String,
    pub timeout: u64,
    pub max_tokens: u32,
    pub temperature: f64,
}
pub struct Completion {
    pub code: String,
    pub truncated: bool,
}
pub struct Completions {
    pub choices: Vec<Completion>,
    pub usage: Usage,
}
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Usage {
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub requests: u64,
}
impl Usage {
    pub fn add(&mut self, other: &Self) {
        self.prompt_tokens += other.prompt_tokens;
        self.completion_tokens += other.completion_tokens;
        self.requests += other.requests;
    }
}
impl Client {
    pub fn load(
        path: Option<&Path>,
        timeout: u64,
        max_tokens: u32,
        temperature: f64,
    ) -> Result<Self> {
        // Resolve credentials in the application, without a shell/Python loader.
        let default_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../apikey");
        let local_file = Path::new("apikey");
        let use_env = ["VERUSSEEK_API_KEY", "VERUSSEEK_API_BASE", "VERUSSEEK_MODEL"]
            .iter()
            .all(|name| std::env::var(name).is_ok_and(|v| !v.trim().is_empty()));
        let path = path.or_else(|| {
            if use_env {
                None
            } else if local_file.is_file() {
                Some(local_file)
            } else if default_file.is_file() {
                Some(default_file.as_path())
            } else {
                None
            }
        });
        let fields = match path {
            Some(path) => {
                let content =
                    fs::read_to_string(path).context("read three-line API configuration")?;
                let fields: Vec<String> = content
                    .lines()
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .map(str::to_string)
                    .collect();
                ensure!(
                    fields.len() == 3,
                    "API file must contain key, base URL and model on three lines"
                );
                fields
            }
            None => vec![
                std::env::var("VERUSSEEK_API_KEY").context("missing VERUSSEEK_API_KEY")?,
                std::env::var("VERUSSEEK_API_BASE").context("missing VERUSSEEK_API_BASE")?,
                std::env::var("VERUSSEEK_MODEL").context("missing VERUSSEEK_MODEL")?,
            ],
        };
        ensure!(
            fields[1].starts_with("https://")
                || fields[1].starts_with("http://127.0.0.1:")
                || fields[1].starts_with("http://localhost:"),
            "API requires HTTPS or loopback HTTP"
        );
        ensure!(
            fields.iter().all(|f| !f.trim().is_empty()),
            "API key, URL and model must not be empty"
        );
        ensure!(
            !fields[0].contains(['\r', '\n', '"', '\\']),
            "invalid credential characters"
        );
        ensure!(
            !fields[1].contains(['\r', '\n', '"', '\\', '@', '?', '#']),
            "invalid API endpoint"
        );
        ensure!(
            (0.0..=2.0).contains(&temperature),
            "temperature must be 0..2"
        );
        Ok(Self {
            key: fields[0].clone(),
            base: fields[1].trim_end_matches('/').to_string(),
            model: fields[2].clone(),
            timeout,
            max_tokens,
            temperature,
        })
    }
    fn post(&self, resource: &str, body: Value) -> Result<Value> {
        let payload = tempfile::NamedTempFile::new()?;
        fs::write(payload.path(), serde_json::to_vec(&body)?)?;
        let secret = tempfile::NamedTempFile::new()?;
        fs::write(
            secret.path(),
            format!("header = \"Authorization: Bearer {}\"\n", self.key),
        )?;
        let output = crate::process::run(
            Command::new("curl")
                .arg("--disable")
                .arg("--config")
                .arg(secret.path())
                .args([
                    "--silent",
                    "--show-error",
                    "--fail",
                    "--connect-timeout",
                    "10",
                    "--max-time",
                    &self.timeout.to_string(),
                    "--header",
                    "Content-Type: application/json",
                    "--data-binary",
                ])
                .arg(format!("@{}", payload.path().display()))
                .arg(format!("{}/{resource}", self.base)),
            self.timeout + 2,
        )?;
        ensure!(output.exit_code==Some(0) && !output.timed_out,"API transport failed: curl exit {:?}, timeout {} (6=DNS, 7=connection, 22=HTTP, 28=timeout)",output.exit_code,output.timed_out);
        serde_json::from_str(&output.stdout).context("invalid API JSON response")
    }
    pub fn candidate_count(&self, requested: usize) -> usize {
        // Preserve the upstream provider adaptation: DeepSeek returns one choice per round.
        if self.model.to_ascii_lowercase().contains("deepseek") {
            1
        } else {
            requested
        }
    }
    fn completion_payload(&self, system: &str, prompt: &str, count: usize) -> Value {
        let mut payload = json!({"model":self.model,"temperature":self.temperature,
            "max_tokens":self.max_tokens,"n":self.candidate_count(count),
            "messages":[{"role":"system","content":system},{"role":"user","content":prompt}]});
        let model = self.model.to_ascii_lowercase();
        if model.contains("deepseek") && !model.contains("reasoner") {
            payload["thinking"] = json!({"type":"disabled"});
        }
        payload
    }
    pub fn complete(&self, system: &str, prompt: &str, count: usize) -> Result<Completions> {
        let value = self.post(
            "chat/completions",
            self.completion_payload(system, prompt, count),
        )?;
        let choices = value["choices"]
            .as_array()
            .context("missing model choices")?;
        ensure!(
            !choices.is_empty() && choices.len() <= self.candidate_count(count),
            "unexpected number of model choices"
        );
        let choices = choices
            .iter()
            .map(|choice| {
                let truncated = choice["finish_reason"] == "length";
                let content = choice["message"]["content"].as_str().unwrap_or("");
                ensure!(
                    truncated || !content.trim().is_empty(),
                    "missing or empty model response content"
                );
                Ok(Completion {
                    code: clean(content),
                    truncated,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Completions {
            choices,
            usage: Usage {
                requests: 1,
                prompt_tokens: value["usage"]["prompt_tokens"].as_u64().unwrap_or(0),
                completion_tokens: value["usage"]["completion_tokens"].as_u64().unwrap_or(0),
            },
        })
    }
}
pub fn clean(code: &str) -> String {
    let code = code.trim();
    if code.starts_with("```") {
        if let Some((_, body)) = code.split_once('\n') {
            if let Some((body, tail)) = body.rsplit_once("```") {
                if tail.trim().is_empty() {
                    return body.trim().to_string();
                }
            }
        }
    }
    code.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reads_three_line_configuration_without_exposing_key() {
        let file = tempfile::NamedTempFile::new().unwrap();
        fs::write(
            file.path(),
            "test-private-key\r\nhttps://example.test/v1/\r\ntest-model\r\n",
        )
        .unwrap();
        let client = Client::load(Some(file.path()), 30, 1024, 0.0).unwrap();
        assert_eq!(client.base, "https://example.test/v1");
        assert_eq!(client.model, "test-model");
        assert_eq!(client.key, "test-private-key");
        fs::write(file.path(), "test-private-key\nhttps://example.test/v1\n").unwrap();
        let error = Client::load(Some(file.path()), 30, 1024, 0.0)
            .err()
            .unwrap()
            .to_string();
        assert!(!error.contains("test-private-key"));
    }
}
