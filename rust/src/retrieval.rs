use anyhow::{ensure, Context, Result};
use serde::Serialize;
use std::{collections::BTreeSet, fs, path::Path};

#[derive(Debug, Serialize)]
pub struct Hit {
    pub id: String,
    pub score: f64,
    pub document: String,
}
fn words(text: &str) -> BTreeSet<String> {
    text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .filter(|s| s.len() > 1)
        .map(str::to_lowercase)
        .collect()
}

/// Deterministic lexical retrieval; existing vector-store JSON is supported as
/// document storage, but vectors are not used or mislabelled as semantic search.
pub fn retrieve(path: Option<&Path>, query: &str, top_k: usize) -> Result<Vec<Hit>> {
    let Some(path) = path else {
        return Ok(Vec::new());
    };
    let value: serde_json::Value = serde_json::from_str(&fs::read_to_string(path)?)?;
    let entries = value
        .as_object()
        .context("knowledge base must be an object keyed by document ID")?;
    let query = words(query);
    let mut hits = Vec::new();
    for (id, item) in entries {
        let doc = item
            .get("document")
            .and_then(|v| v.as_str())
            .context("entry missing document text")?;
        ensure!(
            doc.len() <= 100_000,
            "knowledge base document too large: {id}"
        );
        let terms = words(doc);
        let union = query.union(&terms).count();
        let score = if union == 0 {
            0.0
        } else {
            query.intersection(&terms).count() as f64 / union as f64
        };
        hits.push(Hit {
            id: id.clone(),
            score,
            document: doc.to_string(),
        });
    }
    hits.sort_by(|a, b| b.score.total_cmp(&a.score).then(a.id.cmp(&b.id)));
    hits.truncate(top_k);
    Ok(hits)
}
