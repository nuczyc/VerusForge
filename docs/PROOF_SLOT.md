# 受限插槽回归接口

完整程序证明和 benchmark 请使用根目录 [README](../README.md) 中的 `synthesize`、`benchmark`。`prove` 是 Rust 实现的早期受限插槽接口，仅用于回归。

输入必须包含一个 `/* VERUSSEEK_PROOF */`，候选只能填写受限 `assert(expression);` 序列；插槽外文本保持不变。可选 `--kb` 使用词项检索，不需要 embedding 服务。

从仓库根目录运行，输出目录须不存在：

```bash
source scripts/env-rust-local.sh
cargo run --locked -p verusseek-rs -- prove rust/examples/input.rs \
  --kb rust/examples/kb.json --output-dir results/proof-slot-demo \
  --replay rust/examples/bad-proof.txt --replay rust/examples/good-proof.txt
```

该用例读取固定候选并调用真实 Verus，验证失败反馈与接受流程，不代表真实模型评测。输出包含 `report.json` 和通过验证后的 `verified.rs`。
