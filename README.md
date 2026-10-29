<div align="center">

# VerusSeek-RS

**Verifier-Guided Proof Synthesis for Rust**

自然语言生成 Rust · Verus 证明生成与修复 · 可复核的 Benchmark

![Rust](https://img.shields.io/badge/Rust-1.91-DEA584?logo=rust)
![Interface](https://img.shields.io/badge/Interface-CLI_%2F_TUI-5B8DEF)
![Verification](https://img.shields.io/badge/Verifier-Verus-45B8AC)
[![License](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

[功能亮点](#highlights) · [安装](#setup) · [使用](#usage) · [测试与评测](#evaluation) · [实现](#implementation) · [许可与来源](#license)

</div>

VerusSeek-RS 是使用 Rust 实现的 Verus 证明生成、修复与评测工具，面向 Rust 学习者、形式化验证研究者和开发者。输入自然语言需求或带规约的程序，工具生成候选、调用真实 Verus、根据错误反馈修复证明，并保存代码和运行记录。

项目基于 [VerusSeek](https://github.com/nuczyc/VerusSeek) 的证明策略开发 Rust 版本，新增交互式终端和自然语言开发入口。核心流程由 Rust 实现，无需 Python 运行时；当前主流程不使用检索增强。

<a id="highlights"></a>

## ✨ Highlights

- **自然语言到证明**：先生成普通 Rust 并编译，再补充 Verus 规约，交由同一证明管线验证和修复。
- **验证反馈驱动**：多轮候选生成、排序、合并、精化、Houdini 注解筛除与分类修复，成功后提前结束。
- **Rust 核心实现**：API 协议、AST 保留检查、候选调度、预算管理和进程控制均由 Rust 实现。
- **交互与自动化**：Ratatui 启动首页支持选择文件、任务和需求预览，Clap 子命令支持脚本运行。
- **过程可复核**：保存候选、验证诊断、Score / Safe 标记、CSV 和 JSON 汇总，区分在线实验与固定响应回放。

<a id="setup"></a>

## 📦 Setup

所有命令默认在仓库根目录执行。

| 依赖 | 要求与用途 |
| --- | --- |
| Rust / Cargo | 建议 Rust 1.91；TUI 依赖要求 Rust 1.88 或更新版本 |
| Verus | 安装与主机架构匹配的版本，设置 `VERUS_PATH` 或加入 `PATH` |
| Verus 所需 Rust 工具链、Z3、vstd | 按所用 Verus 发布包说明配置 |
| curl | 仅在线模型调用需要 |
| date | 默认结果目录的时间戳生成需要 |
| 模型 API | 仅在线生成需要，使用兼容的 Chat Completions 接口 |

已验证的开发环境：Linux ARM64、Rust 1.91.0、Verus `0.2026.01.02.6f52890`。其他平台尚未完整验证，仓库不附带 Verus 二进制。Verus 安装参考[官方仓库](https://github.com/verus-lang/verus)。

```bash
export VERUS_PATH=/absolute/path/to/verus
cargo build --locked -p verusseek-rs
cargo run --locked -p verusseek-rs -- --help
```

首次构建需要下载 Cargo 依赖；依赖准备好后可使用 `--offline`。本开发机可选执行 `source scripts/env-rust-local.sh` 复用本机工具链，该脚本不替代其他机器上的依赖安装。

<a id="usage"></a>

## ⚙️ Usage

所有命令在仓库根目录执行。可先通过下列命令查看各入口参数：

```bash
cargo run --locked -p verusseek-rs -- --help
cargo run --locked -p verusseek-rs -- benchmark --help
```

| 入口 | 输入 | 输出 |
| --- | --- | --- |
| Single File | 带 Verus 规约的 `.rs` 文件 | 证明候选、验证诊断与最终结果；也可仅验证 |
| Benchmark | Clover、Diffy、MBPP、Misc 或自定义目录 | 逐题结果、阶段候选、CSV 与 JSON 汇总 |
| Natural Language → Rust | 自然语言需求文件或命令行文本 | 普通 Rust、编译诊断、Verus 规约与证明结果 |

### 1. 运行最小证明用例

> [!TIP]
> 首次体验可从本用例开始：不需要 API 密钥，也不调用模型。

本用例覆盖程序读取、确定性循环不变量合成、真实 Verus 验证、边界检查和结果导出，不需要 API 密钥或模型网络访问。

输入 [rust/examples/count-input.rs](rust/examples/count-input.rs)：在 `n < 100` 条件下，从 `0` 循环计数到 `n`，要求返回值 `r == n`。原始输入缺少循环不变量。

```bash
# 输出目录必须尚不存在；重复运行时更换目录名
cargo run --locked -p verusseek-rs -- synthesize rust/examples/count-input.rs \
  --local-only --config rust/config.benchmark.json \
  --output-dir results/minimal-count
```

预期：终端先报告原始程序证明失败，随后 `deterministic_loop_synthesis` 生成不变量并通过验证；最后 JSON 包含 `"verified": true`，模型请求数 `requests` 为 `0`，命令退出码为 `0`。结果保存于 `results/minimal-count/`。

也可直接验证一个已有的正确程序：

```bash
cargo run --locked -p verusseek-rs -- verify examples/quickstart/smoke.rs
```

输入函数返回参数自身，规约要求 `y == x`。预期输出 `"verified": true`，退出码为 `0`。该命令不调用模型。

### 2. 打开交互式首页

```bash
cargo run --locked -p verusseek-rs
```

交互终端中打开启动首页，提供上述三个入口。↑↓ 选择、Enter 确认，Esc 返回，首页 Q 退出；文件通过目录浏览器选择，无需手动输入路径。执行时显示真实进度日志，完成后按 Enter 返回首页。管道或重定向环境下显示 CLI 帮助。

Natural Language → Rust 提供 NL2VBench 的四份原始需求：最大值下标、循环求最大值、计数返回和首次线性查找。选择 **Preview requirement** 或按 **P** 预览完整文本，Esc 返回；也可选择自己的 `.md` / `.txt` 文件。

### 3. 配置模型服务

在仓库根目录创建本地 `apikey` 文件，依次填写三行：API 密钥、API base URL、模型名称。文件已加入 `.gitignore`，不要提交凭据。也可通过 `--api-config PATH` 指定文件，或设置 `VERUSSEEK_API_KEY`、`VERUSSEEK_API_BASE`、`VERUSSEEK_MODEL` 环境变量。

### 4. 生成 Rust 与 Verus 证明

```bash
# 自然语言 → Rust → Verus 证明
cargo run --locked -p verusseek-rs -- develop \
  --request-file requirements/nl2vbench/DAFNY2VERUS-COLLECTION_1/description.txt \
  --attempts 3 --config rust/config.benchmark.json

# 仅预览需求，不读取凭据、不调用模型或验证器
cargo run --locked -p verusseek-rs -- develop \
  --request-file requirements/nl2vbench/DAFNY2VERUS-COLLECTION_1/description.txt --preview

# 为已有规约的程序生成证明；generate 是 synthesize 的别名
cargo run --locked -p verusseek-rs -- synthesize rust/examples/count-input.rs \
  --config rust/config.benchmark.json

# 小规模实时 benchmark
cargo run --locked -p verusseek-rs -- benchmark --name clover --limit 3
```

标准配置为 [rust/config.benchmark.json](rust/config.benchmark.json)：最多 3 个阶段，每阶段 3 轮生成、每轮请求最多 5 个候选；DeepSeek 接口适配为每轮 1 个候选。每题最多 96 次模型请求、512 次验证，输出额度固定为 8192 token；通过后提前结束。截断候选被丢弃，连续 3 次空截断停止该题，不自动提高 token 额度。自然语言入口的 `--attempts` 控制 Rust 生成和规约适配尝试，证明阶段仍受总体请求预算约束。

### 5. 查看输出

默认输出目录为 `results/YYYYMMDD-HHMMSS-benchmark名/`，自然语言任务使用后缀 `develop`；`--output-dir` 可指定新目录。

```text
results/YYYYMMDD-HHMMSS-clover/
├── 1-task.rs                  # 第一阶段结果，包含 Score / Safe 注释
├── 1-task.time                # 执行日志
├── intermediate-1-task/       # 各轮候选、合并、精化与修复文件
├── 2-task.rs                  # 前一阶段失败时继续生成
├── results.csv
└── summary.json
```

中间文件仅在对应步骤执行时创建。`summary.json` 保存逐题状态并指向最后阶段结果，失败任务也保留真实诊断和评分。

自然语言输出包含 `requirements.md`、`implementation.rs`、`contracts.json`、`rust/` 编译候选、`proof/verusseek/` 证明过程和 `report.json`。`verified.rs` 仅在最终验证与独立复验成功后生成；编译成功而证明失败不计为验证成功。

<a id="evaluation"></a>

## 🧪 Evaluation

```bash
export VERUS_PATH=/absolute/path/to/verus
cargo test --locked -p verusseek-rs

# 原始输入的验证基线，不调用模型
cargo run --locked -p verusseek-rs -- benchmark --verify-only \
  --output-dir results/baseline

# 固定响应回放，不调用模型；用于检查调度和修复流程
cargo run --locked -p verusseek-rs -- benchmark \
  --replay-manifest rust/benchmark-replay.json \
  --config rust/config.benchmark.json --output-dir results/replay

# 完整在线评测；可用 --name diffy / mbpp / misc 选择数据集
cargo run --locked -p verusseek-rs -- benchmark
```

默认评测集合为 CloverBench 11 题、Diffy 38 题、MBPP 78 题、Misc 23 题，共 150 题；`--root PATH` 支持自定义 `.rs` 目录。

2026-10-30 在上述 ARM64 环境执行回归测试：**48 项通过，1 项默认忽略**。覆盖自然语言到编译再到证明、AST 保留检查、候选批处理、合并、分类修复、Houdini、预算与截断控制、终端选择及真实 Verus 调用。默认忽略项需要本地 TCP 监听权限；未设置 `VERUS_PATH` 时部分集成测试会提前返回，因此复核时应显式设置该变量。

这些结果是工程回归验证，不是模型证明成功率。当前 README 不报告完整实时 150 题模型评测成绩。`live`、`replay`、`verify-only` 和 `local-only` 结果分别记录，不能混作同一实验；回放候选可能失败，不保证全题通过。实际评估应记录固定 commit、工具链、模型、配置、逐题通过数、调用量和耗时，以当次 `summary.json` 为准。

<a id="implementation"></a>

## 🦀 Implementation

自然语言开发先生成普通 Rust 并使用 `rustc` 检查，再补充 Verus 规约，交给已有证明管线生成和修复证明。编译检查不执行生成的程序。自然语言与生成规约是否一致仍需人工审查，验证通过表示程序满足所提交规约。

```text
自然语言 → 普通 Rust → rustc 编译 → 规约适配 ─┐
                                             ↓
带规约的 Rust / Verus ──────────────→ 候选生成与排序
                                             ↓
                                    合并 / 精化 / 分类修复
                                             ↕
                                      真实 Verus 验证
                                             ↓
                                    AST 边界检查与独立复验
                                             ↓
                                      结果文件与验证记录
```

Rust 在核心功能和可靠性边界中承担实质作用：

- 使用 `syn_verus` 解析和比较 AST，检查执行逻辑与规约保留边界，拒绝新增信任绕过或削弱原规约。
- 实现多轮候选生成、排序与不变量合并、Houdini 注解筛除、分类修复和跨阶段继承。
- 管理模型请求、验证次数、超时和错误状态；Unix 下验证超时会清理子进程组。
- 使用 Ratatui、Crossterm 和 Clap 实现终端交互与脚本命令，统一调用同一套核心逻辑。

模型负责生成候选，Verus 负责实际证明检查；HTTP 传输由外部 `curl` 执行，协议组装与响应解析由 Rust 完成。本工具不是对 Python 项目的 Rust 包装。

### 支持范围

当前自然语言入口支持标准类型的独立函数和导入，不支持任意 Cargo 工程、struct/trait/impl 或外部依赖。演示 `main` 可以保留在 `verus!` 外，验证范围为带规约的函数。AST 保留检查是保守的结构检查，不是语义等价证明；输入原有信任假设不会自动消除。结果中的 Safe 标记表示通过本工具的保留检查，不代表无条件安全认证。

### 项目结构与贡献

```text
rust/src/          CLI、TUI、自然语言开发、模型客户端与证明管线
rust/assets/       上游证明策略提示词
rust/vendor/       固定版本的 Verus 解析器及其许可证
rust/tests/        回归测试、测试配置与固定回放候选
benchmarks/        Verus-Bench 输入集合
examples/ lemmas/  证明策略使用的示例与 lemma
requirements/      自然语言任务及来源记录
scripts/           环境辅助与启动检查
```

提交修改前运行 `cargo fmt --all --check` 和 `cargo test --locked -p verusseek-rs`，涉及证明判定、AST 边界或进程控制的修改应附故障回归用例。提交中说明变更、验证命令及结果，不提交 API 凭据和生成缓存。开发历史由 Git 保留，评审版本应使用完整 commit ID 或固定标签；可通过 `git rev-parse HEAD` 获取当前版本，未提交修改不属于该 commit。

<a id="license"></a>

## 📄 License & Acknowledgments

本仓库保留 [MIT 许可证](LICENSE) 及原版权声明。第三方代码与数据遵循各自许可，项目许可证不构成对第三方数据的重新授权。

| 来源 | 复用范围与版本 |
| --- | --- |
| [VerusSeek](https://github.com/nuczyc/VerusSeek) | 上游基线 `291bbe72982a0527c209013384b6095a15f0ce49`；证明策略、提示词、示例、lemma、benchmark 和部分回放候选 |
| [Verus](https://github.com/verus-lang/verus) | `syn_verus` 源码基线 `142e202798538e782bc1ada3b300730a9d07fce9`；许可证见 `rust/vendor/syn_verus/LICENSE-MIT`、`LICENSE-APACHE`；本地补充显式生命周期标注 |
| [NL2VBench](https://github.com/Xidian-ICTT-GZ/NL2VBench) | 原始需求 `_1`、`_2`、`_3`、`_9`；固定版本与文件 SHA 见 [来源清单](requirements/nl2vbench/sources.json)，未导入参考证明；导入版本根目录未列出 LICENSE |
| Cargo 依赖 | 依赖及固定版本见 `rust/Cargo.toml` 和 `Cargo.lock`，遵循各包许可证 |

本次新增内容包括 Rust 原生证明管线、模型 API 适配、AST 保留检查、预算与进程管理、兼容阶段结构的评测输出、交互式终端，以及自然语言生成 Rust 后交由同一证明管线验证的流程。上游策略和数据不作为本次原创成果；旧版 Python、Web、Docker 和检索增强功能不属于当前交付范围。早期受限 `prove` 接口仅保留用于回归，说明见 [PROOF_SLOT](docs/PROOF_SLOT.md)。

### AI 使用与参赛材料

开发过程中使用 OpenAI Codex 辅助代码、文档和测试编写及问题排查。仓库记录的构建、自动化测试和运行输出可用于复核，不能替代参赛成员的人工审查；本文不声称团队已完成审查。提交前，参赛成员应实际审阅源码、复核运行结果和来源许可，并按真实情况补充审查人员、范围及方式。工具运行时调用的模型用于生成候选，模型回答本身不作为证明成功依据。

本 README 提供 [2026 年 Rust 软件原型开发竞赛](https://chinasoft.ccf.org.cn/2026/#competition/rust-prototype-competition) 所要求的仓库使用、设计、Rust 核心作用、最小运行用例、贡献方式与来源说明。报名表、中文参赛 PDF、固定评审版本及最终提交材料仍须按组委会要求另行准备；开发提交历史与实验结果须以真实记录为准。
