<div align="center">

# VerusForge

**Verifier-Guided Proof Synthesis for Rust**

自然语言生成 Rust · Verus 证明生成与修复 · 可复核的 Benchmark

![Rust](https://img.shields.io/badge/Rust-1.91-DEA584?logo=rust)
![Interface](https://img.shields.io/badge/Interface-CLI_%2F_TUI-5B8DEF)
![Verification](https://img.shields.io/badge/Verifier-Verus-45B8AC)
[![License](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

[功能亮点](#highlights) · [安装](#setup) · [使用](#usage) · [测试与评测](#evaluation) · [实现](#implementation)

</div>

VerusForge 是使用 Rust 实现的 Verus 证明生成、修复与评测工具，面向 Rust 学习者、形式化验证研究者和开发者。输入自然语言需求或带规约的程序，工具生成候选、调用真实 Verus、根据错误反馈修复证明，并保存代码和运行记录。

<a id="highlights"></a>

## ✨ Highlights

- **自然语言到证明**：先生成普通 Rust 并编译，再补充 Verus 规约，交由同一证明管线验证和修复。
- **验证反馈驱动**：多轮候选生成、排序、合并、精化、Houdini 注解筛除与分类修复，成功后提前结束。
- **Rust 核心实现**：API 协议、AST 保留检查、候选调度、预算管理和进程控制均由 Rust 实现。
- **交互与自动化**：Ratatui 启动首页支持选择文件、任务和需求预览，Clap 子命令支持脚本运行。
- **过程可复核**：保存候选、验证诊断、Score / Safe 标记、CSV 和 JSON 汇总。

<a id="setup"></a>

## 📦 Setup

### 🛠️ 本机安装

在仓库根目录执行，一键安装依赖、配置 Rust 和 Verus、构建并启动：

```bash
bash scripts/setup.sh --run
```

支持 Linux x86_64 / ARM64、macOS Intel / Apple Silicon；Windows 使用 WSL2。缺少系统依赖时使用 apt、dnf、pacman 或 Homebrew 安装，可能需要管理员密码。首次安装需要网络；macOS 需先安装 Homebrew 和 Xcode Command Line Tools。

脚本配置 Rust 1.91.0，优先复用 `VERUS_PATH` 或 PATH 中已有的 Verus，否则自动下载固定版本源码并构建匹配本机架构的 Verus、Z3 和 vstd。源码安装首次耗时较长，后续运行复用已有安装。下载与环境文件保存在 `.local/`，不修改 shell 启动配置。

```bash
# 只配置和构建，不启动页面
bash scripts/setup.sh

# 使用已安装的 Verus
bash scripts/setup.sh --verus /absolute/path/to/verus

# 后续启动；也可传入 benchmark、verify 等子命令
bash scripts/run.sh
bash scripts/run.sh benchmark --name clover --limit 3

# 使用下面的原始 Cargo 命令前加载环境
source scripts/env-rust-local.sh
```

模型生成仍需配置 API，见下文“配置模型服务”。一键配置的最后一步运行本地 Verus 用例，不需要 API 密钥。

<a id="usage"></a>

## ⚙️ Usage

所有命令在仓库根目录执行。可先通过下列命令查看各入口参数：

```bash
cargo run --locked -p verusforge -- --help
cargo run --locked -p verusforge -- benchmark --help
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
cargo run --locked -p verusforge -- synthesize rust/examples/count-input.rs \
  --local-only --config rust/config.benchmark.json \
  --output-dir results/minimal-count
```

预期：终端先报告原始程序证明失败，随后 `deterministic_loop_synthesis` 生成不变量并通过验证；最后 JSON 包含 `"verified": true`，模型请求数 `requests` 为 `0`，命令退出码为 `0`。结果保存于 `results/minimal-count/`。

也可直接验证一个已有的正确程序：

```bash
cargo run --locked -p verusforge -- verify examples/quickstart/smoke.rs
```

输入函数返回参数自身，规约要求 `y == x`。预期输出 `"verified": true`，退出码为 `0`。该命令不调用模型。

### 2. 打开交互式首页

```bash
cargo run --locked -p verusforge
```

交互终端中打开启动首页，提供上述三个入口。↑↓ 选择、Enter 确认，Esc 返回，首页 Q 退出；文件通过目录浏览器选择，无需手动输入路径。执行时显示真实进度日志，完成后按 Enter 返回首页。管道或重定向环境下显示 CLI 帮助。

Natural Language → Rust 提供 NL2VBench 的四份原始需求：最大值下标、循环求最大值、计数返回和首次线性查找。选择 **Preview requirement** 或按 **P** 预览完整文本，Esc 返回；也可选择自己的 `.md` / `.txt` 文件。

### 3. 配置模型服务

在仓库根目录创建本地 `apikey` 文件，依次填写三行：API 密钥、API base URL、模型名称。文件已加入 `.gitignore`，不要提交凭据。也可通过 `--api-config PATH` 指定文件，或设置 `VERUSFORGE_API_KEY`、`VERUSFORGE_API_BASE`、`VERUSFORGE_MODEL` 环境变量。

### 4. 生成 Rust 与 Verus 证明

```bash
# 自然语言 → Rust → Verus 证明
cargo run --locked -p verusforge -- develop \
  --request-file requirements/nl2vbench/DAFNY2VERUS-COLLECTION_1/description.txt \
  --attempts 3 --config rust/config.benchmark.json

# 仅预览需求，不读取凭据、不调用模型或验证器
cargo run --locked -p verusforge -- develop \
  --request-file requirements/nl2vbench/DAFNY2VERUS-COLLECTION_1/description.txt --preview

# 为已有规约的程序生成证明；generate 是 synthesize 的别名
cargo run --locked -p verusforge -- synthesize rust/examples/count-input.rs \
  --config rust/config.benchmark.json

# 小规模实时 benchmark
cargo run --locked -p verusforge -- benchmark --name clover --limit 3
```

标准配置为 [rust/config.benchmark.json](rust/config.benchmark.json)：最多 3 个阶段，每阶段 3 轮生成、每轮请求最多 5 个候选；DeepSeek 接口适配为每轮 1 个候选。每题最多 96 次模型请求、512 次验证，输出额度固定为 8192 token；通过后提前结束。截断候选被丢弃，连续 3 次空截断停止该题，不自动提高 token 额度。自然语言入口的 `--attempts` 控制 Rust 生成和规约适配尝试，证明阶段仍受总体请求预算约束。

### 5. 查看输出

仓库提供三份[运行结果展示](results/README.md)：

| 场景 | 结果 | 查看 |
| --- | --- | --- |
| Clover benchmark | 10 / 11 题验证通过 | [汇总](results/20261027-170046-clover/summary.json) |
| 单文件证明 | array_append_strong 验证通过 | [代码](results/20261029-230856-array_append_strong/verified.rs) |
| 自然语言开发 | Rust 编译与 Verus 验证通过 | [Rust](results/20261030-000407-develop/implementation.rs) · [Verus](results/20261030-000407-develop/verified.rs) |

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

自然语言输出包含 `requirements.md`、`implementation.rs`、`contracts.json`、`rust/` 编译候选、`proof/verusforge/` 证明过程和 `report.json`。`verified.rs` 仅在最终验证与独立复验成功后生成。

<a id="evaluation"></a>

## 🧪 Evaluation

```bash
export VERUS_PATH=/absolute/path/to/verus
cargo test --locked -p verusforge

# 原始输入的验证基线，不调用模型
cargo run --locked -p verusforge -- benchmark --verify-only \
  --output-dir results/baseline

# 固定响应回放，不调用模型；用于检查调度和修复流程
cargo run --locked -p verusforge -- benchmark \
  --replay-manifest rust/benchmark-replay.json \
  --config rust/config.benchmark.json --output-dir results/replay

# 完整在线评测；可用 --name diffy / mbpp / misc 选择数据集
cargo run --locked -p verusforge -- benchmark
```

默认评测集合为 CloverBench 11 题、Diffy 38 题、MBPP 78 题、Misc 23 题，共 150 题；`--root PATH` 支持自定义 `.rs` 目录。

<a id="implementation"></a>

## 🦀 Implementation

自然语言开发先生成普通 Rust 并使用 `rustc` 检查，再补充 Verus 规约，交给已有证明管线生成和修复证明。

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

模型负责生成候选，Verus 负责实际证明检查；HTTP 传输由外部 `curl` 执行，协议组装与响应解析由 Rust 完成。

### 支持范围

当前自然语言入口支持标准类型的独立函数和导入，不支持任意 Cargo 工程、struct/trait/impl 或外部依赖。演示 `main` 可以保留在 `verus!` 外，验证范围为带规约的函数。Safe 标记表示通过 AST 保留检查。

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
