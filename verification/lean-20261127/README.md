# Lean 构建与核验（2026-11-27）

对应提交基线 `bf9e6f5`；构建目标 `lean/`（`lake build`）。审计表见 `AUDIT.md`。

## 版本锁定

| 组件 | 版本 |
|---|---|
| Lean | `leanprover/lean4:v4.36.0`（`lean-toolchain`） |
| Mathlib | `v4.36.0`，提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`（`lean/lake-manifest.json`） |
| 平台 | macOS arm64（`arm64-apple-darwin24.6.0`） |

## 复现

在干净机器上（需要网络，首次约需拉取 Mathlib 与 olean 缓存）：

    cd lean
    lake exe cache get      # 拉取与 v4.36.0 对应的预编译 oleans
    lake build              # 构建 All 及其全部依赖模块

本机复用了同版本 Mathlib 的既有构建产物：`lean/.lake/packages` 是指向另一份
v4.36.0 检出的符号链接（`.lake/` 已被 `.gitignore` 排除，不进入提交）。因此本机的
`lake build` 只重新 elaboration 本仓库的 16 个模块，耗时约 2–3 分钟；数值见 `build.log`。
在干净机器上按上面两条命令执行即可得到同样的 olean，不需要这个符号链接。

## 干净检出复现

    ./verification/lean-20261127/clean-checkout.sh

脚本从本分支 `git clone` 到一个空目录，接上同版本 Mathlib（或 `lake exe cache get`）后执行
`lake build`。本次运行的输出存于 `clean-checkout.log`：`Build completed successfully
(7188 jobs)`，66 条公理诊断，0 次 `sorryAx`，耗时 17.4 秒（Mathlib 为同版本预编译产物，
未重新编译）。这确认提交的文件本身足以构建，不依赖工作区里的临时状态。

## 逐文件复核

    ./verification/lean-20261127/verify.sh

该脚本对每个模块执行 `lake env lean <file>.lean`（从源码重新 elaboration，而非读取缓存），
把 `#print axioms` 的输出写入 `axioms.txt`。

## 本轮结果

- `build.log`：`Build completed successfully (5608 jobs)`。
- `axioms.txt`：66 条 `#print axioms`，全部为 `[propext, Classical.choice, Quot.sound]`；
  `sorryAx` 出现 0 次。

`propext`、`Classical.choice`、`Quot.sound` 是 Lean/Mathlib 的标准公理，本文件原样列出，
未引入任何项目自设公理、`axiom` 声明或未审计的外部结果。

## 模块

| 文件 | 内容 |
|---|---|
| `LowerBounds.lean` | v1.0.0 起就在仓库中的有理数取整与常数比较（原样保留） |
| `Cubes.lean` | 冻结快照副本：方体测度、截断、弱型比、`sqrtLog_of_truncated_halo` |
| `LogTensor.lean` | 冻结快照副本：对数余项、张量阈值、Bonferroni 计数 |
| `RudinShapiro.lean` | 冻结快照副本：`P/Q` 递推、单位圆能量、`5√N` 前缀界 |
| `Model.lean` | 模型锁定：`C_n` 的上确界刻画、截断极大算子、`ℝ≥0∞ ↔ ℝ` 转换 |
| `Coefficients.lean` | `Rudin–Shapiro` 的系数展开、`±1` 性与前缀多项式 |
| `Trig.lean` | 整周期三角积分与 `∫cos cos = ½δ` 正交性 |
| `Abel.lean` | `rsPrefix`、Abel 求和、`15√K` 加权估计、`1/2 ≤ ρ_K ≤ 3/2` |
| `CosineForm.lean` | `ρ_K` 的余弦级数 |
| `Average.lean` | 余弦平均与正弦恒等式 |
| `Periodic.lean` | 周期性与一维箱质量 |
| `Variance.lean` | `S_t` 的均值与方差恒等式 |
| `RhoNormalise.lean` | 整周期复指数积分与 `∫ρ_K=1` |
| `SqrtLimit.lean` | `C_*`、`C_* > 1/35`、`h → liminf`、`liminf → √n/35` |
| `SqrtLogWiring.lean` | `HaloData` 结构与 `SqrtLogLowerBound` 的装配 |
| `All.lean` | 构建根，导入以上全部模块 |

`Cubes.lean`、`LogTensor.lean`、`RudinShapiro.lean` 与 `sqrt-log-20261127/` 中的冻结快照
逐字节相同，哈希见 `lean/REUSE.sha256`；快照目录本身未被修改。
