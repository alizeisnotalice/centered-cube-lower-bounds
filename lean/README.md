# Lean 构建目标

本目录是两篇中心立方体下界稿的 Lean 4 形式化工程（Lake 包）。
审计表与缺口清单见 [`../verification/lean-20261127/AUDIT.md`](../verification/lean-20261127/AUDIT.md)。

## 构建

    lake exe cache get
    lake build

`All.lean` 是构建根，导入全部模块；每个模块末尾的 `#print axioms` 会在 elaboration 时打印。
逐文件复核（从源码重新 elaboration 并保存报告）：

    ../verification/lean-20261127/verify.sh

## 目录

| 路径 | 说明 |
|---|---|
| `All.lean`、`lakefile.lean`、`lean-toolchain`、`lake-manifest.json` | 构建入口与版本锁定 |
| `Cubes.lean`、`LogTensor.lean`、`RudinShapiro.lean` | 2026-11-27 冻结快照的逐字节副本（哈希见 `REUSE.sha256`） |
| `Model.lean` | `C_n` 的定义与最小上界性质、截断极大算子、`ℝ≥0∞ ↔ ℝ` 转换 |
| `Coefficients.lean` | 系数族 `coef`、`P_q`/`Q_q` 的级数展开、系数 `±1`、前缀的多项式表示 |
| `Trig.lean` | 整周期三角积分：`∫₀¹cos(2πkx)`、`∫₀¹sin(2πkx)`、`∫₀¹cos²`、`∫₀¹cos cos = ½δ` |
| `Abel.lean` | Rudin–Shapiro 密度的 Abel 求和、`15√K` 估计、`1/2 ≤ ρ_K ≤ 3/2` |
| `CosineForm.lean` | `ρ_K` 的实余弦级数（式 (1.2)） |
| `Average.lean` | 余弦平均、`sin(π(K+l)r(t))` 恒等式、式 (3.1) 的完整装配（`integral_rho_shift`、`average_rho`） |
| `Kernel.lean` | `κ_K`、`l_{t,s}`、`lem:finite-kernel`（`8/K`） |
| `ClosedForm.lean` | 式 (3.5)：`D_K` 闭式与 `\|D_K\|` 模长公式 |
| `Window.lean` | `eq:window-bounds` 三式、`\|∑e^{4πit(1+l/K)}\|≤2`、`‖Y_t‖_∞≤5√8`（窗口） |
| `Dirichlet.lean` | `D_K`、`eq:exact-covariance`、`\|D_K\|≤1` |
| `Bounded.lean` | `S_t` 的指数分解、`sup\|S_t\|≤5√K`、`‖Y_t‖_∞≤5√8` |
| `Center.lean` | `V_K`、`σ_t`、`eq:center`（`V_K(K/4)=K/4`、`σ=1/(90πK)`）、`E d_t²=σ_t²` |
| `Product.lean` | 张量密度 `tensorRho`、`∫_{[-R,R]ⁿ}∏ρ_K=(2R)ⁿ`、`absMass` 质量 |
| `Periodic.lean` | `ρ_K` 的周期性与连续性、周期函数整区间积分、`∫_{-R}^{R}ρ_K = 2R` |
| `Variance.lean` | `S_t` 的余弦级数、`E S_t = 0`、`V_K(t) = ½∑sin²`、缩放步骤 |
| `RhoNormalise.lean` | 整周期复指数积分、`∫₀¹ρ_K = 1`（`lem:density` 第三式） |
| `SqrtLimit.lean` | 显式常数 `87/(220√(58π))`、`C_* > 1/35`、liminf 与「`√n/35`」的互推 |
| `SqrtLogWiring.lean` | `HaloData` ⇒ `SqrtLogLowerBound` 的装配 |
| `sqrt-log-20261127/` | 第一轮冻结快照（含原始 ZIP 与核验日志），**未改动** |

## 状态

两篇主定理**尚未**完整形式化。`Abel.lean`、`Model.lean`、`SqrtLimit.lean` 中不含 `sorry`，
也不含项目自设公理；`SqrtLogWiring.lean` 与 `SqrtLimit.liminf_sqrt_ge` 的结论是条件性的，
其前提（周期水平集的测度下界、`∀b<C_*` 的维数下界）在原稿中证明、在 Lean 中未接入，
逐条列在 `AUDIT.md` 的缺口清单里。
