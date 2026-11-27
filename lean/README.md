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
| `SqrtLimit.lean` | 显式常数 `87/(220√(58π))`、`C_* > 1/35`、liminf 与「`√n/35`」的互推 |
| `SqrtLogWiring.lean` | `HaloData` ⇒ `SqrtLogLowerBound` 的装配 |
| `sqrt-log-20261127/` | 第一轮冻结快照（含原始 ZIP 与核验日志），**未改动** |

## 状态

两篇主定理**尚未**完整形式化。`Abel.lean`、`Model.lean`、`SqrtLimit.lean` 中不含 `sorry`，
也不含项目自设公理；`SqrtLogWiring.lean` 与 `SqrtLimit.liminf_sqrt_ge` 的结论是条件性的，
其前提（周期水平集的测度下界、`∀b<C_*` 的维数下界）在原稿中证明、在 Lean 中未接入，
逐条列在 `AUDIT.md` 的缺口清单里。
