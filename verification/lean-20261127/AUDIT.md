# Lean 形式化审计（2026-11-27，第二轮）

本文件记录 `lean/` 下的构建目标与两篇下界稿的对应关系。**先说结论：两篇主定理都尚未完整形式化。**
本轮新增的是一批可独立核验、无 `sorry` 的定理，以及一份把缺口钉到具体命题的清单。

- 提交基线：`bf9e6f5`（工作树干净，`v1.0.0` 未改动）。
- 工具链：Lean `4.36.0`，Mathlib `v4.36.0`（`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`），见 `lean/lake-manifest.json`。
- 构建：`lake build`（目标 `All`），日志 `build.log`；公理报告 `axioms.txt`。
- 公理：51 条 `#print axioms` 全部只依赖 `[propext, Classical.choice, Quot.sound]`，`sorryAx` 计数 0。
- 复用：`lean/{Cubes,LogTensor,RudinShapiro}.lean` 是 `lean/sqrt-log-20261127/` 冻结快照的逐字节副本，哈希见 `lean/REUSE.sha256`；快照目录未改动。

## A. √n/log n 稿

| 论文命题（`paper/sqrt-log/source`） | Lean 声明 | 依赖 | 状态 |
|---|---|---|---|
| 模型：`M_n`、`C_n`（式 (1)） | `Cubes.maximal` / `Cubes.weakConstant` | — | 完整（快照） |
| 引理 `lem:transfer`：环面水平集 → `C_n ≥ λ m_n(E)(1-R⁻¹)ⁿ` | `Cubes.lower_bound_of_average_on_set`、`Cubes.truncation_retention`、`Cubes.halo_of_truncated_average` | `volume_cube` | **部分**：ℝⁿ 一侧完整；周期提升的测度恒等式 `\|π⁻¹(E) ∩ [-R+1,R-1]ⁿ\| = (2R-2)ⁿ m_n(E)` 未接入（缺口 G1） |
| 引理 `lem:rudin`：`\|∑_{l<N} ε_l z^l\| ≤ 5√N` | `RudinShapiro.prefix_bound`；`RudinDensity.rsPrefix_bound` | `prefixes_full`、`energy` | 完整（对递归前缀多项式） |
| 系数识别：`P_q(z)=∑_{j<2^q} ε_j z^j`，`Q_q` 同，且 `ε_j ∈ {±1}` | `RudinDensity.polys_coef`、`RudinDensity.coef_unit` | `coef`、`coef_succ_of_lt` | **完整**（本轮新增）：显式系数族 `coef`，两条递推分支 `coef_succ_of_lt/ge` |
| 前缀是多项式：`(prefixes z q n).1`、`.2` 均为 `∑_{j<n} c_j z^j`；`rsPrefix` 同 | `RudinDensity.prefixes_poly`、`self_prefix_poly`、`rsPrefix_poly` | `polys_coef` | **完整**（本轮新增） |
| 截断相容：`n ≤ 2^q` 时前缀就是 `P_q`、`Q_q` 的长度 `n` 截断，系数即 `coef q j` | `RudinDensity.prefixes_trunc` | `polys_coef`、`prefixes_poly` | **完整**（本轮新增） |
| 跨层稳定：`K ≥ N` 时 `rsPrefix z N = (prefixes z K N).1` | `RudinDensity.prefixes_stable_le` | `RudinShapiro.prefix_stable` | **完整**（本轮新增） |
| 加权和即论文级数：`weightedSum z K = ∑_{l<K} ε_l(1+l/K) z^l`，`ε_l=(coef K l).1∈{±1}` | `RudinDensity.rsPrefix_eq_coef`、`weightedSum_eq_series` | `prefixes_trunc`、`prefixes_stable_le`、`coef_unit` | **完整**（本轮新增） |
| 引理 `lem:density` 第一式：`sup_{\|z\|=1} \|∑_{l<K} ε_l(1+l/K)z^l\| ≤ 15√K` | `RudinDensity.weighted_bound` | `weightedSum_abel`、`rsPrefix_bound` | **完整**（本轮新增；Abel 求和，常数 10√K+5√K=15√K） |
| 引理 `lem:density` 第二式：`1/2 ≤ ρ_K ≤ 3/2` | `RudinDensity.rho_bounds` | `weighted_bound` | **完整**（本轮新增） |
| 引理 `lem:density` 第三式：`∫_T ρ_K dm_1 = 1` | `RudinDensity.integral_rho` | `integral_re_mul_zof_pow`、`weightedSum_eq_series`、`Trig` | **完整**（本轮新增）：所有频率为 `K+l ≥ 1`，逐项均值为零 |
| 式 `eq:variances` 的三角正交性：`∫₀¹cos(2πmx)cos(2πnx)dx = ½δ_{mn}` | `Trig.integral_cos_mul_cos_two_pi` | `Trig.integral_cos_two_pi_mul_int` | **完整**（本轮新增） |
| 式 `eq:variances`：`E S_t = E d_t = 0`，`V_K(t)`、`σ_t²` 恒等式 | — | `Trig` | **部分**：正交性底座已证；恒等式本身还需 `S_t` 的余弦级数（依赖 G2）并按 `Finset.sum` 展开，未接入（缺口 G3） |
| `eq:center`：`V_K(t_0)=K/4`、`σ_{t_0}=1/(90πK)` | — | — | 未接入（同上） |
| 引理 `lem:bounded`：`‖Y_t‖_∞ ≤ B=5√8` | — | — | 未接入（依赖 G2、G3） |
| 引理 `lem:finite-kernel`、`lem:continuous-kernel`、`lem:quadratic`、`lem:global` | — | — | 未接入（尺度协方差，依赖 G3） |
| 引理 `lem:md`：一致中偏差 | — | — | 未接入（缺口 G4） |
| 引理 `lem:rounding`、`lem:thresholds`、`lem:one-point`、`lem:two-point`、命题 `prop:sum`、`prop:conditions` | — | — | 未接入（缺口 G4/G5） |
| 定理 `thm:main`：`∃ c>0, ∃ n₀, ∀ n≥n₀, C_n ≥ c√n/log n` | `Cubes.SqrtLogLowerBound`；装配 `sqrtLogLowerBound_of_haloData` | `sqrtLog_of_truncated_halo` | **条件性**：由「每个充分大 `n` 都有 `HaloData n c`」推出 `SqrtLogLowerBound`，常数 `c e^{-5/2}/2`；`HaloData` 本身未构造 |

## B. √n 稿

| 论文命题（`paper/sqrt/source/paper.tex`） | Lean 声明 | 依赖 | 状态 |
|---|---|---|---|
| 式 `eq:definitionCn`：`C_n` 为上确界 | `Model.paperWeakConstant`、`Model.paperWeakConstant_eq`、`Model.weakConstant_le_iff`、`Model.le_weakConstant_iff`、`Model.exists_weakRatio_gt` | `Cubes.weakConstant` | **完整**（本轮新增）：上确界等于 `weakConstant`，并给出最小上界性质；含 `maximalTrunc_le_maximal`、`weakRatio_trunc_le` |
| 定理 `thm:main` 的数值部分：`C_* > 1/35` | `SqrtLimit.Cstar_gt_one_div_35` | `Real.pi_lt_d4` | **完整**（本轮新增）：`π<3.1416 ⇒ √(58π)<13.6 ⇒ 220√(58π)<3045=35·87` |
| 定理 `thm:main`：`liminf C_n/√n ≥ C_*` | `SqrtLimit.liminf_sqrt_ge` | `Model`、`le_liminf_iff` | **条件性**：由「`∀ b<C_*`，充分大 `n` 有 `b√n ≤ C_n`」推出 liminf；该前提未证 |
| 推论：「充分大 `n` 有 `C_n ≥ √n/35`」 | `SqrtLimit.sqrt_div_35_eventually`、`SqrtLimit.sqrt_div_35_of_liminf`（由 liminf 反向推出）、`SqrtLimit.sqrt_div_35_eventually_toReal` | `Cstar_gt_one_div_35` | **完整（相对于前提）**：量词覆盖所有 `n ≥ N`；`ℝ≥0∞` 与 `ℝ` 的转换显式给出（后者需 `C_n ≠ ∞`） |
| 引理 `lem:paperplateau`（正谱恒等式）、`lem:papersidon`（有限域标签存在） | — | — | 未接入（缺口 G6） |
| 引理 `lem:papercross`、`lem:paperkernel`、`lem:paperweighted`、`lem:paperpair`、`prop:paperallpairs` | — | — | 未接入（缺口 G6） |
| 引理 `lem:paperphysicalcount`、`lem:paperlocal`、`lem:paperpolyface`、`thm:paperwinner`（含奇异协方差） | — | — | 未接入（缺口 G6） |
| 引理 `lem:paperbrownian`、`lem:papermesh` | — | — | 未接入（缺口 G6） |
| 引理 `lem:paperpackets`、推论 `cor:paperwitness` | — | — | 未接入（缺口 G6） |

## 缺口清单（按「离闭合最近」排序）

- **G1（√n/log n，确定性，最小）** 周期提升的测度恒等式：对可测 `E ⊆ Tⁿ`，
  `\|π⁻¹(E) ∩ [-R+1,R-1]ⁿ\| = (2R-2)ⁿ m_n(E)`，以及 `‖ind_{[-R,R]ⁿ}·H̃_n‖₁ = (2R)ⁿ`。
  论文位置：`foundations.tex` 引理 `lem:transfer` 的证明；`main-proof.tex` 中 `‖f_n‖₁` 一段。
  形式化所需：`[0,1)ⁿ` 单位胞分解 + `volume_pi` 的可数可加，约 300–500 行。做完这一条，
  `lem:transfer` 与论文的 `‖f_n‖₁` 即可全部落地，`HaloData.mass` / `HaloData.volume_ge` 只剩概率输入。
- **G2（√n/log n，确定性）** 系数与级数。已证：`P_q`、`Q_q` 的系数是显式的 `±1` 族
  （`polys_coef` + `coef_unit`，`coef_succ_of_lt` 给出沿层的稳定性），且递归前缀都是多项式
  （`prefixes_poly`），且截断相容（`prefixes_trunc`）——即 `rsPrefix` 的系数就是 `coef`。
  已完成：`∫ρ_K=1`（`integral_rho`）。G2 **闭合**——`lem:density` 三式全部形式化。
- **G3（两稿共用）** 式 `eq:variances`：三角正交性 `∫₀¹cos(2πmx)cos(2πnx) dx = ½δ_{mn}` 已在
  `Trig.integral_cos_mul_cos_two_pi` 中证完（`m,n>0`）；余下是把 `S_t` 写成余弦级数后按 `Finset.sum`
  展开，故仍依赖 G2。
- **G4（√n/log n）** 引理 `lem:md` 的一致中偏差：指数倾斜、`ψ'''` 控制、Berry–Esseen、
  换测度与区间质量。这是该稿最重的一块，也是「不能用固定阈值 CLT 替代」的那一块。
- **G5（√n/log n）** 概率模型的装配：同一组 `U_1,…,U_n` 下的 `X_t`、`F_t`、`G_t`，
  网格单点/双点界与四区域求和、二阶 Bonferroni。依赖 G3、G4。
- **G6（√n）** 整条构造链：正谱补偿与平坦方差、有限域标签、协方差核（含奇异协方差的
  有限面比较）、局部越阈（倾斜 + 带漂移 Brownian 最大值 + 网格逼近）、安全删除后的段数与
  成对交集、有限质量 L¹ 见证。目前只有链尾（`C_*`、liminf 转换）落地。

## 本轮实际推进（按要求的三句式）

- **本轮证明的此前缺失命题**：`lem:density` 三式全部——`15√K` 加权估计、`1/2 ≤ ρ_K ≤ 3/2`、
  `∫ρ_K=1`；三角正交性 `∫₀¹cos cos = ½δ`；整周期复指数积分；Rudin–Shapiro 系数展开与 `±1` 性；
  `C_n` 作为上确界的模型锁定（含截断极大算子）；`C_* > 1/35`（实数域）；`h → liminf`、
  `liminf → √n/35` 两个方向的量词转换。
- **本轮接上的主定理依赖**：`sqrtLog_of_truncated_halo` 已接到 `SqrtLogLowerBound`
  （`sqrtLogLowerBound_of_haloData`）；`√n` 稿的「`∀b<C_*` 形式 ⇒ liminf ⇒ 推论」已闭合。
- **最小剩余缺口**：G1（周期提升测度恒等式）。它不是研究性缺口，但工作量最大；
  G2 次之。两篇主定理本身仍**未**形式化，不能用本轮结果替代。

## 未声称的内容

- 覆盖上界、单窗上界、强极大算子：本仓库与本轮工作均不涉及。
- 数值模拟、有限维测试、常数小数近似：均不作为证明步骤。
- 论文原文若有推导缺口，本文件只记录「未能形式化」，不代为修补，也不弱化目标。
