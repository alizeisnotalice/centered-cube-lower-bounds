# 中心立方体极大算子的高维弱型下界

设 $C_n$ 为 $\mathbb R^n$ 上关于 Lebesgue 测度的中心、轴平行立方体 Hardy–Littlewood 极大算子的最优弱型 $(1,1)$ 常数。

| 下界 | 主结论 | 构造 |
|---|---|---|
| $\sqrt n$ | $\liminf_{n\to\infty} C_n/\sqrt n\ge 87/(220\sqrt{58\pi})$。充分大维数下，$C_n\ge\sqrt n/35$。 | 有限域标签排列的周期窄峰与正谱补偿，结合局部 Brownian 越阈估计。 |
| $\sqrt n/\log n$ | 存在绝对常数 $c>0$，使充分大维数下 $C_n\ge c\sqrt n/\log n$。 | Rudin–Shapiro 序列与正周期密度的张量积。 |

## A Square-Root Lower Bound for the Weak $(1,1)$ Constant of the Centered Cubic Maximal Operator

Zhihao Zheng, Haotian Tang, and Yibo Peng

**Abstract.** We study the centered Hardy–Littlewood maximal operator over axis-parallel cubes in $\mathbb R^n$ with Lebesgue measure. For its optimal weak-type $(1,1)$ constant $C_n$, Aldaz proved divergence, Aubrun obtained lower bounds of order $(\log n)^{1-\varepsilon}$ for every $0<\varepsilon<1$, and Iakovlev and Strömberg proved an $n^{1/4}$ lower bound. We improve these bounds by proving $\liminf_{n\to\infty} C_n/\sqrt n\ge 87/(220\sqrt{58\pi})$. The proof constructs bounded, compactly supported, nonnegative test functions using periodic narrow peaks indexed by finite-field labels and a positive spectral correction that flattens the normalized variance over a range of scales. Exponential tilting and a Brownian crossing estimate control the local exceedance probabilities. [Aldaz (2011)](https://doi.org/10.4007/annals.2011.173.2.10) · [Aubrun (2009)](https://arxiv.org/abs/0902.4305) · [Iakovlev–Strömberg (2013)](https://doi.org/10.4310/MRL.2013.v20.n5.a7)

**Theorem.** Let $C_n$ be the least constant such that $\lambda\lvert\{x:M_nf(x)>\lambda\}\rvert\le C_n\lVert f\rVert_1$ for all $f\in L^1(\mathbb R^n)$ and $\lambda>0$, where $M_n$ takes the supremum of the Lebesgue averages of $\lvert f\rvert$ over axis-parallel cubes centered at $x$. Then
$$
\liminf_{n\to\infty}\frac{C_n}{\sqrt n}\ge \frac{87}{220\sqrt{58\pi}}>\frac1{35}.
$$
The limit inferior is taken over all positive integer dimensions. In particular, there exists an integer $n_0$ such that $C_n\ge\sqrt n/35$ for every $n\ge n_0$. The manuscript leaves $n_0$ unspecified.

## 从这里读／如何引用

引用时可使用对应稿件的 BibTeX，PDF 和条目均指向固定版本。[v1.0.0 发布页](https://github.com/alizeisnotalice/centered-cube-lower-bounds/releases/tag/v1.0.0)

| 稿件 | v1.0.0 PDF | v1.0.0 BibTeX |
|---|---|---|
| $\sqrt n$ | [中文全文](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt/manuscript-zh.pdf) | [平方根下界](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt/citation.bib) |
| $\sqrt n/\log n$ | [中文全文](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt-log/manuscript-zh.pdf) · [English full text](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt-log/manuscript-en.pdf) | [Rudin–Shapiro 下界](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt-log/citation.bib) |

## 作者

1. 郑之浩，北京师范大学物理与天文学院 2026 级本科生
2. 唐浩天，北京师范大学数学科学学院 2024 级本科生
3. 彭奕博，北京师范大学数学科学学院 2025 级本科生

## 复现与版本沿革

[复现说明与结果](verification/README.md)给出编译命令、有限数值检查和 Lean 公理报告。Lean 验证有理数上的取整误差与显式常数比较。两份渐近下界的完整证明见各自论文。

平方根下界稿件源于 2026 年 11 月 12 日修订稿。两份稿件均提供 LaTeX 源码。[平方根下界源码](paper/sqrt/source/) · [Rudin–Shapiro 下界源码](paper/sqrt-log/source/)

Rudin–Shapiro 下界稿件取自[第 45 轮的接受版快照](https://github.com/alizeisnotalice/Math-Research/tree/5b381aaa8b3b2a14778f8d644e91284e1f286ce9/centered-cube-lower-log/rounds/045)。

## Lean 阶段归档（2026 年 11 月 27 日）

对应 $\sqrt n/\log n$ 下界。[源码、核验日志和复现说明](lean/sqrt-log-20261127/) · [原始 ZIP](lean/sqrt-log-20261127/maximal-proof-snapshot.zip)

已核验的部分包括 Rudin–Shapiro 部分和界、对数余项与张量积阈值、Bonferroni 计数不等式、Lebesgue 方体截断，以及给定测试函数质量和超水平集估计后的下界推导。三份 Lean 文件通过检查，13 条公理诊断均无 `sorryAx`。

**完整主定理尚未形式化。** 一致中偏差、尺度相关性和周期超水平集测度仍待接入。本快照位于主分支，原有 `v1.0.0` 保持原版本。
