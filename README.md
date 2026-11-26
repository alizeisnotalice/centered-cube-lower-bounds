# 中心立方体极大算子的高维弱型下界

Two manuscripts on the weak $(1,1)$ constant of the centered cubic Hardy–Littlewood maximal operator.

设 $C_n$ 是 Lebesgue 测度下中心、轴平行立方体极大算子的最优弱型 $(1,1)$ 常数。两份稿件分别给出如下下界。

| 稿件 | 主结论与构造 | 阅读与引用 |
|---|---|---|
| $\sqrt n/\log n$ 下界 | 对充分大的整数 $n$，$C_n\ge c\sqrt n/\log n$，其中 $c>0$ 为绝对常数。构造使用 Rudin–Shapiro 序列和正周期密度张量积。 | [中文 PDF](paper/sqrt-log/manuscript-zh.pdf) · [English PDF](paper/sqrt-log/manuscript-en.pdf) · [LaTeX](paper/sqrt-log/source/) · [BibTeX](paper/sqrt-log/citation.bib) |
| $\sqrt n$ 下界 | $\liminf_{n\to\infty} C_n/\sqrt n\ge 87/(220\sqrt{58\pi})$。特别地，充分大维数下 $C_n\ge\sqrt n/35$。构造使用有限域标签、平坦方差与 Brownian 局部越阈估计。 | [中文 PDF](paper/sqrt/manuscript-zh.pdf) · [LaTeX](paper/sqrt/source/) · [BibTeX](paper/sqrt/citation.bib) |

## 作者

1. 郑之浩，北京师范大学物理与天文学院 2026 级本科生
2. 唐浩天，北京师范大学数学科学学院 2024 级本科生
3. 彭奕博，北京师范大学数学科学学院 2025 级本科生

## 复现与版本

[复现说明与结果](verification/README.md)给出编译命令、有限数值检查和 Lean 公理报告。Lean 验证有理数上的取整误差与显式常数比较。两份渐近下界的完整证明见各自论文。

首份稿件源于 2026 年 11 月 12 日修订稿。第二份稿件取自[第 45 轮的接受版快照](https://github.com/alizeisnotalice/Math-Research/tree/5b381aaa8b3b2a14778f8d644e91284e1f286ce9/centered-cube-lower-log/rounds/045)。[v1.0.0 发布页](https://github.com/alizeisnotalice/centered-cube-lower-bounds/releases/tag/v1.0.0)提供可引用的固定版本。
