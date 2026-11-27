# High-Dimensional Lower Bounds for the Centered Cubic Maximal Operator

[Square-root paper (English)](paper/sqrt/manuscript-en.pdf) · [Chinese](paper/sqrt/manuscript-zh.pdf) · [Rudin–Shapiro paper (English)](paper/sqrt-log/manuscript-en.pdf) · [Reproduction guide](verification/README.md) · [Citation](#citation)

Zhihao Zheng<sup>1</sup>, Haotian Tang<sup>2</sup>, and Yibo Peng<sup>2</sup>

<sup>1</sup> School of Physics and Astronomy, Beijing Normal University<br>
<sup>2</sup> School of Mathematical Sciences, Beijing Normal University

Let $C_n$ be the optimal weak-type $(1,1)$ constant of the centered Hardy–Littlewood maximal operator over axis-parallel cubes in $\mathbb R^n$ with Lebesgue measure. The two papers in this repository obtain lower bounds on $C_n$ using different constructions.

## Square-root lower bound

**A Square-Root Lower Bound for the Weak $(1,1)$ Constant of the Centered Cubic Maximal Operator**

**Abstract.** We study the centered Hardy–Littlewood maximal operator over axis-parallel cubes in $\mathbb R^n$ with Lebesgue measure. Aldaz proved that its optimal weak-type constant $C_n$ diverges with dimension. Aubrun gave lower bounds of order $(\log n)^{1-\varepsilon}$ for every $0<\varepsilon<1$, and Iakovlev and Strömberg proved a lower bound of order $n^{1/4}$. We obtain a square-root lower bound by constructing bounded, nonnegative, compactly supported test functions from periodically arranged finite-field peaks. A spectral correction flattens the normalized variance over a range of scales, and a Brownian crossing estimate controls local exceedances. [Aldaz](https://doi.org/10.4007/annals.2011.173.2.10) · [Aubrun](https://arxiv.org/abs/0902.4305) · [Iakovlev–Strömberg](https://doi.org/10.4310/MRL.2013.v20.n5.a7)

**Theorem.** For the optimal weak-type $(1,1)$ constant $C_n$ of this operator,

$$
\liminf_{n\to\infty}\frac{C_n}{\sqrt n}
\ge \frac{87}{220\sqrt{58\pi}}>\frac1{35}.
$$

The limit inferior ranges over all positive integer dimensions. In particular, $C_n\ge \sqrt n/35$ for every sufficiently large $n$.

[Full paper (English)](paper/sqrt/manuscript-en.pdf) · [Chinese](paper/sqrt/manuscript-zh.pdf) · [English LaTeX](paper/sqrt/source/manuscript-en.tex) · [Chinese LaTeX](paper/sqrt/source/paper.tex)

## Rudin–Shapiro lower bound

A tensor product of positive periodic densities built from Rudin–Shapiro sequences gives $C_n\ge c\sqrt n/\log n$ for every sufficiently large integer $n$, with an absolute constant $c>0$. [Full paper (Chinese)](paper/sqrt-log/manuscript-zh.pdf) · [English full text](paper/sqrt-log/manuscript-en.pdf) · [LaTeX source](paper/sqrt-log/source/)

## Reproduction

The reproduction guide covers manuscript builds and finite numerical checks. The Lean archive verifies selected lemmas for the Rudin–Shapiro construction, including partial-sum bounds, logarithmic remainders, and truncation. The analytical proofs appear in the two papers. [Reproduction guide](verification/README.md) · [Lean source and verification scope](lean/sqrt-log-20261127/)

## Citation

[v1.0.0](https://github.com/alizeisnotalice/centered-cube-lower-bounds/releases/tag/v1.0.0) archives both manuscripts. Use the BibTeX entry for the paper you cite. [Square-root paper](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt/citation.bib) · [Rudin–Shapiro paper](https://github.com/alizeisnotalice/centered-cube-lower-bounds/blob/v1.0.0/paper/sqrt-log/citation.bib)
