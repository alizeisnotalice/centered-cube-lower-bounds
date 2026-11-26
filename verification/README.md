# 复现

## 编译稿件

使用 TeX Live 或 MacTeX 的 XeLaTeX，含 CTeX、Fandol、Latin Modern、AMS、microtype 和 hyperref。

```sh
(cd paper/sqrt-log/source && latexmk -xelatex -interaction=nonstopmode -halt-on-error manuscript-zh.tex)
(cd paper/sqrt-log/source && latexmk -xelatex -interaction=nonstopmode -halt-on-error manuscript-en.tex)
(cd paper/sqrt/source && latexmk -xelatex -interaction=nonstopmode -halt-on-error paper.tex)
```

## 计算材料

在仓库根目录运行。第 45 轮的冻结回放使用原始源码快照，署名版在 `paper/sqrt/source/`。严格字节比较对 NumPy 版本和平台浮点差异敏感。

```sh
python3 -m pip install numpy==2.5.4 scipy==1.18.1
python3 verification/sqrt-log/verify_math.py
python3 verification/round045/verify_saved.py --output /tmp/centered-cube-round045-new.json
```

- [Rudin–Shapiro 稿检查结果](sqrt-log/release-check.json)包含 21 项有理数与有限网格一致性检查。
- [第 45 轮回放结果](round045-release-check.json)记录有限模型、参数回放和已冻结随机样本。各项适用范围见[原复现说明](round045/REPRODUCE.md)。

## Lean

```sh
(cd lean && lean -DwarningAsError=true LowerBounds.lean)
```

[代码](../lean/LowerBounds.lean)将 Rudin–Shapiro 稿主证明的舍入规则直接写成有理数取整命题，并复核平方根稿“常数与结论的范围”一节的常数比较。解析输入 $\pi<22/7$ 由论文使用。[公理报告](lean-axioms.txt)列出各条证明的依赖。
