# 中心立方体极大算子下界的 Lean 阶段快照

2026 年 11 月 27 日。源码原样归档，对应 √n/log n 下界稿。

| 文件 | 已验证内容 |
|---|---|
| RudinShapiro.lean | 有限层 P、Q 多项式的递推、单位圆能量恒等式、5√N 截断界与 P 前缀的逐层稳定性。 |
| LogTensor.lean | 对数余项下界、有限张量积超过阈值的点态条件、Bonferroni 计数不等式。 |
| Cubes.lean | Lebesgue 方体体积、内外方体截断、弱型测试、边界因子。sqrtLog_of_truncated_halo 在给定测试函数质量与超水平集估计时推出所需数量级。 |

完整主定理仍待形式化。一致中偏差、尺度相关性和周期超水平集测度尚未接入。

## 复现

使用 Lean 4.36.0 和 Mathlib v4.36.0，Mathlib 提交为 fc4f59e577feb1a4956671bc04ac18aaaf8cd842。取得该版本后，在 Mathlib 根目录执行以下命令，其中 proof_dir 指向解压后的绝对路径。

    lake exe cache get
    for name in Cubes LogTensor RudinShapiro; do
      lake env lean "$proof_dir/$name.lean" || exit 1
    done

verification/ 保存本次实际运行的输出，本机绝对路径已缩短为文件名。三份文件均返回成功，13 条公理诊断均无 sorryAx。LogTensor.lean 保留一处未执行 tactic 的 lint 提示。
