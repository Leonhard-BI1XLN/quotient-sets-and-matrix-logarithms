# 无限群的左右商集与两族矩阵的对数

**BI1XLN 和 GPT-6.2 Astra** · 2026 年 11 月 26 日

| 中文研究稿 | 主要结论 |
| --- | --- |
| [无限群的左右商集差](Quotient-growth-zh.pdf) | 在无限群中，若有一个有限集合的左右商集大小不同，则在至多含 $n$ 个元素的集合中，最大差值的绝对值随 $n$ 以平方阶增长。 |
| [群的左右商集失衡具有统一的有限见证](Uniform-quotient-witness-zh.pdf) | 每个无限不平衡群都有至多六元的失衡集合，无限二面体群说明六是最优值。对全体不平衡群，稿中给出的统一上界为 $2^{142}$。 |
| [两族系数矩阵的对数](Cigler-matrix-logarithms-zh.pdf) | 推导 Cigler 猜想 2、3 中的副对角线乘数，并追溯相关整数序列、迭代对数及 $q$ 指数恒等式。 |

对有限集合 $A$，两个商集分别为 $AA^{-1}=\{ab^{-1}:a,b\in A\}$ 和 $A^{-1}A=\{a^{-1}b:a,b\in A\}$。第一份研究稿讨论它们的大小能相差多少，第二份讨论最少检查几个元素就能发现差异。问题分别见 [Duvivier 等，第 5 问](https://math.colgate.edu/~integers/aap8/aap8.pdf#page=14) 和 [Herzog 等，2014](https://doi.org/10.1007/s13366-013-0141-y)。第三份稿件讨论的两个矩阵猜想见 [Cigler 原文，第 9、12 页](https://homepage.univie.ac.at/johann.cigler/preprints/q-pol.pdf)。

## 复核证明

[下载全部验证材料（ZIP）](Algebra-verification.zip?raw=true) · [浏览源码及 TeX 稿件](source/) · [Lean 运行记录](source/lean-run.txt)

四个 Lean 文件均已用 Lean 4.36.0 标准库编译通过。无限二面体群的五元下界与六元例子已完整形式化。其余文件检验一般群证明中的群词消去、平移恒等式、跨块权重及部分逻辑推论。一般群定理的完整论证见中文稿，其中 Ramsey 抽取、FC 群中的平移选取和六元上界的构造仍由书面证明给出。

在仓库根目录运行以下命令即可分别复核。两个 Python 脚本仅用标准库，分别核对 518,940 对置换和两族各 160 个矩阵。

```sh
lean -DwarningAsError=true source/DihedralSix.lean
lean -DwarningAsError=true source/QuotientGrowthCore.lean
lean -DwarningAsError=true source/QuotientPairWeights.lean
lean -DwarningAsError=true source/QuotientWitnessCore.lean
python source/check_quotient_overlaps.py
python source/CiglerMatrixCheck.py
```
