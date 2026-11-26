群的左右商集差 · 证明与核验材料
BI1XLN 与 GPT-6.2 Astra，2026-11-26

阅读顺序
1. quotient-growth.tex 是《无限群的左右商集差》的中文稿源文件。
2. quotient-witness.tex 是《群的左右商集失衡具有统一的有限见证》的中文稿源文件。
3. cigler-logarithms.tex 是两条矩阵对数公式的独立附稿。三份稿件均可用 XeLaTeX 编译，使用 TeX Gyre Pagella 和 Windows 等线字体。

Lean 4.36.0
四份文件只依赖发行版自带的 Std，可在解压目录分别运行下列命令。
lean DihedralSix.lean
lean QuotientGrowthCore.lean
lean QuotientPairWeights.lean
lean QuotientWitnessCore.lean

DihedralSix.lean 在无限二面体群的整数半直积模型上，证明任意至多五个不同元素的集合两商集等势，并给出恰有六个元素、左右商集分别含 13 和 14 个元素的例子。其入口定理是 five_distinct_equal_cardinalities 和 six_is_sharp。
QuotientGrowthCore.lean 核验齐性子列上含单个索引的群词不可能恒等、两份平移的左右商集恒等式，以及计数公式蕴含无界增长。
QuotientPairWeights.lean 核验两个跨块方向出现重合时的有限权重计数。
QuotientWitnessCore.lean 核验共轭条件如何给出商集相等，并在明确传入分类、可定义性和紧致性的前提后验证统一见证的逻辑推论。
运行记录及所列定理的公理依赖见 lean-run.txt。一般无限群的增长定理、统一六元上界和显式有限界均在中文稿中给出完整书面论证。Ramsey 抽取、FC 群的标签选择和三块随机选取尚未全部形式化。

Python 3
python check_quotient_overlaps.py
python CiglerMatrixCheck.py

第一条命令直接构造两个二元块的全部左右跨块商。对置换群 S3、S4、S5、S6 逐对枚举，共检查 518940 对满足假设的元素。第二条命令用有理数从多项式的三项递推构造两族矩阵，直接取对数。每族共验证 160 个矩阵、35280 个元素。两个程序均仅使用 Python 标准库。
