# 当前项目复核标注

Current release scope excludes `stat-learning-theory:slt-master`: **171 inputs across 16 batches**, with **81 aligned and 90 misaligned provisional labels**. Dated historical records below retain their original scope.


2026-11-16 按用户逐题确认，将 `stacks:STK-0B34-right` 从 `undetermined` 改为 `misaligned`：选定根只覆盖非 quasi-sober，遗漏原文非 T0 的独立结论（P），并推广了具体空间条件（A）。不以 sorry 判负，不合并同文件的未选定根。本轮 33 个待处理输入均已完成二分类标注。旧标签、论证和用户确认见 [标注记录](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/user-annotations-2026-11-16/STK-0B34-right.json)。

2026-11-16 按用户逐题确认，将 `stacks:STK-0B34-left` 从 `undetermined` 改为 `misaligned`：选定根只覆盖非 T0，遗漏原文非 quasi-sober 的独立结论（P），并推广了具体空间条件（A）。不以 sorry 判负，不合并同文件的未选定根。旧标签、论证和用户确认见 [标注记录](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/user-annotations-2026-11-16/STK-0B34-left.json)。

2026-11-16 按用户逐题确认，将 `stacks:STK-08ZR` 从 `undetermined` 改为 `misaligned`：原文 Hausdorff 前提被严格更弱的 R1Space 替换，适用范围扩大，按 A 类判负；局部紧致性概念对应，保留这是正确推广的说明。旧标签、论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/STK-08ZR.json)。

2026-11-16 按用户逐题确认，为 `imperial-flt:flt-c05` 新增 `aligned` 标签：有限阿代尔单位群、对角嵌入、左右双陪集关系、开放子群条件和有限性结论均与原文对应。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/flt-c05.json)。

2026-11-16 按用户逐题确认，为 `imperial-flt:flt-c04` 新增 `aligned` 标签：数域、有限维、中心除代数条件有原文上下文依据；Haar 核、全局单位嵌入、Hx 陪集方向和商拓扑对应。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/flt-c04.json)。

2026-11-16 按用户逐题确认，为 `imperial-flt:flt-c03` 新增 `aligned` 标签：有限维有理向量空间及自同构、实际标量扩张、阿代尔模拓扑和 Haar 因子归一化与原文对应；Borel 条件不增加实质范围限制。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/flt-c03.json)。

2026-11-16 按用户逐题确认，为 `imperial-flt:flt-c02` 新增 `aligned` 标签：FreyPackage 字段与原文定义对应，一对互素加费马方程可推出两两互素。按绑定 lemma 的存在性结论评价，保留声明未保证输出指数等于输入指数的范围说明。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/flt-c02.json)。

2026-11-16 按用户逐题确认，为 `imperial-flt:flt-c01` 新增 `misaligned` 标签：galoisRep 整体为数据占位，缺少与原文自然伽罗瓦作用的绑定，按对象不对齐判负；knownin1980s 的证明占位本身不作为判负依据。保留已确认的参数、曲线及不可约性对应。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/flt-c01.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-sheffer` 新增 `misaligned` 标签：独立原文允许空 magma，而 formal 的逆向构造要求 Inhabited；空载体满足等式却无法承载 BooleanAlgebra。按原文范围裁定，保留元数据摘要补写非空条件的范围说明。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-sheffer.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-obelix` 新增 `aligned` 标签：Facts 展开为同一 magma 满足 1491 且违反 65，与独立 blueprint 的 Obelix 非 Asterix 推论对应；具体初始部分解、closure 构造和失败见证均有绑定。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-obelix.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-law-coverage` 新增 `aligned` 标签：按已选定的覆盖性目标，运算次数≤4、一般 magma 上的语义等价及具体定律表对应；规范化在证明内部完成，Nat 仅编码变量名。不扩展到编号唯一性或完整蕴含图。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-law-coverage.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-greedy1729` 新增 `aligned` 标签：同一个 magma 满足 1729 并违反 817 的存在性、独立编号表中的等式及否定范围对应；根声明没有额外前提，扩张与链覆盖条件在证明内部处理。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-greedy1729.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-fullspectrum-1682` 新增 `aligned` 标签：各大小模型存在性、等式括号与分段构造对应；n=2 的模 2 加法及 n≤1 的投影覆盖小尺寸，额外 n=0 分支可无条件补出。按已选定的单律构造端点评价。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-fullspectrum-1682.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-fullspectrum-1482` 新增 `aligned` 标签：各正整数大小的模型存在性、等式括号与大部分取值为常量的显式构造对应；额外 n=0 分支可由空类型上的运算与全称等式无条件补出。按已选定的单律构造端点评价。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-fullspectrum-1482.json)。

2026-11-16 按用户逐题确认，为 `equational-theories:etp-endtoend` 新增 `aligned` 标签：4694 条律的全部有序对均返回检查通过的推导或反驳证据，并断言一般 magma 上的对应数学结论；具体证书、定律表和带证明的正负事实表均有绑定。按当前所选端点评价，不将背景统计或有限 magma 图纳入结论。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/etp-endtoend.json)。

2026-11-16 按用户逐题确认，为 `arklib:sumcheck-full-rbr-before` 新增 `misaligned` 标签：原文要求有限整环，before 连 IsDomain 也未要求，容许有零因子的 Z/4Z 等结构。判负依据为适用范围差异，不将此结构区分例声称为协议反例。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/sumcheck-full-rbr-before.json)。

2026-11-16 按用户逐题确认，为 `arklib:sumcheck-full-rbr-after` 新增 `misaligned` 标签：原文要求有限整环，formal 的有限交换半环加 IsDomain 仍容许没有加法逆元的布尔半环，适用范围扩大。此例区分参数域，不声称推翻概率界。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/sumcheck-full-rbr-after.json)。

2026-11-16 按用户逐题确认，为 `arklib:stir-rbr-withdrawn-before` 新增 `misaligned` 标签：参数条件使初始码率为 1，与非负距离严格小于 0 矛盾；误差输入量词、+s 的位置、folding 参数与首轮索引亦错配。不将矛盾前提下的条件定理声称为假。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/stir-rbr-withdrawn-before.json)。

2026-11-16 按用户逐题确认，为 `arklib:stir-proximity-before` 新增 `misaligned` 标签：无约束 GenFun 替代原文 r^j；F_5 上四点评价域的零生成器反例满足概率前提，却不存在要求的三点一致集合。反例、精确枚举结果和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/stir-proximity-before.json)。

2026-11-16 按用户逐题确认，为 `arklib:stir-proximity-after` 新增 `aligned` 标签：均匀随机幂组合、共享一致子集及两段误差公式对应；按原文含 1/ρ 的有定义参数域解释正次数条件。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/stir-proximity-after.json)。

2026-11-16 按用户逐题确认，为 `arklib:stir-main-withdrawn-before` 新增 `misaligned` 标签：域大小下界被改为上界，复杂度参数未绑定到存在协议，且渐近常数缺少统一性。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/stir-main-withdrawn-before.json)。

2026-11-16 按用户逐题确认，为 `arklib:kzg-function-binding-before` 新增 `misaligned` 标签：ARSDH 假设量化所有 Lean 攻击者，无界函数可恢复 τ 并以概率 1 成功，使 error<1 的前提不成立；同时缺少原文具体电路规模开销。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/kzg-function-binding-before.json)。

2026-11-16 按用户逐题确认，为 `arklib:kzg-function-binding-after` 新增 `misaligned` 标签：当前原文明确要求电路规模及具体归约开销，formal 仅表达抽象类上的概率界，并将归约属于该类作为 hAdv 前提，未建立所需资源保证。论证、参数核对和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/kzg-function-binding-after.json)。

2026-11-16 按用户逐题确认，为 `arklib:kzg-binding-reduction-before` 新增 `misaligned` 标签：原文要求的概率等式和效率结论仍未完整表达；确定性攻击者的区分例同样得到绑定概率 0、t-SDH 概率 1/(p-1)，不受 before 随机查询处理器的影响。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/kzg-binding-reduction-before.json)。

2026-11-16 按用户逐题确认，为 `arklib:kzg-binding-reduction-after` 新增 `misaligned` 标签：当前完整原文要求相等成功概率及少量运行时间开销，formal 仅表达单向概率界。归约忽略验证结果的具体例子得到绑定概率 0、t-SDH 概率 1/(p-1)，且缺少效率结论。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/kzg-binding-reduction-after.json)。

2026-11-16 按用户逐题确认，为 `arklib:kzg-binding-before` 新增 `misaligned` 标签：困难性假设量化所有 Lean 函数，而原文只考虑 PPT 攻击者；无界函数可恢复 trapdoor，使 error<1 时的前提不成立。论证和用户确认见 [标注记录](../reports/user-annotations-2026-11-16/kzg-binding-before.json)。

2026-11-16 用户查看完整 informal、formal 及详细复核后，为 `arklib:kzg-binding-after` 指定 `aligned` 标签。此前模型的 `undetermined` 建议及随机实验、攻击者类相关证据继续保留，本次没有新增等价证明或修改输入。用户决定见 [标注记录](../reports/user-annotations-2026-11-16/kzg-binding-after.json)，此前分析见 [复核记录](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/kzg-binding-after-recheck-2026-11-16/review.json)。

2026-11-16 按用户逐题确认，为 `apap:int-uniform-before` 新增 `misaligned` 标签：输入与 `int-sign-after` 完全相同，同样把统一 c 的存在量词放在 A、N 之后。输入一致性核对、论证和本题用户确认见 [复核记录](../reports/user-annotations-2026-11-16/int-uniform-before.json)。

2026-11-16 按用户逐题确认，为 `apap:int-uniform-after` 新增 `aligned` 标签：统一 c、指数符号及 1/12 幂对应，未使用的 C 可消去，端点可平移。双方共同的小 N 缺陷仍待来源修订，evaluation_eligible 保持 false。论证和用户确认见 [复核记录](../reports/user-annotations-2026-11-16/int-uniform-after.json)。

2026-11-16 按用户逐题确认，为 `apap:int-sign-before` 新增 `misaligned` 标签：formal 分母的负指数将衰减界变为增长界，单凭 A⊆range N 即满足结论；同时仍缺少独立于 A、N 的统一 c。论证和用户确认见 [复核记录](../reports/user-annotations-2026-11-16/int-sign-before.json)。

2026-11-16 按用户逐题确认，为 `apap:int-sign-after` 新增 `misaligned` 标签：原文要求统一 c>0，formal 在 A、N 及假设之后存在量化 c，允许常数依赖输入。两边共同存在的小 N 来源问题单独记录，端点平移差异不作为判负依据。论证和用户确认见 [复核记录](../reports/user-annotations-2026-11-16/int-sign-after.json)。

2026-11-16 按用户逐题确认，为 `apap:bohr-regular-before` 新增 `misaligned` 标签：同样存在 rank 错配，且 κ 的范围为 d/100，而非原文预期的 1/(100d)。Z/2 区分例在 before 的整个检查区间仍满足 formal，却违反原文。具体论证和用户确认见 [复核记录](../reports/user-annotations-2026-11-16/bohr-regular-before.json)。

2026-11-16 按用户逐题确认，为 `apap:bohr-regular-after` 新增 `misaligned` 标签：formal 的 rank 统计有限宽度字符，原文统计宽度小于 2 的字符；Z/2 上的区分例说明两种正则性不等价。输入、源码及技术状态保持不变。理由、精确算术核对和用户确认见 [复核记录](../reports/user-annotations-2026-11-16/bohr-regular-after.json)。

**当前 173 个版本化输入中，173 个有标签记录：91 misaligned、82 aligned、0 undetermined；另有 0 个尚无标签记录，二分类待处理合计 0 个。** 本次为用户确认的暂定标签，未升级为人类金标。以下为历史复核记录。

2026-11-06 合并 `origin/refactor/aml-preparation-layout-2026-11-05`（`a5590632`）后，迁入合并前已完成的 2026-11-05 复核。

**137 个项目：70 misaligned、67 aligned、0 undetermined。** 全部项目均有暂定二分类标签。

2026-11-09 按用户要求继续查仓库，在迁移后的 IEANTN 初始提交 `0885c4e7` 找到完整 Vinogradov bound、Eπ/Eπ′、π/π*/Li 的自然语言定义，为最后四项补入共同目标。两个 after 判 aligned，两个 before 判 misaligned：before 的分数指数均被自然数除法算成 0，π* before 还使用不同的计数函数。全文历史检索确认旧目标从入库起即为空，所以本次明确记录为后续来源的新绑定，不冒充恢复旧主注释。来源提交含 Claude Opus 5 协作署名；标签仍是模型暂定判断。完整来源、定义域约定、旧空输入和新哈希见 [review.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/vinogradov-target-search-2026-11-09/review.json)，具体数学区分见 [upstream-search.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/vinogradov-target-search-2026-11-09/upstream-search.json)。现有 Qwen 结果与其旧输入、标签快照保持原样。

2026-11-09 继续复核剩余 13 项：6 项改为 aligned，3 项改为 misaligned，4 个 Vinogradov 条目仍缺主陈述。PFR independent-blocks 两项和 StatsML 两项补入有独立来源的数学目标后重新绑定输入哈希；所有 formal 均未修改。逐项理由见 [decisions.csv](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/undetermined-review-2026-11-09/decisions.csv)，旧标签、旧 informal、输入变更和审查范围见 [review.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/undetermined-review-2026-11-09/review.json)。杜萨尔 after 按独立作者原文确认的主条件判 aligned，冲突括注登记为解释性笔误；immersion-after 按同修订明确使用的实有限维、n=∞ 映射判 aligned。Vaught coupled 的额外前提现已有新上游反例，核对冻结定义后判 misaligned，不声称 R1 本身被反驳。此前 Qwen 评测保留原始标签和输入快照。

2026-11-09 在恢复历史后，按用户要求并行复核全部 60 个待定项：28 项改为 aligned，19 项改为 misaligned，13 项保留待定并记录具体障碍。逐项结论见 [decisions.csv](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/pre-qwen-review-2026-11-09/decisions.csv)，完整旧记录、证据及复核见 [review.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/pre-qwen-review-2026-11-09/review.json)。KLN 两项从作者论文式 (4.17) 补入独立 informal 并重新绑定哈希；其余输入未变。此次判断仍是模型暂定标注，不是人类金标或新 Lean 编译认证。

2026-11-09 按用户要求，从 `d6a463a1` 的 `metadata/labels/` 恢复其余 84 项历史记录（9 misaligned、16 aligned、59 undetermined）。每项的项目标识、根声明和输入哈希均与当前版本一致；保留原判断及原因，不覆盖已有 53 项的较新复核，也不重新采用已被撤回的早期标签。恢复清单见 [history-restoration-2026-11-09.json](history-restoration-2026-11-09.json)。历史 `reports/...` 证据路径通过 `scripts/data/provenance.py` 解析。此次恢复不是新的语义认证；待定项不参与二分类准确率计分。

项目的 `status` 和 `index.csv` 已直接更新：初次迁移时将 11 个旧 undetermined 改为 misaligned；2026-11-09 按用户确认将 CAR-01-before、CAR-01-after、CAR-CTRL-02 和 CAR-CTRL-03 从 undetermined 改为 misaligned，同日按用户确认将 GCG24UserItemFairness-before 和 GCG24UserItemFairness-after-spec 改为 misaligned，原四批共 37 个负例；补回历史记录后共 46 个负例。原状态保存在 `historical_status`，编译/提取状态在 `technical_status` 与原技术字段中。所有标签仍为模型暂定判断，不是人类金标。

CAR-01-before 的新依据是全空间与球内 Lipschitz 范数导致消去性前提不等价；完整的 ℚ₂ 区分构造、精确算术核查和旧标签保存在 [2026-11-09 复核记录](../reports/carleson-review-2026-11-09/CAR-01-before.json)。该结论涉及适用条件，不宣称 formal 主结论为假，也不以尚未闭合的 toReal 问题判负。数学论证尚未编码为 Lean 机器验证证明。

CAR-01-after 经独立核对后也确认了该范数差异；完整区分构造与原标签保存在 [CAR-01-after 复核记录](../reports/carleson-review-2026-11-09/CAR-01-after.json)。其 hT 已直接使用 ENNReal，此次判负不涉及 toReal；数学论证尚未做 Lean 机器认证。

CAR-CTRL-02 和 CAR-CTRL-03 的新依据是消去测试函数类扩大：formal 要求球内 Lipschitz 范数有限、球外为零，原文要求全局 Lipschitz。固定 a=4、Θ={0,id} 和 d_B=2^18R 的实数轴模型满足原文消去条件，却被 formal 的开球指示函数测试排除。取零核（CTRL-03 再取常值 Q）可同时满足其余假设。详细推导及旧标签见 [CAR-CTRL-02](../reports/carleson-review-2026-11-09/CAR-CTRL-02.json) 和 [CAR-CTRL-03](../reports/carleson-review-2026-11-09/CAR-CTRL-03.json)。判定固定同一辅助度量，不排除另行重选度量的等价论证；尚未做 Lean 机器认证。CTRL-03 的全相位量词正确，此次判负不涉及 CAR-02 的量词问题。

GCG24UserItemFairness-after-spec 的新依据是人数与比例的桥接矛盾：canonicalReduction 使用整数人数权重，twoTypeReducedModel 使用 α、1−α，而 hred 要求结构严格相等，与 0<α<1 冲突。相关原始定义片段已在 Lean 4.12.0-rc1 独立验证，无 sorryAx；并非完整快照的编译认证，也不使用缺少后半区间的旧理由。原标签、证明代码与日志见 [2026-11-09 复核记录](../reports/applied-modeling-lib-review-2026-11-09/GCG24UserItemFairness-after-spec.json)。

GCG24UserItemFairness-before 的新依据同样是人数权重与比例权重混用：根定理 hred 将未归一化的人数与 α 严格等同，由第一类至少有一名用户及 α<1 得到矛盾，使 formal 前提无实例。定义位置、数学推导和旧标签见 [before 复核记录](../reports/applied-modeling-review-2026-11-09/GCG24UserItemFairness-before.json)。此判定不依赖前半区间的覆盖争议；本次 before 复核未做 Lean 编译认证，技术状态仍为 blocked。

GHW-theorem9_3_deterministic_truthful_lower_bound 经完整上下文复核改为 aligned：采用原稿 §2、§5.1 的匿名报价集合模型，并以原作者后续对早期结果的明确归属佐证；这不是从一般诚实性推出匿名性。固定报价 1 的派生机制将 formal 见证传回实际 min=1、max=H 的输入，保留 O(1/H) 和 F≥αH。模型解释、数学桥接与旧标签见 [2026-11-09 复核记录](../reports/applied-modeling-lib-review-2026-11-09/GHW-theorem9_3_deterministic_truthful_lower_bound.json)。本判定不覆盖任意身份定价的非匿名机制；桥接尚未做 Lean 机器认证。项目正标签对应现有状态词 ready，标签本身为 aligned。

标签文件保存具体原因与输入哈希；`status-changes.json` 保存状态变更。语义待定与技术受阻分别记录。GHW 9.1 经固定报价 1 的派生规则归约改为 aligned；SLT 经局部上确界的可积性及空球面分支归约改为 aligned，但其技术状态仍为 blocked。

上一轮 13 个待定项的原始记录保留在 [旧 unresolved.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/pre-qwen-review-2026-11-09/unresolved.json)。其中四个 Vinogradov 曾按用户要求暂时留空，旧检索和局部实现诊断仍保留在 [PNT 记录](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/undetermined-review-2026-11-09/pnt-decisions.json)。随后按用户指示扩大到迁移仓库，找到了可新绑定的完整来源；当前待定清单已为空，见 [unresolved.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/vinogradov-target-search-2026-11-09/unresolved.json)。

LG21 交叉引理等负例保留原审查口径：完整论文命题与局部引理的范围不匹配，不宣称引理本身错误。

迁移时恢复了相关已审查 informal 配对，核验其输入哈希与复核标签完全一致；Formal 源码未修改。

OpenAI/FLT/Kakeya 数据与活动标签已从主分支移除，完整旧版本保存在 `11_9_shenhao` 分支（`07e36bb64b0cff457694cfe9f1e156a3966a0dbc`）。当前记录覆盖全部 137 个项目。跨数据集的历史复核报告保留原文，供现有标签追溯；其中旧数据集的条目及汇总不属于当前 benchmark。

Stacks has five input-bound reviews after merging the two 0B34 components: 2 aligned, 3 misaligned and 0 undetermined. Current totals are 142 records (73 misaligned, 69 aligned, 0 undetermined); the dated 137-input review account above remains historical. See [Stacks admission](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/stacks-admission/README.md).

2026-11-12 按用户明确指示，将 STK-08ZR 从 undetermined 改为 misaligned：绑定原文要求 Hausdorff，而形式化使用更弱的 R1Space 假设，扩大了适用域，属于适用条件不匹配（A）。作者明确声明的推广不作为当前原文目标的精确对齐；该判断不否定推广定理的正确性。旧审核及用户指示保存在 [reviews.json](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/stacks-admission/reviews.json)。沿用已有用户确认标签的暂定记录格式；formal、informal 和输入哈希均未改变。

2026-11-12 的单根审核曾按用户指示将 STK-0B34-left 改为 misaligned，理由包含条件更弱（A）和只覆盖一半结论（P）；STK-0B34-right 当时仍为 undetermined。这些判断现作为历史记录保存在 [合并记录](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/stacks-admission/merges/STK-0B34.json)。

随后按用户指示合并为 STK-0B34：两个根声明共同绑定一条完整的原文 informal，作为一个样本审核。合并后的两条结论共同覆盖原文合取，因此撤回 P 理由；沿用用户确认的 formal 假设更弱这一 A 类差异，标签仍为 misaligned。原文正文和 formal 源码字节均保持不变，联合绑定生成新的输入哈希；其余 141 个输入哈希不变。旧条目、标签和技术证据均可从合并记录追溯。

2026-11-12 按用户明确指示，确认 STK-09Y5-before 为 misaligned：formal 的输入为普通有限集合划分，遗漏原文 Definition 09XZ 要求的各块局部闭条件，属于适用条件不匹配（A）。余有限拓扑反例支持该判断；已有 Lean 验证覆盖障碍，划分细化到该覆盖的桥接仍是数学论证，不声称已形式化旧根声明的完整否定。原标签本已是 misaligned，此次补充用户确认记录及具体理由；标签总数、formal、informal 和输入哈希均不变。

2026-11-12 按用户明确指示，确认 STK-09Y5-after 为 aligned：输入 LocallyClosedPartition 恢复原文 Definition 09XZ 要求的各块局部闭条件，输入有限性和 Noetherian 假设保留；输出类型保证各块局部闭，IsFiniteGoodRefinement 的 finite、refines、isGood 字段对应有限性、细化关系和 Definition 09Y0 的 frontier 条件。该标签确认陈述对齐，不表示原有 sorry 证明已经完成。原标签本已是 aligned，项目状态保持 ready；此次补充用户确认记录及具体理由，标签总数和输入哈希均不变。
