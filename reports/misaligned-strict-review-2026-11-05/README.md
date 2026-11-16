# Misaligned 严格复核（2026-11-05）

本轮逐项复核原有 **52** 个 `misaligned` 快照：**45 个确认保留，7 个撤回为 `undetermined`**。原有 4 个 Carleson 待定项未在本轮转正或转负。因此全库 554 个目标当前为 **45 misaligned、498 aligned、11 undetermined**；before/after 快照分别计数，不等于 554 个独立数学问题。

| 数据集 | 本轮审查 | 确认 misaligned | 本轮撤回 |
| --- | ---: | ---: | ---: |
| AppliedModelingLib | 22 | 18 | 4 |
| Carleson | 2 | 2 | 0 |
| CoarseDeGiorgi | 5 | 5 | 0 |
| Sphere-Packing | 6 | 6 | 0 |
| OpenAI | 4 | 2 | 2 |
| FLT | 7 | 7 | 0 |
| Kakeya | 6 | 5 | 1 |
| 合计 | 52 | 45 | 7 |

## 判定口径与局限

- 对此前未固定的 AML 配对，遵循用户明确选择的**完整论文命题**口径；条件性证明步骤缺少完整命题的覆盖，可构成范围不匹配。`LG21-T31-HIST` 原来仅有 pending 通知，本轮补入独立 Theorem 3.1 摘录并重新计算输入哈希，旧配对完整保存在 [pairing-change.json](pairing-change.json)。
- 冻结的 OpenAI/FLT/Kakeya 任务继续比较其**实际绑定的完整主描述**，不把 paper_context 擅自换成主配对。故有些负标签来自描述的附带解释，而主公式本身正确；下文明确区分。
- 核查目标类型、可达定义、量词、参数域、常数与对象绑定，并考虑对称性、换元、渐近阈值和常数吸收。仅“文本没写出某条件/结论”不足以判负。
- 本轮是模型的语义复核，不是人类金标、Lean 证明正确性认证或全项目编译。`human_adjudicated=false`、`reference_ready=false` 保持；技术 blocked 状态保留。语义不匹配不等于论文为假或 Lean 内核有问题。
- `undetermined` 表示负标签的证据不足，**不等于 aligned**。本轮没有重新审核其余 498 个 aligned。

## 标签落盘与证据

确认项写回对应 `references/*.jsonl` 的 `label`、`reason`、`review_report` 和复核状态。AML 的 4 个撤回项在原 references 中改为 `undetermined`，可编译的两项状态同步改为 undetermined；GCG 两项继续 blocked。

冻结评分协议只接受二分类标签，因此 GaussianReplacement 两项和 Frostman 一项从活动二分类 references 中移出，保存在本目录 [withdrawn.jsonl](withdrawn.jsonl)；输入任务仍保留，manifest 只更新 reference 数量及 reference 文件哈希。缺失标签不进入评分分母，没有修改评分代码以绕过校验。`withdrawn.jsonl` 同时保存全部 7 个撤回记录；统计时不要与 AML 活动 references 中的 4 项重复计数。

[before.json](before.json) 保存全部 52 项原记录；[review.json](review.json) 为本轮逐项决断。旧 source-review URL/graph hash 保留为历史来源，不冒称新输入的编译结果。输入中的 Lean 文件没有更改。

辅助来源：[前轮完整论文配对及精确 EOS 依赖证据](../undetermined-decisions-2026-11-05/review.txt)、[CDG-L94 定量核查](../undetermined-recheck-2026-11-03/README.md)、[FLT 历史详细证据](../flt-misaligned-review-2026-10-20/review.json)、[Sphere 历史审定记录](../misaligned-selection-2026-11-05/sphere-packing-historical-adjudication.json)。这些来源用于定位；本轮理由与撤回结论以下文为准。

## 逐项结论

### 01. PRPKG-P4-before — `misaligned`

目标：`PRPKG24AccuracyDiversity.PaperInterface.proposition4`。

**理由：** Proposition 4 的径向非恒定概率核未要求连续；Lean 把 Continuous p 作为前提，缩小了适用域。

**反向核查与边界：** 径向阶跃函数（半径小于 1 时 1/2，否则 3/4）说明值域与径向性不蕴涵连续。Γ 与球面 supremum 在连续、full support 条件下的 Laplace 联系不是判负理由；此处只判完整命题覆盖不足。

**证据定位：** Main.lean 中 theorem4/proposition4 附近（before 1841、after 1854）；论文 §3、Proposition 4；前轮报告有源文摘录。

[Formal](../../datasets/applied-modeling-lib/projects/PRPKG-P4-before/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/PRPKG-P4-before/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/PRPKG-P4-before/project.json)

### 02. PRPKG-P4-after — `misaligned`

目标：`PRPKG24AccuracyDiversity.PaperInterface.proposition4`。

**理由：** Proposition 4 的径向非恒定概率核未要求连续；Lean 把 Continuous p 作为前提，缩小了适用域。

**反向核查与边界：** 径向阶跃函数（半径小于 1 时 1/2，否则 3/4）说明值域与径向性不蕴涵连续。Γ 与球面 supremum 在连续、full support 条件下的 Laplace 联系不是判负理由；此处只判完整命题覆盖不足。

**证据定位：** Main.lean 中 theorem4/proposition4 附近（before 1841、after 1854）；论文 §3、Proposition 4；前轮报告有源文摘录。

[Formal](../../datasets/applied-modeling-lib/projects/PRPKG-P4-after/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/PRPKG-P4-after/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/PRPKG-P4-after/project.json)

### 03. LG21-T31-HIST — `misaligned`

目标：`LG21TestOptionalPolicies.PaperInterface.theorem3_1_optional_reporting`。

**理由：** 完整 Theorem 3.1 要求实际均衡的策略具有阈值并满足不公平结论；此根对每个抽象 e 构造 ∃W，却未把 W.takes/W.reports 绑定为 e 的真实行为。

**反向核查与边界：** 即使输出包含 fairness 公式，构造一个策略见证仍不等于刻画所有实际均衡。本轮补齐此前缺失的独立论文配对并更新输入哈希；不把 pending 通知当作论文命题。

**证据定位：** Main.lean:45 → dep/LG21TestOptionalPolicies/PostPaperAudit.lean:448 → ProofInterface.lean:22905；论文 Theorem 3.1。

[Formal](../../datasets/applied-modeling-lib/projects/LG21-T31-HIST/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/LG21-T31-HIST/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/LG21-T31-HIST/project.json)

### 04. GN21-SMALL-final_sign — `misaligned`

目标：`GN21DriverSurgePricing.PaperInterface.theorem3_small_surge_final_sign`。

**理由：** 完整 Theorem 3 同时规定分情形的最优结构与几乎处处唯一性；目标只是结构化正质量可测策略下的激励相容/符号结论，未给出完整唯一性及一般分支。

**反向核查与边界：** 条件性步骤可以正确；本轮依用户口径，不能以该步骤替代完整定理。只比较论文采用的可测策略域，不要求论文之外的任意策略。

**证据定位：** Main.lean:130/137/144 → dep/GN21DriverSurgePricing/Theorem3Frontier.lean:36/54/72；查 dynamicPositiveMassMeasurableIncentiveCompatible；论文 Theorem 3。

[Formal](../../datasets/applied-modeling-lib/projects/GN21-SMALL-final_sign/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GN21-SMALL-final_sign/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GN21-SMALL-final_sign/project.json)

### 05. GN21-SMALL-interval_final_sign — `misaligned`

目标：`GN21DriverSurgePricing.PaperInterface.theorem3_small_surge_interval_final_sign`。

**理由：** 完整 Theorem 3 同时规定分情形的最优结构与几乎处处唯一性；目标只是结构化正质量可测策略下的激励相容/符号结论，未给出完整唯一性及一般分支。

**反向核查与边界：** 条件性步骤可以正确；本轮依用户口径，不能以该步骤替代完整定理。只比较论文采用的可测策略域，不要求论文之外的任意策略。

**证据定位：** Main.lean:130/137/144 → dep/GN21DriverSurgePricing/Theorem3Frontier.lean:36/54/72；查 dynamicPositiveMassMeasurableIncentiveCompatible；论文 Theorem 3。

[Formal](../../datasets/applied-modeling-lib/projects/GN21-SMALL-interval_final_sign/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GN21-SMALL-interval_final_sign/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GN21-SMALL-interval_final_sign/project.json)

### 06. GN21-SMALL-mass_affine_interval_final_sign — `misaligned`

目标：`GN21DriverSurgePricing.PaperInterface.theorem3_small_surge_mass_affine_interval_final_sign`。

**理由：** 完整 Theorem 3 同时规定分情形的最优结构与几乎处处唯一性；目标只是结构化正质量可测策略下的激励相容/符号结论，未给出完整唯一性及一般分支。

**反向核查与边界：** 条件性步骤可以正确；本轮依用户口径，不能以该步骤替代完整定理。只比较论文采用的可测策略域，不要求论文之外的任意策略。

**证据定位：** Main.lean:130/137/144 → dep/GN21DriverSurgePricing/Theorem3Frontier.lean:36/54/72；查 dynamicPositiveMassMeasurableIncentiveCompatible；论文 Theorem 3。

[Formal](../../datasets/applied-modeling-lib/projects/GN21-SMALL-mass_affine_interval_final_sign/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GN21-SMALL-mass_affine_interval_final_sign/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GN21-SMALL-mass_affine_interval_final_sign/project.json)

### 07. GN21-CROSS — `misaligned`

目标：`GN21DriverSurgePricing.PaperInterface.theorem3_structured_measurable_ic_ae_unique_of_bracket_cross_fields`。

**理由：** 根的前提固定 C < ρ < 1，只覆盖 Theorem 3 的一个参数分支；完整论文命题还包含另一分支。

**反向核查与边界：** 此根已有唯一性结论，不能沿用 SMALL 条目的“缺唯一性”理由。判负依据仅为完整分支覆盖不足。

**证据定位：** Main.lean:104；依赖中 assumption/fixed_response 字段和 C、rho 条件；论文 Theorem 3。

[Formal](../../datasets/applied-modeling-lib/projects/GN21-CROSS/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GN21-CROSS/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GN21-CROSS/project.json)

### 08. LG21-report_required-threshold_equilibrium_exists_of_crossing — `misaligned`

目标：`LG21TestOptionalPolicies.paper_interface_theorem3_1_report_required_threshold_equilibrium_exists_of_crossing`。

**理由：** Lean 从连续性、严格单调性和交叉条件推出阈值均衡存在；完整 Theorem 3.1 要刻画每个实际均衡并给出公平性失败，根不包含这些结论。

**反向核查与边界：** 交叉存在性是合法证明步骤。判负取决于本轮明确固定的完整论文范围，而非否定中间引理。

**证据定位：** Main.lean:1802（required）/1736（optional）；论文 Theorem 3.1 及证明中的交叉步骤。

[Formal](../../datasets/applied-modeling-lib/projects/LG21-report_required-threshold_equilibrium_exists_of_crossing/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/LG21-report_required-threshold_equilibrium_exists_of_crossing/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/LG21-report_required-threshold_equilibrium_exists_of_crossing/project.json)

### 09. LG21-report_required-source_witness_of_base_crossings — `misaligned`

目标：`LG21TestOptionalPolicies.paper_interface_theorem3_1_report_required_source_witness_of_base_crossings`。

**理由：** 根从各 base 的交叉条件构造 ∃W；未将该见证绑定到所有实际均衡，也未给出 Theorem 3.1 的完整不公平结论。

**反向核查与边界：** source_witness 的名称不是实际均衡语义绑定；应审查结论中的量词及对象。即使只取对应 reporting 分支，也存在这个缺口。

**证据定位：** Main.lean:1827（required）/1762（optional）；论文 Theorem 3.1。

[Formal](../../datasets/applied-modeling-lib/projects/LG21-report_required-source_witness_of_base_crossings/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/LG21-report_required-source_witness_of_base_crossings/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/LG21-report_required-source_witness_of_base_crossings/project.json)

### 10. LG21-optional_reporting-threshold_equilibrium_exists_of_crossing — `misaligned`

目标：`LG21TestOptionalPolicies.paper_interface_theorem3_1_optional_reporting_threshold_equilibrium_exists_of_crossing`。

**理由：** Lean 从连续性、严格单调性和交叉条件推出阈值均衡存在；完整 Theorem 3.1 要刻画每个实际均衡并给出公平性失败，根不包含这些结论。

**反向核查与边界：** 交叉存在性是合法证明步骤。判负取决于本轮明确固定的完整论文范围，而非否定中间引理。

**证据定位：** Main.lean:1802（required）/1736（optional）；论文 Theorem 3.1 及证明中的交叉步骤。

[Formal](../../datasets/applied-modeling-lib/projects/LG21-optional_reporting-threshold_equilibrium_exists_of_crossing/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/LG21-optional_reporting-threshold_equilibrium_exists_of_crossing/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/LG21-optional_reporting-threshold_equilibrium_exists_of_crossing/project.json)

### 11. LG21-optional_reporting-source_witness_of_base_crossings — `misaligned`

目标：`LG21TestOptionalPolicies.paper_interface_theorem3_1_optional_reporting_source_witness_of_base_crossings`。

**理由：** 根从各 base 的交叉条件构造 ∃W；未将该见证绑定到所有实际均衡，也未给出 Theorem 3.1 的完整不公平结论。

**反向核查与边界：** source_witness 的名称不是实际均衡语义绑定；应审查结论中的量词及对象。即使只取对应 reporting 分支，也存在这个缺口。

**证据定位：** Main.lean:1827（required）/1762（optional）；论文 Theorem 3.1。

[Formal](../../datasets/applied-modeling-lib/projects/LG21-optional_reporting-source_witness_of_base_crossings/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/LG21-optional_reporting-source_witness_of_base_crossings/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/LG21-optional_reporting-source_witness_of_base_crossings/project.json)

### 12. EOS-lemma5_locally_envy_free_stable — `misaligned`

目标：`EOS07GSP.PaperInterface.lemma5_locally_envy_free_stable`。

**理由：** 论文稳定性是 assignment game 无阻挡对；Lean 的 StableAssignment 只有可行、个体理性和对已分配槽位的无获利偏离，遗漏未分配槽位的阻挡。

**反向核查与边界：** 所有槽位均未分配时，后三条件可以真空成立；若某 bidder-slot 配对有正价值，原 assignment game 仍有阻挡。该差异在定义层，不靠 theorem 名称或缺失依赖推断。

**证据定位：** dep/EOS07GSP/PostPaperAudit.lean:146；精确上游 Position.lean:77/82/244/279/334，见前轮 evidence（Git blob aa52281fc0087ceabdc75ab66409a57ab220331f）；作者稿 Lemma 1。

[Formal](../../datasets/applied-modeling-lib/projects/EOS-lemma5_locally_envy_free_stable/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/EOS-lemma5_locally_envy_free_stable/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/EOS-lemma5_locally_envy_free_stable/project.json)

### 13. EOS-lemma6_stable_assignment_slot_envy_free — `misaligned`

目标：`EOS07GSP.PaperInterface.lemma6_stable_assignment_slot_envy_free`。

**理由：** 原 Lemma 6（作者稿 Lemma 2）从稳定结果得到实现它的 locally envy-free GSP 均衡；Lean 只推出 SlotEnvyFree，没有存在 bids 和 GSP/Nash 实现的结论。

**反向核查与边界：** 结果的槽位无嫉妒性质不是拍卖机制能实现该结果的存在性；同时 StableAssignment 定义也存在前项所述缺口。

**证据定位：** dep/EOS07GSP/PostPaperAudit.lean:160；同一精确提交 Position.lean；作者稿 Lemma 2。

[Formal](../../datasets/applied-modeling-lib/projects/EOS-lemma6_stable_assignment_slot_envy_free/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/EOS-lemma6_stable_assignment_slot_envy_free/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/EOS-lemma6_stable_assignment_slot_envy_free/project.json)

### 14. EOS-theorem7_no_positive_transfer_conclusion — `misaligned`

目标：`EOS07GSP.PaperInterface.theorem7_no_positive_transfer_conclusion`。

**理由：** 完整 Theorem 7（作者稿 Theorem 1）涉及 GSP 均衡 B*、VCG 支付及稳定结果比较；根由 ComparisonPaymentCertificate 得到抽象 outcome，只在相同 slotOf、无正转移类内比较，未绑定 GSP 均衡。

**反向核查与边界：** 证书下的代数结果可以正确；缺少机制实现与完整比较域，不能替代原定理。编译依赖未补全，仍保持 blocked。

**证据定位：** dep/EOS07GSP/PostPaperAudit.lean:739；作者稿 Theorem 1；前轮 EOS 源文及 Position.lean 证据。

[Formal](../../datasets/applied-modeling-lib/projects/EOS-theorem7_no_positive_transfer_conclusion/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/EOS-theorem7_no_positive_transfer_conclusion/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/EOS-theorem7_no_positive_transfer_conclusion/project.json)

### 15. GHW-theorem9_1_bid_independent_lower_bound — `undetermined`

目标：`GHW01DigitalGoods.PaperInterface.theorem9_1_bid_independent_lower_bound`。

**理由：** 撤回旧负标签：lowCount 可为 0 确实使“实际最小出价等于 1”的直接解释有缺口，但根是存在量词；允许退化见证不证明不存在满足原文的替代见证。

**反向核查与边界：** 仍需核实原文 h=max/min 的规范化、自然数 highValue 对一般 h 的覆盖及见证修复。尚不能判 aligned，也不能仅凭缺 lowCount>0 确认 misaligned。

**证据定位：** Main.lean:1636；论文 §3 和 Theorem 9.1。

[Formal](../../datasets/applied-modeling-lib/projects/GHW-theorem9_1_bid_independent_lower_bound/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GHW-theorem9_1_bid_independent_lower_bound/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GHW-theorem9_1_bid_independent_lower_bound/project.json)

### 16. GHW-theorem9_3_deterministic_truthful_lower_bound — `undetermined`

目标：`GHW01DigitalGoods.PaperInterface.theorem9_3_deterministic_truthful_lower_bound`。

**理由：** 撤回旧负标签：focusedOutcome 强制匿名的 erased-bid-multiset 表示，但论文 §5.1 本身以从 bid sets 到 prices 的共同函数定义机制。旧理由未排除论文原本就在此模型内。

**反向核查与边界：** 非匿名的分 bidder 定价反例只有在论文允许该类机制时才有效；“arbitrary truthful auction”与前文模型范围之间仍须澄清。不能把模型解释争议写成已证实的不匹配。

**证据定位：** dep/GHW01DigitalGoods/AuctionMainTheorems.lean:13404；论文 §5.1、Lemma 9.2、Theorem 9.3。

[Formal](../../datasets/applied-modeling-lib/projects/GHW-theorem9_3_deterministic_truthful_lower_bound/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GHW-theorem9_3_deterministic_truthful_lower_bound/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GHW-theorem9_3_deterministic_truthful_lower_bound/project.json)

### 17. GCG24UserItemFairness-before — `undetermined`

目标：`GCG24UserItemFairness.PaperInterface.theorem3_price_decreases_first_half`。

**理由：** 撤回旧负标签：根仅陈述 α≤1/2 的单调性，但 opposing types 模型交换两类后对应 α↦1−α，可能由此恢复论文的另一半。

**反向核查与边界：** 缺少一个显式 conjunct 不足以判负。还需核对交换对 canonical reduction、priceOfFairness 和类型满射的保持，故本轮不直接改 aligned。

**证据定位：** Main.lean:1385（before）/474（after）；同文件 second_half spec:495；论文 Theorem 3 和 Appendix D。

[Formal](../../datasets/applied-modeling-lib/projects/GCG24UserItemFairness-before/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GCG24UserItemFairness-before/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GCG24UserItemFairness-before/project.json)

### 18. GCG24UserItemFairness-after-spec — `undetermined`

目标：`GCG24UserItemFairness.PaperInterface.theorem3_price_decreases_first_halfSpec`。

**理由：** 撤回旧负标签：根仅陈述 α≤1/2 的单调性，但 opposing types 模型交换两类后对应 α↦1−α，可能由此恢复论文的另一半。

**反向核查与边界：** 缺少一个显式 conjunct 不足以判负。还需核对交换对 canonical reduction、priceOfFairness 和类型满射的保持，故本轮不直接改 aligned。

**证据定位：** Main.lean:1385（before）/474（after）；同文件 second_half spec:495；论文 Theorem 3 和 Appendix D。

[Formal](../../datasets/applied-modeling-lib/projects/GCG24UserItemFairness-after-spec/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GCG24UserItemFairness-after-spec/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GCG24UserItemFairness-after-spec/project.json)

### 19. GJ19OptimalBinaryRatingSystems-before — `misaligned`

目标：`GJ19OptimalBinaryRatingSystems.PaperInterface.theorem31_source_matching_function_unique_value_argmax_lexicographic`。

**理由：** 根假设任意 limitingValue 的最优点及整个 cut : ℕ→ℝ 的唯一性；论文的有限分割目标既未绑定到该任意函数，也不区分有限端点之后的尾部。

**反向核查与边界：** feasible 仅要求 Monotone cut、cut 0=0、cut M=1。改变 M 之后的单调尾部不改变有限分割目标，却改变整个函数；因此若绑定为论文目标，hcut_value_unique 会要求不应有的唯一性。

**证据定位：** dep/GJ19OptimalBinaryRatingSystems/SourceTheorem31.lean:214–235；AppendixB.lean:8948–8953；论文 Theorem 3.1。

[Formal](../../datasets/applied-modeling-lib/projects/GJ19OptimalBinaryRatingSystems-before/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GJ19OptimalBinaryRatingSystems-before/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GJ19OptimalBinaryRatingSystems-before/project.json)

### 20. GJ19OptimalBinaryRatingSystems-after-spec — `misaligned`

目标：`GJ19OptimalBinaryRatingSystems.PaperInterface.theorem31_source_matching_function_unique_value_argmax_lexicographicSpec`。

**理由：** 根假设任意 limitingValue 的最优点及整个 cut : ℕ→ℝ 的唯一性；论文的有限分割目标既未绑定到该任意函数，也不区分有限端点之后的尾部。

**反向核查与边界：** feasible 仅要求 Monotone cut、cut 0=0、cut M=1。改变 M 之后的单调尾部不改变有限分割目标，却改变整个函数；因此若绑定为论文目标，hcut_value_unique 会要求不应有的唯一性。

**证据定位：** dep/GJ19OptimalBinaryRatingSystems/SourceTheorem31.lean:214–235；AppendixB.lean:8948–8953；论文 Theorem 3.1。

[Formal](../../datasets/applied-modeling-lib/projects/GJ19OptimalBinaryRatingSystems-after-spec/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GJ19OptimalBinaryRatingSystems-after-spec/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GJ19OptimalBinaryRatingSystems-after-spec/project.json)

### 21. LG21-GAUSSIAN-P42 — `misaligned`

目标：`LG21TestOptionalPolicies.paper_interface_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap`。

**理由：** Lean 假设条件输出律已经等于给定 Gaussian laws 且均值严格不同，再推出不公平；原 Proposition 4.2 从观测 access 与 Bayesian policy 得出此分布及不公平，根缺少这一模型到输出律的联系。

**反向核查与边界：** 高斯分布比较步骤本身可以正确；在完整命题口径下，尚未建立的模型结论不能作为前提替代。

**证据定位：** Main.lean:326；论文 Proposition 4.2；输出律/fairness 定义见本项目 dep。

[Formal](../../datasets/applied-modeling-lib/projects/LG21-GAUSSIAN-P42/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/LG21-GAUSSIAN-P42/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/LG21-GAUSSIAN-P42/project.json)

### 22. GS62-T2-before — `misaligned`

目标：`GS62CollegeAdmissions.PaperInterface.theorem2_applicant_optimality`。

**理由：** 形式结论是存在一个 applicant-optimal stable matching；绑定的原文婚姻特例要求给定 deferred-acceptance 程序产出的匹配具有此最优性。根没有算法输出绑定。

**反向核查与边界：** 存在最优匹配不刻画指定算法的输出。判负仅依当前明确冻结的 DA 语义范围，不将一般婚姻存在性命题误判为假。

**证据定位：** Main.lean:44（optimal 定义）/90（目标）；informal.jsonl 中完整配对。

[Formal](../../datasets/applied-modeling-lib/projects/GS62-T2-before/formal/Main.lean) · [主描述及来源](../../datasets/applied-modeling-lib/projects/GS62-T2-before/informal.jsonl) · [目标绑定](../../datasets/applied-modeling-lib/projects/GS62-T2-before/project.json)

### 23. CAR-02-before — `misaligned`

目标：`linearized_metric_carleson`。

**理由：** 蓝图假设对所有 phase θ 的算子范数控制；Lean 的 hT 只对隐式单个 θ 成立，却推出不含该 θ 的 linearizedCarleson 结论，量词范围不匹配。

**反向核查与边界：** 已比较 before 的 toReal 与 after 的 ENNReal 版本，核心 ∀θ 缺口均在。此判断是前提/作用域审查，不声称已构造或用 Lean 验证完整解析反例。

**证据定位：** Main.lean:20；绑定蓝图 linearized Carleson 命题及 hT。

[Formal](../../datasets/carleson/projects/CAR-02-before/formal/Main.lean) · [主描述及来源](../../datasets/carleson/projects/CAR-02-before/informal.jsonl) · [目标绑定](../../datasets/carleson/projects/CAR-02-before/project.json)

### 24. CAR-02-after — `misaligned`

目标：`linearized_metric_carleson`。

**理由：** 蓝图假设对所有 phase θ 的算子范数控制；Lean 的 hT 只对隐式单个 θ 成立，却推出不含该 θ 的 linearizedCarleson 结论，量词范围不匹配。

**反向核查与边界：** 已比较 before 的 toReal 与 after 的 ENNReal 版本，核心 ∀θ 缺口均在。此判断是前提/作用域审查，不声称已构造或用 Lean 验证完整解析反例。

**证据定位：** Main.lean:20；绑定蓝图 linearized Carleson 命题及 hT。

[Formal](../../datasets/carleson/projects/CAR-02-after/formal/Main.lean) · [主描述及来源](../../datasets/carleson/projects/CAR-02-after/informal.jsonl) · [目标绑定](../../datasets/carleson/projects/CAR-02-after/project.json)

### 25. CDG-D1 — `misaligned`

目标：`CoarseDeGiorgi.moment_bounds_lebesgue`。

**理由：** 固定配对的完整 Theorem D 包含 ∞ 端点；Lean 以实数 p,q>1 及有限指数公式建模，未表达 ∞ 端点分支。

**反向核查与边界：** D2 的有限平均不含相应最大值端点；D3 的 p/(p−1)>1 不含对偶指数 1。有限指数子命题可以正确，本标签说明完整定理覆盖不足。

**证据定位：** 各 Main.lean 的 p,q 类型/取值；论文 Theorem D(i)/(ii)/(iii)。

[Formal](../../datasets/coarse-degiorgi/projects/CDG-D1/formal/Main.lean) · [主描述及来源](../../datasets/coarse-degiorgi/projects/CDG-D1/informal.jsonl) · [目标绑定](../../datasets/coarse-degiorgi/projects/CDG-D1/project.json)

### 26. CDG-D2 — `misaligned`

目标：`CoarseDeGiorgi.moment_bounds_besov`。

**理由：** 固定配对的完整 Theorem D 包含 ∞ 端点；Lean 以实数 p,q>1 及有限指数公式建模，未表达 ∞ 端点分支。

**反向核查与边界：** D2 的有限平均不含相应最大值端点；D3 的 p/(p−1)>1 不含对偶指数 1。有限指数子命题可以正确，本标签说明完整定理覆盖不足。

**证据定位：** 各 Main.lean 的 p,q 类型/取值；论文 Theorem D(i)/(ii)/(iii)。

[Formal](../../datasets/coarse-degiorgi/projects/CDG-D2/formal/Main.lean) · [主描述及来源](../../datasets/coarse-degiorgi/projects/CDG-D2/informal.jsonl) · [目标绑定](../../datasets/coarse-degiorgi/projects/CDG-D2/project.json)

### 27. CDG-D3 — `misaligned`

目标：`CoarseDeGiorgi.moment_bounds_sobolev`。

**理由：** 固定配对的完整 Theorem D 包含 ∞ 端点；Lean 以实数 p,q>1 及有限指数公式建模，未表达 ∞ 端点分支。

**反向核查与边界：** D2 的有限平均不含相应最大值端点；D3 的 p/(p−1)>1 不含对偶指数 1。有限指数子命题可以正确，本标签说明完整定理覆盖不足。

**证据定位：** 各 Main.lean 的 p,q 类型/取值；论文 Theorem D(i)/(ii)/(iii)。

[Formal](../../datasets/coarse-degiorgi/projects/CDG-D3/formal/Main.lean) · [主描述及来源](../../datasets/coarse-degiorgi/projects/CDG-D3/informal.jsonl) · [目标绑定](../../datasets/coarse-degiorgi/projects/CDG-D3/project.json)

### 28. CDG-L41 — `misaligned`

目标：`CoarseDeGiorgi.LowerFractional.lower_auxAverage_norm_local`。

**理由：** 左端 auxAverage m k 实际使用边长 3^(1−k) 的后代单元，相当于论文 P_(k−1)；右端仍在第 k 层 triangulationIn 求和，层级不匹配。

**反向核查与边界：** 不能以统一 k↦k+1 消除：它会同时移动右端到第 k+1 层。结论不是单纯命名差异。

**证据定位：** Main.lean:15；Statements/AuxAverage.lean:17 及 Foundations/Reconstruction/Defs.lean 中 auxDescendantAverage、simplexCell。

[Formal](../../datasets/coarse-degiorgi/projects/CDG-L41/formal/Main.lean) · [主描述及来源](../../datasets/coarse-degiorgi/projects/CDG-L41/informal.jsonl) · [目标绑定](../../datasets/coarse-degiorgi/projects/CDG-L41/project.json)

### 29. CDG-L94 — `misaligned`

目标：`CoarseDeGiorgi.Harnack.Iterations.uniform_three_iterations_of_power_caccioppoli`。

**理由：** 按已固定的 Lemma 9.4 定量指数范围，Lean 的半径损失指数 γ6 与论文不同。d=3,p=10,q=2,s=1/100,t=3/10 时，γ6_paper=209/3，γ6_Lean=3005/42，相差 79/42。

**反向核查与边界：** 令 δ=ρ₂−ρ₁，额外 δ^(−79/42) 随 δ→0 无界，不能由与半径无关的乘法常数吸收。不以 hPowerCaccioppoli 这个证明步骤或起始矩的可重参数化单独判负；不排除另用更强估计重新证明原引理。

**证据定位：** 完整推导、参数条件和原文定位见 ../undetermined-recheck-2026-11-03/README.md 的 CDG-L94 追加审查。

[Formal](../../datasets/coarse-degiorgi/projects/CDG-L94/formal/Main.lean) · [主描述及来源](../../datasets/coarse-degiorgi/projects/CDG-L94/informal.jsonl) · [目标绑定](../../datasets/coarse-degiorgi/projects/CDG-L94/project.json)

### 30. flt.CuspForm_finiteDimensional_cuspForm — `misaligned`

目标：`CuspForm.finiteDimensional_cuspForm`。

**理由：** 有限维主结论匹配；但主描述的“that is”把 cuspidality 解释为所有 slash translates 在无穷处有界。CuspForm 要求趋于 0，有界是不同条件。

**反向核查与边界：** 经典 level-one E4 有界但常数项非零，是二者不同的例子。本标签针对完整描述内的错误定义，不是否定有限维定理。

**证据定位：** Main.lean 和绑定主描述；CuspForm.zero_at_infty 定义；既有 FLT review 第 1 项。

[Formal](../../datasets/flt/projects/flt.CuspForm_finiteDimensional_cuspForm/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.CuspForm_finiteDimensional_cuspForm/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.CuspForm_finiteDimensional_cuspForm/project.json)

### 31. flt.Deformation_TraceAlgebra_descends — `misaligned`

目标：`Deformation.TraceAlgebra.descends`。

**理由：** 主描述把 G 称为拓扑群；形式只要求 Group G 与 TopologicalSpace G，没有 IsTopologicalGroup，因而声明域更广。

**反向核查与边界：** 一个群上赋任意拓扑并不自动使群运算连续；连续表示假设也不迫使该性质成立（平凡表示即可说明）。这是对象域/术语不匹配，不声称表示论结论错误。

**证据定位：** 各 Main.lean 的 G 相关类型类；对应绑定主描述；既有 FLT review 第 2–4 项。

[Formal](../../datasets/flt/projects/flt.Deformation_TraceAlgebra_descends/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.Deformation_TraceAlgebra_descends/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.Deformation_TraceAlgebra_descends/project.json)

### 32. flt.Deformation_hom_ext_of_traceSubalgebra_eq_top — `misaligned`

目标：`Deformation.hom_ext_of_traceSubalgebra_eq_top`。

**理由：** 主描述把 G 称为拓扑群；形式只要求 Group G 与 TopologicalSpace G，没有 IsTopologicalGroup，因而声明域更广。

**反向核查与边界：** 一个群上赋任意拓扑并不自动使群运算连续；连续表示假设也不迫使该性质成立（平凡表示即可说明）。这是对象域/术语不匹配，不声称表示论结论错误。

**证据定位：** 各 Main.lean 的 G 相关类型类；对应绑定主描述；既有 FLT review 第 2–4 项。

[Formal](../../datasets/flt/projects/flt.Deformation_hom_ext_of_traceSubalgebra_eq_top/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.Deformation_hom_ext_of_traceSubalgebra_eq_top/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.Deformation_hom_ext_of_traceSubalgebra_eq_top/project.json)

### 33. flt.Deformation_isCorepresentable_conjQuotSubfunctor_of_descends — `misaligned`

目标：`Deformation.isCorepresentable_conjQuotSubfunctor_of_descends`。

**理由：** 主描述把 G 称为拓扑群；形式只要求 Group G 与 TopologicalSpace G，没有 IsTopologicalGroup，因而声明域更广。

**反向核查与边界：** 一个群上赋任意拓扑并不自动使群运算连续；连续表示假设也不迫使该性质成立（平凡表示即可说明）。这是对象域/术语不匹配，不声称表示论结论错误。

**证据定位：** 各 Main.lean 的 G 相关类型类；对应绑定主描述；既有 FLT review 第 2–4 项。

[Formal](../../datasets/flt/projects/flt.Deformation_isCorepresentable_conjQuotSubfunctor_of_descends/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.Deformation_isCorepresentable_conjQuotSubfunctor_of_descends/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.Deformation_isCorepresentable_conjQuotSubfunctor_of_descends/project.json)

### 34. flt.Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero — `misaligned`

目标：`Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero`。

**理由：** 数论主结论相符，但描述附带说明把任意二次多项式根都当作具有该多项式 trace/norm，并称平移后不被任何有理素数整除；可约情形不成立。

**反向核查与边界：** 取 t=1,q=0,p=5,a=2，判别式 1、g=6 满足相应数值条件；根 α=0 给出 α+a=2，显然可被 2 整除。标签针对额外解释，不是否定主不等式。

**证据定位：** 绑定主描述；既有 FLT review 第 5 项与 evidence。

[Formal](../../datasets/flt/projects/flt.Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero/project.json)

### 35. flt.Nat_exists_squarefree_sq_add — `misaligned`

目标：`Nat.exists_squarefree_sq_add`。

**理由：** 主命题 D≥1 与 Lean 相符；附带解释声称排除 D=0 是必要的，而 D=0,c=1 时 c²+D=1 仍 squarefree。

**反向核查与边界：** 反例仅推翻附带解释；不把正确的正 D 存在性主命题说成错误。

**证据定位：** 绑定主描述；既有 FLT review 第 6 项。

[Formal](../../datasets/flt/projects/flt.Nat_exists_squarefree_sq_add/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.Nat_exists_squarefree_sq_add/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.Nat_exists_squarefree_sq_add/project.json)

### 36. flt.WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero — `misaligned`

目标：`WeierstrassCurve.Affine.Point.eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero`。

**理由：** 主结论对已给定的 F-有理点成立；描述进一步把多项式在 F 中的根都解释为 F-有理点横坐标，遗漏 y 坐标存在于 F 的条件。

**反向核查与边界：** 在 Q 上 y²=x³+2，n=3 的除法多项式为 3x⁴+24x，x=0 是根，但 y²=2 在 Q 无解。

**证据定位：** 绑定主描述；既有 FLT review 第 7 项。

[Formal](../../datasets/flt/projects/flt.WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero/formal/Main.lean) · [主描述及来源](../../datasets/flt/projects/flt.WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero/informal.jsonl) · [目标绑定](../../datasets/flt/projects/flt.WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero/project.json)

### 37. kakeya.Kakeya.FrostmanEstimate.ball2_version_edUpToMult — `undetermined`

目标：`Kakeya.FrostmanEstimate.ball2_version_edUpToMult`。

**理由：** 撤回旧负标签：形式额外要求 M_cap+1≤δ^(−η)，但描述明确说 M_cap 是固定自然数。η>0 时，对每个固定 M_cap，该条件在 δ 足够小时自动满足。

**反向核查与边界：** 正式定理对随 δ 变化的允许重数还有统一性；需精确比较描述对阈值依赖的约定。不能仅凭多出这个前提确认不匹配，因此保守置为 undetermined。

**证据定位：** Main.lean:302–315；绑定描述的 fixed natural 和 eventually-small-scale 语境。

[Formal](../../datasets/kakeya/projects/kakeya.Kakeya.FrostmanEstimate.ball2_version_edUpToMult/formal/Main.lean) · [主描述及来源](../../datasets/kakeya/projects/kakeya.Kakeya.FrostmanEstimate.ball2_version_edUpToMult/informal.jsonl) · [目标绑定](../../datasets/kakeya/projects/kakeya.Kakeya.FrostmanEstimate.ball2_version_edUpToMult/project.json)

### 38. kakeya.Kakeya.ML2Reduction.rescaledCore_dist_ge — `misaligned`

目标：`Kakeya.ML2Reduction.rescaledCore_dist_ge`。

**理由：** 主距离下界一致；描述标题另称变换把距离精确缩短固定倍数，而实际还需将方向归一化，得到的是下界而非统一等式。

**反向核查与边界：** 归一化因子依赖原方向，不能把 inequality 解释为 exact scaling。此标签针对完整文字中的额外等式承诺。

**证据定位：** Main.lean:20；绑定主描述标题及正文。

[Formal](../../datasets/kakeya/projects/kakeya.Kakeya.ML2Reduction.rescaledCore_dist_ge/formal/Main.lean) · [主描述及来源](../../datasets/kakeya/projects/kakeya.Kakeya.ML2Reduction.rescaledCore_dist_ge/informal.jsonl) · [目标绑定](../../datasets/kakeya/projects/kakeya.Kakeya.ML2Reduction.rescaledCore_dist_ge/project.json)

### 39. kakeya.Kakeya.StickyKakeya.subStickyFrostmanLemma — `misaligned`

目标：`Kakeya.StickyKakeya.subStickyFrostmanLemma`。

**理由：** 主描述只有严格递减尺度等条件；Lean 明确要求相邻尺度满足 8ρ_(k+1)≤ρ_k，缩小允许的尺度链。

**反向核查与边界：** StrictAnti 本身不推出八倍间隔，例如相邻比值 1/2。其他定量前提还需同时检查，故不把这个尺度例子冒称满足全部 tube 假设的完整反模型；判负是描述遗漏实质前提。

**证据定位：** Main.lean:45 起的 hρ_sep/尺度条件；绑定主描述。

[Formal](../../datasets/kakeya/projects/kakeya.Kakeya.StickyKakeya.subStickyFrostmanLemma/formal/Main.lean) · [主描述及来源](../../datasets/kakeya/projects/kakeya.Kakeya.StickyKakeya.subStickyFrostmanLemma/informal.jsonl) · [目标绑定](../../datasets/kakeya/projects/kakeya.Kakeya.StickyKakeya.subStickyFrostmanLemma/project.json)

### 40. kakeya.ShadedBody.IsCRefinement.mul_multiplicity_le — `misaligned`

目标：`ShadedBody.IsCRefinement.mul_multiplicity_le`。

**理由：** 核心 c·μ≤μ′ 正确匹配；附带说明用 c⁻¹ 改写并称 c=0 时无条件真空成立，在 ENNReal 的 μ′=0 情形错误。

**反向核查与边界：** 取正测度单 shaded body，refinement 的 shading 为空，c=0。原式 0≤0 成立，但逆式 μ≤0⁻¹·0=∞·0=0 失败。

**证据定位：** Main.lean 的目标；dep/Multiplicity.lean 与 refinement 定义；绑定描述。

[Formal](../../datasets/kakeya/projects/kakeya.ShadedBody.IsCRefinement.mul_multiplicity_le/formal/Main.lean) · [主描述及来源](../../datasets/kakeya/projects/kakeya.ShadedBody.IsCRefinement.mul_multiplicity_le/informal.jsonl) · [目标绑定](../../datasets/kakeya/projects/kakeya.ShadedBody.IsCRefinement.mul_multiplicity_le/project.json)

### 41. kakeya.ShadedTube.exists_balanced_shadeRefinement_of_cover — `misaligned`

目标：`ShadedTube.exists_balanced_shadeRefinement_of_cover`。

**理由：** 描述给出每个 dyadic 分组上界 <2^(Pstar+1)；Lean 给出 <4·2^Pstar，较弱一倍。

**反向核查与边界：** 两者是冻结的明确数值，不是隐藏在 ≲ 中的任意常数。

**证据定位：** Main.lean:211 起；绑定主描述。

[Formal](../../datasets/kakeya/projects/kakeya.ShadedTube.exists_balanced_shadeRefinement_of_cover/formal/Main.lean) · [主描述及来源](../../datasets/kakeya/projects/kakeya.ShadedTube.exists_balanced_shadeRefinement_of_cover/informal.jsonl) · [目标绑定](../../datasets/kakeya/projects/kakeya.ShadedTube.exists_balanced_shadeRefinement_of_cover/project.json)

### 42. kakeya.Tube.exists_pruned_subset — `misaligned`

目标：`Tube.exists_pruned_subset`。

**理由：** 描述只承诺每个非空 fiber 大小 ≥1 且 <2N_k；Lean 承诺 N_k≤fiber size<2N_k，包含真正的同层可比性。

**反向核查与边界：** 仅有正性和可任选的大上界不足以表达同层 fiber 的二倍可比性；如大小 1 与 100 可满足前者，却不能共同满足后者。该例解释承诺的差异，不声称整个存在性定理为假。

**证据定位：** Main.lean 中目标 exists_pruned_subset；对照 N k 下界与绑定主描述。

[Formal](../../datasets/kakeya/projects/kakeya.Tube.exists_pruned_subset/formal/Main.lean) · [主描述及来源](../../datasets/kakeya/projects/kakeya.Tube.exists_pruned_subset/informal.jsonl) · [目标绑定](../../datasets/kakeya/projects/kakeya.Tube.exists_pruned_subset/project.json)

### 43. GaussianReplacement — `undetermined`

目标：`PaperLeanBench.GaussianReplacement.main`。

**理由：** 撤回旧负标签：Lean 使用 ∃d0,∀d≥d0，短描述未写 d0；但线性量级估计通常可能增大常数覆盖有限个小维度。摘要省略渐近阈值本身不足以判负。

**反向核查与边界：** 仍需核对小维度定义、熵控制及常数依赖；main 的“stated linear block cost”也未在描述内给出完整公式。未完成等价性核查，不能改 aligned。

**证据定位：** dep/HybridModel.lean:89；dep/FiberBlock.lean:105；两条冻结主描述。

[Formal](../../datasets/openai/projects/GaussianReplacement/formal/Main.lean) · [主描述及来源](../../datasets/openai/projects/GaussianReplacement/informal.jsonl) · [目标绑定](../../datasets/openai/projects/GaussianReplacement/project.json)

### 44. GaussianReplacement — `undetermined`

目标：`PaperLeanBench.GaussianReplacement.main_2`。

**理由：** 撤回旧负标签：Lean 使用 ∃d0,∀d≥d0，短描述未写 d0；但线性量级估计通常可能增大常数覆盖有限个小维度。摘要省略渐近阈值本身不足以判负。

**反向核查与边界：** 仍需核对小维度定义、熵控制及常数依赖；main 的“stated linear block cost”也未在描述内给出完整公式。未完成等价性核查，不能改 aligned。

**证据定位：** dep/HybridModel.lean:89；dep/FiberBlock.lean:105；两条冻结主描述。

[Formal](../../datasets/openai/projects/GaussianReplacement/formal/Main.lean) · [主描述及来源](../../datasets/openai/projects/GaussianReplacement/informal.jsonl) · [目标绑定](../../datasets/openai/projects/GaussianReplacement/project.json)

### 45. Laughlin — `misaligned`

目标：`PaperLeanBench.Laughlin.main`。

**理由：** 冻结描述给出固定常数 1/25；形式模型给出 1/100，数值结论不同。

**反向核查与边界：** 这不是存在某个通用常数的渐近表述；在固定系数的配对口径下不能任意吸收。未声称较强论文界为假。

**证据定位：** dep/Model.lean:61 的 MainTarget；绑定主描述。

[Formal](../../datasets/openai/projects/Laughlin/formal/Main.lean) · [主描述及来源](../../datasets/openai/projects/Laughlin/informal.jsonl) · [目标绑定](../../datasets/openai/projects/Laughlin/project.json)

### 46. RegularParity — `misaligned`

目标：`PaperLeanBench.RegularParity.main`。

**理由：** 描述要求存在一个输入使所有给定类电路失败（∃x∀C）；Lean 只要求每个电路分别有失败输入（∀C∃x）。

**反向核查与边界：** 量词不能交换：给定 x，总可以取输出其 parity 的常值电路；而每个常值电路仍有另一输入使其失败。

**证据定位：** Main.lean:37；绑定主描述。

[Formal](../../datasets/openai/projects/RegularParity/formal/Main.lean) · [主描述及来源](../../datasets/openai/projects/RegularParity/informal.jsonl) · [目标绑定](../../datasets/openai/projects/RegularParity/project.json)

### 47. SP-LP — `misaligned`

目标：`LinearProgrammingBound`。

**理由：** 根新增 Summable f，其中 f 的索引是整个欧氏空间，不是离散格点；论文允许非零 Schwartz 辅助函数，没有此全空间计数可和假设。

**反向核查与边界：** 可和族只有可数非零支撑；正维欧氏空间中非零连续函数在一个开球内非零，故不满足此假设。快速衰减能保证格点和收敛，不能保证对所有实向量计数求和。

**证据定位：** Main.lean:642（全局）/533（periodic）；变量 f 与维数 hd；论文 linear programming bound。

[Formal](../../datasets/sphere-packing/projects/SP-LP/formal/Main.lean) · [主描述及来源](../../datasets/sphere-packing/projects/SP-LP/informal.jsonl) · [目标绑定](../../datasets/sphere-packing/projects/SP-LP/project.json)

### 48. SP-LP-PERIODIC — `misaligned`

目标：`LinearProgrammingBound'`。

**理由：** 根新增 Summable f，其中 f 的索引是整个欧氏空间，不是离散格点；论文允许非零 Schwartz 辅助函数，没有此全空间计数可和假设。

**反向核查与边界：** 可和族只有可数非零支撑；正维欧氏空间中非零连续函数在一个开球内非零，故不满足此假设。快速衰减能保证格点和收敛，不能保证对所有实向量计数求和。

**证据定位：** Main.lean:642（全局）/533（periodic）；变量 f 与维数 hd；论文 linear programming bound。

[Formal](../../datasets/sphere-packing/projects/SP-LP-PERIODIC/formal/Main.lean) · [主描述及来源](../../datasets/sphere-packing/projects/SP-LP-PERIODIC/informal.jsonl) · [目标绑定](../../datasets/sphere-packing/projects/SP-LP-PERIODIC/project.json)

### 49. SP-B-EIG — `misaligned`

目标：`MagicFunction.b.Fourier.eig_b`。

**理由：** 目标引用的 b 定义中，最后的 i→i∞ 积分系数是 +2；论文定义式 (52) 是 −2。其余路径方向和 ψ 对应后，此差异改变被讨论的函数。

**反向核查与边界：** 参数 z=it 的导数为 +i，方向由 1 到 ∞，不能用方向变换解释。两函数相差 4H，H=i∫₁∞ψS(it)e^(−πt‖x‖²)dt，不是整体乘 −1；论文后续整体符号问题也不能修复单项符号。

**证据定位：** dep/SpherePacking/MagicFunction/b/Basic.lean:129–155；IntegralParametrisations.lean；论文 (52)；历史交叉核查见 initial selection 的 sphere adjudication。

[Formal](../../datasets/sphere-packing/projects/SP-B-EIG/formal/Main.lean) · [主描述及来源](../../datasets/sphere-packing/projects/SP-B-EIG/informal.jsonl) · [目标绑定](../../datasets/sphere-packing/projects/SP-B-EIG/project.json)

### 50. SP-B-ZERO — `misaligned`

目标：`MagicFunction.b.SpecialValues.b_zero`。

**理由：** 目标引用的 b 定义中，最后的 i→i∞ 积分系数是 +2；论文定义式 (52) 是 −2。其余路径方向和 ψ 对应后，此差异改变被讨论的函数。

**反向核查与边界：** 参数 z=it 的导数为 +i，方向由 1 到 ∞，不能用方向变换解释。两函数相差 4H，H=i∫₁∞ψS(it)e^(−πt‖x‖²)dt，不是整体乘 −1；论文后续整体符号问题也不能修复单项符号。

**证据定位：** dep/SpherePacking/MagicFunction/b/Basic.lean:129–155；IntegralParametrisations.lean；论文 (52)；历史交叉核查见 initial selection 的 sphere adjudication。

[Formal](../../datasets/sphere-packing/projects/SP-B-ZERO/formal/Main.lean) · [主描述及来源](../../datasets/sphere-packing/projects/SP-B-ZERO/informal.jsonl) · [目标绑定](../../datasets/sphere-packing/projects/SP-B-ZERO/project.json)

### 51. SP-A-CUTOFF — `misaligned`

目标：`MagicFunction.a.SpecialValues.a_zero`。

**理由：** 根声称 a(0)=−8640i/π，但实际六个 Schwartz 积分构件均经 ofDecayOn(a:=1) 乘平滑 cutoff；原点 cutoff 为 0，因此包装后的 a(0)=0。

**反向核查与边界：** 这不是“Schwartz 性证明采用截断而数值定义不变”：目标实际依赖截断后的函数。应检查定义展开，不能只看 theorem 的显示公式。

**证据定位：** dep/SpherePacking/MagicFunction/a/Schwartz.lean:123–143；ofDecayOn 的定义与 smoothTransition 在 0 的值；Main.lean 的 a_zero。

[Formal](../../datasets/sphere-packing/projects/SP-A-CUTOFF/formal/Main.lean) · [主描述及来源](../../datasets/sphere-packing/projects/SP-A-CUTOFF/informal.jsonl) · [目标绑定](../../datasets/sphere-packing/projects/SP-A-CUTOFF/project.json)

### 52. SP-I6-BOUND — `misaligned`

目标：`MagicFunction.a.IntegralEstimates.I₆.I₆'_bounding`。

**理由：** 绑定原文是存在一个与半径无关的常数控制所有半径；Lean 将常数放在 r 之后，变成 ∀r≥0,∃C 的逐点界。

**反向核查与边界：** 固定 r 时可任意放大 C，不能推出统一衰减估计。r 表示平方半径的换元、固定因子 2 均可吸收，不是判负理由。这里比较冻结的统一积分估计，不扩展到整个 Schwartz 定理。

**证据定位：** Main.lean:115；informal.jsonl 的 uniform-bound 范围和源文积分估计。

[Formal](../../datasets/sphere-packing/projects/SP-I6-BOUND/formal/Main.lean) · [主描述及来源](../../datasets/sphere-packing/projects/SP-I6-BOUND/informal.jsonl) · [目标绑定](../../datasets/sphere-packing/projects/SP-I6-BOUND/project.json)

## 校验

校验结果记录在 [verification.json](verification.json)。本轮运行项目输入/索引检查、冻结发布任务与 reference 哈希检查，以及 diff 空白检查；不声称运行全库 Lean 编译。

## PRPKG-P4：提交标签补充核查

用户要求参照对应 commit 的分类信息。本节只复核当前讨论的 PRPKG-P4 两个快照，其他条目的提交标签尚未在本次补充中逐项读取。

- before：`e298529dc9f3a48e74afb4b64f4bcde1b85faa46`，提交标题为 `Scope CI to changed papers and repair trusted startup (#44)`。该标题本身不提供 Proposition 4 的语义判定。
- after：`c2a77d260e596444f5678d9d4e5017992738da87`，标题为 `Publish PRPKG proof update and deployed website safeguards`；其直接父提交就是 before。
- 该 diff 的 `HUMAN_REVIEW_PACKET.tex` 对应行保留 verdict `matches_approved_corrected_target`。`paper_statement_map.json` 的相关行标为 `coverage_status: corrected_source_statement`、`source_status: corrected`，并明确 `archival_equivalence_claimed: false`。
- before 的报告把连续性称为当前证明的充分条件，并说明对原 Proposition 4 是否必要仍未解决；after 将其展示分类改为 `Exact with clarified regularity conditions`，明确加入正的 a.e. 密度及连续径向核。这个分类是**带修订条件的精确性**，没有宣称论文原文已经写了这些条件。

**本轮决定：两项仍为 `misaligned`，限定在当前绑定的完整论文原文范围内。** 上游信息支持把负标签的原因写成“相对原文显式加入正则性条件的修订目标”，而不是“作者无意中写错了 Lean”。若另建包含上游修订条件的 informal 配对，则上游给出的标签是匹配该修订目标；它是另一输入任务，不能悄悄替换当前论文原文配对。连续性是否为原命题成立所必需，仍不由这些标签证明。

证据：[固定提交的相关 diff](evidence/prpkg-commit-review.json)；[上游提交](https://github.com/nikhgarg/AppliedModelingLib/commit/c2a77d260e596444f5678d9d4e5017992738da87)；[after statement map](https://github.com/nikhgarg/AppliedModelingLib/blob/c2a77d260e596444f5678d9d4e5017992738da87/papers/PRPKG24AccuracyDiversity/audit/paper_statement_map.json)。这里读取的是提交内的审查分类，不是 GitHub PR 的 issue-label 列表。
