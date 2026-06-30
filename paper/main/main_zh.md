# CausalQIF：有限量化信息流证书的类型化 Lean 库

## 摘要

量化信息流（QIF）经常被用来说明一个系统中哪些状态没有被观察者恢复、哪些状态仍然影响后续行为。可是，在实际论文中，这类论证常把三种不同对象混在一起：有限分布上的信息论恒等式、部署图上的 Markov 或割集假设、以及具体实验探针得到的数值。本文的主角不是一个新的实验审计协议，而是 `CausalQIF`：一个面向有限离散系统的 Lean 4 类型化库，用来把这些对象分层、命名并机械化检查。

`CausalQIF` 提供三层接口。第一层是有限 PMF 上的信息论核心，包括熵、条件熵、互信息、条件互信息、KL 非负性、链式法则以及条件数据处理不等式。第二层是证书库，将 QIF 中常用的审计语句表达为可复用的 Lean 定理：动态探针证书来自 `cond_dpi` 和 `prop2_dynamic_lb`；确定性探针由 `prop2_dynamic_lb_deterministic_probe` 自动卸除 Markov 前提；静态证书由 `static_decomposition`、`prop1_static_ub` 和 `prop1_static_ub_from_cut` 把迹缺口分解、割变量 DPI 与容量上界连接起来。第三层是有限有向图和 d-separation 接口，它证明了查询域受保护时的图分离结果，同时把仍未闭合的 graphoid/global-Markov 桥接假设集中在 `UnsafeBridge.lean` 的 5 个显式 `axiom` 中，并用 `not_forall_dsep_complete` 记录不受限 d-separation 命题为假。

因此，本文的 POPL 式贡献是一个可检查的 proof engineering artifact：它说明在有限 QIF 证书中，哪些结论已经由 Lean 的类型和定理保证，哪些结论仍是部署建模前提，哪些实验数值只是库接口的客户端实例。智能体、扩散语言模型和多智能体通信实验在本文中只作为应用用例；它们展示如何实例化库中的状态、轨迹、探针和割变量，而不是替代形式化结果本身。

## 关键词

Lean 4、量化信息流（QIF）、有限概率、类型化 PMF、条件数据处理不等式、d-separation、形式化验证、证书库、AI agent auditing

## 一、引言

QIF 论文中常见的核心判断很简单：观察者看到的轨迹是否足以恢复系统的有效状态？剩余状态是否影响下一步行为？如果答案依赖一个实验探针、一个图结构假设和一个信息论不等式，那么读者需要知道每一步到底由什么保证。

这正是 POPL 读者会关心的问题。一个实验系统可以报告互信息估计值，但该估计值何时是目标量的下界？一个部署图可以报告割集容量，但该容量何时约束不可见状态熵？一个 d-separation 图可以暗示条件独立，但查询域、positivity、local Markov 和 graphoid 闭包条件在哪里出现？如果这些边界没有被机器检查，论文容易把“已证明的有限恒等式”和“应由部署者承担的建模前提”写成同一种语气。

`CausalQIF` 把这个边界作为库设计目标。它不试图认证真实世界智能体，也不声称解决连续状态、无限测度或任意黑盒系统的可审计性。它做一件更窄但更适合 POPL 的事：在 Lean 4 中建立一个有限、类型化、可导入的 QIF 证明栈，使常用证书语句必须通过显式类型、显式 PMF、显式条件独立谓词和显式外部前提表达。

本文因此把问题从“实验是否证明某个 agent 隐藏状态活跃”改写为：

1. 有限 QIF 证书需要哪些基础信息论定理？
2. 这些定理在 Lean 中应如何类型化，才能避免状态、轨迹、探针和行动变量混淆？
3. 图结构、Markov 条件、容量预算和经验探针哪些部分能在库内证明，哪些部分必须留作外部假设？
4. 一个下游审计实验如何作为库客户端，而不是作为论文主论证的替代物？

### 1.1 贡献

本文贡献如下。

**有限信息论核心。** `CausalQIF.InfoTheory` 在有限类型和显式 PMF 上定义熵、条件熵、互信息和条件互信息，并证明非负性、链式法则、log-cardinality 上界以及条件 DPI。核心结论 `cond_dpi` 是后续动态证书和割集归约的共同基础。

**类型化证书接口。** `CausalQIF.Certificates` 提供面向 QIF 的 proof API。动态证书由 `prop2_dynamic_lb` 表达：若探针在给定轨迹下只通过状态影响行动，则探针与行动的条件互信息下界真实残差决策相关性。确定性读出 `probe : State -> Trace -> Probe` 通过 `condMarkov_deterministicProbePMF` 自动满足 Markov 前提。静态证书由 `static_decomposition` 精确分解可见/完整轨迹缺口，再由 `prop1_static_ub`、`cut_set_dpi_bound` 和 `prop1_static_ub_from_cut` 在外部割容量前提下给出上界。

**图层和前提账本。** `CausalQIF.Graph` 与 `CausalQIF.DSeparation` 提供有限 DAG、trail、Bayes-ball、moralization 和 d-separation 机制。库证明了 pairwise-disjoint 查询域下的 `dsep_complete_of_query`，并给出 `not_forall_dsep_complete` 作为反例，防止把标准查询域外的错误命题写进论文。仍未闭合的全局 Markov 桥接被集中在 `DSeparation/UnsafeBridge.lean` 的 5 个显式 `axiom` 中。

**可复用案例接口。** `Examples.CaseStudy` 展示一比特 cut-set bound 案例如何从 typed deployment、d-separation 前提、KKT 容量证书和 cut-set 归约组合出来。智能体、扩散 LM 和多智能体实验被重新定位为客户端：它们提供状态、轨迹、探针和容量实例，调用库中的定理边界，而不是构成库本身的正确性证明。

## 二、库的范围与非目标

`CausalQIF` 的范围是有限离散系统。所有主要定理都在 `Fintype` 和 `DecidableEq` 假设下工作，概率对象是显式的 `FinitePMF`，熵和互信息是有限求和公式。这个选择牺牲了测度论一般性，但换来了三个工程性质。

第一，变量的角色由类型区分。状态、可见轨迹、缺失轨迹、行动、探针和割变量在 Lean 中不是同一个无类型随机变量集合，而是不同类型参数。错误地把 probe 当成 action、把 missing trace 当成 visible trace，不能在 API 层静默通过。

第二，证书前提不会消失在自然语言中。动态证书要求 `condMarkov` 或由确定性 probe 构造卸除该前提；静态 cut-set 证书要求容量上界和 cut 变量的 Markov 前提；图到条件独立的桥接要求 positivity、合法查询域和当前仍显式列出的 graphoid/global-Markov 假设。

第三，库不把经验估计包装成定理。互信息估计器、bootstrap 置信区间、模型扰动协议和实验任务划分都属于客户端代码或论文实验。Lean 证明的是：如果客户端提供的变量满足接口前提，那么相应的数量具有上界或下界意义。

非目标也同样明确。本文不声称认证真实部署的 alignment，不处理连续状态或无限样本极限，不证明任意经验 probe 都可容许，也不把 d-separation 到概率条件独立的全部 Verma-Pearl 定理闭合在当前版本内。相反，库把这些内容标成 proof boundary。

## 三、有限信息论核心

`CausalQIF.InfoTheory` 是库的底层。它将常用 QIF 量写成有限类型上的函数，而不是纸面上的重载符号。

核心对象包括：

- `entropyOf`：对有限质量函数计算 Shannon 熵。
- `condEntropy` 与条件熵相关边缘化定义。
- `I_XZ_W`、`I_YZ_W`、`I_SA_cond_T`：四变量或三变量 PMF 上的条件互信息接口。
- `condMarkov`：四变量 PMF 上的具体条件 Markov 方程。

这一层证明的关键结果包括 `entropy_nonneg`、`entropy_le_log_card`、`condMutualInfo_nonneg`、`I_XY_Z_W_eq_I_XZ_W_add_I_YZ_XW`、`I_XY_Z_W_eq_I_YZ_W_add_I_XZ_YW` 和 `cond_dpi`。`cond_dpi` 的 Lean 形状是：

```lean
theorem cond_dpi
    (P : FinitePMF (α × β × γ × δ))
    (h : condMarkov P) :
    I_XZ_W P ≤ I_YZ_W P
```

这个定理就是 QIF 动态证书的类型化核心：如果四元组解释为 `(Probe, State, Action, Trace)`，则条件 Markov 前提表达 `Probe -> State -> Action | Trace`；结论表达 probe-action 条件互信息不超过 state-action 条件互信息。

重要的是，库没有把变量名写死在定理中。`cond_dpi` 是通用有限信息论定理；证书层只是在特定变量角色上实例化它。

## 四、证书层：从信息论到 QIF API

证书层将信息论核心包装成论文中真正使用的接口。下表列出主要 theorem family 及其 proof boundary。

| 证书角色 | Lean 声明 | 库内保证 | 外部前提 |
|---|---|---|---|
| 动态探针下界 | `prop2_dynamic_lb` | 由 `cond_dpi` 得出 `I(Probe; Action | Trace) <= I(State; Action | Trace)` | `condMarkov P` |
| 确定性 probe | `prop2_dynamic_lb_deterministic_probe` | 从 `probe : State -> Trace -> Probe` 构造 PMF 并自动证明 `condMarkov` | probe 必须确为状态和轨迹的确定性读出 |
| 多 probe 聚合 | `aggregated_dynamic_lb` | max 聚合保持下界方向 | 每个 probe 分布分别满足前提 |
| 迹缺口分解 | `static_decomposition` | 精确等式 `H(S | T_tilde) = H(S | T_full) + I(S; M | T_tilde)` | 有限 `(State, VisibleTrace, MissingTrace)` PMF |
| 静态 cut 上界 | `prop1_static_ub` | 若缺失迹信息流受 `C_cut` 约束，则状态熵受上界约束 | `I(S; M | T_tilde) <= C_cut Ω` |
| cut-set 抽取 | `cut_set_dpi_bound`、`abstract_cut_set_bound`、`prop1_static_ub_from_cut` | 把 cut 变量 DPI 与容量证书组合 | cut 变量提取、`condMarkov` 和容量上界 |
| 容量/量化边界 | `capacity_le_of_kkt`、`quantized_vector_entropy_bound` | KKT 证书或有限量化向量给出信息上界 | KKT 字段或量化方案由调用者提供 |

这张表体现了本文的基本工程原则：Lean 定理负责保持不等式方向、边缘化定义、条件化对象和 max 聚合不会出错；部署者负责证明自己的变量确实满足接口前提。

### 4.1 动态证书

动态证书的目标量是：

\[
  \delta_\mathrm{act} = I(S; A \mid T).
\]

如果审计者只能读取一个 probe `X`，则需要证明在给定 `T` 下 `X` 对 `A` 的影响只通过 `S`。在 Lean 中，这不是一句自然语言假设，而是 `condMarkov P`。`prop2_dynamic_lb` 直接把它变成下界：

\[
  I(X; A \mid T) \le I(S; A \mid T).
\]

经验 probe 最容易出错的地方是把“读到了某个变量”误写成“该变量是可容许下界”。库提供一个保守入口：如果 probe 是 `State` 和 `Trace` 的确定性读出，`condMarkov_deterministicProbePMF` 会在 Lean 中构造四变量 PMF 并证明 Markov 方程。更复杂的随机 probe、干预 probe 或 replay probe 可以使用同一接口，但必须显式给出相应的条件 Markov 前提。

### 4.2 静态证书

静态证书的目标是约束可见轨迹无法恢复的状态熵：

\[
  H(S \mid \tilde T).
\]

库首先证明一个纯代数分解：

\[
  H(S \mid \tilde T)
  =
  H(S \mid T_\mathrm{full}) + I(S; M \mid \tilde T),
\]

其中 `M` 是缺失轨迹。这个等式由 `static_decomposition` 给出，不涉及部署图。随后，`prop1_static_ub` 说明：如果调用者提供 `I(S; M | T_tilde) <= C_cut Ω`，则得到状态熵上界。`CutSetBoundExtract` 再把 cut 变量、条件 DPI 和容量前提组合成更接近部署图的入口。

这一区分是 POPL 版本必须强调的：Lean 证明了分解和归约，但不会从任意工程系统中自动提取正确的 cut 变量，也不会凭空证明接口容量。容量可以由 `capacity_le_of_kkt` 或 `quantized_vector_entropy_bound` 等库定理支持，但具体建模仍是调用者义务。

## 五、图层：d-separation 的类型化边界

QIF 证书经常依赖因果图或部署图。`CausalQIF` 的图层由三组模块组成：

- `Graph/*`：有限 DAG、祖先关系和 moralization 辅助定义。
- `DSeparation/*`：trail、Bayes-ball、d-separation graph 和查询域保护。
- `Examples/*`：将图层、信息论层和证书层组合的最小部署例子。

库中特别重要的结果不是“我们证明了所有 d-separation 事实”，而是“我们证明了受限查询域下的正确事实，并机器检查了错误泛化”。`dsep_complete_of_query` 要求 `DSeparationQuery X Y Z`，其中包含 pairwise-disjoint 约束。相反，`not_forall_dsep_complete` 证明不带该约束的全称命题为假。

这对论文写作很关键。很多纸面证明会把端点是否可被条件集包含当成小技术细节；在 Lean 中，它直接决定定理真假。当前库把标准查询域作为类型化 API 的一部分，而不是埋在证明脚注里。

图到概率条件独立的桥接也被显式分层。`MarkovGenerator`、`GlobalMarkov` 和 `DSepCMIBridge` 提供公开接口，`UnsafeBridge.lean` 集中放置当前仍未完全闭合的 5 个 axiom：四个 graphoid 闭包律和一个 local-Markov-to-global-d-separation 桥。这让下游 theorem 可以被使用，但其依赖不会被误报为 closed theorem。

## 六、其他有限证书族

除了双重证书，库还包含若干有限 QIF 中常见的辅助 theorem family。它们不是本文的叙事主线，但说明 `CausalQIF` 是一个库而非单点证明。

**可辨识性缺口。** `identifiability_gap_extremes` 证明：对任意有限 `(T, A)` 分布，只要状态类型足够大，就存在两个具有相同可观察 `(T, A)` 边缘分布的有限 PMF，一个满足 `I(S; A | T) = 0`，另一个达到 `H(A | T)`。这给“仅输出轨迹不能识别残差决策相关性”提供有限离散核心。

**自回归 trace recoverability。** `no_entropic_eis_autoregressive` 表达一个 exact finite theorem：若状态由轨迹确定性恢复，则内生有限 Shannon witness 不可能有正的 `H(I | T)`。这不是连续近似命题，也不覆盖 epsilon-screenability；它是精确有限定理。

**语义闭包和覆盖。** `semantic_factorization_iff` 把函数尊重语义等价关系与通过 quotient factorization 等价起来；`fcg_covering_bound` 和相关结果给出有限覆盖到格式信道缺口的界。

**有限查询和几何不可能性。** `finite_query_decision_impossibility`、`finite_support_cannot_cover_separated_sequence`、`theorem3_pac_lower_bound` 等结果保留为证书库的扩展部分。它们有各自的建模前提，不应被合并成一个未经限定的总 theorem。

## 七、库架构与构建边界

当前公共入口是：

```lean
import CausalQIF
```

源码布局如下：

```text
lean/CausalQIF/
  InfoTheory/       -- finite entropy, MI, CMI, KL, DPI
  Certificates/     -- QIF certificate reductions and finite bounds
  Graph/            -- finite DAG utilities
  DSeparation/      -- trail, Bayes-ball, d-separation, bridge boundary
  Examples/         -- typed deployment sanity checks
  Experimental/     -- compatibility and pending bridge material
```

当前活动源码没有 `sorry` 或 `admit` 占位；剩余未闭合内容以 5 个 `axiom` 集中在 `DSeparation/UnsafeBridge.lean`。这种状态比简单写“mechanized in Lean”更具体：读者能看到哪些 theorem 是 closed proof，哪些 theorem 经由显式 assumption boundary。

`THEOREM_INDEX.csv` 和 `docs/THEOREM_DEPENDENCIES.md` 是论文写作的约束文件。它们列出 theorem 名、文件位置、支持的 paper claim、假设和不声称内容。POPL 版本应该把这些表作为 artifact 叙事的一部分，而不是把 Lean 工件压缩成摘要末尾一句话。

## 八、客户端用例：实验如何降级为库实例

原先的智能体审计实验仍然有价值，但它们在 POPL 论文中的角色应改变。它们不是主论证，而是 `CausalQIF` 的客户端。

**ReAct scratchpad。** 客户端把未记录 scratchpad 建模为 `MissingTrace` 或 cut channel，把工具选择建模为 `Action`，把 replay/intervention 读数建模为 `Probe`。库能检查的是：在调用者给出 `condMarkov` 或确定性 probe 构造后，probe-action 信息量是否具有下界意义；在调用者给出容量预算后，cut-set 上界是否以正确方向组合。

**扩散 LM 去噪轨迹。** 客户端把去噪步骤索引为 probe family。不同时间步的数值差异可以形成 activation profile，但 Lean 只证明 profile 中每个分量在满足前提时是目标互信息的下界。

**多智能体私人报告边。** 客户端把 Worker 的私人报告建模为通信边或 probe 变量。报告替换实验可以展示某条边在具体任务上 action-relevant，但该实验不能替代库中的 `cond_dpi` 或 cut-set theorem。

原稿中出现的数值，例如 ReAct replay 的 `0.0163` 位、LLaDA 终步的 `0.110` 位、多智能体 report swap 的 `0.901` 位，可以保留在 artifact evaluation 或 case-study 小节中。但它们应被解释为“调用库接口后的客户端输出”，而不是摘要和引言的核心贡献。

## 九、相关工作定位

POPL 版本的相关工作应从形式化和程序语言角度组织，而不是以 agent audit 实验为中心。

**量化信息流与信息论安全。** QIF 研究提供了用熵、互信息和信道容量描述泄露的传统。`CausalQIF` 的区别在于，它不只给出纸面公式，而是为有限 QIF 证书建立 Lean API，并把容量、Markov 和图结构前提显式化。

**形式化概率和信息论。** 现有工作在 Coq、Isabelle、Lean 或其他证明助手中处理概率、测度和信息论。本文选择有限 PMF 片段，是为了服务部署证书和可执行 artifact，而不是追求测度论最大一般性。

**因果图和 d-separation。** 因果图提供把结构假设转成条件独立的语言。`CausalQIF` 的贡献不是宣称图语义全闭合，而是给出 finite DAG 机制、合法查询域保护、反例和显式桥接账本。

**AI agent auditing。** 智能体审计、probe、patching、representation engineering 和 causal tracing 提供客户端变量和实验协议。它们在本文中是应用来源，而不是形式化核心。

## 十、局限性

本文的有限边界是有意设计，但也限制了适用范围。

第一，所有定理都是有限离散定理。连续激活、无限上下文、采样极限和估计一致性不在当前 Lean 核心内。

第二，部署到 Lean 变量的映射由调用者承担。库可以检查一个给定 `FinitePMF` 和给定 `condMarkov` 前提推出什么，不能检查真实系统是否真的实现了该 PMF。

第三，cut-set capacity 是证书前提而非自动发现结果。`capacity_le_of_kkt` 和 `quantized_vector_entropy_bound` 能帮助证明有限容量上界，但接口规格、量化方案和 graph extraction 仍在库外。

第四，d-separation 到条件独立的完整桥接仍有显式 axiom boundary。库的价值在于把这条边界集中、命名并暴露给论文，而不是把它藏起来。

## 十一、结论

如果目标是 POPL，`CausalQIF` 的论文主角应是 Lean/typed finite QIF library。实验审计协议只能作为客户端实例。这样的改写使论文从“我们做了若干 agent 实验并附带 Lean 段落”变成“我们构建了一个可检查的有限 QIF 证明栈，并用 agent 实验展示它如何被调用”。

核心 claim 也随之改变：本文不以某个具体模型的隐藏状态数值为主要发现，而以 proof boundary 的机械化为主要贡献。`CausalQIF` 告诉读者：动态证书何时由条件 DPI 保证，静态证书何时由迹缺口分解和 cut-set 前提保证，d-separation 何时可以被使用，以及哪些假设仍必须由部署者或后续理论工作承担。

## 术语对照表

| 中文 | English | 备注 |
|------|---------|------|
| 量化信息流 | quantitative information flow (QIF) | 本文核心领域 |
| 有限 PMF | finite PMF | Lean 中的显式概率对象 |
| 类型化证书 | typed certificate | 由变量类型区分状态、轨迹、探针等角色 |
| 条件数据处理不等式 | conditional data processing inequality | `cond_dpi` |
| 条件 Markov 前提 | conditional Markov premise | `condMarkov` |
| 动态探针证书 | dynamic probe certificate | `prop2_dynamic_lb` |
| 静态 cut-set 证书 | static cut-set certificate | `prop1_static_ub_from_cut` |
| 迹缺口分解 | trace-gap decomposition | `static_decomposition` |
| 查询域保护 | query-domain guard | `DSeparationQuery` |
| 前提账本 | premise ledger | theorem dependencies and axiom boundary |
| 工件客户端 | artifact client | 实验或案例对库接口的实例化 |
| 显式 axiom boundary | explicit axiom boundary | 当前集中在 `UnsafeBridge.lean` |
