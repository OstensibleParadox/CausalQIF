
# Context

GPT 太沉迷于lean-modular skill 的 “保留向下兼容 wrapper” 特性了，把工具当成了教条。
但在真实世界的POPL 27 或者开源合并中，带着 Screenability.lean 或者 FiniteQuerySandbox 这种带着严重历史背景（甚至包含废弃业务逻辑）的命名，是对代码洁癖和可维护性的巨大侮辱。
在建立新的合并公共库 ~/Documents/anon-lean4，并且作为未来两篇顶会论文的Source of Truth 时，Destructive Reconstruction不仅是允许的，更是必须之举。


# 一、命名问题
dSeparated_implies_certifiedShannonCutSetBound 是一个非常典型的“人类阅读习惯”，但在 Mathlib/Lean 4 社区，他们极度反感用 implies 这个词作为定理名连接词，会起到反效果。
Mathlib 官方标准： [结论] _of_ [前提1] _of_ [前提2] 或者 [主词] _le_ [比较词]。如果定理是给出上限的，必须有 _le_（Less than or equal to）或者 bound 的字眼。

# 二、架构目录问题
为了未来这个库有潜力被PR到 Mathlib4/Probability 或是独立的成熟开源库，目录结构必须高度数学化. Assembly这种太像业务代码了，缺乏数学抽象感。

## 建议的新架构（ai可建议，可改）
CasualQIF/  
├── Graph/                    <-- 取代笼统的 Core
│   ├── DirectedAcyclic.lean  <-- 也就是原来的 Basic.lean，定义纯 DAG
│   ├── Reachability.lean
│   └── Moralization.lean
├── DSeparation/
│   ├── Path/                 <-- 替代 Trail 和 BayesBall (内部拆分)
│   ├── MAGWalk.lean
│   └── Equivalence.lean      <-- dSeparated_iff_dSeparates 核心所在
├── Probability/              <-- 取代俗气的 ProbSemantics
│   ├── FinitePMF.lean        <-- 单独抽离
│   ├── Entropy.lean          <-- 包含 Shannon entropy, CMI, KL
│   └── Markov.lean           <-- IsMarkovChain, condMarkov
├── CausalModel/              <-- 第一处真正 Join 的地方 (DAG + Probability)
│   ├── Factorization.lean    <-- 对应旧的 MarkovGenerator.lean (语义桥接)
│   └── DataProcessing.lean   <-- cond_dpi，基于 causal Markov 条件
├── InformationFlow/          <-- 取代 CutSet (这是一个具体的数学工具，InfoFlow 是目的)
│   ├── CutSetBound.lean      <-- abstract_cut_set_bound 所在
│   └── ChannelCapacity.lean  <-- KKT certificates 所在
└── Main.lean                 <-- (不要多开 Assembly 文件夹，顶层定理直接放在入口)

类似DSeparation.lean wrapper 或者 FiniteQuerySandbox 文件夹，应该在这个合并的过程中就被清理掉，不用旧命名污染新库。


# 三、Risk Management: Three-Phase Migration

neurips26 和 popl27 的 .lean 已经被copy-paste到~/Documents/anon-lean4。

1. Phase 1: Topology Transfer 先不管内部依赖关系，把旧的 import path 改为对应的新路径（e.g., import CausalQIF.Graph.DirectedAcyclic）。 此时你会得到大量因为 Name Space 不一致而导致的错误。
2. Phase 2: Find & Replace in Isolation 在这个过程中，把所有的废弃命题注释掉或删掉。跑 lake build，必须绿灯。
3. Phase 3: The Final Join 这是 POPL27 facing 技术债的核心——把你在旧版本里打的 InfoTheoryBridge.lean 里的那两个 intentional sorrys 用新版的DSepCMIBridge.lean干掉。


# 四、论文重写

#### Methodology 1：Stratification of Structural Flow and Quantitative Capacity
    "Previous attempts to derive strict capacity bounds floundered because they conflated topological constraints (d-separation) with metric approximations ($\epsilon$-leakage from continuous functions). We methodologically bypass this by **stratifying the verification stack**. By restricting the base formalization to a finite-discrete probabilistic semantics (`FinitePMF`), we completely decouple the static non-interference guarantee from functional noise parameters, yielding a purely structural, type-safe bottleneck limit without metric contamination.
#### Methodology 2：Trace Compression via Static Abstract Interpretation 
    "Deriving leakage limits by chaining the Data Processing Inequality (DPI) along dynamic information paths causes bound explosion due to overlapping execution trails (multiplexing). Instead of analyzing combinatorial trail traversals, we implement a **certified trace optimizer**. Operational trace semantics (`Trail`) are deterministically compressed into a global reachability invariant over an abstract static intermediate representation (`MAGWalk`). This converts unmanageable path-wise capacity integration into a single global minimal-cut evaluation."
#### Methodology 3：Well-Defined Modular Boundaries for Measure-Theoretic Obligations 
    "Deploying cut-set capacity frameworks directly onto continuous activation spaces violates channel memory assumptions, resulting in infinite-capacity singularities. We formally circumscribe this hazard by erecting a strict module boundary (`InfoTheoryBridge.lean`). The cut-set extraction operates as a parameterized module where probabilistic conditional-independence theorems are isolated as explicit verification obligations. This strictly quarantines our zero-sorry graph calculus from continuous heuristic anomalies."

### Contribution & Future Works: Information-Preserving Abstraction Target

**Contributions:**
    1.  **Formalization of a Bipartite Graph Semantics:** (Methodology 1 & 2 - Trails $\to$ MAGWalk )
    2.  **Explicit Modular Boundary for Probabilistic Inference:** (Methodology 3 -InfoTheoryBridge)
    3.  **Foundational Substrate for Leakage Quantification:** (The "Sanctuary" defense )

While our machine-checked theorems operate fundamentally over a discrete, finite-variable domain, this constraint represents a rigorous architectural design rather than a compromise. The mathematical complexities inherent in arbitrary continuous neural manifolds routinely obscure definitive topological leakage boundaries.
By forging a closed, bisimulation-verified equivalence isolated from metric artifacts, we establish a robust **formal substrate**. Any future endeavor to definitively resolve Shannon leakage bounds in infinite-precision continuous models will naturally reduce to discovering a sound abstraction refinement—specifically, an **information-preserving homomorphism (or Galois connection)** mapping the continuous network dynamics into our discrete graph-theoretic framework. Thus, our mechanized algebra does not sidestep the original continuous capacity conjecture, but rather rigorously anchors its future proof target.
