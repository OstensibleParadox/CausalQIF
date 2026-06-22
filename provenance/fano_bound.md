### 预备：概率空间的严格构造

设 $(\mathcal{X}, \mathcal{F}_X, P_X)$ 为概率空间，其中 $\mathcal{F}_X$ 为 $\mathcal{X}$ 上的 $\sigma$-代数。设 $\mathcal{B}(\mathbb{R})$ 为 $\mathbb{R}$ 上的 Borel $\sigma$-代数。

**假设 1（Cell 结构）：** 存在 $K \in \mathbb{N}$ 及互不相交的集合 $C_1, \dots, C_K \in \mathcal{F}_X$，满足：
$$P_X(C_j) = \alpha \in (0,1), \quad \forall j \in \{1,\dots,K\}$$

**假设 2（奖励可测性）：** 尖峰奖励函数族 $\mathcal{F} = \{R_0, R_1, \dots, R_K\}$ 定义为：
$$R_0(x) = 0, \quad R_j(x) = \tau \cdot \mathbf{1}_{C_j}(x), \quad j \in \{1,\dots,K\}$$
其中 $\tau > 0$ 为固定常数。由构造，每个 $R_j: (\mathcal{X}, \mathcal{F}_X) \to (\mathbb{R}, \mathcal{B}(\mathbb{R}))$ 均为可测函数。

**假设 3（样本空间）：** 设 $(\Omega, \mathcal{F}, P)$ 为足够大的基础概率空间，支撑所有随机变量。观测样本 $S = \{(X_t, Y_t)\}_{t=1}^m$ 取值于 $(\mathcal{X} \times \mathbb{R})^m$，装备乘积 $\sigma$-代数 $(\mathcal{F}_X \otimes \mathcal{B}(\mathbb{R}))^{\otimes m}$。

在假设 $R_j$ 下，样本的联合分布 $P_j^m$ 定义为：
$$P_j^m(A) = \int_{\mathcal{X}^m} \left[ \prod_{t=1}^m \int_{\mathbb{R}} \mathbf{1}_A(x_1,\dots,x_m, y_1,\dots,y_m) \, \mathcal{N}(R_j(x_t); \sigma^2)(dy_t) \right] P_X^{\otimes m}(dx_1,\dots,dx_m)$$
对所有 $A \in (\mathcal{F}_X \otimes \mathcal{B}(\mathbb{R}))^{\otimes m}$，其中 $\mathcal{N}(\mu, \sigma^2)$ 表示均值为 $\mu$、方差为 $\sigma^2$ 的正态分布。

---

### 定理（PAC 下界，修正版）

设 $\varepsilon \in (0, \frac{\alpha\tau}{2})$，$\delta \in (0, \frac{1}{2})$。若存在估计器 $\hat{R}: (\mathcal{X} \times \mathbb{R})^m \times \Omega \to \mathbb{R}^{\mathcal{X}}$ 满足：
$$\inf_{\text{estimator } \hat{R}} \sup_{j \in \{0,\dots,K\}} P_j^m\left( \|\hat{R} - R_j\|_{L_1(P_X)} > \varepsilon \right) \le \delta$$
则必有：
$$m \ge \max\left\{ \frac{\sigma^2}{\alpha\tau^2} \left(1 + \frac{1}{K}\right)^2 \left((1-\delta)\log(K+1) - \log 2\right), \frac{\log(1/(2\delta))}{-\log(1-\alpha)} \right\}$$

---

### 证明

#### 第一步：距离结构与最近邻解码

**引理 1（分离性）：** 对任意 $i \neq j$ 且 $i,j \in \{1,\dots,K\}$：
$$\|R_i - R_j\|_{L_1(P_X)} = 2\alpha\tau$$
对任意 $j \in \{1,\dots,K\}$：
$$\|R_0 - R_j\|_{L_1(P_X)} = \alpha\tau$$

*证明：* 由 $C_i \cap C_j = \emptyset$ 对 $i \neq j$，
$$\|R_i - R_j\|_{L_1(P_X)} = \int_{C_i} |\tau - 0| dP_X + \int_{C_j} |0 - \tau| dP_X = \tau P_X(C_i) + \tau P_X(C_j) = 2\alpha\tau$$
同理 $\|R_0 - R_j\|_{L_1(P_X)} = \int_{C_j} \tau \, dP_X = \alpha\tau$。$\square$

**引理 2（解码器的良定义性）：** 取定 $\hat{R}$ 为满足 $\sup_{j \in \{0,\dots,K\}} P_j^m\left( \|\hat{R} - R_j\|_{L_1(P_X)} > \varepsilon \right) \le \delta$ 的估计器。定义随机变量：
$$\hat{J}(\omega) = \begin{cases} \displaystyle\arg\min_{i \in \{0,1,\dots,K\}} \|\hat{R}(\cdot; S(\omega)) - R_i\|_{L_1(P_X)} & \text{若最小值唯一} \\ 0 & \text{否则} \end{cases}$$

则 $\hat{J}$ 为 $(\mathcal{F}_X \otimes \mathcal{B}(\mathbb{R}))^{\otimes m}$-可测随机变量，且：
$$\left\{ \|\hat{R} - R_j\|_{L_1(P_X)} \le \varepsilon \right\} \subseteq \left\{ \hat{J} = j \right\}, \quad \forall j \in \{0,1,\dots,K\}$$

*证明：* 映射 $(f, i) \mapsto \|f - R_i\|_{L_1(P_X)}$ 对固定 $i$ 关于 $f$ 连续（在 $L_1(P_X)$ 拓扑下），故对每个 $\omega$，最小值在有限集 $\{0,1,\dots,K\}$ 上可达。由于 $\hat{R}$ 作为样本的函数是可测的，且有限个可测函数的 min 仍可测，故 $\hat{J}$ 可测。

对包含关系：设 $\omega \in \{\|\hat{R} - R_j\|_{L_1} \le \varepsilon\}$。对任意 $i \neq j$，由三角不等式：
$$\|\hat{R} - R_i\|_{L_1} \ge \|R_j - R_i\|_{L_1} - \|\hat{R} - R_j\|_{L_1} \ge \alpha\tau - \varepsilon > \frac{\alpha\tau}{2} > \varepsilon \ge \|\hat{R} - R_j\|_{L_1}$$
故 $j$ 是唯一最小值点，$\hat{J}(\omega) = j$。$\square$

**推论 1（错误率控制）：** 由引理 2 及测度单调性：
$$P_j^m(\hat{J} \neq j) \le P_j^m\left( \|\hat{R} - R_j\|_{L_1} > \varepsilon \right) \le \delta, \quad \forall j \in \{0,1,\dots,K\}$$

---

#### 第二步：Fano 下界

**引理 3（单样本 KL 散度）：** 对 $i, j \in \{0, 1,\dots,K\}$ 且 $i \neq j$：
$$D_{\text{KL}}(P_i \| P_j) = \begin{cases} \frac{\alpha\tau^2}{\sigma^2} & \text{若 } i, j \neq 0 \\ \frac{\alpha\tau^2}{2\sigma^2} & \text{若 } i = 0 \text{ 或 } j = 0 \end{cases}$$

*证明：* 记 $p_i(y|x) = \frac{1}{\sqrt{2\pi}\sigma} \exp\left(-\frac{(y-R_i(x))^2}{2\sigma^2}\right)$ 为条件密度。由链式法则和正态分布 KL 散度公式：
$$D_{\text{KL}}(P_i \| P_j) = \mathbb{E}_X\left[ \frac{(R_i(X)-R_j(X))^2}{2\sigma^2} \right] = \frac{1}{2\sigma^2} \|R_i - R_j\|_{L_2(P_X)}^2$$

当 $i, j \neq 0$ 时，$\|R_i - R_j\|_{L_2(P_X)}^2 = \int_{C_i} \tau^2 dP_X + \int_{C_j} \tau^2 dP_X = 2\alpha\tau^2$。
当 $i=0, j \neq 0$ 时，$\|R_0 - R_j\|_{L_2(P_X)}^2 = \int_{C_j} \tau^2 dP_X = \alpha\tau^2$。
同理，当 $j=0, i \neq 0$ 时，$L_2$ 范数平方亦为 $\alpha\tau^2$。代入即得结论。$\square$

**引理 4（互信息上界）：** 设 $J \sim \text{Uniform}\{0, 1,\dots,K\}$，$S | J=j \sim P_j^m$。则：
$$I(J; S) \le m \frac{\alpha\tau^2}{\sigma^2} \left( \frac{K}{K+1} \right)^2$$

*证明：* 由 KL 表示的互信息：
$$I(J; S) = \frac{1}{K+1} \sum_{j=0}^K D_{\text{KL}}(P_j^m \| \bar{P}^m)$$
其中 $\bar{P}^m = \frac{1}{K+1}\sum_{i=0}^K P_i^m$ 为混合分布。

利用凸性及样本独立性：
$$I(J; S) \le \frac{1}{(K+1)^2} \sum_{j=0}^K \sum_{i=0}^K D_{\text{KL}}(P_j^m \| P_i^m) = \frac{m}{(K+1)^2} \sum_{j=0}^K \sum_{i=0}^K D_{\text{KL}}(P_j \| P_i)$$

将所有配对的 KL 散度相加（根据引理 3）：
- 当 $i, j \in \{1,\dots,K\}$ 且 $i \neq j$ 时，共有 $K(K-1)$ 项，每项为 $\frac{\alpha\tau^2}{\sigma^2}$；
- 当 $i=0, j \neq 0$ 或 $j=0, i \neq 0$ 时，共有 $2K$ 项，每项为 $\frac{\alpha\tau^2}{2\sigma^2}$。

总和为：
$$\sum_{j=0}^K \sum_{i=0}^K D_{\text{KL}}(P_j \| P_i) = K(K-1) \frac{\alpha\tau^2}{\sigma^2} + 2K \frac{\alpha\tau^2}{2\sigma^2} = K^2 \frac{\alpha\tau^2}{\sigma^2}$$

代入即得：
$$I(J; S) \le \frac{m}{(K+1)^2} K^2 \frac{\alpha\tau^2}{\sigma^2} = m \frac{\alpha\tau^2}{\sigma^2} \left( \frac{K}{K+1} \right)^2$$ $\square$

**引理 5（Fano 不等式应用）：** 设 $P_e = P(\hat{J} \neq J)$ 为先验均匀下的平均错误率。则：
$$P_e \ge 1 - \frac{I(J; S) + \log 2}{\log(K+1)}$$

*证明：* 这是标准 Fano 不等式。假设空间大小为 $K+1$。由数据处理不等式，$I(J; \hat{J}) \le I(J; S)$。而 $H(J|\hat{J}) = H(J) - I(J;\hat{J}) = \log(K+1) - I(J;\hat{J})$。由 Fano 不等式：
$$H(J|\hat{J}) \le H(P_e) + P_e \log K \le \log 2 + P_e \log(K+1)$$
重排即得。$\square$

**Fano 下界的推导：**

由推论 1，$P_j^m(\hat{J} \neq j) \le \delta$ 对所有 $j \in \{0, 1, \dots, K\}$ 成立，故在 $J \sim \text{Uniform}\{0, 1,\dots,K\}$ 下平均错误率：
$$P_e = \frac{1}{K+1}\sum_{j=0}^K P_j^m(\hat{J} \neq j) \le \delta$$

结合引理 4 和引理 5：
$$\delta \ge P_e \ge 1 - \frac{m \frac{\alpha\tau^2}{\sigma^2} \left( \frac{K}{K+1} \right)^2 + \log 2}{\log(K+1)}$$

重排：
$$m \frac{\alpha\tau^2}{\sigma^2} \left( \frac{K}{K+1} \right)^2 \ge (1-\delta)\log(K+1) - \log 2$$

因此：
$$\boxed{m \ge \frac{\sigma^2}{\alpha\tau^2} \left( 1 + \frac{1}{K} \right)^2 \left( (1-\delta)\log(K+1) - \log 2 \right)}$$

---

#### 第三步：Missed-Cell 下界（结构性不可识别）

**引理 6（条件测度等价）：** 定义事件 $M_j = \{X_t \notin C_j, \forall t=1,\dots,m\}$。则在 $M_j$ 上，条件概率测度满足：
$$P_0^m(\cdot \mid M_j) = P_j^m(\cdot \mid M_j)$$

*证明：* 需证对任意可测集 $A \in (\mathcal{F}_X \otimes \mathcal{B}(\mathbb{R}))^{\otimes m}$：
$$P_0^m(A \cap M_j) = P_j^m(A \cap M_j)$$

在 $M_j$ 上，对所有 $t$，$X_t \notin C_j$，故 $R_j(X_t) = 0 = R_0(X_t)$。因此对任意 $(x_1,\dots,x_m) \in M_j$ 和 Borel 集 $B_1,\dots,B_m \subseteq \mathbb{R}$：

$$\prod_{t=1}^m \mathcal{N}(0, \sigma^2)(B_t) = \prod_{t=1}^m \mathcal{N}(R_j(x_t), \sigma^2)(B_t)$$

因为 $R_j(x_t) = 0$ 当 $x_t \notin C_j$。由 Fubini 定理和乘积测度的唯一性，对 $A = A_X \times A_Y$（其中 $A_X \in \mathcal{F}_X^{\otimes m}$，$A_Y \in \mathcal{B}(\mathbb{R})^{\otimes m}$）：
$$P_0^m(A \cap M_j) = \int_{A_X \cap M_j} \prod_{t=1}^m \mathcal{N}(0,\sigma^2)(A_Y^{(t)}) \, dP_X^{\otimes m} = \int_{A_X \cap M_j} \prod_{t=1}^m \mathcal{N}(R_j(x_t),\sigma^2)(A_Y^{(t)}) \, dP_X^{\otimes m} = P_j^m(A \cap M_j)$$

由 $\pi$-$\lambda$ 定理，此等式对乘积 $\sigma$-代数中所有集合成立。再由条件概率的定义：
$$P_0^m(A \mid M_j) = \frac{P_0^m(A \cap M_j)}{P_0^m(M_j)} = \frac{P_j^m(A \cap M_j)}{P_j^m(M_j)} = P_j^m(A \mid M_j)$$
（注意 $P_0^m(M_j) = P_j^m(M_j) = (1-\alpha)^m > 0$）。$\square$

**引理 7（互斥事件构造）：** 定义：
$$\mathcal{A} = \left\{ \|\hat{R} - R_0\|_{L_1(P_X)} \le \varepsilon \right\}, \quad \mathcal{B}_j = \left\{ \|\hat{R} - R_j\|_{L_1(P_X)} \le \varepsilon \right\}$$

则 $\mathcal{A} \cap \mathcal{B}_j = \emptyset$。

*证明：* 假设存在 $\omega \in \mathcal{A} \cap \mathcal{B}_j$。则由三角不等式：
$$\|R_0 - R_j\|_{L_1} \le \|R_0 - \hat{R}\|_{L_1} + \|\hat{R} - R_j\|_{L_1} \le 2\varepsilon < \alpha\tau$$
但由引理 1，$\|R_0 - R_j\|_{L_1} = \alpha\tau$，矛盾。$\square$

**Missed-Cell 下界的推导：**

考虑两点先验：$J \in \{0, j\}$ 且 $P(J=0) = P(J=j) = \frac{1}{2}$。贝叶斯错误率为：
$$P_e^{(2)} = \frac{1}{2} P_0^m(\mathcal{A}^c) + \frac{1}{2} P_j^m(\mathcal{B}_j^c)$$

由引理 6 和全概率公式：
$$P_0^m(\mathcal{A}^c) \ge P_0^m(\mathcal{A}^c \mid M_j) P_0^m(M_j) = P_0^m(\mathcal{A}^c \mid M_j) (1-\alpha)^m$$
$$P_j^m(\mathcal{B}_j^c) \ge P_j^m(\mathcal{B}_j^c \mid M_j) P_j^m(M_j) = P_j^m(\mathcal{B}_j^c \mid M_j) (1-\alpha)^m$$

由引理 6，$P_j^m(\mathcal{B}_j^c \mid M_j) = P_0^m(\mathcal{B}_j^c \mid M_j)$。因此：
$$P_e^{(2)} \ge \frac{(1-\alpha)^m}{2} \left[ P_0^m(\mathcal{A}^c \mid M_j) + P_0^m(\mathcal{B}_j^c \mid M_j) \right]$$

由引理 7，$\mathcal{A} \cap \mathcal{B}_j = \emptyset$，故 $\mathcal{A}^c \cup \mathcal{B}_j^c = \Omega$。因此：
$$P_0^m(\mathcal{A}^c \mid M_j) + P_0^m(\mathcal{B}_j^c \mid M_j) \ge P_0^m(\mathcal{A}^c \cup \mathcal{B}_j^c \mid M_j) = 1$$

所以：
$$P_e^{(2)} \ge \frac{(1-\alpha)^m}{2}$$

由于最大错误率不小于平均错误率：
$$\max\left\{ P_0^m(\mathcal{A}^c), P_j^m(\mathcal{B}_j^c) \right\} \ge P_e^{(2)} \ge \frac{(1-\alpha)^m}{2}$$

由 PAC 条件，$P_0^m(\mathcal{A}^c) \le \delta$ 且 $P_j^m(\mathcal{B}_j^c) \le \delta$，故：
$$\delta \ge \frac{(1-\alpha)^m}{2}$$

取对数（注意 $-\log(1-\alpha) > 0$ 因 $\alpha \in (0,1)$）：
$$\boxed{m \ge \frac{\log(1/(2\delta))}{-\log(1-\alpha)}}$$

---

#### 第四步：合并

PAC 学习器必须同时满足所有 $j \in \{0,1,\dots,K\}$ 的精度要求，因此两个必要条件必须同时成立：

$$\boxed{m \ge \max\left\{ \frac{\sigma^2}{\alpha\tau^2} \left( 1 + \frac{1}{K} \right)^2 \left((1-\delta)\log(K+1) - \log 2\right), \frac{\log(1/(2\delta))}{-\log(1-\alpha)} \right\}}$$

$\square$
