# 0020 · 平方根尺度的尝试与数字中点构造的首项

2026-11-19。所有对数为自然对数。设 $V$ 为同色不同元的普通整数和并，$K(N)$ 为使 $|V|<N/10$ 的最少非空颜色数。下文给出 $K(N)$ 的一个上界，以及一个带构造假设的下界。两者的量词不同。

## 1. 直接尝试平方根尺度

取 $B=2^d,\ N=B^d$。以 $1+e(u)$ 编号区间，其中 $e(u)=\sum_{i=0}^{d-1}u_iB^i,\ 0\le u_i<B$。给每个点的标签为各位奇偶及精确能量 $f(u)=\sum_i u_i^2$。标签数至多 $2^d(d(B-1)^2+1)=\exp(O(\sqrt{\log N}))$。这试图以能量相等代替 0018 中昂贵的距离着色。

该尝试实际生成至少 $(B-4)^d$ 个同色和。对每个 $z\in\{2,\ldots,B-3\}^d$，考察 $z\cdot v$，其中 $v\in\{0,1,2\}^d$。这些整数至多有 $2d(B-1)+1$ 个值，而 $3^d>2d(B-1)+1$ 对充分大 $d$ 成立。取碰撞之差 $h\ne0$，则 $\|h\|_\infty\le2$、$z\cdot h=0$。两个端点 $z+h,z-h$ 在盒内，逐位同奇偶，又因平方能量差为 $4z\cdot h=0$ 而同色。各中心给出彼此不同的实际和 $2e(z)+2$。由于 $d/B\to0$，下界是 $(1-o(1))N$。合并标签也保留这些和。这个反证只针对该着色及其粗化；颜色数量的估计只确定到平方根尺度的常数倍。

**替换能量标签也受到限制。** 在相同的 $B=2^d$ 完整数字盒上，设有限阿贝尔群 $G$ 满足 $|G|\le e^{Cd}$，其中 $C$ 固定。允许着色取决于逐位奇偶和任意二次标签
$$
P(u)=c+\ell(u)+H(u,u)\in G,
$$
其中 $\ell:\mathbb Z^d\to G$ 加性、$H:\mathbb Z^d\times\mathbb Z^d\to G$ 双加性。有限组标签可用直积群表示，容量条件作用于直积的阶。此时 $|V|\ge(1-o(1))N$ 仍成立。

取固定正整数 $R$ 使 $R+1>e^C$。对每个 $z\in\{R,\ldots,B-1-R\}^d$，映射 $L_z(v)=\ell(v)+H(z,v)+H(v,z)$ 加性。在 $\{0,\ldots,R\}^d$ 上有 $(R+1)^d>|G|$ 个输入，因此有非零核差 $h$ 且 $\|h\|_\infty\le R$。展开得 $P(z+h)-P(z-h)=2L_z(h)=0$，不需要除以 2。每个这样的中心都产生一个不同的实际同色和，故 $|V|\ge(B-2R)^d$，除以 $N$ 后下界趋于 1。本结论要求群的阶受限，允许对标签作任意粗化；对额外细分没有给出下界。

## 2. 对所有充分大的 N 改进一般上界

对构造出的着色可同时达到
$$
|V|=o(N),\qquad
\limsup_{N\to\infty}\frac{\log k\,\log\log N}{\log N}\le2\log 2 .
$$
因而同一 limsup 上界适用于 $K(N)$。取 $n=\log N$，并令
$$
B=\left\lfloor\sqrt n/(\log n)^4\right\rfloor,\qquad
d=\left\lceil n/\log B\right\rceil,\qquad M=B^d,\qquad
D=\left\lceil B^2(\log d)^3\right\rceil,\quad q=d^5.
$$
充分大时 $B\ge2,\ N\le M<BN,\ d\sim2n/\log n$。定义 $F(E)=\{u:f(u)\le E\}$，令 $p(E)=|F(E)|/M$，从 $H=dB^2$ 开始取 $E_j=H-jD$。取首个 $p(E_j-D)\le p(E_j)/q$ 的 $j$。初值 $p(H)=1$，负水平为空，故 $j\le\lfloor H/D\rfloor$，并且
$$
0<p=p(E_j),\qquad p\ge q^{-j},\qquad \log(1/p)=O(d/(\log d)^2)=o(d).
$$
这一步允许端点集的密度趋于零。设 $A=F(E_j), W=F(E_j-D)$；决定和集成本的是比值 $|W|/|A|\le1/q$。

取 $L=\lceil2\log M/p\rceil$ 个独立均匀的模 $M$ 平移。漏点数的期望至多 $M(1-p)^L\le M e^{-pL}<1$。固定一个覆盖，给每个区间点指定第一个覆盖它的平移。记录平移编号、恢复后各数字的奇偶，并对 $A$ 中平方距离至多 $4D$ 的不同点作正常的图着色。由稀疏差异计数与贪心着色，这一步至多使用 $(dB+2)^{4D+1}$ 个局部标签；同色的不同端点满足距离平方 $>4D$。于是整数中点 $z=(u+v)/2$ 满足
$$
f(z)=\tfrac12(f(u)+f(v))-\tfrac14\|u-v\|^2<E_j-D .
$$
由于 $e(u)+e(v)=2e(z)$，每个平移的全部局部标签共用 $W$。每个模 $M$ 剩余类至多给出两个区间整数和。按 $[N]$ 编号时和整体加 2。因此
$$
\frac{|V|}{N}\le\frac{2L|W|}{N}
\le 2B(2\log M+1)d^{-5}=o(1).
$$
最后，$\log L=o(d)$；又有 $B^2\le n/(\log n)^8,\ \log d\sim\log n,\ \log(dB+2)=O(\log n)$，故 $(4D+1)\log(dB+2)=O(n/(\log n)^4)=o(d)$。总色数的对数至多 $d\log 2+o(d)$，证明上界。如需更多非空颜色，可拆分至任意不超过 $N$ 的指定类数。

## 3. 任意层厚与重叠平移的限制

保留 $B\ge2,\ d=\lceil\log N/\log B\rceil,\ M=B^d$，允许任意统一间隙 $D>0$，可随 $N$ 变化。每类在某个固定平移 $t$ 下恢复为 $F(E_t)$ 中逐位同奇偶、不同点平方距离 $>4D$ 的数字向量。允许平移标签有各自的阈值，或不同标签使用相同平移。按上述中点证明包住全部零基同色和的模剩余集是
$$
S=\bigcup_t\{\,2t+2e(z)\bmod M:z\in F(E_t-D)\,\}.
$$
这里计算并集本身的大小，因此允许任意重叠。若 $|S|=o(N)$，则此类着色满足
$$
\liminf_{N\to\infty}\frac{\log k\,\log\log N}{\log N}\ge2\log 2.
$$
即使仅要求 $|S|\le N/10$，也有 $\log k=\Omega(\log N/\log\log N)$。这是使用整个下层 $F(E_t-D)$ 作为和集上界时的限制；实际和集很小并不自动保证这个包络也小。

**逐坐标计数。** 令 $h=\lceil\sqrt D\rceil$。若区间点 $x\in\{0,\ldots,N-1\}$ 恢复后的第 $i$ 位 $u_i\ge h$，将该位减少 $h$。能量减少 $2hu_i-h^2\ge h^2\ge D$，所以新向量属于 $F(E_t-D)$。因此 $2x-2hB^i\bmod M\in S$。对每个固定 $i$，此模映射每个值在区间内至多有两个原像，故第 $i$ 位大于等于 $h$ 的点至多有 $2|S|$ 个。这个计数不依赖于恢复该点时选了哪个平移。

**分格。** 设 $\rho=2|S|/N$。每个点的大数字个数平均至多 $\rho d$。任取 $0<\beta<1$，至少 $(1-\rho/\beta)N$ 个点的大数字个数至多为 $\beta d$。在一个颜色类内，大数字的位置及值至多有 $2^d B^{\lfloor\beta d\rfloor}$ 种指定。其余坐标在 $[0,h-1]$；按宽度 $\lfloor\sqrt{D/d}\rfloor+1$ 分成连续整数段，每轴至多 $\sqrt d+2$ 段，因为分母至少为 1 且严格大于 $\sqrt{D/d}$。每个格内的平方距离至多 $D$，故每类每格至多一点。

**取极限。** 对 $|S|=o(N)$ 取 $\beta=\max(2\rho,1/\sqrt n)$，则最终至少一半点满足上述条件，且 $\beta\to0$。若 $d\ge2$，有 $d\log B\le2n$；若 $d=1$，则 $\lfloor\beta d\rfloor=0$。故
$$
n-O(1)\le \log k+d\big(\tfrac12\log d+O(1)\big)+o(n).
$$
沿归一化色数 $\log k\,\log n/n$ 有界的任意子列，用 $d\le1+n/\log2$ 得 $d\ge(2-o(1))n/\log n$，从而 $\log B=O(\log n)$。若 $B$ 在进一步的子列有界，则 $d=\Omega(n)$，而逐位奇偶给出的单类容量至多 $\lceil B/2\rceil^d$，会推出 $\log k\ge d\log(3/2)-\log B=\Omega(n)$，矛盾。因此 $B\to\infty$，同一容量界给出
$$
\log k\ge d\log\big(B/\lceil B/2\rceil\big)-\log B
\ge (2\log 2-o(1))n/\log n .
$$
对 $|S|\le N/10$ 改取 $\beta=1/4$，至少 $N/5$ 个点合格。此时 $\lfloor\beta d\rfloor\log B\le n/2$。若存在子列使 $\log k=o(n/\log n)$，分格迫使 $d=\Omega(n/\log n)$ 和 $\log B=O(\log n)$，再用 $B/\lceil B/2\rceil\ge3/2$ 即得矛盾。第 2 节的构造有 $|S|\le L|W|=o(N)$，故其首项达到本节的界。

## 证据和剩余问题

- 分别在独立上下文中攻击了第 1 节的碰撞、第 2 节的密度与颜色数估计及第 3 节的包络计数，未发现反例。检查覆盖了取整、$D<1$、$d=1$、奇数进制、重叠平移和模翻倍不单射。
- [Lean 有限定理](../Green25/AdaptiveLayer.lean) 同时给出端点数 $a>0$、$B^d\le q^{\lfloor dB^2/D\rfloor}a$，以及满足明确覆盖和标签数条件时的精确分划与 $q|V|\le2La$。第 2 节的新渐近系数和第 3 节的极限下界仍为纸面证明。先前的无条件 $C=16000$ 渐近定理有单独的 Lean 证明。
- 公开查询使用了 “restricted sumsets Ruzsa partition union Behrend monochromatic Green midpoint” 等组合；也复查了 2026 年 Kościuszko 预印本的 Problem 2 与 KitaKen1 的公开仓库。这次有限检索不能确认新颖性。[Kościuszko](https://arxiv.org/html/2610.11847v1) · [KitaKen1](https://github.com/KitaKen1/green-25-upper-bound)
- 对一般着色，$k=\lceil e^{\sqrt{\log N}}\rceil$ 时 Green 的断言仍未判定。第 1 节排除了一个直接的着色；第 3 节排除了让上述完整包络足够小的策略。利用实际可表示中点而不纳入整个下层，或建立适用于任意着色的下界，仍是不同的问题。
