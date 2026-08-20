# 0010 — 二进制码陪集路线的隔离攻击与撞车审计

- 审计日期：2026-08-19
- 对象：0008 的 `N^(7/8)` 版本及 0009 的重量枚举器强化版
- 状态：`mathematical attacks passed / no exact collision found / expert review absent`
- 原则：每个数学攻击上下文先只找漏洞和反例，不替原证明补台；主线程只在收到报告后
  处理意见。

## 1. 0008 的两路数学攻击

### A. XOR、普通整数和与 restricted 条件

结论：核心 PASS；发现一个非致命解释错误并已修正。

- 同陪集等价于 `a xor b in H`，无遗漏。
- `a=b` 等价于 `a xor b=0`；删掉 `h=0` 正好实施 restricted 条件。
- 固定 `h!=0` 时，攻击者给出精确恒等式

  \[
  a+(a\mathbin{\mathrm{xor}}h)=h+2(a\mathbin{\&}\neg h),
  \]

  所以不同和的个数恰为 `2^(d-wt(h))`。
- 原稿“进位可能造成不同未进位表达式碰撞”的句子不准确：这里不会碰撞。这个错误只在
  解释层，上界本身仍正确；0008 已改成精确恒等式。
- 独立穷举覆盖 `d<=14` 的 32,752 个非零 `h`；另对 `d<=4` 的全部线性子空间核对陪集
  restricted 和并与 XOR 差枚举完全相同，未见反例。

### B. 码存在、取整、裁剪和精确类数

结论：PASS。

- 二项式尾界、`H_2(1/4)<7/8` 及随机线性映射的 union bound 均正确。
- 无低重量非零像自动排除核，不需要另找一个同时单射的随机映射。
- `N>=2^40` 下 0008 的所有严格不等号、`M<2N`、类数和 `N/10` 常数均成立。
- 限制区间、删除空类、整体平移和继续拆分类均只删除同类配对，不产生新和。
- 唯一措辞建议：0008 “强于 `N/log N`”应明确为渐近量级比较，而非对未知常数作逐点比较；
  已修正。

## 2. 0009 强化版的两路数学攻击

### C. 随机重量和及同一次实现

结论：PASS。

攻击重点是下面这个可能的同时性陷阱：平均意义上 `Q(T)` 很小的映射是否可能全都不单射？
答案是否定的，因为若非零 `v` 在核中，`Q(T)` 中对应项已经等于 `1`。所以任一
`Q(T)<1/32` 的实现都自动单射。独立审计重算得到

\[
\mathbb E Q(T)=(2^m-1)(3/4)^d<1/32.
\]

取 `m=floor(log_2(4/3)d-5)` 后，`K<96N^theta`、`|V|<N/16`、ceiling 和所有严格
不等号均通过，`theta=log_2(3/2)`。

### D. 纯反例搜索与方法边界

结论：定理链 PASS；一个可能的过度结论 FAIL。

- 没有找到普通整数加法、跨 `h` 并集、裁剪或拆分类的反例。
- MacWilliams 恒等式只说明 `theta` 对当前
  `M sum_(h!=0) 2^(-wt(h))` **证书**是自然极限。
- 它不能证明整个线性陪集方法最优，因为不同 `h` 的和集可能高度重叠。0009 只保留受限
  的“证书边界”表述，未声称方法或 Green 25 阈值最优。

## 3. 独立计算审计

脚本：`code_coset_weight_audit.py`。

- `d<=6` 的全部 3289 个不同线性子空间逐一通过实际和并/XOR 差/加权上界核对；
- 38,798 个小型线性映射用 `Fraction` 精确验证期望公式及 `Q<1` 自动单射；
- 参数扫描到 `d=4096` 无失败；
- `96N^theta<=N` 首次在 `N=59721` 成立，`N=59720` 是最后失败值；因此定理采用的
  `N>=2^16` 是保守门槛；
- 原脚本一度使用当前 Python 3.7 不支持的 `int.bit_count()`；已机械改为
  `bin(word).count("1")` 并在本机完整重跑通过。这个兼容性问题不涉及数学。

本机复现：

```powershell
py -3 problems\green25\attempts\code_coset_weight_audit.py
```

## 4. 2026-08-19 撞车审计

在本轮实际可访问来源中，未发现同时包含“`[N]` 的分划、普通整数 restricted 类内和的
总并集、二元线性码陪集/XOR、重量枚举器估计”的论文、预印本或公开 AI 解题记录。
这只能表述为“未发现”，绝不是新颖性的证明。

### 已核的最近来源

- Ben Green, *100 Open Problems*, Problem 25：
  https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf
  （版本标注更新 2025-12，仍记录 `k >> N/log N` 的负面范围。）
- ESS89 原文：https://combinatorica.hu/~p_erdos/1989-14.pdf
- Ruzsa 2004 DOI：https://doi.org/10.1090/conm/342/06144
- Ruzsa zbMATH 记录：https://zbmath.org/2145244
- Katz–Tardos 公开稿：https://www.renyi.hu/~tardos/katz.pdf
- Garibaldi–Iosevich–Senger 公开专著：https://alexiosevich.com/erdosbook.pdf
- Irawan 2025：https://arxiv.org/abs/2509.20568
  （研究 `Z_n` 中的 `max_i`，不是 `[N]` 中的 `union_i`，是假阳性。）
- Erdős Problem #484：https://www.erdosproblems.com/484
  （“PROVED (LEAN)” 是固定颜色数 Roth 问题，不是 Green 25。）
- UnsolvedMath GREEN-068：https://www.unsolvedmath.com/problems/GREEN-068
- GPT-Erdős manifest：
  https://github.com/neelsomani/gpt-erdos/blob/main/data/solutions/manifest.json

检索还覆盖 arXiv API、MathOverflow、OpenAlex、Crossref、OpenCitations、zbMATH 公开入口，
并使用 `binary linear code cosets`、`XOR coloring integers`、`weight enumerator restricted
sumset`、`a + (a xor h)`、`N^(7/8)` 等同义组合。

### 未闭合限制

- Google Scholar 的完整引用页触发 CAPTCHA，没有绕过；
- MathSciNet 完整引用网没有订阅访问；
- OpenAlex/Crossref/OpenCitations 把 Ruzsa 被引数记作 0，与已知引用冲突，不能作负证据；
- 尚未向 Green、Ruzsa 或相关专家询问，也没有检查可能尚未公开的工作。

## 5. 当前裁决

0009 可升级为：`candidate partial theorem / internally adversarially reviewed`。

仍不能升级为：

- Green 25 已解决；
- 新颖性已确认；
- `lean-verified-core`；
- `expert-reviewed`；
- `preprint-ready`。

下一项高价值工作不是继续压常数 96，而是由相关方向数学家检查这个短构造是否已知、是否
遗漏了问题语境中的约定，并决定它是否值得独立写成部分结果。
