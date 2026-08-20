# 0009 到 Lean statement 的逐项翻译

冻结对象：`attempts/0009-weight-enumerator-strengthening.md` 的候选部分定理，而不是整个
Green Problem 25。

| 非形式化对象 | Lean 表达 | 等价性说明 |
|---|---|---|
| `[N]={1,...,N}` | `Fin N`，元素解释为 `i.val+1` | 恰好覆盖 `1,...,N` |
| 恰好 `k` 个非空类 | `color : Fin N -> Fin k` 且 `Function.Surjective color` | 每种颜色至少出现一次 |
| 同类且不同的 `a,b` | `a != b` 且 `color a = color b` | 保留 restricted 条件 |
| 普通整数和 | `(a.val+1)+(b.val+1) : Nat` | 不是 XOR，也不是模加法 |
| 所有类受限自和集的并 | `restrictedSameColorSums color` | 枚举有序对后用 `Finset.image` 去重；顺序不改变集合 |
| `|V|<N/10` | `10 * V.card < N` | 对自然数基数与正整数 10 完全等价 |
| `theta=log_2(3/2)` | `Real.log (3/2) / Real.log 2` | 采用换底公式 |
| `ceil(96*N^theta)` | `colorThreshold N` | `Nat.ceil` 作用于非负实数幂 |
| `N>=2^16` | `2^16 <= N` | 与 0009 相同 |

`Green25.PartialTheorem` 是冻结的 `Prop` 定义。现已有

```lean
theorem green25_partial : Green25.PartialTheorem := by
  ...
```

位于 `Green25/Parameters.lean`，并已通过完整构建及公理审计。因此可以称这条**部分定理**
经过 Lean 验证；这仍不等于 Green Problem 25 的完整阈值刻画。

## 已完成的证明分层

1. **确定性码引理**：给定满足重量和界的二元线性码，构造陪集着色并控制和并。
2. **位运算核心**：形式化 `a+(a xor h)=h+2*(a & ~h)` 的有限位版本。
3. **好码存在性**：把随机矩阵论证改写成有限矩阵空间上的平均计数。
4. **裁剪与拆色**：从二次幂区间裁剪到任意 `N`，再拆到精确 `k` 个非空类。
5. **数值层**：闭合 `96`、`2^16`、ceil 与 `N/16<N/10`。

上述五层均已编译；专家材料仍须把“完整 0009 已验证”和“Green 25 未解决”分开写。
