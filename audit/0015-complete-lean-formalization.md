# 0015：0009 的完整 Lean 形式化

日期：2026-08-20（Asia/Shanghai）

## 结论

冻结命题 `Green25.PartialTheorem` 现有证明项：

```lean
theorem Green25.green25_partial : Green25.PartialTheorem
```

它断言：若 `N >= 2^16` 且
`ceil(96 * N^(log_2(3/2))) <= k <= N`，则 `[N]` 存在恰好 `k` 个非空类的分划，全部类的
restricted 普通整数自和集之并满足 `10 * |V| < N`。

这是 Green Problem 25 的构造侧部分定理，不是完整阈值刻画。

## 新增形式层

- `Averaging.lean`：把随机矩阵论证改成有限函数空间的精确双计数；严格证书同时推出矩阵
  单射。
- `Cosets.lean`：证明 `Nat.ofBits` 保持 XOR 和 Hamming weight；构造像子群与商群颜色，
  用 Lagrange 定理算出 `2^(d-m)` 个颜色。
- `Refinement.lean`：先删除空标签，再逐次拆出单点类，得到恰好 `k` 个非空类；证明细化
  不创造同色和。
- `Assembly.lean`：在纯整数参数和精确平均不等式下组装最终分划。
- `Parameters.lean`：取 `d=Nat.clog 2 N`、
  `m=floor((1-theta)d)-5`，验证 `2^d<2N`、平均不等式、常数 `96`、floor/ceil/rpow，最后
  给出 `green25_partial`。

## 机器核验

固定版本：Lean `v4.32.1`、mathlib `v4.32.1`。

```powershell
lake build
lake env lean Green25\Audit.lean
```

结果：完整构建退出码 `0`，共 2019 jobs。最终定理及关键中间声明的 `#print axioms` 均只
列出 `propext`、`Classical.choice`、`Quot.sound`。源文件扫描没有 `sorry`、`admit`、自定义
`axiom` 或 `opaque`；唯一字符串 `sorry` 位于 `Statement.lean` 的说明注释。

## 仍未由 Lean 解决的事项

1. 形式 statement 是否忠实表达人工题面，需要人类逐项审读。
2. 定理是否已有同构版本、构造是否实质新颖，需要更新的完整文献检索与专家判断。
3. 该部分范围对 Green 25 的研究价值和最佳表述，需要加法组合专家审读。
4. Green 25 要求的整体 `k(N)` 阈值刻画仍未解决。
