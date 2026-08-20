# 以 Lean 为骨架的专家审读图

审读对象仅为 `attempts/0009-weight-enumerator-strengthening.md` 的候选部分定理，不是
Green Problem 25 的完整解答。Lean 与人工稿必须双向对应：人工稿负责解释思想与新颖性，
Lean 负责核对被冻结命题内的推导链。

## 当前总状态

| 层 | 人工稿 | Lean 目标 | 当前状态 | 专家需要重点看什么 |
|---|---|---|---|---|
| 0. 精确题面 | 0009 §1 | `Green25.PartialTheorem` | 已编译并由总定理实现 | 是否忠实表达分划、restricted 普通整数和与全部量词 |
| 1. 加权码存在 | 0009 §2, (3)–(8) | `sum_matrixScore`, `exists_matrixScore_certificate` | 已证 | 双计数是否与人工稿的随机矩阵完全同义 |
| 2. 陪集和集界 | 0009 §3, (9)–(11) | `card_codeQuotient` 等 | 已证 | Boolean 加法、Nat XOR、普通整数和三者的翻译 |
| 3. 裁剪与拆色 | 0009 §4, (12) | `exists_surjective_refinement` | 已证 | 恰好 `k` 个非空类以及 refinement 方向 |
| 4. 数值常数 | 0009 §4, (13) | `finite_average_inequality`, `codeColorCount_le_threshold` | 已证 | floor/ceil、`96`、`2^16` 的人工可读推导 |
| 5. 总装配 | 0009 §1–4 | `green25_partial : PartialTheorem` | 已证；2019-job build 通过 | 题面翻译、新颖性、重要性；不是再找 Lean 类型错误 |

## 状态词的严格含义

- `statement 已编译`：Lean 接受定义和类型；不表示命题为真。
- `引理已证明`：相应证明项编译通过，但只覆盖表中明确范围。
- `core verified`：第 1–5 层全部编译、零 `sorry`，并完成 `#print axioms` 审计。
- `expert reviewed`：相关领域研究者核对数学翻译、语境与可能的既有结果；Lean 不能给出
  这一状态。

## 审读材料顺序

1. 一页结论与非结论：精确写出 0009，并说明它只覆盖构造侧的
   `k >= ceil(96 N^theta)`。
2. `statement-map.md`：先请专家检查形式化题面有没有误译。
3. 本表：逐层列出人工证明位置、Lean 覆盖范围和未闭合风险。
4. 0009 正文：作为可读的数学证明。
5. 0010 的独立攻击和计算脚本：作为审计附件，不替代证明。
6. 文献检索表：单独处理新颖性，避免把 Lean 正确性误当成首次发现。

当前对专家可称 `candidate partial theorem 0009 with a complete Lean verification`。仍必须明确：
专家尚未审读，公开撞车检索受数据库限制，且该定理只给 Green 25 的构造侧部分范围。
