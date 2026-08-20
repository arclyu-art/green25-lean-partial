# Green Problem 25: a Lean-verified partial construction

> **Status:** private expert-review snapshot. This is a partial result, not a solution of Green
> Problem 25. Novelty and significance have not yet been confirmed by a domain expert.

For a finite set of integers $A$, let

$$
A\widehat{+}A=\{a+b:a,b\in A,\ a\ne b\}.
$$

The formalized result states that, for

$$
N\ge 2^{16},\qquad
\left\lceil 96N^{\log_2(3/2)}\right\rceil\le k\le N,
$$

there is a partition of $[N]$ into exactly $k$ nonempty classes for which the union of all
restricted monochromatic integer sums has cardinality less than $N/10$. The informal construction
actually obtains the stronger bound $N/16$.

The construction colors binary strings by cosets of a binary linear code. Its central bridge from
Boolean addition to ordinary integer addition is

$$
a+(a\mathbin{\mathrm{xor}}h)=h+2(a\mathbin{\&}\neg h).
$$

## What is verified

Lean proves:

```lean
theorem Green25.green25_partial : Green25.PartialTheorem
```

The project builds with Lean 4.32.1 and mathlib 4.32.1, with no `sorry`, `admit`, custom `axiom`, or
`opaque` declaration in the proof. The final theorem uses only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## What is not claimed

- This does not determine the threshold in Green Problem 25.
- It gives no matching lower bound for smaller $k$.
- Lean does not establish novelty, significance, or faithfulness to the intended literature context.
- The repository should not be cited as a solved open problem.

## Contents

- `Green25/`: Lean proof modules.
- `paper/technical-note.pdf`: self-contained expert-review note.
- `audit/statement-map.md`: informal-to-formal statement correspondence.
- `audit/0010-code-coset-adversarial-audit.md`: internal adversarial review.
- `audit/code_coset_weight_audit.py`: finite regression checks; not part of the proof.

See `REPRODUCE.md` for verification commands.
