# Reproducing the verification

Install Git and Elan. The repository pins Lean 4.32.1 and the mathlib dependency revision. In a new clone run the following commands from its root.

```sh
lake exe cache get
lake build
lake env lean Green25/Audit.lean
```

The first command downloads mathlib's precompiled cache. The second builds the default `Green25` library. The third prints the axiom lists for the 14 declarations named in [Audit.lean](Green25/Audit.lean). The final four entries should be

```text
'Green25.Midpoint.exists_exact_of_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green25.Midpoint.subpolynomial_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green25.Midpoint.exact_fixed_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green25.Midpoint.exists_adaptive_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The last entry verifies the finite statement in the adaptive-layer note. Its asymptotic leading constant and the random-model results are recorded as paper arguments. [Adaptive layers](paper/0020-adaptive-energy-layers.md) · [Random permitted sums](paper/0021-periods-and-random-envelopes.md)

## Optional finite checks

For the binary-code construction, run the existing Python regression script.

```sh
python audit/code_coset_weight_audit.py
```

For the finite random-set example with $N=10^6$, 42 colours and 99,999 permitted sums, the following exact integer comparison prints `True`. The proof of the probability bound and the choice of sample size 218 appear in [the random-set note, §2](paper/0021-periods-and-random-envelopes.md).

```sh
python -c "from math import comb; print(comb(10**6,218)*99999**11904*10**14000 < 1999997**11904)"
```
