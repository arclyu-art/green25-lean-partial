# Green Problem 25 · Restricted sums in partitions of an interval

This repository gives a Lean-verified construction for Ben Green's Problem 25. For every fixed $\eta\in(0,1]$, one can partition a sufficiently long interval into exactly $\lceil N^\eta\rceil$ nonempty classes so that the ordinary sums of distinct same-colour elements occupy a vanishing fraction of $N$. The proof also gives a subpolynomial choice of colour count. The threshold for arbitrary partitions remains open. [Green's problem list, Problem 25](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.25)

## The verified theorem

Write $[N]=\{1,\ldots,N\}$. For a partition into $k$ classes, let $V$ contain each integer $a+b$ for which $a$ and $b$ are **distinct** members of the same class. Repeated values count once across the whole partition. Green asks for which $k=k(N)$ every such partition satisfies $|V|\ge N/10$.

The formal proof supplies the absolute constant $C=16000$. For **every** $\varepsilon>0$, for all sufficiently large $N$ depending on $\varepsilon$, and for **every integer** $k$ in the range

$$
\left\lceil\exp\!\left(C\,\frac{\log N}{\log\log N}\right)\right\rceil\le k\le N,
$$

there exists a partition of $[N]$ into exactly $k$ nonempty classes with $|V|<\varepsilon N$. Logs are natural. Taking $\varepsilon=1/10$ gives counterexamples in this range. For example, $k=\lceil N^{0.01}\rceil$ eventually suffices. The proof gives no numerical cutoff for this example. [Frozen Lean statement](Green25/Midpoint.lean) · [Proofs of `subpolynomial_bound` and `exact_fixed_power`](Green25/MidpointAsymptotics.lean)

**How the construction works.** Encode integers as digit vectors. Give two endpoints the same colour only if their digits have matching parity and the vectors are far enough apart. Their midpoint is then an integer vector. The squared-norm identity forces it into a small set of low-energy vectors. Translates cover the interval, and the proof counts how many ordinary integer sums each permitted midpoint can produce. [Proof note, in Chinese](paper/0018-midpoint-concentration.md)

## Results and verification status

| Result | Evidence |
| --- | --- |
| Subpolynomial colour count and the fixed-power corollary above | [Full Lean proof](Green25/MidpointAsymptotics.lean) |
| Earlier explicit bound for $N\ge 2^{16}$ and $\lceil96N^{\log_2(3/2)}\rceil\le k\le N$ | [Lean proof](Green25/Parameters.lean) · [English technical note on the binary-code construction](paper/technical-note.pdf) |
| Sharper bound $\limsup_{N\to\infty}\log K(N)\,\log\log N/\log N\le 2\log 2$, where $K(N)$ is the first colour count permitting $\lvert V\rvert<N/10$ | [Written argument and limitations of the construction (Chinese)](paper/0020-adaptive-energy-layers.md) · [Lean proof of the finite layer-selection step](Green25/AdaptiveLayer.lean). The asymptotic constant has a paper proof only. |
| Necessary condition on every nonempty set of permitted sums, and typical behaviour for a uniformly sampled set of permitted sums | [Written proofs and finite check (Chinese)](paper/0021-periods-and-random-envelopes.md). For $s\sim N/10$ permitted sums sampled uniformly without replacement, the minimum colour count is $\Theta(N/\log N)$ with probability tending to one. This statement concerns the random model. |

## What remains open

For the particular scale $k=\lceil\exp(\sqrt{\log N})\rceil$, these arguments leave open whether every partition has $|V|\ge N/10$ for all sufficiently large $N$. A general lower bound follows by observing that the points whose doubles are absent from $V$ form a three-term-progression-free set within each colour class. [Kościuszko, §1](https://arxiv.org/html/2610.11847v1) · [Bloom–Sisask](https://arxiv.org/abs/2309.02353)

A separate Lean project by KitaKen1 already gives the fixed exponent $23/40$ using binary colouring. The random-set argument draws on known bounds for random Cayley sum graphs. These links document prior work relevant to interpreting the results. Priority and expert review are still open. [KitaKen1's construction](https://github.com/KitaKen1/green-25-upper-bound) · [Green–Morris](https://arxiv.org/abs/1305.3079) · [Campos–Dahia–Marciano](https://arxiv.org/abs/2406.09361)

## Reproduce the Lean check

With Elan and Git installed, run from the repository root using the pinned Lean 4.32.1 toolchain.

```sh
lake exe cache get
lake build
lake env lean Green25/Audit.lean
```

The audit prints the axiom dependencies of 14 declarations, including the two asymptotic theorems. Expected output and the finite numerical check are in the [reproduction guide](REPRODUCE.md).

## AI assistance

OpenAI Codex assisted with the constructions, literature searches, proof drafts, counterexample searches, Lean implementation, and exposition. Separate model contexts challenged the paper arguments. The Lean kernel checks the linked formal declarations. The interpretation of the problem, attribution, and mathematical significance require human review.
