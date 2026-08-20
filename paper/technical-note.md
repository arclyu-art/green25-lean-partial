# A binary-code coset construction for restricted monochromatic sums

**Technical note for expert review - 20 August 2026**  
**Status:** candidate partial result; Lean-verified; novelty and significance not yet expert-reviewed.

## Abstract

For a finite set of integers (A), write

\[
A\widehat{+}A=\{a+b:a,b\in A,\ a\ne b\}.
\]

Problem 25 in Ben Green's *100 Open Problems* asks for which (k=k(N)) every partition
([N]=A_1\sqcup\cdots\sqcup A_k) satisfies

\[
\left|\bigcup_{i=1}^k(A_i\widehat{+}A_i)\right|\ge N/10.
\]

This note gives a candidate result on the opposite, constructive side. Put

\[
\theta=\log_2(3/2)=0.5849625007\ldots.
\]

For every (N\ge2^{16}) and every

\[
\lceil96N^\theta\rceil\le k\le N,
\]

we construct a partition into exactly (k) nonempty classes for which the union of all restricted
monochromatic sums has size (<N/16), and hence (<N/10). The construction colors binary strings
by the cosets of a linear code (H\le\mathbb F_2^d) with a small weighted enumerator
(\sum_{0\ne h\in H}2^{-\operatorname{wt}(h)}). The bridge from XOR to ordinary integer addition is
the identity

\[
a+(a\mathbin{\mathrm{xor}}h)=h+2(a\mathbin{\&}\mathord{\sim}h).
\]

The complete frozen statement and proof have been checked in Lean 4. This note does **not** claim a
solution of Green's problem, a matching threshold, or established novelty. We are seeking expert
review of the problem interpretation, literature position, and mathematical significance.

## 1. Statement and scope

All sums in this note are ordinary integer sums, never sums modulo (N). Empty color classes are
not permitted.

**Candidate partial theorem.** Let (\theta=\log_2(3/2)). For every pair of integers (N,k) such
that

\[
N\ge2^{16},\qquad \lceil96N^\theta\rceil\le k\le N,
\tag{1}
\]

there is a partition

\[
[N]=A_1\sqcup\cdots\sqcup A_k
\]

into exactly (k) nonempty classes satisfying

\[
\left|\bigcup_{i=1}^k(A_i\widehat{+}A_i)\right|<\frac N{16}.
\tag{2}
\]

In particular, this partition violates the (N/10) lower bound in Green's question.

This is only a one-sided result. It gives no lower bound for smaller (k), does not locate the true
threshold, and does not solve Green's Problem 25.

### The construction in one paragraph

Choose (d=\lceil\log_2N\rceil) and initially work on the full binary interval
([0,2^d-1]). A finite averaging argument supplies an (m)-dimensional binary linear code
(H\le\mathbb F_2^d) whose weighted enumerator is (<1/32), with
(m\approx\log_2(4/3)d). Color binary strings by the cosets of (H). Two strings of the same color
have XOR difference (h\in H); for a fixed nonzero (h), the identity above shows that their
ordinary integer sums take exactly (2^{d-\operatorname{wt}(h)}) values. Summing this bound over
(h\ne0) gives fewer than (2^d/32) monochromatic sums. Restricting to the first (N) integers
only deletes pairs, and splitting color classes reaches every larger number (k\le N) without
creating new monochromatic sums.

## 2. A code with small weighted enumerator

Set

\[
\gamma=\log_2(4/3)=1-\theta=0.4150374992\ldots.
\]

Fix (d\ge16), and let

\[
m=\lfloor\gamma d-5\rfloor.
\tag{3}
\]

Choose a uniformly random linear map

\[
T:\mathbb F_2^m\longrightarrow\mathbb F_2^d
\]

and define

\[
Q(T)=\sum_{0\ne v\in\mathbb F_2^m}2^{-\operatorname{wt}(T(v))}.
\tag{4}
\]

For each fixed (v\ne0), the vector (T(v)) is uniform on (\mathbb F_2^d). Therefore

\[
\mathbb E\,2^{-\operatorname{wt}(T(v))}
=\left(\frac12\cdot1+\frac12\cdot\frac12\right)^d
=\left(\frac34\right)^d.
\tag{5}
\]

Linearity of expectation gives

\[
\mathbb E Q(T)
=(2^m-1)(3/4)^d
<2^{m-\gamma d}
\le\frac1{32}.
\tag{6}
\]

Hence some (T) satisfies (Q(T)<1/32). This same map is automatically injective: if
(0\ne v\in\ker T), then the corresponding summand in (4) equals (1), a contradiction. Thus

\[
H=T(\mathbb F_2^m)\le\mathbb F_2^d
\]

is an (m)-dimensional code satisfying

\[
\sum_{0\ne h\in H}2^{-\operatorname{wt}(h)}<\frac1{32}.
\tag{7}
\]

The argument uses only a finite average over all (d\times m) binary matrices. Independence between
the terms indexed by different (v) is neither asserted nor needed.

## 3. Code cosets and ordinary integer sums

Let (M=2^d), identify ({0,\ldots,M-1}) with (\mathbb F_2^d) by binary expansion, and color
each vector by its coset modulo (H). There are

\[
K=2^{d-m}
\tag{8}
\]

cosets.

If distinct (a,b\in[0,M-1]) have the same color, then

\[
h=a\mathbin{\mathrm{xor}}b\in H\setminus\{0\}.
\]

Conversely, for each fixed (0\ne h\in H), all pairs (a,a\mathbin{\mathrm{xor}}h) are
monochromatic. The following identity is the central link between the Boolean group and ordinary
integer addition:

\[
a+(a\mathbin{\mathrm{xor}}h)
=h+2(a\mathbin{\&}\mathord{\sim}h).
\tag{9}
\]

Here the complement is taken only in the lowest (d) bits. At a coordinate where (h) is (1),
the two summands have complementary bits and contribute that bit of (h). At a coordinate where
(h) is (0), their common bit contributes twice that power of two. This proves (9) as an exact
identity of ordinary integers, with carries already accounted for.

For fixed (h), the mask (a\mathbin{\&}\mathord{\sim}h) is free precisely on the zero coordinates
of (h). Consequently the sums in (9) take exactly

\[
2^{d-\operatorname{wt}(h)}
\]

distinct values. The omitted case (h=0) is exactly the forbidden case (a=b). If (V_M) is the
union of all restricted monochromatic sums, then (7) yields

\[
\begin{aligned}
|V_M|
&\le\sum_{0\ne h\in H}2^{d-\operatorname{wt}(h)}\\
&=M\sum_{0\ne h\in H}2^{-\operatorname{wt}(h)}\\
&<\frac M{32}.
\end{aligned}
\tag{10}
\]

The first line is only a union bound; possible overlaps between the sets belonging to different
(h) can make the true union smaller.

## 4. From a power of two to arbitrary (N) and exact (k)

For the given (N), take (d=\lceil\log_2N\rceil) and (M=2^d). Then

\[
N\le M<2N.
\]

Restrict the coset coloring to ({0,\ldots,N-1}) and discard empty labels. Restriction only
deletes monochromatic pairs, so

\[
|V_N|\le|V_M|<\frac M{32}<\frac N{16}.
\tag{11}
\]

Let (K_0) denote the number of surviving classes. Since (d) is an integer, (3) gives

\[
d-m=\lceil\theta d\rceil+5.
\]

Using (2^\theta=3/2), we obtain

\[
\begin{aligned}
K_0\le K
&=2^{\lceil\theta d\rceil+5}
<2^{\theta d+6}
=64M^\theta\\
&<64(2N)^\theta
=96N^\theta.
\end{aligned}
\tag{12}
\]

For (N\ge2^{16}), the interval in (1) is nonempty because

\[
(2^{16})^{1-\theta}=(4/3)^{16}>96.
\tag{13}
\]

Thus every (k) in (1) satisfies (K_0\le k\le N). Repeatedly split any nonsingleton class until
exactly (k) nonempty classes remain. A refinement cannot create a monochromatic pair, so (11)
continues to hold. Finally, translating ({0,\ldots,N-1}) to ([N]) translates every sum by two
and preserves the cardinality of the union. This proves the candidate theorem.

## 5. Formal verification and its limits

The Lean statement represents ([N]) by `Fin N`, interprets `a : Fin N` as the ordinary integer
`a.val + 1`, and forms the union by enumerating all ordered pairs of distinct elements with equal
color and deduplicating their ordinary sums. Surjectivity of the coloring means that all (k)
classes are nonempty. The inequality is represented exactly as (10|V|<N).

The development proves

```lean
theorem Green25.green25_partial : Green25.PartialTheorem
```

and checks the following layers:

1. the finite matrix-space average in (5)--(7);
2. injectivity of the selected matrix;
3. the XOR, Hamming-weight, and ordinary-integer bridge in (9)--(10);
4. coset coloring and its number of colors;
5. restriction, removal of empty labels, and refinement to exactly (k) nonempty classes;
6. all floor, ceiling, real-power, and numerical estimates in (11)--(13).

With Lean 4.32.1 and mathlib 4.32.1, the project builds with no `sorry`, `admit`, custom `axiom`, or
`opaque` declaration in the proof. The final theorem depends only on `propext`, `Classical.choice`,
and `Quot.sound`.

Lean verifies the implication expressed by the frozen statement. It does not verify that this is
the intended interpretation of Green's question, that the construction is new, or that it is
significant enough for publication.

## 6. Method boundary

MacWilliams' identity implies that every (m)-dimensional binary linear code satisfies

\[
1+\sum_{0\ne h\in H}2^{-\operatorname{wt}(h)}
\ge2^m(3/4)^d.
\tag{14}
\]

Therefore (\theta=\log_2(3/2)) is a natural boundary for the particular certificate obtained by
summing the fixed-(h) bounds in (10). This is **not** an optimality statement for the entire
code-coset method: fixed-(h) sumsets can overlap. It says still less about the true threshold in
Green's problem.

## 7. Literature status

The principal starting references are:

1. B. Green, *100 Open Problems*, Problem 25.
2. P. Erdős, A. Sárközy, and V. T. Sós, *On a conjecture of Roth and some related problems. I*,
   1989.
3. I. Z. Ruzsa, *A problem on restricted sumsets*, Contemporary Mathematics 342 (2004), 245--248,
   DOI: 10.1090/conm/342/06144.
4. N. H. Katz and G. Tardos, *A new entropy inequality for the Erdős distance problem*, 2004.

A public search on 19 August 2026 did not find the specific combination used here: an interval
partition by binary-code cosets, the XOR-to-integer identity (9), and control through
(\sum_{h\ne0}2^{-\operatorname{wt}(h)}). The search covered arXiv, MathOverflow, the public zbMATH
interface, OpenAlex, Crossref, OpenCitations, and several open-problem and AI-solution trackers.

This is not proof of novelty. The complete Google Scholar citation view was blocked by CAPTCHA,
full MathSciNet citation access was unavailable, and no relevant expert has yet been consulted.
The coding-theoretic ingredients are standard individually, and the entire construction may be
known in another language.

## 8. Questions for the reviewer

The most useful feedback would address the following.

1. Does the theorem faithfully address the negative side of Green's Problem 25, including ordinary
   integer sums and exactly (k) nonempty classes?
2. Is the construction, or a directly equivalent formulation, already known in additive
   combinatorics, Ramsey theory, or coding theory?
3. Is there a reference that already implies the range
   (k\ge96N^{\log_2(3/2)}), perhaps with different constants?
4. Assuming novelty is confirmed, is this result suitable for a short note?
5. Is there a known way to exploit overlaps between the fixed-(h) sumsets in (10), or a structural
   obstruction to doing so?

## Appendix A. Internal checks and reproducibility

Independent internal reviews separately attacked the probabilistic/parameter argument and the
XOR/ordinary-addition argument; no counterexample was found. Exact computations checked every
binary linear subspace through dimension six, 38,798 small linear maps, and the numerical parameter
chain through dimension 4096. These are regression tests only and are not used to prove the theorem.

Relevant files:

- Frozen Lean statement: `lean/Green25/Statement.lean`
- Final theorem: `lean/Green25/Parameters.lean`
- Axiom audit: `lean/Green25/Audit.lean`
- Informal-to-formal map: `lean/statement-map.md`
- Adversarial audit: `attempts/0010-code-coset-adversarial-audit.md`
- Finite audit script: `attempts/code_coset_weight_audit.py`

Local verification:

```powershell
cd C:\math\problems\green25\lean
$env:PATH="C:\math\tools\lean-4.32.1-windows\lean-4.32.1-windows\bin;$env:PATH"
lake build
lake env lean Green25\Audit.lean
```
