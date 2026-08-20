import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card

/-!
# Green 25 candidate partial theorem: frozen Lean statement

This file defines the exact statement to be formalized from attempt 0009. It intentionally contains
no proof, no `sorry`, and no custom axiom. Defining `PartialTheorem` does not assert that it is true.
-/

namespace Green25

/-- Ordinary integer sums of distinct elements of `[N]` that receive the same color. -/
def restrictedSameColorSums {N k : ℕ} (color : Fin N → Fin k) : Finset ℕ :=
  ((((Finset.univ : Finset (Fin N)).product (Finset.univ : Finset (Fin N))).filter
      (fun pair ↦ pair.1 ≠ pair.2 ∧ color pair.1 = color pair.2)).image
    (fun pair ↦ (pair.1.val + 1) + (pair.2.val + 1)))

/-- The exponent `log_2(3/2)` appearing in attempt 0009. -/
noncomputable def theta : ℝ := Real.log (3 / 2) / Real.log 2

/-- The exact lower threshold for the number of colors in attempt 0009. -/
noncomputable def colorThreshold (N : ℕ) : ℕ :=
  ⌈96 * Real.rpow N theta⌉₊

/--
The complete candidate partial theorem from attempt 0009, expressed as a proposition.

`Function.Surjective color` says that all `k` classes are nonempty. The final natural-number
inequality is exactly the strict real inequality `|V| < N / 10`.
-/
def PartialTheorem : Prop :=
  ∀ N k : ℕ,
    2 ^ 16 ≤ N →
      colorThreshold N ≤ k →
        k ≤ N →
          ∃ color : Fin N → Fin k,
            Function.Surjective color ∧ 10 * (restrictedSameColorSums color).card < N

end Green25
