import Green25.Cosets
import Green25.Partition
import Green25.Refinement

/-!
# Assembly of the finite code construction

This file combines finite averaging, quotient coloring, and the deterministic sumset bound.  The
first theorem produces the coarse `2^(d-m)`-label coloring; exact nonempty `k`-color refinement and
the real-parameter estimates are kept as separate later layers.
-/

namespace Green25

/-- The quotient coloring, with its codomain rewritten to the explicit cardinal `2^(d-m)`. -/
noncomputable def coarseIntervalColor {m d N : ℕ} (T : BMatrix m d)
    (hT : Function.Injective (applyMatrix T)) (hmd : m ≤ d) :
    Fin N → Fin (2 ^ (d - m)) :=
  fun a ↦ Fin.cast (card_codeQuotient T hT hmd) (intervalCosetColor T a)

theorem intervalColor_eq_of_coarseIntervalColor_eq {m d N : ℕ} (T : BMatrix m d)
    (hT : Function.Injective (applyMatrix T)) (hmd : m ≤ d) {a b : Fin N}
    (hab : coarseIntervalColor T hT hmd a = coarseIntervalColor T hT hmd b) :
    intervalCosetColor T a = intervalCosetColor T b := by
  exact Fin.cast_injective (card_codeQuotient T hT hmd) hab

/--
Purely integer-parameter coarse construction.  The only numerical input is the exact finite-average
inequality `havg`; all additive-combinatorial conclusions are assembled here.
-/
theorem exists_coarseColor_of_average {N m d : ℕ}
    (hN : N ≤ 2 ^ d) (hM : 2 ^ d < 2 * N) (hmd : m ≤ d)
    (havg :
      32 * ((2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d) <
        (2 ^ m) ^ d * 2 ^ d) :
    ∃ color : Fin N → Fin (2 ^ (d - m)),
      10 * (restrictedSameColorSums color).card < N := by
  obtain ⟨T, hcert⟩ := exists_matrixScore_certificate havg
  have hT : Function.Injective (applyMatrix T) :=
    applyMatrix_injective_of_certificate T hcert
  let color : Fin N → Fin (2 ^ (d - m)) :=
    coarseIntervalColor (N := N) T hT hmd
  have hdiff : ∀ a b, color a = color b → a.val ^^^ b.val ∈ codeNatFinset T := by
    intro a b hab
    apply xor_mem_codeNatFinset_of_intervalColor_eq T hN
    exact intervalColor_eq_of_coarseIntervalColor_eq T hT hmd hab
  have hweight :
      32 * (∑ h ∈ (codeNatFinset T).erase 0, 2 ^ (d - natBitWeight d h)) < 2 ^ d := by
    rw [codeNatFinset_weight_sum_eq_matrixScore T hT]
    exact hcert
  refine ⟨color, ?_⟩
  exact target_bound_of_weight_certificate hN hM color hdiff hweight

/--
Complete exact-`k` construction for integer parameters satisfying the finite-average inequality.
All `k` color classes are nonempty.
-/
theorem exists_exactColor_of_average {N m d k : ℕ}
    (hN : N ≤ 2 ^ d) (hM : 2 ^ d < 2 * N) (hmd : m ≤ d)
    (havg :
      32 * ((2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d) <
        (2 ^ m) ^ d * 2 ^ d)
    (hcolors : 2 ^ (d - m) ≤ k) (hkN : k ≤ N) :
    ∃ color : Fin N → Fin k,
      Function.Surjective color ∧ 10 * (restrictedSameColorSums color).card < N := by
  obtain ⟨coarse, hcoarse⟩ := exists_coarseColor_of_average hN hM hmd havg
  obtain ⟨fine, hfineSurj, hfineRefines⟩ :=
    exists_surjective_refinement coarse hcolors hkN
  refine ⟨fine, hfineSurj, ?_⟩
  have hcard :
      (restrictedSameColorSums fine).card ≤ (restrictedSameColorSums coarse).card :=
    card_restrictedSameColorSums_le_of_refines hfineRefines
  exact (Nat.mul_le_mul_left 10 hcard).trans_lt hcoarse

end Green25
