import Green25.MidpointPartition

/-! # Selecting a digital energy layer by its relative drop in cardinality (attempt 0020) -/

namespace Green25.Midpoint

private theorem exists_drop (q steps : ℕ) (a : ℕ → ℕ) (hstart : 0 < a 0)
    (hend : a steps = 0) :
    ∃ j < steps, 0 < a j ∧ a 0 ≤ q ^ j * a j ∧ q * a (j + 1) ≤ a j := by
  induction steps generalizing a with
  | zero => omega
  | succ s ih =>
    by_cases h : q * a 1 ≤ a 0
    · exact ⟨0, Nat.zero_lt_succ _, hstart, by simp, h⟩
    have hp : 0 < a 1 := by
      by_contra! hn
      simp [Nat.eq_zero_of_le_zero hn] at h
    obtain ⟨j, hj, hpos, hbound, hdrop⟩ :=
      ih (fun i ↦ a (i + 1)) hp hend
    refine ⟨j + 1, by omega, hpos, ?_, hdrop⟩
    calc
      a 0 ≤ q * a 1 := Nat.le_of_lt (Nat.lt_of_not_ge h)
      _ ≤ q * (q ^ j * a (j + 1)) := Nat.mul_le_mul_left _ hbound
      _ = _ := by rw [pow_succ]; ring

/-- For some nonempty endpoint set of size a, the translated-cover criterion only depends on a,
and q times the number of restricted sums is bounded by twice the number of translates times a. -/
theorem exists_adaptive_partition {B d N D q : ℕ} (hB : 0 < B) (hD : 0 < D)
    (hq : 1 ≤ q) (hN : N ≤ B ^ d) :
    ∃ a : ℕ, 0 < a ∧ a ≤ B ^ d ∧ B ^ d ≤ q ^ (d * B ^ 2 / D) * a ∧
      ∀ L k : ℕ, B ^ d * (B ^ d - a) ^ L < (B ^ d) ^ L →
        L * ((ballBound B d (4 * D) + 1) * 2 ^ d) ≤ k → k ≤ N →
        ∃ color : Fin N → Fin k, Function.Surjective color ∧
          q * (restrictedSameColorSums color).card ≤ 2 * L * a := by
  classical
  let H := d * B ^ 2
  let level (j : ℕ) : ℝ := H - (j : ℝ) * D
  let A (j : ℕ) := endpoints (B := B) (d := d) (level j)
  have htop : A 0 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro u
    simp only [A, endpoints, Finset.mem_filter, Finset.mem_univ, true_and]
    calc
      energy u ≤ ∑ _i : Fin d, (B : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (u i).isLt.le) 2
      _ = level 0 := by simp [level, H]
  have htopcard : (A 0).card = B ^ d := by simp [htop, Box]
  have hlast : (A (H / D + 1)).card = 0 := by
    have hl : level (H / D + 1) < 0 := by
      apply sub_neg.mpr
      exact_mod_cast (show H < (H / D + 1) * D by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ H hD)
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hu' : energy u ≤ level (H / D + 1) := (Finset.mem_filter.mp hu).2
    have he : 0 ≤ energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  obtain ⟨j, hj, ha, hab, hdrop⟩ :=
    exists_drop q (H / D + 1) (fun j ↦ (A j).card) (by rw [htopcard]; positivity) hlast
  have hj' : j ≤ H / D := by omega
  refine ⟨(A j).card, ha, (Finset.card_le_univ _).trans_eq (by simp [Box]), ?_, ?_⟩
  · rw [← htopcard]
    exact hab.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hj'))
  intro L k hcover hk hkN
  let μ := level j - D / 2
  let T : ℝ := D / 2
  have he : μ + T = level j := by dsimp [μ, T]; ring
  have hw : μ - T = level (j + 1) := by simp [μ, T, level]; ring
  obtain ⟨color, hs, hv⟩ := exists_exact_of_tail_counts (μ := μ) (T := T) hB hN
    (by dsimp [T]; push_cast; linarith : 8 * T ≤ ((4 * D : ℕ) : ℝ))
    (by simpa only [he] using hcover) hk hkN
  have hsub : low (B := B) (d := d) (μ - T) ⊆ A (j + 1) := by
    intro u hu
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← hw]
    exact (Finset.mem_filter.mp hu).2.le
  refine ⟨color, hs, ?_⟩
  calc
    _ ≤ q * (2 * (L * (low (B := B) (d := d) (μ - T)).card)) := Nat.mul_le_mul_left _ hv
    _ = (2 * L) * (q * (low (B := B) (d := d) (μ - T)).card) := by ring
    _ ≤ 2 * L * (A j).card := Nat.mul_le_mul_left _
      ((Nat.mul_le_mul_left q (Finset.card_le_card hsub)).trans hdrop)

end Green25.Midpoint
