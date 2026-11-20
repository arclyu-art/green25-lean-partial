import Green25.Midpoint
import Green25.SparseColor
import Green25.TranslateCover
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

/-! # From digital tail cardinalities to an exact Green 25 interval partition -/

namespace Green25.Midpoint

noncomputable def endpoints {B d : ℕ} (r : ℝ) : Finset (Box B d) :=
  Finset.univ.filter (fun u ↦ energy u ≤ r)

theorem differences_le_sqDist {B d : ℕ} (u v : Box B d) :
    (differences u v : ℝ) ≤ sqDist u v := by
  classical
  simp only [differences, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, sqDist]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · have hne : (u i).val ≠ (v i).val := fun e ↦ h (Fin.ext e)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh : ((u i).val : ℝ) + 1 ≤ (v i).val := by exact_mod_cast hlt
      push_cast
      nlinarith [sq_nonneg (((v i).val : ℝ) - (u i).val - 1)]
    · have hh : ((v i).val : ℝ) + 1 ≤ (u i).val := by exact_mod_cast hgt
      push_cast
      nlinarith [sq_nonneg (((u i).val : ℝ) - (v i).val - 1)]
  · simpa using sq_nonneg (((u i).val : ℝ) - (v i).val)

/-- Finite form of the construction. Its premises only involve numbers and the sizes of two
explicit digit sets. All coloring, translate-cover and exact-partition witnesses are constructed. -/
theorem exists_exact_of_tail_counts {B d N L m k : ℕ} {μ T : ℝ} (hB : 0 < B)
    (hN : N ≤ B ^ d) (hm : 8 * T ≤ m)
    (hcover : B ^ d * (B ^ d - (endpoints (B := B) (d := d) (μ + T)).card) ^ L <
      (B ^ d) ^ L)
    (hk : L * ((ballBound B d m + 1) * 2 ^ d) ≤ k) (hkN : k ≤ N) :
    ∃ color : Fin N → Fin k, Function.Surjective color ∧
      (restrictedSameColorSums color).card ≤ 2 * (L * (low (B := B) (d := d) (μ - T)).card) := by
  classical
  let M := B ^ d
  haveI : NeZero M := ⟨(pow_pos hB d).ne'⟩
  let A := endpoints (B := B) (d := d) (μ + T)
  let castWord (u : Box B d) : ZMod M := (encode u : ℕ)
  have hval (u : Box B d) : encode u = (finFunctionFinEquiv u).val :=
    (finFunctionFinEquiv_apply u).symm
  have hinj : Function.Injective castWord := by
    intro u v h
    have he := congrArg ZMod.val h
    simp only [castWord, ZMod.val_natCast_of_lt (hval _ ▸ (finFunctionFinEquiv _).isLt)] at he
    apply finFunctionFinEquiv.injective
    exact Fin.ext ((hval u).symm.trans (he.trans (hval v)))
  have hcard : (A.image castWord).card = A.card := Finset.card_image_of_injective _ hinj
  obtain ⟨t, ht⟩ := exists_translate_cover (A.image castWord) L (by
    simpa only [ZMod.card, hcard] using hcover)
  obtain ⟨label, sep⟩ := exists_sparse_color B d m
  apply exists_exact_of_cover hN (fun i ↦ (t i).val) label _ _ hk hkN
  · intro a
    obtain ⟨i, hi⟩ := ht (a.val : ZMod M)
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hi
    refine ⟨i, u, (Finset.mem_filter.mp hu).2, (ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    change castWord u = (a.val : ZMod M) - t i at he
    change (a.val : ZMod M) = t i + castWord u
    rw [he]
    abel
  · intro u v huv _ _ hl
    have hs : (m : ℝ) < differences u v := by exact_mod_cast sep u v huv hl
    exact (hm.trans_lt hs).trans_le (differences_le_sqDist u v)

end Green25.Midpoint
