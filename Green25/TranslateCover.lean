import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! # Finite translate covers by counting tuples that miss a point -/

namespace Green25.Midpoint

/-- If the union bound for all missed points is strictly below the size of the tuple space,
some tuple of translations covers the group. -/
theorem exists_translate_cover {G : Type*} [AddCommGroup G] [Fintype G] (A : Finset G) (L : ℕ)
    (h : Fintype.card G * (Fintype.card G - A.card) ^ L < Fintype.card G ^ L) :
    ∃ t : Fin L → G, ∀ x : G, ∃ i, x - t i ∈ A := by
  classical
  let bad (x : G) := Aᶜ.image (fun y ↦ x - y)
  let missed (x : G) := Fintype.piFinset (fun _ : Fin L ↦ bad x)
  let allBad := Finset.univ.biUnion missed
  have hmiss (x : G) : (missed x).card ≤ (Fintype.card G - A.card) ^ L := by
    rw [show (missed x).card = (bad x).card ^ L from Fintype.card_piFinset_const _ _]
    apply Nat.pow_le_pow_left
    simpa only [bad, Finset.card_compl] using
      (Finset.card_image_le (s := Aᶜ) (f := fun y ↦ x - y))
  have htotal : allBad.card < (Finset.univ : Finset (Fin L → G)).card := by
    calc
      allBad.card ≤ ∑ x : G, (missed x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x : G, (Fintype.card G - A.card) ^ L := Finset.sum_le_sum fun x _ ↦ hmiss x
      _ = Fintype.card G * (Fintype.card G - A.card) ^ L := by simp
      _ < Fintype.card G ^ L := h
      _ = _ := by simp
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card htotal
  refine ⟨t, fun x ↦ ?_⟩
  by_contra! hx
  apply ht
  apply Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_image.mpr ⟨x - t i, Finset.mem_compl.mpr (hx i), by simp⟩

end Green25.Midpoint
