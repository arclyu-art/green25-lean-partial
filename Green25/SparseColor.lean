import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Bounds

/-! # A finite coloring separating words that differ in few positions -/

namespace Green25.Midpoint

private def changes {B d : ℕ} (u v : Fin d → Fin B) : Finset (Fin d × Fin B) :=
  (Finset.univ.filter (fun i ↦ u i ≠ v i)).image (fun i ↦ (i, v i))

private theorem mem_changes {B d : ℕ} {u v : Fin d → Fin B} {i : Fin d} {a : Fin B} :
    (i, a) ∈ changes u v ↔ u i ≠ v i ∧ v i = a := by
  simp [changes]

private theorem changes_injective {B d : ℕ} (u : Fin d → Fin B) :
    Function.Injective (changes u) := by
  intro v w h
  funext i
  by_cases hv : u i = v i
  · by_contra hn
    have hm := mem_changes.mpr (show u i ≠ w i ∧ w i = w i from ⟨hv ▸ hn, rfl⟩)
    rw [← h] at hm
    exact (mem_changes.mp hm).1 hv
  · have hm := mem_changes.mpr (show u i ≠ v i ∧ v i = v i from ⟨hv, rfl⟩)
    rw [h] at hm
    exact (mem_changes.mp hm).2.symm

def differences {B d : ℕ} (u v : Fin d → Fin B) : ℕ :=
  (Finset.univ.filter (fun i ↦ u i ≠ v i)).card

def ballBound (B d m : ℕ) : ℕ := ∑ j ∈ Finset.range (m + 1), (d * B).choose j

theorem ballBound_add_one_le (B d m : ℕ) : ballBound B d m + 1 ≤ (d * B + 2) ^ (m + 1) := by
  induction m with
  | zero => simp [ballBound]
  | succ m ih =>
    have hc := (Nat.choose_le_pow (d * B) (m + 1)).trans
      (Nat.pow_le_pow_left (show d * B ≤ d * B + 2 by omega) _)
    change (∑ j ∈ Finset.range (m + 1 + 1), (d * B).choose j) + 1 ≤ _
    rw [Finset.sum_range_succ]
    change ballBound B d m + _ + 1 ≤ _
    calc
      _ ≤ (d * B + 2) ^ (m + 1) * 2 := by omega
      _ ≤ (d * B + 2) ^ (m + 1) * (d * B + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := (pow_succ _ _).symm

theorem card_sparse_ball {B d : ℕ} (m : ℕ) (u : Fin d → Fin B) :
    (Finset.univ.filter (fun v ↦ differences u v ≤ m)).card ≤ ballBound B d m := by
  classical
  let U := (Finset.univ : Finset (Fin d × Fin B))
  let S := (Finset.range (m + 1)).biUnion (fun j ↦ U.powersetCard j)
  have hcard (v) : (changes u v).card = differences u v :=
    Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)
  calc
    _ ≤ S.card := by
      apply Finset.card_le_card_of_injOn (changes u) _ (changes_injective u).injOn
      intro v hv
      have h := (Finset.mem_filter.mp hv).2
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le h),
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard v⟩⟩
    _ ≤ _ := Finset.card_biUnion_le
    _ = ballBound B d m := by simp [ballBound, U]

/-- Coloring by induction on the vertices present. The extra label handles an empty domain. -/
theorem exists_sparse_color (B d m : ℕ) :
    ∃ label : (Fin d → Fin B) → Fin (ballBound B d m + 1),
      ∀ u v, u ≠ v → label u = label v → m < differences u v := by
  classical
  let V := Fin d → Fin B
  have extend (s : Finset V) : ∃ label : V → Fin (ballBound B d m + 1),
      ∀ u ∈ s, ∀ v ∈ s, u ≠ v → label u = label v → m < differences u v := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ ↦ 0, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨label, good⟩ := ih
      let forbidden := (Finset.univ.filter (fun v ↦ differences x v ≤ m)).image label
      have hcard : forbidden.card < (Finset.univ : Finset (Fin (ballBound B d m + 1))).card := by
        simpa using Nat.lt_succ_of_le (Finset.card_image_le.trans (card_sparse_ball m x))
      obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      have fresh (v) (h : c = label v) : m < differences x v := by
        by_contra! hn
        exact hc (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, h.symm⟩)
      refine ⟨fun u ↦ if u = x then c else label u, ?_⟩
      intro u hu v hv huv he
      rcases Finset.mem_insert.mp hu with rfl | hus
      · exact fresh v (by simpa [Ne.symm huv] using he)
      rcases Finset.mem_insert.mp hv with rfl | hvs
      · have h := fresh u (by simpa [huv] using he.symm)
        simpa only [differences, ne_comm] using h
      · have hux : u ≠ x := fun h ↦ hx (h ▸ hus)
        have hvx : v ≠ x := fun h ↦ hx (h ▸ hvs)
        exact good _ hus _ hvs huv (by simpa [hux, hvx] using he)
  obtain ⟨label, h⟩ := extend Finset.univ
  exact ⟨label, fun u v ↦ h u (Finset.mem_univ _) v (Finset.mem_univ _)⟩

end Green25.Midpoint
