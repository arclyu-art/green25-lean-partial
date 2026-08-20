import Green25.Partition
import Mathlib.Data.Fintype.EquivFin

/-!
# Refining finite colorings to an exact number of nonempty colors

The construction first discards unused labels, then repeatedly splits one non-singleton fiber.
Every new coloring refines the old one, so it cannot create new same-color sums.
-/

namespace Green25

/-- Labels actually used by a finite coloring. -/
def usedColors {N q : ℕ} (color : Fin N → Fin q) : Finset (Fin q) :=
  (Finset.univ : Finset (Fin N)).image color

/-- Relabel the used colors by a consecutive finite type. -/
noncomputable def normalizedColor {N q : ℕ} (color : Fin N → Fin q) :
    Fin N → Fin (usedColors color).card :=
  fun a ↦ (usedColors color).equivFin
    ⟨color a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

theorem normalizedColor_surjective {N q : ℕ} (color : Fin N → Fin q) :
    Function.Surjective (normalizedColor color) := by
  intro j
  let u : usedColors color := (usedColors color).equivFin.symm j
  obtain ⟨a, _ha, hcolor⟩ := Finset.mem_image.mp u.property
  refine ⟨a, ?_⟩
  change (usedColors color).equivFin
      ⟨color a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩ = j
  rw [← (usedColors color).equivFin.apply_symm_apply j]
  exact congrArg (usedColors color).equivFin (Subtype.ext hcolor)

theorem normalizedColor_eq_imp_color_eq {N q : ℕ} (color : Fin N → Fin q) {a b : Fin N}
    (hab : normalizedColor color a = normalizedColor color b) :
    color a = color b := by
  have hsub := (usedColors color).equivFin.injective hab
  exact congrArg Subtype.val hsub

theorem card_usedColors_le {N q : ℕ} (color : Fin N → Fin q) :
    (usedColors color).card ≤ q := by
  calc
    (usedColors color).card ≤ (Finset.univ : Finset (Fin q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = q := Fintype.card_fin q

/-- More domain points than labels force a repeated color. -/
theorem exists_distinct_same_color_of_lt {N r : ℕ} (color : Fin N → Fin r) (hrN : r < N) :
    ∃ a b, a ≠ b ∧ color a = color b := by
  by_contra hn
  have hinj : Function.Injective color := by
    intro a b hab
    by_contra habne
    exact hn ⟨a, b, habne, hab⟩
  have hcard : N ≤ r := by
    simpa using Fintype.card_le_of_injective color hinj
  omega

/-- Split one non-singleton fiber to add one new nonempty color. -/
theorem splitSurjectiveColor {N r : ℕ} (color : Fin N → Fin r)
    (hsurj : Function.Surjective color) (hrN : r < N) :
    ∃ fine : Fin N → Fin (r + 1),
      Function.Surjective fine ∧
        ∀ a b, fine a = fine b → color a = color b := by
  obtain ⟨x, y, hxy, hcolor⟩ := exists_distinct_same_color_of_lt color hrN
  let fine : Fin N → Fin (r + 1) := fun a ↦
    if a = x then Fin.last r else Fin.castSucc (color a)
  have hfineSurj : Function.Surjective fine := by
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · exact ⟨x, by simp [fine]⟩
    · obtain ⟨a, ha⟩ := hsurj i
      by_cases hax : a = x
      · subst a
        refine ⟨y, ?_⟩
        have hyx : y ≠ x := Ne.symm hxy
        simp [fine, hyx, hcolor.symm.trans ha]
      · exact ⟨a, by simp [fine, hax, ha]⟩
  refine ⟨fine, hfineSurj, ?_⟩
  intro a b hab
  by_cases hax : a = x
  · by_cases hbx : b = x
    · simp [hax, hbx]
    · have hbad : Fin.last r = Fin.castSucc (color b) := by
        simpa [fine, hax, hbx] using hab
      exact (Fin.castSucc_ne_last (color b) hbad.symm).elim
  · by_cases hbx : b = x
    · have hbad : Fin.castSucc (color a) = Fin.last r := by
        simp [fine, hax, hbx] at hab
      exact (Fin.castSucc_ne_last (color a) hbad).elim
    · apply Fin.castSucc_injective r
      simpa [fine, hax, hbx] using hab

/-- Raise a surjective coloring from `r` to any `k` between `r` and `N`. -/
theorem exists_surjective_refinement_of_surjective {N r k : ℕ} (color : Fin N → Fin r)
    (hsurj : Function.Surjective color) (hrk : r ≤ k) (hkN : k ≤ N) :
    ∃ fine : Fin N → Fin k,
      Function.Surjective fine ∧
        ∀ a b, fine a = fine b → color a = color b := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrk
  clear hrk
  revert hkN
  induction t with
  | zero =>
      intro _hkN
      simpa using ⟨color, hsurj, fun _a _b hab ↦ hab⟩
  | succ t ih =>
      intro hkN
      have hprevN : r + t ≤ N := by omega
      obtain ⟨mid, hmidSurj, hmidRefines⟩ := ih hprevN
      have hlt : r + t < N := by omega
      obtain ⟨fine, hfineSurj, hfineRefines⟩ :=
        splitSurjectiveColor mid hmidSurj hlt
      refine ⟨fine, hfineSurj, ?_⟩
      intro a b hab
      exact hmidRefines a b (hfineRefines a b hab)

/-- Any coloring can be refined to exactly `k` nonempty colors once `q ≤ k ≤ N`. -/
theorem exists_surjective_refinement {N q k : ℕ} (color : Fin N → Fin q)
    (hqk : q ≤ k) (hkN : k ≤ N) :
    ∃ fine : Fin N → Fin k,
      Function.Surjective fine ∧
        ∀ a b, fine a = fine b → color a = color b := by
  have hrk : (usedColors color).card ≤ k := (card_usedColors_le color).trans hqk
  obtain ⟨fine, hfineSurj, hfineRefines⟩ :=
    exists_surjective_refinement_of_surjective (normalizedColor color)
      (normalizedColor_surjective color) hrk hkN
  refine ⟨fine, hfineSurj, ?_⟩
  intro a b hab
  exact normalizedColor_eq_imp_color_eq color (hfineRefines a b hab)

end Green25
