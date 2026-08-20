import Green25.Statement
import Green25.Bitwise
import Green25.Counting

/-!
# From a coloring to the code-displacement sumset

These lemmas connect the bitwise core to the exact ordinary-integer sumset in the frozen statement.
-/

namespace Green25

/-- The same restricted sumset as in the statement, before translating `{0, ..., N - 1}` by one. -/
def restrictedSameColorSumsZero {N k : ℕ} (color : Fin N → Fin k) : Finset ℕ :=
  ((((Finset.univ : Finset (Fin N)).product (Finset.univ : Finset (Fin N))).filter
      (fun pair ↦ pair.1 ≠ pair.2 ∧ color pair.1 = color pair.2)).image
    (fun pair ↦ pair.1.val + pair.2.val))

theorem mem_restrictedSameColorSums_iff {N k s : ℕ} {color : Fin N → Fin k} :
    s ∈ restrictedSameColorSums color ↔
      ∃ a b : Fin N,
        a ≠ b ∧ color a = color b ∧ (a.val + 1) + (b.val + 1) = s := by
  simp [restrictedSameColorSums, eq_comm, and_assoc]

theorem mem_restrictedSameColorSumsZero_iff {N k s : ℕ} {color : Fin N → Fin k} :
    s ∈ restrictedSameColorSumsZero color ↔
      ∃ a b : Fin N, a ≠ b ∧ color a = color b ∧ a.val + b.val = s := by
  simp [restrictedSameColorSumsZero, eq_comm, and_assoc]

/-- Translating the ground interval by one translates every ordinary pair sum by two. -/
theorem restrictedSameColorSums_eq_image_add_two {N k : ℕ} (color : Fin N → Fin k) :
    restrictedSameColorSums color =
      (restrictedSameColorSumsZero color).image (fun s ↦ s + 2) := by
  classical
  ext s
  constructor
  · intro hs
    rw [mem_restrictedSameColorSums_iff] at hs
    obtain ⟨a, b, hab, hcolor, rfl⟩ := hs
    rw [Finset.mem_image]
    refine ⟨a.val + b.val, ?_, by omega⟩
    rw [mem_restrictedSameColorSumsZero_iff]
    exact ⟨a, b, hab, hcolor, rfl⟩
  · intro hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [mem_restrictedSameColorSumsZero_iff] at ht
    obtain ⟨a, b, hab, hcolor, rfl⟩ := ht
    rw [mem_restrictedSameColorSums_iff]
    exact ⟨a, b, hab, hcolor, by omega⟩

theorem card_restrictedSameColorSums_eq_zero_version {N k : ℕ} (color : Fin N → Fin k) :
    (restrictedSameColorSums color).card = (restrictedSameColorSumsZero color).card := by
  rw [restrictedSameColorSums_eq_image_add_two]
  apply Finset.card_image_of_injective
  intro s t hst
  change s + 2 = t + 2 at hst
  omega

/--
If equal-colored points have XOR displacement in `H`, every unshifted restricted sum is included in
the union of the fixed-displacement sumsets.
-/
theorem restrictedSameColorSumsZero_subset_codePairSums {N k d : ℕ} {H : Finset ℕ}
    (hN : N ≤ 2 ^ d) (color : Fin N → Fin k)
    (hdiff : ∀ a b, color a = color b → a.val ^^^ b.val ∈ H) :
    restrictedSameColorSumsZero color ⊆ codePairSums d H := by
  intro s hs
  rw [mem_restrictedSameColorSumsZero_iff] at hs
  obtain ⟨a, b, hab, hcolor, rfl⟩ := hs
  let h := a.val ^^^ b.val
  have hhH : h ∈ H := hdiff a b hcolor
  have hh0 : h ≠ 0 := by
    intro hh
    have habval : a.val = b.val := by
      have hc := congrArg (fun x ↦ x ^^^ b.val) hh
      simpa [h, Nat.xor_assoc] using hc
    exact hab (Fin.ext habval)
  have ha : a.val < 2 ^ d := a.isLt.trans_le hN
  rw [codePairSums, Finset.mem_biUnion]
  refine ⟨h, Finset.mem_erase.mpr ⟨hh0, hhH⟩, ?_⟩
  simp only [fixedXorPairSums, Finset.mem_image]
  refine ⟨a.val, Finset.mem_range.mpr ha, ?_⟩
  simp [h]

/-- Deterministic form of equation (11), stated for the exact shifted sumset in the theorem. -/
theorem card_restrictedSameColorSums_le_sum_card_allowedMasks {N k d : ℕ} {H : Finset ℕ}
    (hN : N ≤ 2 ^ d) (color : Fin N → Fin k)
    (hdiff : ∀ a b, color a = color b → a.val ^^^ b.val ∈ H) :
    (restrictedSameColorSums color).card ≤
      ∑ h ∈ H.erase 0, (allowedMasks d h).card := by
  calc
    (restrictedSameColorSums color).card = (restrictedSameColorSumsZero color).card :=
      card_restrictedSameColorSums_eq_zero_version color
    _ ≤ (codePairSums d H).card :=
      Finset.card_le_card (restrictedSameColorSumsZero_subset_codePairSums hN color hdiff)
    _ ≤ ∑ h ∈ H.erase 0, (allowedMasks d h).card :=
      card_codePairSums_le_sum_card_allowedMasks d H

/-- Equation (11) with the explicit Hamming-weight bound for every displacement. -/
theorem card_restrictedSameColorSums_le_weight_sum {N k d : ℕ} {H : Finset ℕ}
    (hN : N ≤ 2 ^ d) (color : Fin N → Fin k)
    (hdiff : ∀ a b, color a = color b → a.val ^^^ b.val ∈ H) :
    (restrictedSameColorSums color).card ≤
      ∑ h ∈ H.erase 0, 2 ^ (d - natBitWeight d h) := by
  refine (card_restrictedSameColorSums_le_sum_card_allowedMasks hN color hdiff).trans ?_
  exact Finset.sum_le_sum fun h _ ↦ card_allowedMasks_le_two_pow_sub_weight d h

/--
A `1/32` weight certificate on the surrounding power-of-two interval implies the target `N/10`
bound after cropping. This is the integer form of equation (12).
-/
theorem target_bound_of_weight_certificate {N k d : ℕ} {H : Finset ℕ}
    (hN : N ≤ 2 ^ d) (hM : 2 ^ d < 2 * N) (color : Fin N → Fin k)
    (hdiff : ∀ a b, color a = color b → a.val ^^^ b.val ∈ H)
    (hweight : 32 * (∑ h ∈ H.erase 0, 2 ^ (d - natBitWeight d h)) < 2 ^ d) :
    10 * (restrictedSameColorSums color).card < N := by
  let c := (restrictedSameColorSums color).card
  let S := ∑ h ∈ H.erase 0, 2 ^ (d - natBitWeight d h)
  have hc : c ≤ S := card_restrictedSameColorSums_le_weight_sum hN color hdiff
  have hscaled : 32 * c < 2 * N :=
    (Nat.mul_le_mul_left 32 hc).trans_lt (hweight.trans hM)
  change 10 * c < N
  omega

/-- Refining color classes cannot create a new same-color restricted sum. -/
theorem restrictedSameColorSums_mono_of_refines {N k₁ k₂ : ℕ}
    {coarse : Fin N → Fin k₁} {fine : Fin N → Fin k₂}
    (hrefines : ∀ a b, fine a = fine b → coarse a = coarse b) :
    restrictedSameColorSums fine ⊆ restrictedSameColorSums coarse := by
  intro s hs
  rw [mem_restrictedSameColorSums_iff] at hs ⊢
  obtain ⟨a, b, hab, hsame, rfl⟩ := hs
  exact ⟨a, b, hab, hrefines a b hsame, rfl⟩

theorem card_restrictedSameColorSums_le_of_refines {N k₁ k₂ : ℕ}
    {coarse : Fin N → Fin k₁} {fine : Fin N → Fin k₂}
    (hrefines : ∀ a b, fine a = fine b → coarse a = coarse b) :
    (restrictedSameColorSums fine).card ≤ (restrictedSameColorSums coarse).card :=
  Finset.card_le_card (restrictedSameColorSums_mono_of_refines hrefines)

/-- Restricting a coloring to an initial interval cannot create a new ordinary sum. -/
theorem restrictedSameColorSums_restrict_subset {N N' k : ℕ} (hN : N' ≤ N)
    (color : Fin N → Fin k) :
    restrictedSameColorSums (fun a ↦ color (Fin.castLE hN a)) ⊆
      restrictedSameColorSums color := by
  intro s hs
  rw [mem_restrictedSameColorSums_iff] at hs ⊢
  obtain ⟨a, b, hab, hsame, rfl⟩ := hs
  exact ⟨Fin.castLE hN a, Fin.castLE hN b, by simpa using hab, hsame, by simp⟩

theorem card_restrictedSameColorSums_restrict_le {N N' k : ℕ} (hN : N' ≤ N)
    (color : Fin N → Fin k) :
    (restrictedSameColorSums (fun a ↦ color (Fin.castLE hN a))).card ≤
      (restrictedSameColorSums color).card :=
  Finset.card_le_card (restrictedSameColorSums_restrict_subset hN color)

end Green25
