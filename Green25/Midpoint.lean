import Green25.Refinement
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Digital midpoints in the subpolynomial construction (attempt 0018) -/

namespace Green25.Midpoint

abbrev Box (B d : ℕ) := Fin d → Fin B

def encode {B d : ℕ} (u : Box B d) : ℕ := ∑ i, (u i).val * B ^ i.val

def energy {B d : ℕ} (u : Box B d) : ℝ := ∑ i, ((u i).val : ℝ) ^ 2

def sqDist {B d : ℕ} (u v : Box B d) : ℝ :=
  ∑ i, ((u i).val - (v i).val : ℝ) ^ 2

def parity {B d : ℕ} (u : Box B d) : Fin d → Fin 2 :=
  fun i ↦ ⟨(u i).val % 2, Nat.mod_lt _ (by decide)⟩

def mid {B d : ℕ} (u v : Box B d) : Box B d :=
  fun i ↦ ⟨((u i).val + (v i).val) / 2, by have := (u i).isLt; have := (v i).isLt; omega⟩

theorem twice_mid_digit {B d : ℕ} {u v : Box B d} (hp : parity u = parity v) (i : Fin d) :
    2 * (mid u v i).val = (u i).val + (v i).val := by
  have h := congrArg (fun p : Fin d → Fin 2 ↦ (p i).val) hp
  change (u i).val % 2 = (v i).val % 2 at h
  unfold mid
  dsimp
  omega

/-- An identity of ordinary integers, including when doubling the midpoint carries. -/
theorem encode_mid {B d : ℕ} {u v : Box B d} (hp : parity u = parity v) :
    encode u + encode v = 2 * encode (mid u v) := by
  simp only [encode, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_mul, ← mul_assoc, twice_mid_digit hp]

theorem energy_mid {B d : ℕ} {u v : Box B d} (hp : parity u = parity v) :
    4 * energy (mid u v) + sqDist u v = 2 * (energy u + energy v) := by
  simp only [energy, sqDist, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : 2 * ((mid u v i).val : ℝ) = (u i).val + (v i).val := by
    exact_mod_cast twice_mid_digit hp i
  linear_combination (2 * ((mid u v i).val : ℝ) + (u i).val + (v i).val) * h

/-- All separated pairs of the same parity, across every color, share this one midpoint set. -/
noncomputable def low {B d : ℕ} (r : ℝ) : Finset (Box B d) :=
  Finset.univ.filter (fun u ↦ energy u < r)

theorem mid_mem_low {B d : ℕ} {u v : Box B d} {μ T : ℝ}
    (hp : parity u = parity v) (hu : energy u ≤ μ + T) (hv : energy v ≤ μ + T)
    (hfar : 8 * T < sqDist u v) : mid u v ∈ low (μ - T) := by
  simp only [low, Finset.mem_filter, Finset.mem_univ, true_and]
  linarith [energy_mid hp]

/-- The number of ordinary integer sums is at most twice the number of allowed residues. -/
theorem card_sums_of_residues {N M k : ℕ} (hNM : N ≤ M) (color : Fin N → Fin k)
    (R : Finset ℕ) (hits : ∀ a b, a ≠ b → color a = color b → (a.val + b.val) % M ∈ R) :
    (restrictedSameColorSums color).card ≤ 2 * R.card := by
  rw [card_restrictedSameColorSums_eq_zero_version]
  have hsub : restrictedSameColorSumsZero color ⊆ R ∪ R.image (fun r ↦ r + M) := by
    intro s hs
    obtain ⟨a, b, hab, hc, rfl⟩ := mem_restrictedSameColorSumsZero_iff.mp hs
    have h := hits a b hab hc
    have ha := a.isLt
    have hb := b.isLt
    by_cases hlt : a.val + b.val < M
    · exact Finset.mem_union_left _ (Nat.mod_eq_of_lt hlt ▸ h)
    · have hmod : (a.val + b.val) % M = a.val + b.val - M := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, h, by omega⟩)
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 * R.card := by have := Finset.card_image_le (s := R) (f := fun r ↦ r + M); omega

/-- A cover of the interval by translates of the light endpoint set and a local separation
coloring give an exact partition with at most two integer lifts per translated low midpoint. -/
theorem exists_exact_of_cover {B d N M L q k : ℕ} {μ T : ℝ} (hNM : N ≤ M)
    (t : Fin L → ℕ) (label : Box B d → Fin q)
    (cover : ∀ a : Fin N, ∃ (i : Fin L) (u : Box B d), energy u ≤ μ + T ∧ a.val ≡ t i + encode u [MOD M])
    (sep : ∀ u v, u ≠ v → energy u ≤ μ + T → energy v ≤ μ + T →
      label u = label v → 8 * T < sqDist u v)
    (hcolors : L * (q * 2 ^ d) ≤ k) (hkN : k ≤ N) :
    ∃ color : Fin N → Fin k, Function.Surjective color ∧
      (restrictedSameColorSums color).card ≤ 2 * (L * (low (B := B) (d := d) (μ - T)).card) := by
  classical
  choose i u hu hx using cover
  let V := Fin L × Fin q × (Fin d → Fin 2)
  let color (a : Fin N) := Fintype.equivFin V (i a, label (u a), parity (u a))
  let W := low (B := B) (d := d) (μ - T)
  let R := (Finset.univ ×ˢ W).image (fun p : Fin L × Box B d ↦ (2 * (t p.1 + encode p.2)) % M)
  have hR : R.card ≤ L * W.card := by
    exact Finset.card_image_le.trans (by simp)
  have hc := card_sums_of_residues hNM color R (by
    intro a b hab hcol
    have he := (Fintype.equivFin V).injective hcol
    have hi : i a = i b := congrArg Prod.fst he
    have hl : label (u a) = label (u b) := congrArg (fun p : V ↦ p.2.1) he
    have hp : parity (u a) = parity (u b) := congrArg (fun p : V ↦ p.2.2) he
    have hne : u a ≠ u b := by
      intro heq
      have ha := hx a
      rw [hi, heq] at ha
      have habm : a.val % M = b.val % M := ha.trans (hx b).symm
      rw [Nat.mod_eq_of_lt (a.isLt.trans_le hNM), Nat.mod_eq_of_lt (b.isLt.trans_le hNM)] at habm
      exact hab (Fin.ext habm)
    have hz := mid_mem_low hp (hu a) (hu b) (sep _ _ hne (hu a) (hu b) hl)
    apply Finset.mem_image.mpr
    refine ⟨(i a, mid (u a) (u b)), Finset.mem_product.mpr ⟨Finset.mem_univ _, hz⟩, ?_⟩
    have hm := (hx a).add (hx b)
    rw [← hi, show t (i a) + encode (u a) + (t (i a) + encode (u b)) =
      2 * (t (i a) + encode (mid (u a) (u b))) by linarith only [encode_mid hp]] at hm
    exact hm.symm)
  have hqk : Fintype.card V ≤ k := by simpa [V] using hcolors
  obtain ⟨fine, hs, hf⟩ := exists_surjective_refinement color hqk hkN
  exact ⟨fine, hs, (card_restrictedSameColorSums_le_of_refines hf).trans
    (hc.trans (Nat.mul_le_mul_left 2 hR))⟩

/-- Exact asymptotic target. Each tolerance may have its own threshold, with one absolute C. -/
def SubpolynomialBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ∀ k : ℕ, ⌈Real.exp (C * Real.log N / Real.log (Real.log N))⌉₊ ≤ k → k ≤ N →
      ∃ color : Fin N → Fin k, Function.Surjective color ∧
        ((restrictedSameColorSums color).card : ℝ) < ε * N

end Green25.Midpoint
