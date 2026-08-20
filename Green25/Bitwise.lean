import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bitwise identity for the Green 25 candidate construction

This file formalizes the ordinary-integer identity used in equation (10) of attempt 0009.
`Nat.ldiff a h` keeps exactly the bits of `a` at positions where `h` has a zero bit.
-/

namespace Green25

/-- The XOR pair sum is an ordinary integer determined by `h` and the bits of `a` outside `h`. -/
theorem add_xor_eq_add_two_mul_ldiff (a h : ℕ) :
    a + (a ^^^ h) = h + 2 * Nat.ldiff a h := by
  induction a using Nat.binaryRec' generalizing h with
  | zero => simp [Nat.ldiff]
  | bit ab a ha ih =>
      induction h using Nat.binaryRec' with
      | zero =>
          simp [Nat.ldiff, Nat.bit_val]
          omega
      | bit hb h hh =>
          rw [Nat.xor_bit, Nat.ldiff_bit]
          simp only [Nat.bit_val]
          have hih := ih h
          cases ab <;> cases hb <;> simp at hih ⊢ <;> omega

/-- Deleting bits never increases a natural number. -/
theorem ldiff_le_left (a h : ℕ) : Nat.ldiff a h ≤ a := by
  induction a using Nat.binaryRec' generalizing h with
  | zero => simp [Nat.ldiff]
  | bit ab a ha ih =>
      induction h using Nat.binaryRec' with
      | zero => simp [Nat.ldiff]
      | bit hb h hh =>
          rw [Nat.ldiff_bit]
          simp only [Nat.bit_val]
          have hih := ih h
          cases ab <;> cases hb <;> simp at hih ⊢ <;> omega

/-- All ordinary sums obtained from the XOR displacement `h` on the `d`-bit interval. -/
def fixedXorPairSums (d h : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ d)).image fun a ↦ a + (a ^^^ h)

/-- Values of `a` after deleting every bit that belongs to the displacement `h`. -/
def allowedMasks (d h : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ d)).image fun a ↦ Nat.ldiff a h

/-- Equation (10) identifies the fixed-displacement sums with an affine image of the masks. -/
theorem fixedXorPairSums_eq_image_allowedMasks (d h : ℕ) :
    fixedXorPairSums d h = (allowedMasks d h).image (fun q ↦ h + 2 * q) := by
  classical
  ext s
  simp [fixedXorPairSums, allowedMasks, add_xor_eq_add_two_mul_ldiff]

/-- The affine map in equation (10) is injective, so it creates no extra collisions. -/
theorem card_fixedXorPairSums_eq_card_allowedMasks (d h : ℕ) :
    (fixedXorPairSums d h).card = (allowedMasks d h).card := by
  rw [fixedXorPairSums_eq_image_allowedMasks]
  apply Finset.card_image_of_injective
  intro q r hqr
  change h + 2 * q = h + 2 * r at hqr
  omega

/-- An allowed mask is zero at every bit where `h` has a one. -/
theorem testBit_eq_false_of_mem_allowedMasks {d h q i : ℕ} (hq : q ∈ allowedMasks d h)
    (hi : h.testBit i = true) : q.testBit i = false := by
  classical
  simp only [allowedMasks, Finset.mem_image] at hq
  obtain ⟨a, _, rfl⟩ := hq
  simp [Nat.testBit_ldiff, hi]

theorem lt_two_pow_of_mem_allowedMasks {d h q : ℕ} (hq : q ∈ allowedMasks d h) :
    q < 2 ^ d := by
  classical
  simp only [allowedMasks, Finset.mem_image] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  exact (ldiff_le_left a h).trans_lt (Finset.mem_range.mp ha)

/-- Union of all fixed-displacement ordinary sumsets for the nonzero words in `H`. -/
def codePairSums (d : ℕ) (H : Finset ℕ) : Finset ℕ :=
  (H.erase 0).biUnion (fixedXorPairSums d)

/-- The union bound in equation (11), before evaluating the number of allowed masks. -/
theorem card_codePairSums_le_sum_card_allowedMasks (d : ℕ) (H : Finset ℕ) :
    (codePairSums d H).card ≤ ∑ h ∈ H.erase 0, (allowedMasks d h).card := by
  calc
    (codePairSums d H).card ≤ ∑ h ∈ H.erase 0, (fixedXorPairSums d h).card :=
      Finset.card_biUnion_le
    _ = ∑ h ∈ H.erase 0, (allowedMasks d h).card := by
      apply Finset.sum_congr rfl
      intro h _
      exact card_fixedXorPairSums_eq_card_allowedMasks d h

end Green25
