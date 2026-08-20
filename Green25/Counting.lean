import Green25.Bitwise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Counting binary masks outside a support

This file isolates the finite counting fact behind the factor `2^(d - wt(h))` in attempt 0009.
-/

namespace Green25

/-- Hamming weight of a Boolean vector. -/
def boolWeight {d : ℕ} (h : Fin d → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin d)).filter fun i ↦ h i = true).card

/-- Boolean vectors forced to vanish wherever `h` has a one. -/
def compatibleBits {d : ℕ} (h : Fin d → Bool) : Finset (Fin d → Bool) :=
  Fintype.piFinset fun i ↦ if h i = true then {false} else Finset.univ

theorem card_compatibleBits {d : ℕ} (h : Fin d → Bool) :
    (compatibleBits h).card = 2 ^ (d - boolWeight h) := by
  classical
  rw [compatibleBits, Fintype.card_piFinset]
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_bool, apply_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin d))) (fun i ↦ h i = true)
  have huniv : (Finset.univ : Finset (Fin d)).card = d := Fintype.card_fin d
  change 2 ^ ((Finset.univ.filter fun i ↦ ¬h i = true).card) =
    2 ^ (d - boolWeight h)
  congr 1
  unfold boolWeight
  omega

/-- The lowest `d` bits of a natural number. -/
def natBits (d q : ℕ) : Fin d → Bool := fun i ↦ q.testBit i.val

/-- Two numbers below `2^d` are determined by their lowest `d` bits. -/
theorem natBits_injective_below_two_pow {d q r : ℕ} (hq : q < 2 ^ d) (hr : r < 2 ^ d)
    (hbits : natBits d q = natBits d r) : q = r := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < d
  · exact congrFun hbits ⟨i, hi⟩
  · have hdi : d ≤ i := Nat.le_of_not_gt hi
    have hqi : q < 2 ^ i := hq.trans_le (Nat.pow_le_pow_right (by decide) hdi)
    have hri : r < 2 ^ i := hr.trans_le (Nat.pow_le_pow_right (by decide) hdi)
    rw [Nat.testBit_eq_false_of_lt hqi, Nat.testBit_eq_false_of_lt hri]

/-- Hamming weight of the lowest `d` bits of a natural number. -/
def natBitWeight (d h : ℕ) : ℕ := boolWeight fun i : Fin d ↦ h.testBit i.val

/-- The bit vector of every allowed natural-number mask belongs to the compatible vector set. -/
theorem natBits_mem_compatibleBits_of_mem_allowedMasks {d h q : ℕ}
    (hq : q ∈ allowedMasks d h) :
    natBits d q ∈ compatibleBits (fun i : Fin d ↦ h.testBit i.val) := by
  classical
  rw [compatibleBits, Fintype.mem_piFinset]
  intro i
  by_cases hi : h.testBit i.val = true
  · simp [hi, natBits, testBit_eq_false_of_mem_allowedMasks hq hi]
  · simp [hi]

/-- Bit-vector image of the allowed natural-number masks. -/
def allowedMaskBits (d h : ℕ) : Finset (Fin d → Bool) :=
  (allowedMasks d h).image (natBits d)

theorem allowedMaskBits_subset_compatibleBits (d h : ℕ) :
    allowedMaskBits d h ⊆ compatibleBits (fun i : Fin d ↦ h.testBit i.val) := by
  classical
  intro f hf
  simp only [allowedMaskBits, Finset.mem_image] at hf
  obtain ⟨q, hq, rfl⟩ := hf
  exact natBits_mem_compatibleBits_of_mem_allowedMasks hq

/-- The number of allowed masks is at most `2^(d - wt(h))`, as required in equation (11). -/
theorem card_allowedMasks_le_two_pow_sub_weight (d h : ℕ) :
    (allowedMasks d h).card ≤ 2 ^ (d - natBitWeight d h) := by
  classical
  have hinj : Set.InjOn (natBits d) (allowedMasks d h) := by
    intro q hq r hr hbits
    exact natBits_injective_below_two_pow
      (lt_two_pow_of_mem_allowedMasks hq) (lt_two_pow_of_mem_allowedMasks hr) hbits
  calc
    (allowedMasks d h).card = (allowedMaskBits d h).card := by
      exact (Finset.card_image_of_injOn hinj).symm
    _ ≤ (compatibleBits (fun i : Fin d ↦ h.testBit i.val)).card :=
      Finset.card_le_card (allowedMaskBits_subset_compatibleBits d h)
    _ = 2 ^ (d - natBitWeight d h) := card_compatibleBits _

end Green25
