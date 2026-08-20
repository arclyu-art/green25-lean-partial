import Green25.Counting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Finite averaging for binary linear maps

This file replaces the probabilistic language in attempt 0009 by exact sums over finite
function spaces.  The first layer records the weight enumerator of all Boolean vectors.
-/

namespace Green25

/-- A Boolean vector of length `d`. -/
abbrev BVec (d : ℕ) := Fin d → Bool

/-- Boolean dot product, using xor as addition and `and` as multiplication. -/
def boolDot {m : ℕ} (x v : BVec m) : Bool :=
  ∑ i, x i * v i

/-- Toggle one coordinate of a Boolean vector. -/
def toggleCoord {m : ℕ} (p : Fin m) (x : BVec m) : BVec m :=
  Function.update x p (!x p)

/-- Toggling the same coordinate twice is the identity. -/
theorem toggleCoord_involutive {m : ℕ} (p : Fin m) :
    Function.Involutive (toggleCoord p) := by
  intro x
  funext i
  by_cases hi : i = p
  · subst i
    simp [toggleCoord]
  · simp [toggleCoord, Function.update_of_ne hi]

/-- Toggling a coordinate on which `v` is one toggles the Boolean dot product. -/
theorem boolDot_toggleCoord {m : ℕ} (x v : BVec m) (p : Fin m) (hp : v p = true) :
    boolDot (toggleCoord p x) v = !(boolDot x v) := by
  classical
  unfold boolDot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  simp only [toggleCoord, Function.update_self, hp]
  have htail :
      (∑ i ∈ Finset.univ.erase p, Function.update x p (!x p) i * v i) =
        ∑ i ∈ Finset.univ.erase p, x i * v i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hip : i ≠ p := Finset.ne_of_mem_erase hi
    simp [Function.update_of_ne hip]
  rw [htail]
  generalize (∑ i ∈ Finset.univ.erase p, x i * v i) = b
  cases x p <;> cases b <;> decide

/-- The coordinate toggle as an equivalence of the finite row space. -/
def toggleCoordEquiv {m : ℕ} (p : Fin m) : BVec m ≃ BVec m where
  toFun := toggleCoord p
  invFun := toggleCoord p
  left_inv := toggleCoord_involutive p
  right_inv := toggleCoord_involutive p

/-- A zero dot product has weight two and a one dot product has weight one. -/
def bitScore (b : Bool) : ℕ :=
  if b = true then 1 else 2

theorem bitScore_add_toggle (b : Bool) : bitScore b + bitScore (!b) = 3 := by
  cases b <;> decide

/-- Exact one-row weighted count when `v` has a specified nonzero coordinate. -/
theorem sum_bitScore_boolDot_of_coord_one {m : ℕ} (v : BVec m) (p : Fin m)
    (hp : v p = true) :
    ∑ x : BVec m, bitScore (boolDot x v) = 3 * 2 ^ (m - 1) := by
  classical
  let S : ℕ := ∑ x : BVec m, bitScore (boolDot x v)
  have htoggle :
      (∑ x : BVec m, bitScore (boolDot (toggleCoord p x) v)) = S := by
    exact Equiv.sum_comp (toggleCoordEquiv p) (fun x ↦ bitScore (boolDot x v))
  have htwice : 2 * S = 3 * 2 ^ m := by
    calc
      2 * S = S + S := by omega
      _ = (∑ x : BVec m, bitScore (boolDot x v)) +
          ∑ x : BVec m, bitScore (boolDot (toggleCoord p x) v) := by
        rw [htoggle]
      _ = ∑ x : BVec m,
          (bitScore (boolDot x v) + bitScore (boolDot (toggleCoord p x) v)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _x : BVec m, 3 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [boolDot_toggleCoord x v p hp]
        exact bitScore_add_toggle _
      _ = 3 * 2 ^ m := by simp [mul_comm]
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    exact Fin.elim0 p
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one]
  rw [pow_succ] at htwice
  have hcancel : 2 * S = 2 * (3 * 2 ^ s) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using htwice
  exact Nat.mul_left_cancel (by decide) hcancel

/-- Exact one-row weighted count for every nonzero input vector. -/
theorem sum_bitScore_boolDot_of_ne_zero {m : ℕ} (v : BVec m) (hv : v ≠ 0) :
    ∑ x : BVec m, bitScore (boolDot x v) = 3 * 2 ^ (m - 1) := by
  classical
  have hex : ∃ p : Fin m, v p = true := by
    by_contra hn
    apply hv
    funext p
    cases hp : v p with
    | false => rfl
    | true => exact (hn ⟨p, hp⟩).elim
  obtain ⟨p, hp⟩ := hex
  exact sum_bitScore_boolDot_of_coord_one v p hp

/-- A `d`-row Boolean matrix acting on `m`-bit column vectors. -/
abbrev BMatrix (m d : ℕ) := Fin d → BVec m

/-- Matrix-vector multiplication over the Boolean ring. -/
def applyMatrix {m d : ℕ} (T : BMatrix m d) (v : BVec m) : BVec d :=
  fun j ↦ boolDot (T j) v

/-- The integer weight attached to a Boolean vector in the code construction. -/
def vectorScore {d : ℕ} (x : BVec d) : ℕ :=
  2 ^ (d - boolWeight x)

/-- The score factors coordinate by coordinate: a zero contributes two and a one contributes one. -/
theorem vectorScore_eq_prod {d : ℕ} (x : BVec d) :
    vectorScore x = ∏ i : Fin d, if x i = true then 1 else 2 := by
  classical
  unfold vectorScore
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin d))) (fun i ↦ x i = true)
  have huniv : (Finset.univ : Finset (Fin d)).card = d := Fintype.card_fin d
  change 2 ^ (d - boolWeight x) = 2 ^ ((Finset.univ.filter fun i ↦ ¬x i = true).card)
  congr 1
  unfold boolWeight
  omega

/-- The exact finite average numerator for a uniformly chosen Boolean vector. -/
theorem sum_vectorScore (d : ℕ) :
    ∑ x : BVec d, vectorScore x = 3 ^ d := by
  classical
  simp_rw [vectorScore_eq_prod]
  calc
    (∑ x : BVec d, ∏ i : Fin d, if x i = true then 1 else 2) =
        ∏ i : Fin d, ∑ b : Bool, if b = true then 1 else 2 := by
      exact (Fintype.prod_sum
        (fun (_ : Fin d) (b : Bool) ↦ if b = true then (1 : ℕ) else 2)).symm
    _ = 3 ^ d := by simp

/-- Exact weighted sum over all matrices for one fixed nonzero input vector. -/
theorem sum_vectorScore_applyMatrix_of_ne_zero {m d : ℕ} (v : BVec m) (hv : v ≠ 0) :
    ∑ T : BMatrix m d, vectorScore (applyMatrix T v) =
      (3 * 2 ^ (m - 1)) ^ d := by
  classical
  simp_rw [vectorScore_eq_prod]
  change (∑ T : BMatrix m d, ∏ j : Fin d, bitScore (boolDot (T j) v)) = _
  calc
    (∑ T : BMatrix m d, ∏ j : Fin d, bitScore (boolDot (T j) v)) =
        ∏ _j : Fin d, ∑ row : BVec m, bitScore (boolDot row v) := by
      exact (Fintype.prod_sum (fun (_j : Fin d) (row : BVec m) ↦
        bitScore (boolDot row v))).symm
    _ = (3 * 2 ^ (m - 1)) ^ d := by
      rw [sum_bitScore_boolDot_of_ne_zero v hv]
      simp

/-- Sum of the nonzero-input scores of one matrix. -/
def matrixScore {m d : ℕ} (T : BMatrix m d) : ℕ :=
  ∑ v ∈ (Finset.univ : Finset (BVec m)).erase 0, vectorScore (applyMatrix T v)

@[simp] theorem vectorScore_zero (d : ℕ) : vectorScore (0 : BVec d) = 2 ^ d := by
  simp [vectorScore, boolWeight]

/-- A strict `1/32` certificate forces the selected matrix to be injective. -/
theorem applyMatrix_injective_of_certificate {m d : ℕ} (T : BMatrix m d)
    (hcert : 32 * matrixScore T < 2 ^ d) :
    Function.Injective (applyMatrix T) := by
  classical
  intro v w hvw
  have hkernel : applyMatrix T (v + w) = 0 := by
    funext j
    change boolDot (T j) (v + w) = false
    unfold boolDot
    simp_rw [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
    change applyMatrix T v j + applyMatrix T w j = false
    rw [congrFun hvw j]
    generalize applyMatrix T w j = b
    cases b <;> rfl
  have hvwzero : v + w = 0 := by
    by_contra hne
    have hmem : v + w ∈ (Finset.univ : Finset (BVec m)).erase 0 :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
    have hterm : vectorScore (applyMatrix T (v + w)) ≤ matrixScore T := by
      unfold matrixScore
      exact Finset.single_le_sum
        (f := fun u : BVec m ↦ vectorScore (applyMatrix T u))
        (fun _ _ ↦ Nat.zero_le _) hmem
    rw [hkernel, vectorScore_zero] at hterm
    have hscaled : 32 * 2 ^ d ≤ 32 * matrixScore T := Nat.mul_le_mul_left 32 hterm
    have hpow : 0 < 2 ^ d := pow_pos (by decide) _
    omega
  funext i
  have hi := congrFun hvwzero i
  change v i + w i = false at hi
  cases hv : v i <;> cases hw : w i <;> simp_all [Bool.add_eq_xor]

/-- The exact numerator of the random-matrix expectation in attempt 0009. -/
theorem sum_matrixScore (m d : ℕ) :
    ∑ T : BMatrix m d, matrixScore T =
      (2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d := by
  classical
  unfold matrixScore
  calc
    (∑ T : BMatrix m d, ∑ v ∈ (Finset.univ : Finset (BVec m)).erase 0,
        vectorScore (applyMatrix T v)) =
        ∑ v ∈ (Finset.univ : Finset (BVec m)).erase 0,
          ∑ T : BMatrix m d, vectorScore (applyMatrix T v) := by
      rw [Finset.sum_comm]
    _ = ∑ _v ∈ (Finset.univ : Finset (BVec m)).erase 0,
          (3 * 2 ^ (m - 1)) ^ d := by
      apply Finset.sum_congr rfl
      intro v hv
      exact sum_vectorScore_applyMatrix_of_ne_zero v (Finset.ne_of_mem_erase hv)
    _ = (2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d := by
      simp

/--
Finite averaging in integer form.  If the exact total score is less than `1/32` of the
matrix count times `2^d`, one matrix satisfies the strict certificate used downstream.
-/
theorem exists_matrixScore_certificate {m d : ℕ}
    (havg :
      32 * ((2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d) <
        (2 ^ m) ^ d * 2 ^ d) :
    ∃ T : BMatrix m d, 32 * matrixScore T < 2 ^ d := by
  classical
  by_contra hn
  push Not at hn
  have hsum :
      (∑ _T : BMatrix m d, 2 ^ d) ≤
        ∑ T : BMatrix m d, 32 * matrixScore T := by
    exact Finset.sum_le_sum fun T _hT ↦ hn T
  have hleft :
      (∑ _T : BMatrix m d, 2 ^ d) = (2 ^ m) ^ d * 2 ^ d := by
    simp
  have hright :
      (∑ T : BMatrix m d, 32 * matrixScore T) =
        32 * ((2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d) := by
    rw [← Finset.mul_sum, sum_matrixScore]
  rw [hleft, hright] at hsum
  exact (Nat.not_lt_of_ge hsum) havg

end Green25
