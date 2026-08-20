import Green25.Assembly
import Mathlib.Data.Nat.Log

/-!
# Numerical parameters for the partial theorem

This file discharges the real logarithm, natural floor, and ceiling estimates needed to instantiate
the integer-parameter construction from `Green25.Assembly`.
-/

namespace Green25

/-- Complementary exponent `log_2(4/3) = 1 - theta`. -/
noncomputable def alpha : ℝ := 1 - theta

/-- Number of ambient binary digits. -/
def ambientBits (N : ℕ) : ℕ := Nat.clog 2 N

/-- Dimension of the image code chosen by the averaging argument. -/
noncomputable def codeDimension (d : ℕ) : ℕ :=
  ⌊alpha * (d : ℝ)⌋₊ - 5

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem theta_pos : 0 < theta := by
  unfold theta
  positivity

/-- A rational upper bound used only to guarantee that `codeDimension d` does not truncate at zero. -/
theorem theta_lt_five_eighths : theta < (5 : ℝ) / 8 := by
  have hp : ((3 : ℝ) / 2) ^ 8 < (2 : ℝ) ^ 5 := by norm_num
  have hlog := Real.strictMonoOn_log
    (show (0 : ℝ) < ((3 : ℝ) / 2) ^ 8 by norm_num)
    (show (0 : ℝ) < (2 : ℝ) ^ 5 by norm_num) hp
  rw [Real.log_pow, Real.log_pow] at hlog
  unfold theta
  rw [div_lt_iff₀ log_two_pos]
  nlinarith

theorem alpha_pos : 0 < alpha := by
  unfold alpha
  nlinarith [theta_lt_five_eighths]

theorem alpha_gt_three_eighths : (3 : ℝ) / 8 < alpha := by
  unfold alpha
  nlinarith [theta_lt_five_eighths]

theorem theta_add_alpha : theta + alpha = 1 := by
  unfold alpha
  ring

/-- The defining logarithm identity `2^theta = 3/2`. -/
theorem two_rpow_theta : Real.rpow 2 theta = (3 : ℝ) / 2 := by
  change (2 : ℝ) ^ theta = (3 : ℝ) / 2
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold theta
  have hmul :
      Real.log 2 * (Real.log ((3 : ℝ) / 2) / Real.log 2) = Real.log ((3 : ℝ) / 2) := by
    field_simp [ne_of_gt log_two_pos]
  rw [hmul]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < (3 : ℝ) / 2)]

/-- The complementary identity `2^alpha = 4/3`. -/
theorem two_rpow_alpha : Real.rpow 2 alpha = (4 : ℝ) / 3 := by
  unfold alpha
  change (2 : ℝ) ^ (1 - theta) = (4 : ℝ) / 3
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_one]
  change 2 / Real.rpow 2 theta = (4 : ℝ) / 3
  rw [two_rpow_theta]
  norm_num

theorem ambient_le_two_pow (N : ℕ) : N ≤ 2 ^ ambientBits N := by
  exact Nat.le_pow_clog (by norm_num) N

theorem two_pow_ambient_lt_two_mul {N : ℕ} (hN : 2 ≤ N) :
    2 ^ ambientBits N < 2 * N := by
  have hpos : 0 < ambientBits N := Nat.clog_pos (by norm_num) (by omega)
  have hpred : 2 ^ (ambientBits N).pred < N :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hd : ambientBits N = (ambientBits N).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  rw [hd, pow_succ]
  omega

theorem ambientBits_ge_sixteen {N : ℕ} (hN : 2 ^ 16 ≤ N) : 16 ≤ ambientBits N := by
  unfold ambientBits
  rw [← Nat.clog_pow 2 16 (by norm_num)]
  exact Nat.clog_mono_right 2 hN

theorem six_le_floor_alpha_mul {d : ℕ} (hd : 16 ≤ d) :
    6 ≤ ⌊alpha * (d : ℝ)⌋₊ := by
  rw [Nat.le_floor_iff' (by norm_num : (6 : ℕ) ≠ 0)]
  have hdreal : (16 : ℝ) ≤ d := by exact_mod_cast hd
  have halpha : (3 : ℝ) / 8 < alpha := alpha_gt_three_eighths
  have hdpos : (0 : ℝ) < d := by linarith
  have hmul := mul_lt_mul_of_pos_right halpha hdpos
  have h6 : (6 : ℝ) < alpha * d := by
    calc
      (6 : ℝ) = (3 / 8 : ℝ) * 16 := by norm_num
      _ ≤ (3 / 8 : ℝ) * d := by nlinarith
      _ < alpha * d := hmul
  exact h6.le

theorem codeDimension_pos {d : ℕ} (hd : 16 ≤ d) : 0 < codeDimension d := by
  unfold codeDimension
  have := six_le_floor_alpha_mul hd
  omega

theorem codeDimension_le {d : ℕ} : codeDimension d ≤ d := by
  unfold codeDimension
  apply (Nat.sub_le _ _).trans
  apply Nat.floor_le_of_le
  have htheta : 0 < theta := theta_pos
  have halpha : alpha ≤ 1 := by
    unfold alpha
    linarith
  have hd : (0 : ℝ) ≤ d := by positivity
  nlinarith

theorem codeDimension_add_five {d : ℕ} (hd : 16 ≤ d) :
    codeDimension d + 5 = ⌊alpha * (d : ℝ)⌋₊ := by
  unfold codeDimension
  have hfloor := six_le_floor_alpha_mul hd
  omega

/-- The exact integer inequality behind the `1/32` expectation bound. -/
theorem codeDimension_expectation_key {d : ℕ} (hd : 16 ≤ d) :
    32 * 2 ^ codeDimension d * 3 ^ d ≤ 4 ^ d := by
  have hnonneg : (0 : ℝ) ≤ alpha * d :=
    mul_nonneg alpha_pos.le (Nat.cast_nonneg _)
  have hexp : ((codeDimension d + 5 : ℕ) : ℝ) ≤ alpha * (d : ℝ) := by
    rw [codeDimension_add_five hd]
    exact Nat.floor_le hnonneg
  have hpow : (2 : ℝ) ^ (codeDimension d + 5) ≤
      Real.rpow 2 (alpha * (d : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact (Real.strictMono_rpow_of_base_gt_one (by norm_num)).monotone hexp
  have hidentity : Real.rpow 2 (alpha * (d : ℝ)) = ((4 : ℝ) / 3) ^ d := by
    change (2 : ℝ) ^ (alpha * (d : ℝ)) = ((4 : ℝ) / 3) ^ d
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    change Real.rpow (Real.rpow 2 alpha) (d : ℝ) = ((4 : ℝ) / 3) ^ d
    rw [two_rpow_alpha]
    exact Real.rpow_natCast ((4 : ℝ) / 3) d
  have hreal : (2 : ℝ) ^ (codeDimension d + 5) * (3 : ℝ) ^ d ≤ (4 : ℝ) ^ d := by
    calc
      (2 : ℝ) ^ (codeDimension d + 5) * (3 : ℝ) ^ d ≤
          Real.rpow 2 (alpha * (d : ℝ)) * (3 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = ((4 : ℝ) / 3) ^ d * (3 : ℝ) ^ d := by rw [hidentity]
      _ = (4 : ℝ) ^ d := by
        rw [← mul_pow]
        norm_num
  have hnat : 2 ^ (codeDimension d + 5) * 3 ^ d ≤ 4 ^ d := by
    exact_mod_cast hreal
  simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hnat

/-- The exact finite-average hypothesis required by `exists_exactColor_of_average`. -/
theorem finite_average_inequality {d : ℕ} (hd : 16 ≤ d) :
    32 * ((2 ^ codeDimension d - 1) *
        (3 * 2 ^ (codeDimension d - 1)) ^ d) <
      (2 ^ codeDimension d) ^ d * 2 ^ d := by
  let m := codeDimension d
  let e := (m - 1) * d
  have hmpos : 0 < m := codeDimension_pos hd
  have hkey : 32 * 2 ^ m * 3 ^ d ≤ 4 ^ d := codeDimension_expectation_key hd
  have hsub : 2 ^ m - 1 < 2 ^ m := Nat.sub_lt (pow_pos (by decide) _) (by decide)
  have hfactor : 0 < (3 * 2 ^ (m - 1)) ^ d := pow_pos (by positivity) _
  have hstrict :
      32 * ((2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d) <
        32 * (2 ^ m * (3 * 2 ^ (m - 1)) ^ d) := by
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_right hsub hfactor) (by decide)
  have hfactorEq : (3 * 2 ^ (m - 1)) ^ d = 3 ^ d * 2 ^ e := by
    dsimp [e]
    rw [mul_pow, ← pow_mul]
  have hexp : 2 * d + (m - 1) * d = m * d + d := by
    calc
      2 * d + (m - 1) * d = ((m - 1) + 2) * d := by ring
      _ = (m + 1) * d := by
        congr 1
        omega
      _ = m * d + d := by ring
  apply hstrict.trans_le
  calc
    32 * (2 ^ m * (3 * 2 ^ (m - 1)) ^ d) =
        (32 * 2 ^ m * 3 ^ d) * 2 ^ e := by
      rw [hfactorEq]
      ring
    _ ≤ 4 ^ d * 2 ^ e := Nat.mul_le_mul_right (2 ^ e) hkey
    _ = (2 ^ m) ^ d * 2 ^ d := by
      dsimp [e]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add,
        ← pow_mul, ← pow_add]
      exact congrArg (2 ^ ·) hexp

/-- The quotient color count is bounded by the advertised real threshold. -/
theorem codeColorCount_le_threshold {N d : ℕ} (hd : 16 ≤ d) (hM : 2 ^ d < 2 * N) :
    2 ^ (d - codeDimension d) ≤ colorThreshold N := by
  let F : ℕ := ⌊alpha * (d : ℝ)⌋₊
  let m : ℕ := codeDimension d
  have hF : 6 ≤ F := six_le_floor_alpha_mul hd
  have hm5 : m + 5 = F := codeDimension_add_five hd
  have hmd : m ≤ d := codeDimension_le
  have hfloorlt : alpha * (d : ℝ) < (F : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (alpha * (d : ℝ))
  have hm5real : (m : ℝ) + 5 = (F : ℝ) := by exact_mod_cast hm5
  have hsum : theta + alpha = 1 := theta_add_alpha
  have hexp : ((d - m : ℕ) : ℝ) < theta * (d : ℝ) + 6 := by
    rw [Nat.cast_sub hmd]
    nlinarith
  have hpow : (2 ^ (d - m) : ℕ) < Real.rpow 2 (theta * (d : ℝ) + 6) := by
    have hreal : (2 : ℝ) ^ (d - m) < Real.rpow 2 (theta * (d : ℝ) + 6) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    exact_mod_cast hreal
  have hpowIdentity :
      Real.rpow 2 (theta * (d : ℝ) + 6) =
        64 * Real.rpow ((2 ^ d : ℕ) : ℝ) theta := by
    change (2 : ℝ) ^ (theta * (d : ℝ) + 6) =
      64 * Real.rpow ((2 ^ d : ℕ) : ℝ) theta
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hmul :
        (2 : ℝ) ^ (theta * (d : ℝ)) = Real.rpow ((2 ^ d : ℕ) : ℝ) theta := by
      rw [show theta * (d : ℝ) = (d : ℝ) * theta by ring]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      change Real.rpow (Real.rpow 2 (d : ℝ)) theta =
        Real.rpow ((2 ^ d : ℕ) : ℝ) theta
      have htwo : Real.rpow 2 (d : ℝ) = ((2 ^ d : ℕ) : ℝ) := by
        calc
          Real.rpow 2 (d : ℝ) = (2 : ℝ) ^ d := Real.rpow_natCast 2 d
          _ = ((2 ^ d : ℕ) : ℝ) := by norm_num
      exact congrArg (fun z : ℝ ↦ Real.rpow z theta) htwo
    rw [hmul]
    norm_num
    ring
  have hMreal : (((2 ^ d : ℕ) : ℝ)) < 2 * (N : ℝ) := by exact_mod_cast hM
  have hrpowM :
      Real.rpow (((2 ^ d : ℕ) : ℝ)) theta < Real.rpow (2 * (N : ℝ)) theta :=
    Real.rpow_lt_rpow (by positivity) hMreal theta_pos
  have hmulIdentity :
      Real.rpow (2 * (N : ℝ)) theta =
        (3 / 2 : ℝ) * Real.rpow N theta := by
    change (2 * (N : ℝ)) ^ theta = (3 / 2 : ℝ) * Real.rpow N theta
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg N)]
    change Real.rpow 2 theta * Real.rpow N theta = _
    rw [two_rpow_theta]
  have hthresholdReal :
      ((2 ^ (d - m) : ℕ) : ℝ) < 96 * Real.rpow N theta := by
    calc
      ((2 ^ (d - m) : ℕ) : ℝ) < Real.rpow 2 (theta * (d : ℝ) + 6) := by
        exact_mod_cast hpow
      _ = 64 * Real.rpow (((2 ^ d : ℕ) : ℝ)) theta := hpowIdentity
      _ < 64 * Real.rpow (2 * (N : ℝ)) theta := by nlinarith
      _ = 96 * Real.rpow N theta := by rw [hmulIdentity]; ring
  unfold colorThreshold
  have hceil := Nat.le_ceil (96 * Real.rpow N theta)
  have hltceil :
      ((2 ^ (d - m) : ℕ) : ℝ) < (⌈96 * Real.rpow N theta⌉₊ : ℝ) :=
    hthresholdReal.trans_le hceil
  have hnat : 2 ^ (d - m) < ⌈96 * Real.rpow N theta⌉₊ := by exact_mod_cast hltceil
  simpa [m] using hnat.le

/-- The frozen candidate partial theorem from `Green25.Statement`. -/
theorem green25_partial : PartialTheorem := by
  intro N k hN hthreshold hkN
  let d := ambientBits N
  let m := codeDimension d
  have hNtwo : 2 ≤ N := by
    norm_num at hN
    omega
  have hd : 16 ≤ d := ambientBits_ge_sixteen hN
  have hNpow : N ≤ 2 ^ d := ambient_le_two_pow N
  have hM : 2 ^ d < 2 * N := two_pow_ambient_lt_two_mul hNtwo
  have hmd : m ≤ d := codeDimension_le
  have havg :
      32 * ((2 ^ m - 1) * (3 * 2 ^ (m - 1)) ^ d) <
        (2 ^ m) ^ d * 2 ^ d := finite_average_inequality hd
  have hcolorCount : 2 ^ (d - m) ≤ colorThreshold N :=
    codeColorCount_le_threshold hd hM
  exact exists_exactColor_of_average hNpow hM hmd havg
    (hcolorCount.trans hthreshold) hkN

end Green25
