import Green25.DigitTails
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Subpolynomially many colors for all sufficiently large intervals

Write log N = x^32. A box of base floor(x) and energy window x^22 has a
small enough exceptional set and a sparse enough proximity graph simultaneously. -/

namespace Green25.Midpoint

open Filter Real
open scoped Topology

private theorem scale_color_cost {x : ℝ} {B d L m : ℕ}
    (hx : 1024 ≤ x) (hl : 1 ≤ log x) (hd : (d : ℝ) * log x ≤ 3 * x ^ 32)
    (hL : (L : ℝ) ≤ x ^ 35) (hb : (d : ℝ) * B + 2 ≤ x ^ 35)
    (hm : (m : ℝ) + 1 ≤ 10 * x ^ 22) :
    (L * ((ballBound B d m + 1) * 2 ^ d) : ℕ) ≤
      ⌈exp (16000 * x ^ 32 / (32 * log x))⌉₊ := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : log x ≤ x := (log_le_sub_one_of_pos hx0).trans (by linarith)
  let q := d * B + 2
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  have hpx : log (x ^ 35) = 35 * log x := by norm_num [log_pow]
  have hlogq : log q ≤ 35 * log x := by
    rw [← hpx]
    apply log_le_log hq
    simpa [q] using hb
  have h32 : x ^ 24 ≤ x ^ 32 := pow_le_pow_right₀ hx1 (by decide)
  have hlogcost :
      (35 * log x + ((m : ℝ) + 1) * log q + d * log 2) * log x ≤ 500 * x ^ 32 := by
    have hfirst : 35 * log x * log x ≤ 35 * x ^ 24 := by
      calc
        _ ≤ 35 * x * x := by gcongr
        _ = 35 * x ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hx1 (by decide : 2 ≤ 24)) (by norm_num)
    have hsecond : ((m : ℝ) + 1) * log q * log x ≤ 350 * x ^ 24 := by
      calc
        _ ≤ (10 * x ^ 22) * (35 * x) * x := by
          gcongr
          exact hlogq.trans (by gcongr)
        _ = _ := by ring
    have hthird : (d : ℝ) * log 2 * log x ≤ 3 * x ^ 32 := by
      calc
        _ = ((d : ℝ) * log x) * log 2 := by ring
        _ ≤ ((d : ℝ) * log x) * 1 := by
          gcongr
          linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ _ := by simpa using hd
    linarith only [hfirst, hsecond, hthird, h32, pow_nonneg hx0.le 32]
  have he : 35 * log x + ((m : ℝ) + 1) * log q + d * log 2 ≤
      16000 * x ^ 32 / (32 * log x) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [hlogcost]
  have hc : (L : ℝ) * (((ballBound B d m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ d) ≤
      exp (16000 * x ^ 32 / (32 * log x)) := by
    calc
      _ ≤ x ^ 35 * ((q : ℝ) ^ (m + 1) * 2 ^ d) := by
        gcongr
        exact_mod_cast ballBound_add_one_le B d m
      _ = exp (35 * log x + ((m : ℝ) + 1) * log q + d * log 2) := by
        rw [exp_add, exp_add, ← hpx, exp_log (by positivity)]
        rw [← Nat.cast_add_one, ← log_pow (q : ℝ), exp_log (by positivity)]
        rw [← log_pow (2 : ℝ), exp_log (by positivity)]
        ring
      _ ≤ _ := exp_le_exp.mpr he
  exact_mod_cast hc.trans (Nat.le_ceil _)

private theorem scale_tail {x : ℝ} {B d : ℕ} (hx : 1024 ≤ x) (hB : 0 < B)
    (hd : 0 < d) (hb : (B : ℝ) ≤ x) (hdx : (d : ℝ) ≤ 3 * x ^ 32) :
    tailBound B d (x ^ 22) ≤ exp (-x) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  apply exp_le_exp.mpr
  apply (div_le_iff₀ (by positivity)).mpr
  have h : x * (2 * (d * (((B : ℝ) ^ 2 / 2) ^ 2))) ≤ (x ^ 22) ^ 2 := by
    calc
      _ ≤ x * (2 * ((3 * x ^ 32) * ((x ^ 2 / 2) ^ 2))) := by gcongr
      _ = (3 / 2 : ℝ) * x ^ 37 := by ring
      _ ≤ x * x ^ 37 := by gcongr; linarith
      _ = x ^ 38 := by ring
      _ ≤ x ^ 44 := pow_le_pow_right₀ hx1 (by decide)
      _ = _ := by ring
  linarith only [h]

private theorem partition_at_scale {N k : ℕ} {x ε : ℝ} (hN : 1 < N)
    (hx : 1024 ≤ x) (hl : 1 ≤ log x) (hxN : x ^ 32 = log N)
    (herr : 2 * (x ^ 36 * exp (-x)) < ε)
    (hk : ⌈exp (16000 * log N / log (log N))⌉₊ ≤ k) (hkN : k ≤ N) :
    ∃ color : Fin N → Fin k, Function.Surjective color ∧
      ((restrictedSameColorSums color).card : ℝ) < ε * N := by
  let B := ⌊x⌋₊
  let d := Nat.clog B N
  let L := d * B + 1
  let m := ⌈8 * x ^ 22⌉₊
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hbp : 1 < B := by
    exact Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ x by norm_num; linarith)
  have hbr : (1 : ℝ) < B := by exact_mod_cast hbp
  have hbx : (B : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlog : log x ≤ x := (log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlogB : 0 < log B := log_pos hbr
  have hlogBx := log_le_log (by positivity : (0 : ℝ) < B) hbx
  have hlogSquare : log x ≤ 2 * log B := by
    have hh : x ≤ (B : ℝ) ^ 2 := by
      have h2 : (2 : ℝ) ≤ B := by exact_mod_cast hbp
      have hfloor : x < (B : ℝ) + 1 := Nat.lt_floor_add_one x
      nlinarith [sq_nonneg ((B : ℝ) - 2)]
    simpa only [log_pow, Nat.cast_ofNat] using log_le_log hx0 hh
  have hdpos : 0 < d := Nat.clog_pos hbp hN
  have hbox : N ≤ B ^ d := Nat.le_pow_clog hbp N
  have hpad : B ^ d ≤ B * N := by
    have hpred := Nat.pow_pred_clog_lt_self hbp hN
    calc
      B ^ d = B ^ (d.pred + 1) := congrArg (B ^ ·) (Nat.succ_pred_eq_of_pos hdpos).symm
      _ ≤ B * N := by rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ hpred.le
  have hdlog : (d : ℝ) * log x ≤ 3 * x ^ 32 := by
    have hratio : 0 ≤ logb B N := by rw [logb, ← hxN]; positivity
    have hceil := Nat.ceil_lt_add_one hratio
    rw [natCeil_logb_natCast, logb, ← hxN] at hceil
    have haux : (d : ℝ) * log B < x ^ 32 + log B := by
      calc
        _ < (x ^ 32 / log B + 1) * log B := mul_lt_mul_of_pos_right hceil hlogB
        _ = _ := by field_simp
    have htwox : 2 * x ≤ x ^ 32 := calc
      _ ≤ x ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ hx1 (by decide)
    have hmul := mul_le_mul_of_nonneg_left hlogSquare (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith only [haux, htwox, hmul, hlogBx, hlog]
  have hdx : (d : ℝ) ≤ 3 * x ^ 32 := by
    calc
      _ = (d : ℝ) * 1 := by ring
      _ ≤ (d : ℝ) * log x := by gcongr
      _ ≤ _ := hdlog
  have hb : (d : ℝ) * B + 2 ≤ x ^ 35 := by
    calc
      _ ≤ (3 * x ^ 32) * x + 2 := by gcongr
      _ ≤ 5 * x ^ 33 := by linarith only [one_le_pow₀ hx1 (n := 33)]
      _ ≤ x * x ^ 33 := by gcongr; linarith
      _ = x ^ 34 := by ring
      _ ≤ _ := pow_le_pow_right₀ hx1 (by decide)
  have hL : (L : ℝ) ≤ x ^ 35 := by dsimp [L]; push_cast; linarith
  have hm : (m : ℝ) + 1 ≤ 10 * x ^ 22 := by
    have hceil : (m : ℝ) < 8 * x ^ 22 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith [one_le_pow₀ hx1 (n := 22)]
  have hcolors := scale_color_cost hx hl hdlog hL hb hm
  rw [← hxN, log_pow] at hk
  have hfit : B ^ d < 2 ^ L := by
    have hs : B ≤ 2 ^ B := (Nat.lt_pow_self (by decide : 1 < 2)).le
    calc
      _ ≤ (2 ^ B) ^ d := Nat.pow_le_pow_left hs _
      _ = 2 ^ (d * B) := by rw [← pow_mul, Nat.mul_comm]
      _ < _ := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  have htail := scale_tail hx (Nat.zero_lt_of_lt hbp) hdpos hbx hdx
  have hsmall : exp (-x) ≤ 1 / 2 := by
    rw [exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [add_one_le_exp x]
  obtain ⟨color, hsurj, hv⟩ := exists_exact_of_parameters (Nat.zero_lt_of_lt hbp) hbox
    (by positivity : 0 ≤ x ^ 22) (Nat.le_ceil _) hfit (htail.trans hsmall) (hcolors.trans hk) hkN
  refine ⟨color, hsurj, hv.trans_lt ?_⟩
  have hpad' : (B : ℝ) ^ d ≤ x * N := by
    calc
      _ ≤ (B : ℝ) * N := by exact_mod_cast hpad
      _ ≤ _ := by gcongr
  calc
    _ ≤ 2 * x ^ 35 * exp (-x) * (x * N) := by
      gcongr
      first | exact htail | exact hL | exact hpad' | exact (exp_pos _).le
    _ = (2 * (x ^ 36 * exp (-x))) * N := by ring
    _ < ε * N := mul_lt_mul_of_pos_right herr (by exact_mod_cast Nat.zero_lt_of_lt hN)

/-- For every positive tolerance, every sufficiently large interval admits the exact
color counts and ordinary restricted sum bound of attempt 0018. -/
theorem subpolynomial_bound : SubpolynomialBound := by
  refine ⟨16000, by norm_num, ?_⟩
  intro ε hε
  let scale (N : ℕ) := (log N) ^ ((32 : ℝ)⁻¹)
  have htop : Tendsto scale atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 32⁻¹)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun x : ℝ ↦ 2 * (x ^ 36 * exp (-x))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero 36).const_mul 2
  filter_upwards [eventually_gt_atTop 1, htop.eventually_ge_atTop 1024,
    (tendsto_log_atTop.comp htop).eventually_ge_atTop 1,
    (hlim.comp htop).eventually_lt_const hε] with N hN hx hl he
  intro k hk hkN
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast hN.le)
  exact partition_at_scale hN hx hl (rpow_inv_natCast_pow hlog (by decide : 32 ≠ 0))
    he hk hkN

/-- In particular, every fixed positive power up to one is a nonvacuous exact color count. -/
theorem exact_fixed_power {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ color : Fin N → Fin ⌈(N : ℝ) ^ η⌉₊,
      Function.Surjective color ∧ ((restrictedSameColorSums color).card : ℝ) < ε * N := by
  obtain ⟨C, hC, h⟩ := subpolynomial_bound
  have htop : Tendsto (fun N : ℕ ↦ log (log (N : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [h ε hε, eventually_gt_atTop 1, htop.eventually_ge_atTop (C / η)]
    with N hN hn ht
  have hn' : (1 : ℝ) < N := by exact_mod_cast hn
  have ht' : C / η ≤ log (log N) := ht
  have hp : 0 < log (log N) := (div_pos hC hη).trans_le ht'
  apply hN
  · apply Nat.ceil_mono
    rw [rpow_def_of_pos (by positivity : (0 : ℝ) < N)]
    apply exp_le_exp.mpr
    apply (div_le_iff₀ hp).mpr
    have hc := (div_le_iff₀ hη).mp ht'
    calc
      _ ≤ (log (log N) * η) * log N := mul_le_mul_of_nonneg_right hc (log_pos hn').le
      _ = _ := by ring
  · apply Nat.ceil_le.mpr
    simpa using rpow_le_rpow_of_exponent_le hn'.le hη1

end Green25.Midpoint
