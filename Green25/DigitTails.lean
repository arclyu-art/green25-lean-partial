import Green25.MidpointPartition
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn

/-! # Hoeffding bounds for the cardinalities of the two tails of digital energy -/

namespace Green25.Midpoint

open MeasureTheory ProbabilityTheory

noncomputable def tailBound (B d : ℕ) (T : ℝ) : ℝ :=
  Real.exp (-T ^ 2 / (2 * (d * (((B : ℝ) ^ 2 / 2) ^ 2))))

/-- A common center gives both cardinality estimates in the full, untruncated digit box. -/
theorem exists_center_tail_bounds {B d : ℕ} (hB : 0 < B) {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ℝ,
      (((endpoints (B := B) (d := d) (μ + T))ᶜ.card : ℕ) : ℝ) / (B : ℝ) ^ d ≤ tailBound B d T ∧
      ((low (B := B) (d := d) (μ - T)).card : ℝ) / (B : ℝ) ^ d ≤ tailBound B d T := by
  classical
  haveI : NeZero B := ⟨hB.ne'⟩
  let ν := uniformOn (Set.univ : Set (Fin B))
  let P := Measure.pi (fun _ : Fin d ↦ ν)
  let D (i : Fin d) (u : Box B d) := ((u i).val : ℝ) ^ 2
  let E (i : Fin d) := ∫ u, D i u ∂P
  let c : NNReal := (‖(B : ℝ) ^ 2 - 0‖₊ / 2) ^ 2
  have hind : iIndepFun (fun i u ↦ D i u - E i) P := by
    apply iIndepFun_pi (X := fun i (x : Fin B) ↦ (x.val : ℝ) ^ 2 - E i)
    exact fun _ ↦ Measurable.of_discrete.aemeasurable
  have hsub (i : Fin d) : HasSubgaussianMGF (fun u ↦ D i u - E i) c P := by
    apply hasSubgaussianMGF_of_mem_Icc (a := 0) (b := (B : ℝ) ^ 2)
    · exact Measurable.of_discrete.aemeasurable
    · apply ae_of_all
      intro u
      change 0 ≤ ((u i).val : ℝ) ^ 2 ∧ ((u i).val : ℝ) ^ 2 ≤ (B : ℝ) ^ 2
      exact ⟨sq_nonneg _, by gcongr; exact_mod_cast (u i).isLt.le⟩
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hind (fun i _ ↦ hsub i)
  let μ := ∑ i, E i
  have hsum (u : Box B d) : ∑ i, (D i u - E i) = energy u - μ := Finset.sum_sub_distrib ..
  have hbound : Real.exp (-T ^ 2 / (2 * ((∑ _ : Fin d, c : NNReal) : ℝ))) =
      tailBound B d T := by simp [tailBound, c, Real.nnnorm_of_nonneg (sq_nonneg (B : ℝ))]
  have hprob (S : Finset (Box B d)) : P.real (S : Set (Box B d)) = (S.card : ℝ) / (B : ℝ) ^ d := by
    have hP : P = uniformOn (Set.univ : Set (Box B d)) := by
      simpa [P, ν] using
        (uniformOn_pi (f := fun _ : Fin d ↦ (Set.univ : Set (Fin B)))).symm
    simp [hP, measureReal_def, uniformOn_univ, ENNReal.toReal_div, Box]
  refine ⟨μ, ?_, ?_⟩
  · rw [← hprob, ← hbound]
    apply le_trans (measureReal_mono _) (hs.measure_ge_le hT)
    intro u hu
    change T ≤ ∑ i, (D i u - E i)
    rw [hsum]
    have h : ¬ energy u ≤ μ + T := by simpa [endpoints] using hu
    linarith
  · rw [← hprob, ← hbound]
    apply le_trans (measureReal_mono _) (hs.neg.measure_ge_le hT)
    intro u hu
    change T ≤ -∑ i, (D i u - E i)
    rw [hsum]
    have h : energy u < μ - T := by simpa [low] using hu
    linarith

/-- Only scalar inequalities remain as inputs. In particular the center and the relative size
of the exceptional sets are conclusions of the uniform product-space argument. -/
theorem exists_exact_of_parameters {B d N L m k : ℕ} {T : ℝ} (hB : 0 < B)
    (hN : N ≤ B ^ d) (hT : 0 ≤ T) (hm : 8 * T ≤ m) (hL : B ^ d < 2 ^ L)
    (hsmall : tailBound B d T ≤ 1 / 2)
    (hk : L * ((ballBound B d m + 1) * 2 ^ d) ≤ k) (hkN : k ≤ N) :
    ∃ color : Fin N → Fin k, Function.Surjective color ∧
      ((restrictedSameColorSums color).card : ℝ) ≤ 2 * L * tailBound B d T * (B : ℝ) ^ d := by
  obtain ⟨μ, hA, hW⟩ := exists_center_tail_bounds (d := d) hB hT
  have hpos : (0 : ℝ) < (B : ℝ) ^ d := by positivity
  let A := endpoints (B := B) (d := d) (μ + T)
  have hhalf := (div_le_iff₀ hpos).mp (hA.trans hsmall)
  have hc : 2 * Aᶜ.card ≤ B ^ d := by exact_mod_cast (show 2 * (Aᶜ.card : ℝ) ≤ (B : ℝ) ^ d by linarith)
  have hid : Aᶜ.card = B ^ d - A.card := by simp [Finset.card_compl, Box]
  have hcover : B ^ d * (B ^ d - A.card) ^ L < (B ^ d) ^ L := by
    rw [← hid]
    apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ L)
    calc
      2 ^ L * (B ^ d * Aᶜ.card ^ L) = B ^ d * (2 * Aᶜ.card) ^ L := by rw [mul_pow]; ring
      _ ≤ B ^ d * (B ^ d) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc L)
      _ < 2 ^ L * (B ^ d) ^ L := Nat.mul_lt_mul_of_pos_right hL (by positivity)
  obtain ⟨color, hs, hcount⟩ := exists_exact_of_tail_counts hB hN hm hcover hk hkN
  refine ⟨color, hs, ?_⟩
  have hw := (div_le_iff₀ hpos).mp hW
  calc
    _ ≤ ((2 * (L * (low (B := B) (d := d) (μ - T)).card) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ 2 * (L : ℝ) * (tailBound B d T * (B : ℝ) ^ d) := by
      push_cast
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

end Green25.Midpoint
