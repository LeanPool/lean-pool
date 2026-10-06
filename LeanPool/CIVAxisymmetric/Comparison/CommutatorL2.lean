/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Mollifier
public import LeanPool.CIVAxisymmetric.Comparison.Commutator

/-! ### The kernel majorizing both terms of the commutator together -/

public section

open MeasureTheory
open CKN

noncomputable section

namespace CIV

variable {m : ℕ}

/-- Cauchy-Schwarz for the integral of a nonnegative kernel against `|g|` and against `g^2`:
`(∫ K |g|)^2 ≤ (∫ K) (∫ K g^2)`. This is the elementary inequality behind the `L²` bound on
`eq:aniso:comparison:mollified`, applied pointwise to the kernel majorizing the commutator. -/
theorem cauchy_schwarz_kernel {K g : Vec m → ℝ} (hK_nonneg : ∀ y, 0 ≤ K y)
    (hK_int : Integrable K volume) (hKg_int : Integrable (fun y => K y * |g y|) volume)
    (hKg2_int : Integrable (fun y => K y * (g y) ^ 2) volume) :
    (∫ y, K y * |g y|) ^ 2 ≤ (∫ y, K y) * ∫ y, K y * (g y) ^ 2 := by
  set A := ∫ y, K y * (g y) ^ 2 with hA_def
  set B := ∫ y, K y * |g y| with hB_def
  set C := ∫ y, K y with hC_def
  have hA_nonneg : 0 ≤ A := integral_nonneg (fun y => mul_nonneg (hK_nonneg y) (sq_nonneg _))
  have hB_nonneg : 0 ≤ B := integral_nonneg (fun y => mul_nonneg (hK_nonneg y) (abs_nonneg _))
  have hC_nonneg : 0 ≤ C := integral_nonneg hK_nonneg
  have h_quad_nonneg : 0 ≤ ∫ y, (B * |g y| - A) ^ 2 * K y := by
    refine integral_nonneg fun y => ?_
    have : 0 ≤ (B * |g y| - A) ^ 2 := sq_nonneg _
    exact mul_nonneg this (hK_nonneg y)
  have h_expand : ∫ y, (B * |g y| - A) ^ 2 * K y = A * (A * C - B ^ 2) := by
    have hpt : ∀ y, (B * |g y| - A) ^ 2 * K y
        = B ^ 2 * (K y * (g y) ^ 2) - 2 * A * B * (K y * |g y|) + A ^ 2 * K y := by
      intro y
      have hsq : |g y| ^ 2 = (g y) ^ 2 := sq_abs (g y)
      have hexp : (B * |g y| - A) ^ 2 = B ^ 2 * |g y| ^ 2 - 2 * A * B * |g y| + A ^ 2 := by ring
      rw [hexp, hsq]; ring
    have h1 : Integrable (fun y => B ^ 2 * (K y * (g y) ^ 2)) volume := hKg2_int.const_mul _
    have h2 : Integrable (fun y => 2 * A * B * (K y * |g y|)) volume := hKg_int.const_mul _
    have h3 : Integrable (fun y => A ^ 2 * K y) volume := hK_int.const_mul _
    calc ∫ y, (B * |g y| - A) ^ 2 * K y
        = ∫ y, (B ^ 2 * (K y * (g y) ^ 2) - 2 * A * B * (K y * |g y|) + A ^ 2 * K y) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ y, B ^ 2 * (K y * (g y) ^ 2) - 2 * A * B * (K y * |g y|)) + ∫ y, A ^ 2 * K y :=
          integral_add (h1.sub h2) h3
      _ = ((∫ y, B ^ 2 * (K y * (g y) ^ 2)) - ∫ y, 2 * A * B * (K y * |g y|)) + ∫ y, A ^ 2 * K y
        := by
          rw [integral_sub h1 h2]
      _ = B ^ 2 * A - 2 * A * B * B + A ^ 2 * C := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul, ← hA_def, ← hB_def,
            ← hC_def]
      _ = A * (A * C - B ^ 2) := by ring
  have h_nonneg_prod : 0 ≤ A * (A * C - B ^ 2) := h_expand ▸ h_quad_nonneg
  by_cases hA_pos : 0 < A
  · have h_nonneg_diff : 0 ≤ A * C - B ^ 2 :=
      nonneg_of_mul_nonneg_right h_nonneg_prod hA_pos
    linarith only [h_nonneg_diff]
  · have hA_zero : A = 0 := le_antisymm (not_lt.mp hA_pos) hA_nonneg
    have h_kg2_nonneg : ∀ y, 0 ≤ K y * (g y) ^ 2 := fun y => mul_nonneg (hK_nonneg y) (sq_nonneg _)
    have h_kg2_zero : (fun y => K y * (g y) ^ 2) =ᵐ[volume] 0 := by
      rw [← integral_eq_zero_iff_of_nonneg h_kg2_nonneg hKg2_int]
      exact hA_zero
    have h_kabs_zero : (fun y => K y * |g y|) =ᵐ[volume] 0 := by
      filter_upwards [h_kg2_zero] with y hy
      have hy' : K y * (g y) ^ 2 = 0 := hy
      rcases mul_eq_zero.mp hy' with hK0 | hgsq0
      · simp [hK0]
      · have hgy : g y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hgsq0
        simp [hgy]
    have hB_zero : B = 0 := by
      rw [hB_def, integral_congr_ae h_kabs_zero]
      simp
    rw [hA_zero, hB_zero]
    simp



/-- The nonnegative kernel `Λ (ε ∑ᵢ|∂ᵢη_ε| + η_ε)` majorizing, jointly, both integrands of
`diPernaLionsCommutator`. It has the same total mass `Λ (C_η + 1)` as the uniform bound of
`eq:aniso:comparison:mollified`, and it vanishes outside the ball of radius `ε`. -/
@[expose] def commutatorMajorant (m : ℕ) (ε Λ : ℝ) : Vec m → ℝ :=
  fun w => Λ * (ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)| + mollifierKernel m ε w)

theorem commutatorMajorant_nonneg {ε Λ : ℝ} (hε : 0 < ε) (hΛ : 0 ≤ Λ) (w : Vec m) :
    0 ≤ commutatorMajorant m ε Λ w := by
  have hsum : 0 ≤ ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hker : 0 ≤ mollifierKernel m ε w := mollifierKernel_nonneg hε w
  have h1 : 0 ≤ ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)| :=
    mul_nonneg hε.le hsum
  exact mul_nonneg hΛ (add_nonneg h1 hker)

theorem commutatorMajorant_eq_zero {ε Λ : ℝ} (hε : 0 < ε) {w : Vec m} (hw : ε < ‖w‖) :
    commutatorMajorant m ε Λ w = 0 := by
  have hker : mollifierKernel m ε w = 0 := mollifierKernel_eq_zero hε hw.le
  have hfd : ∀ i, fderiv ℝ (mollifierKernel m ε) w (basisVec i) = 0 := fun i =>
    fderiv_mollifierKernel_eq_zero hε hw (basisVec i)
  simp [commutatorMajorant, hker, hfd]

theorem continuous_commutatorMajorant (ε Λ : ℝ) : Continuous (commutatorMajorant m ε Λ) := by
  refine continuous_const.mul (Continuous.add ?_ ?_)
  · exact continuous_const.mul
      (continuous_finsetSum _ fun i _ => (continuous_fderiv_mollifierKernel ε (basisVec i)).abs)
  · exact (contDiff_mollifierKernel (m := m) ε).continuous

theorem hasCompactSupport_commutatorMajorant {ε : ℝ} (hε : 0 < ε) (Λ : ℝ) :
    HasCompactSupport (commutatorMajorant m ε Λ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) ε) fun w hw => ?_
  refine commutatorMajorant_eq_zero hε ?_
  by_contra hcon
  exact hw (by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hcon)

theorem integrable_commutatorMajorant {ε : ℝ} (hε : 0 < ε) (Λ : ℝ) :
    Integrable (commutatorMajorant m ε Λ) volume :=
  (continuous_commutatorMajorant ε Λ).integrable_of_hasCompactSupport
    (hasCompactSupport_commutatorMajorant hε Λ)

/-- The total mass of the majorant is `Λ (C_η + 1)`, matching the uniform bound
`abs_diPernaLionsCommutator_le`. -/
theorem integral_commutatorMajorant {ε : ℝ} (hε : 0 < ε) (Λ : ℝ) :
    ∫ w, commutatorMajorant m ε Λ w = Λ * (mollifierGradConst m + 1) := by
  have h1 : Integrable (fun w : Vec m => ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)|)
      volume := (integrable_sum_abs_fderiv_mollifierKernel hε).const_mul _
  have h2 : Integrable (mollifierKernel m ε) volume := integrable_mollifierKernel hε
  unfold commutatorMajorant
  rw [integral_const_mul, integral_add h1 h2, integral_const_mul,
    integral_sum_abs_fderiv_mollifierKernel hε, integral_mollifierKernel hε]
  field_simp

theorem integral_commutatorMajorant_sub {ε : ℝ} (hε : 0 < ε) (Λ : ℝ) (x : Vec m) :
    ∫ y, commutatorMajorant m ε Λ (x - y) = Λ * (mollifierGradConst m + 1) := by
  rw [integral_sub_left_eq_self (commutatorMajorant m ε Λ) volume x, integral_commutatorMajorant hε]

theorem integral_commutatorMajorant_sub' {ε : ℝ} (hε : 0 < ε) (Λ : ℝ) (y : Vec m) :
    ∫ x, commutatorMajorant m ε Λ (x - y) = Λ * (mollifierGradConst m + 1) := by
  rw [integral_sub_right_eq_self (commutatorMajorant m ε Λ) y, integral_commutatorMajorant hε]

/-- The majorant kernel is globally bounded: being continuous with compact support, it attains a
finite maximum over all of `Vec m`. -/
theorem exists_bound_commutatorMajorant {ε : ℝ} (hε : 0 < ε) (Λ : ℝ) :
    ∃ C0 : ℝ, ∀ w, commutatorMajorant m ε Λ w ≤ C0 := by
  obtain ⟨w0, hw0⟩ := (continuous_commutatorMajorant ε Λ).exists_forall_ge_of_hasCompactSupport
    (hasCompactSupport_commutatorMajorant hε Λ)
  exact ⟨commutatorMajorant m ε Λ w0, hw0⟩

/-! ### The pointwise domination of the commutator by the majorant kernel -/

/-- The commutator is dominated, pointwise in `x`, by the majorant kernel against `|g|`:
`|R_ε(x)| ≤ ∫ y, commutatorMajorant (x - y) |g(y)| dy`. This keeps the factor `g y` explicit
(rather than replacing it by the uniform bound `M`, as `abs_diPernaLionsCommutator_le` does),
which is what the `L²` estimate on `eq:aniso:comparison:mollified` needs. -/
theorem abs_diPernaLionsCommutator_le_kernel {ε M : ℝ} {Λ : NNReal} (hε : 0 < ε)
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ y, |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) (x : Vec m) :
    |diPernaLionsCommutator m ε b divb g x|
      ≤ ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * |g y| := by
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := Λ.coe_nonneg
  have hgm_abs : AEStronglyMeasurable (fun y => |g y|) volume := by
    simpa [Real.norm_eq_abs] using hgm.norm
  have hbcont : Continuous b := hlip.continuous
  have hcoord : ∀ y : Vec m, ∀ i : Fin m, |b x i - b y i| ≤ (Λ : ℝ) * ‖x - y‖ := by
    intro y i
    have h1 : |b x i - b y i| ≤ ‖b x - b y‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (b x - b y) i
    have h2 : ‖b x - b y‖ ≤ (Λ : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm] using hlip.dist_le_mul x y
    exact h1.trans h2
  -- the first integrand and its majorant
  have hfirstcont : Continuous fun y : Vec m =>
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_const.sub ((continuous_apply i).comp hbcont)).mul
        ((continuous_fderiv_mollifierKernel ε (basisVec i)).comp
          (continuous_const.sub continuous_id)))
  have hfirstpt : ∀ y : Vec m,
      |g y * ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y| := by
    intro y
    have hsum : |∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ ((Λ : ℝ) * ε) * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by
      by_cases hxy : ‖x - y‖ ≤ ε
      · calc |∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
              ≤ ∑ i, |(b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, ((Λ : ℝ) * ε) *
                  |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [abs_mul]
                refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
                exact (hcoord y i).trans (mul_le_mul_of_nonneg_left hxy hΛ)
            _ = ((Λ : ℝ) * ε) * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
                (Finset.mul_sum _ _ _).symm
      · have hzero : ∀ i : Fin m,
            fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) = 0 := fun i =>
          fderiv_mollifierKernel_eq_zero hε (lt_of_not_ge hxy) (basisVec i)
        simp [hzero]
    calc |g y * ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        = |g y| * |∑ i, (b x i - b y i) *
            fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by rw [abs_mul]
      _ ≤ |g y| * (((Λ : ℝ) * ε) *
            ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y| := by
          ring
  have hmaj1 : Integrable (fun y : Vec m =>
      ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y|)
      volume := by
    have hint : Integrable (fun y : Vec m =>
        (Λ : ℝ) * ε * (∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * M) volume :=
      (((integrable_sum_abs_fderiv_mollifierKernel hε).comp_sub_left x).const_mul
        ((Λ : ℝ) * ε)).mul_const M
    have hmajcont : Continuous fun y : Vec m =>
        ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
      continuous_finsetSum _ fun i _ =>
        (continuous_fderiv_mollifierKernel ε (basisVec i)).abs.comp
          (continuous_const.sub continuous_id)
    refine hint.mono' ((continuous_const.mul hmajcont).aestronglyMeasurable.mul hgm_abs)
      (Filter.Eventually.of_forall fun y => ?_)
    have hnn : 0 ≤ (Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
      mul_nonneg (mul_nonneg hΛ hε.le) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hg y) hnn
  have hint1 : Integrable (fun y : Vec m => g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume :=
    hmaj1.mono' (hgm.mul hfirstcont.aestronglyMeasurable) (Filter.Eventually.of_forall hfirstpt)
  have hbound1 : |∫ y : Vec m, g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ ∫ y : Vec m,
            ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y| := by
    calc |∫ y : Vec m, g y *
          ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ ∫ y : Vec m, ‖g y *
            ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)‖ := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (volume : Measure (Vec m)))
              (fun y : Vec m => g y *
                ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      _ ≤ ∫ y : Vec m,
            ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y| :=
          integral_mono hint1.norm hmaj1 (fun y => by simpa [Real.norm_eq_abs] using hfirstpt y)
  -- the second integrand and its majorant
  have hsecondpt : ∀ y : Vec m,
      |mollifierKernel m ε (x - y) * (divb y * g y)|
        ≤ ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y| := by
    intro y
    have hker : 0 ≤ mollifierKernel m ε (x - y) := mollifierKernel_nonneg hε _
    calc |mollifierKernel m ε (x - y) * (divb y * g y)|
        = mollifierKernel m ε (x - y) * (|divb y| * |g y|) := by
          rw [abs_mul, abs_of_nonneg hker, abs_mul]
      _ ≤ mollifierKernel m ε (x - y) * ((Λ : ℝ) * |g y|) := by
          refine mul_le_mul_of_nonneg_left ?_ hker
          exact mul_le_mul_of_nonneg_right (hdivb y) (abs_nonneg _)
      _ = ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y| := by ring
  have hmaj2 : Integrable
      (fun y : Vec m => ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y|) volume := by
    have hint : Integrable (fun y : Vec m => (Λ : ℝ) * mollifierKernel m ε (x - y) * M) volume :=
      (((integrable_mollifierKernel hε).comp_sub_left x).const_mul (Λ : ℝ)).mul_const M
    refine hint.mono' ((continuous_const.mul ((contDiff_mollifierKernel (m := m) ε).continuous.comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable.mul hgm_abs)
      (Filter.Eventually.of_forall fun y => ?_)
    have hnn : 0 ≤ (Λ : ℝ) * mollifierKernel m ε (x - y) :=
      mul_nonneg hΛ (mollifierKernel_nonneg hε _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hg y) hnn
  have hint2 : Integrable
      (fun y : Vec m => mollifierKernel m ε (x - y) * (divb y * g y)) volume :=
    hmaj2.mono' (((contDiff_mollifierKernel (m := m) ε).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul (hdivbm.mul hgm))
      (Filter.Eventually.of_forall hsecondpt)
  have hbound2 : |∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)|
      ≤ ∫ y : Vec m, ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y| := by
    calc |∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)|
        ≤ ∫ y : Vec m, ‖mollifierKernel m ε (x - y) * (divb y * g y)‖ := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (volume : Measure (Vec m)))
              (fun y : Vec m => mollifierKernel m ε (x - y) * (divb y * g y))
      _ ≤ ∫ y : Vec m, ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y| :=
          integral_mono hint2.norm hmaj2 (fun y => by simpa [Real.norm_eq_abs] using hsecondpt y)
  -- combine the two bounds into the majorant kernel
  have hcomb : (∫ y : Vec m,
        ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y|)
      + ∫ y : Vec m, ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y|
      = ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * |g y| := by
    rw [← integral_add hmaj1 hmaj2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    unfold commutatorMajorant
    ring
  rw [diPernaLionsCommutator]
  calc |(∫ y : Vec m, g y *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      + ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)|
      ≤ |∫ y : Vec m, g y *
          ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        + |∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)| := abs_add_le _ _
    _ ≤ (∫ y : Vec m,
          ((Λ : ℝ) * ε * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) * |g y|)
        + ∫ y : Vec m, ((Λ : ℝ) * mollifierKernel m ε (x - y)) * |g y| :=
        add_le_add hbound1 hbound2
    _ = ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * |g y| := hcomb

/-! ### Measurability of the commutator as a function of `x` -/

/-- The commutator `x ↦ R_ε(x)` is a.e. strongly measurable: each defining integral is the
`x`-marginal of a jointly measurable integrand on `Vec m × Vec m`. -/
theorem aestronglyMeasurable_diPernaLionsCommutator (ε : ℝ) {b : Vec m → Vec m}
    {divb g : Vec m → ℝ} (hb : Continuous b) (hdivbm : AEStronglyMeasurable divb volume)
    (hgm : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun x => diPernaLionsCommutator m ε b divb g x) volume := by
  rw [show (fun x => diPernaLionsCommutator m ε b divb g x) = fun x =>
    (∫ y : Vec m, g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
    + ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y) from rfl]
  refine AEStronglyMeasurable.add ?_ ?_
  · have hcont : Continuous fun p : Vec m × Vec m =>
        ∑ i, (b p.1 i - b p.2 i) * fderiv ℝ (mollifierKernel m ε) (p.1 - p.2) (basisVec i) :=
      continuous_finsetSum _ fun i _ =>
        (((continuous_apply i).comp (hb.comp continuous_fst)).sub
          ((continuous_apply i).comp (hb.comp continuous_snd))).mul
          ((continuous_fderiv_mollifierKernel ε (basisVec i)).comp
            (continuous_fst.sub continuous_snd))
    have hmeas : AEStronglyMeasurable (fun p : Vec m × Vec m => g p.2 *
        ∑ i, (b p.1 i - b p.2 i) * fderiv ℝ (mollifierKernel m ε) (p.1 - p.2) (basisVec i))
        (volume.prod volume) := hgm.comp_snd.mul hcont.aestronglyMeasurable
    exact hmeas.integral_prod_right'
  · have hcont2 : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) :=
      (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_fst.sub continuous_snd)
    have hmeas2 : AEStronglyMeasurable (fun p : Vec m × Vec m =>
        mollifierKernel m ε (p.1 - p.2) * (divb p.2 * g p.2)) (volume.prod volume) :=
      hcont2.aestronglyMeasurable.mul (hdivbm.comp_snd.mul hgm.comp_snd)
    exact hmeas2.integral_prod_right'

/-! ### The `L²` bound on a ball -/

/-- The `L²` bound on a ball for the DiPerna–Lions commutator of `eq:aniso:comparison:mollified`:
the commutator on `closedBall 0 R` is controlled by `g` on the slightly larger
`closedBall 0 (R + ε)`, with a constant depending only on `m`, `Λ`, and the fixed profile's
gradient constant `mollifierGradConst m`. -/
theorem integral_sq_diPernaLionsCommutator_le {ε R M : ℝ} {Λ : NNReal} (hε : 0 < ε)
    (hM : 0 ≤ M) {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ y, |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) :
    ∫ x in Metric.closedBall (0 : Vec m) R, (diPernaLionsCommutator m ε b divb g x) ^ 2
      ≤ ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
          ∫ y in Metric.closedBall (0 : Vec m) (R + ε), (g y) ^ 2 := by
  set s := Metric.closedBall (0 : Vec m) R with hs_def
  set t := Metric.closedBall (0 : Vec m) (R + ε) with ht_def
  set C1 := (Λ : ℝ) * (mollifierGradConst m + 1) with hC1_def
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := Λ.coe_nonneg
  have hC1nonneg : 0 ≤ C1 := mul_nonneg hΛ (add_nonneg mollifierGradConst_nonneg (by norm_num))
  have hsqle : ∀ {a bd : ℝ}, |a| ≤ bd → a ^ 2 ≤ bd ^ 2 := by
    intro a bd hab
    obtain ⟨h1, h2⟩ := abs_le.mp hab
    exact sq_le_sq' h1 h2
  have hsMeas : MeasurableSet s := measurableSet_closedBall
  have htMeas : MeasurableSet t := measurableSet_closedBall
  have hsFin : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) R).measure_ne_top
  have htFin : IsFiniteMeasure (volume.restrict t) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) (R + ε)).measure_ne_top
  -- basic facts about the majorant, uniform in the point subtracted
  have hK_nonneg : ∀ x y : Vec m, 0 ≤ commutatorMajorant m ε (Λ : ℝ) (x - y) := fun x y =>
    commutatorMajorant_nonneg hε hΛ (x - y)
  have hK_int_y : ∀ x, Integrable (fun y => commutatorMajorant m ε (Λ : ℝ) (x - y)) volume :=
    fun x => (integrable_commutatorMajorant hε (Λ : ℝ)).comp_sub_left x
  have hK_int_x : ∀ y, Integrable (fun x => commutatorMajorant m ε (Λ : ℝ) (x - y)) volume :=
    fun y => (integrable_commutatorMajorant hε (Λ : ℝ)).comp_sub_right y
  have hK_cont_y : ∀ x, Continuous fun y => commutatorMajorant m ε (Λ : ℝ) (x - y) := fun x =>
    (continuous_commutatorMajorant ε (Λ : ℝ)).comp (continuous_const.sub continuous_id)
  have hgm_abs : AEStronglyMeasurable (fun y => |g y|) volume := by
    simpa [Real.norm_eq_abs] using hgm.norm
  have hKg_int : ∀ x, Integrable (fun y => commutatorMajorant m ε (Λ : ℝ) (x - y) * |g y|)
      volume := by
    intro x
    have hint : Integrable (fun y => commutatorMajorant m ε (Λ : ℝ) (x - y) * M) volume :=
      (hK_int_y x).mul_const M
    refine hint.mono' ((hK_cont_y x).aestronglyMeasurable.mul hgm_abs)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg x y) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hg y) (hK_nonneg x y)
  have hKg2_int : ∀ x, Integrable (fun y => commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
      volume := by
    intro x
    have hint : Integrable (fun y => commutatorMajorant m ε (Λ : ℝ) (x - y) * M ^ 2) volume :=
      (hK_int_y x).mul_const (M ^ 2)
    refine hint.mono' ((hK_cont_y x).aestronglyMeasurable.mul (hgm.pow 2))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg x y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hsqle (hg y)) (hK_nonneg x y)
  -- the Cauchy-Schwarz pointwise square bound
  have hsqx : ∀ x, (diPernaLionsCommutator m ε b divb g x) ^ 2
      ≤ C1 * ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := by
    intro x
    have hpt := abs_diPernaLionsCommutator_le_kernel hε hlip hdivb hdivbm hg hgm x
    have hcs := cauchy_schwarz_kernel (hK_nonneg x) (hK_int_y x) (hKg_int x) (hKg2_int x)
    have htotal : ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) = C1 :=
      integral_commutatorMajorant_sub hε (Λ : ℝ) x
    calc (diPernaLionsCommutator m ε b divb g x) ^ 2
        = |diPernaLionsCommutator m ε b divb g x| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * |g y|) ^ 2 := by
          gcongr
      _ ≤ (∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y)) *
            ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := hcs
      _ = C1 * ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := by rw [htotal]
  -- measurability of the commutator in `x`, and its global bound
  have hRεmeas : AEStronglyMeasurable (fun x => diPernaLionsCommutator m ε b divb g x) volume :=
    aestronglyMeasurable_diPernaLionsCommutator ε hlip.continuous hdivbm hgm
  have hRεglobal : ∀ x, |diPernaLionsCommutator m ε b divb g x|
      ≤ (Λ : ℝ) * M * (mollifierGradConst m + 1) :=
    fun x => abs_diPernaLionsCommutator_le hε hM hlip hdivb hdivbm hg hgm x
  have hLHSint : IntegrableOn (fun x => (diPernaLionsCommutator m ε b divb g x) ^ 2) s volume := by
    have hbound : Integrable (fun _ : Vec m => ((Λ : ℝ) * M * (mollifierGradConst m + 1)) ^ 2)
        (volume.restrict s) := integrable_const _
    refine hbound.mono' ((hRεmeas.pow 2).mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsqle (hRεglobal x)
  -- measurability and boundedness of `F(x) = ∫ y, commutatorMajorant (x - y) (g y)^2`
  have hFmeas : AEStronglyMeasurable
      (fun x => ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2) volume := by
    have hjcont : Continuous fun p : Vec m × Vec m => commutatorMajorant m ε (Λ : ℝ) (p.1 - p.2) :=
      (continuous_commutatorMajorant ε (Λ : ℝ)).comp (continuous_fst.sub continuous_snd)
    have hjoint : AEStronglyMeasurable (fun p : Vec m × Vec m =>
        commutatorMajorant m ε (Λ : ℝ) (p.1 - p.2) * (g p.2) ^ 2) (volume.prod volume) :=
      hjcont.aestronglyMeasurable.mul (hgm.pow 2).comp_snd
    exact hjoint.integral_prod_right'
  have hFbound : ∀ x, (∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2) ≤ M ^ 2 * C1 := by
    intro x
    have hmaj : Integrable (fun y => commutatorMajorant m ε (Λ : ℝ) (x - y) * M ^ 2) volume :=
      (hK_int_y x).mul_const (M ^ 2)
    calc ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2
        ≤ ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * M ^ 2 :=
          integral_mono (hKg2_int x) hmaj
            (fun y => mul_le_mul_of_nonneg_left (hsqle (hg y)) (hK_nonneg x y))
      _ = (∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y)) * M ^ 2 := integral_mul_const _ _
      _ = C1 * M ^ 2 := by rw [integral_commutatorMajorant_sub hε]
      _ = M ^ 2 * C1 := by ring
  have hRHSint : IntegrableOn
      (fun x => C1 * ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2) s volume := by
    have hFint : IntegrableOn (fun x => ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
        s volume := by
      have hbound : Integrable (fun _ : Vec m => M ^ 2 * C1) (volume.restrict s) :=
        integrable_const _
      refine hbound.mono' (hFmeas.mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun y => mul_nonneg (hK_nonneg x y) (sq_nonneg _))]
      exact hFbound x
    exact hFint.const_mul C1
  -- integrate the pointwise square bound over `s`
  have hstep1 : ∫ x in s, (diPernaLionsCommutator m ε b divb g x) ^ 2
      ≤ ∫ x in s, C1 * ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 :=
    setIntegral_mono hLHSint hRHSint hsqx
  have hstep2 : (∫ x in s, C1 * ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
      = C1 * ∫ x in s, ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 :=
    integral_const_mul _ _
  -- restrict the inner integral to `t`, since the majorant kills `y ∉ t` when `x ∈ s`
  have hrestrict : ∀ x ∈ s, (∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
      = ∫ y in t, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := by
    intro x hx
    rw [← integral_indicator htMeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ t
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hxle : ‖x‖ ≤ R := by
        simpa [hs_def, Metric.mem_closedBall, dist_zero_right] using hx
      have hygt : R + ε < ‖y‖ := by
        simpa [ht_def, Metric.mem_closedBall, dist_zero_right, not_le] using hy
      have hrev : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      have hnormeq : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      rw [hnormeq] at hrev
      have hxy : ε < ‖x - y‖ := by linarith only [hxle, hygt, hrev]
      show commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 = 0
      rw [commutatorMajorant_eq_zero hε hxy, zero_mul]
  have hstep3 : (∫ x in s, ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
      = ∫ x in s, ∫ y in t, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 :=
    setIntegral_congr_fun hsMeas hrestrict
  -- Fubini: swap the order of integration over the two finite-measure balls
  have hFubInt : Integrable
      (fun p : Vec m × Vec m => commutatorMajorant m ε (Λ : ℝ) (p.1 - p.2) * (g p.2) ^ 2)
      ((volume.restrict s).prod (volume.restrict t)) := by
    obtain ⟨C0, hC0⟩ := exists_bound_commutatorMajorant hε (Λ : ℝ)
    have hC0nonneg : 0 ≤ C0 := (hK_nonneg 0 0).trans (hC0 (0 - 0))
    have hjcont : Continuous fun p : Vec m × Vec m => commutatorMajorant m ε (Λ : ℝ) (p.1 - p.2) :=
      (continuous_commutatorMajorant ε (Λ : ℝ)).comp (continuous_fst.sub continuous_snd)
    have hmeas : AEStronglyMeasurable (fun p : Vec m × Vec m =>
        commutatorMajorant m ε (Λ : ℝ) (p.1 - p.2) * (g p.2) ^ 2)
        ((volume.restrict s).prod (volume.restrict t)) :=
      hjcont.aestronglyMeasurable.mul
        ((hgm.mono_measure Measure.restrict_le_self).pow 2).comp_snd
    refine (integrable_const (C0 * M ^ 2)).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg p.1 p.2) (sq_nonneg _))]
    exact mul_le_mul (hC0 (p.1 - p.2)) (hsqle (hg p.2)) (sq_nonneg _) hC0nonneg
  have hstep4 : (∫ x in s, ∫ y in t, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
      = ∫ y in t, ∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 :=
    integral_integral_swap hFubInt
  -- bound the inner (now `x`-first) integral by `C1`, uniformly in `y`
  have hmarginal_x : ∀ y, (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) ≤ C1 := by
    intro y
    calc ∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)
        ≤ ∫ x, commutatorMajorant m ε (Λ : ℝ) (x - y) :=
          setIntegral_le_integral (hK_int_x y) (Filter.Eventually.of_forall fun x => hK_nonneg x y)
      _ = C1 := integral_commutatorMajorant_sub' hε (Λ : ℝ) y
  have hstep5 : ∀ y ∈ t, (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2)
      = (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) * (g y) ^ 2 :=
    fun y _ => integral_mul_const _ _
  have hmarginal_meas : AEStronglyMeasurable
      (fun y => ∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) volume := by
    have hjcont : Continuous fun q : Vec m × Vec m => commutatorMajorant m ε (Λ : ℝ) (q.2 - q.1) :=
      (continuous_commutatorMajorant ε (Λ : ℝ)).comp (continuous_snd.sub continuous_fst)
    exact hjcont.aestronglyMeasurable.integral_prod_right'
  have hRHSfinal : (∫ y in t, (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) * (g y) ^ 2)
      ≤ ∫ y in t, C1 * (g y) ^ 2 := by
    have hgint : IntegrableOn (fun y => (g y) ^ 2) t volume := by
      have hgbound : Integrable (fun _ : Vec m => M ^ 2) (volume.restrict t) := integrable_const _
      exact hgbound.mono' ((hgm.pow 2).mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqle (hg y))
    have hRint : IntegrableOn (fun y => C1 * (g y) ^ 2) t volume := hgint.const_mul C1
    have hLmeas : AEStronglyMeasurable
        (fun y => (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) * (g y) ^ 2) volume :=
      hmarginal_meas.mul (hgm.pow 2)
    have hLint : IntegrableOn
        (fun y => (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) * (g y) ^ 2) t volume := by
      refine hRint.mono' (hLmeas.mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun y => ?_)
      have hmnn : 0 ≤ ∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y) :=
        setIntegral_nonneg hsMeas (fun x _ => hK_nonneg x y)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmnn (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hmarginal_x y) (sq_nonneg _)
    exact setIntegral_mono hLint hRint
      (fun y => mul_le_mul_of_nonneg_right (hmarginal_x y) (sq_nonneg _))
  have hstep6 : (∫ y in t, C1 * (g y) ^ 2) = C1 * ∫ y in t, (g y) ^ 2 := integral_const_mul _ _
  calc ∫ x in s, (diPernaLionsCommutator m ε b divb g x) ^ 2
      ≤ ∫ x in s, C1 * ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := hstep1
    _ = C1 * ∫ x in s, ∫ y, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := hstep2
    _ = C1 * ∫ x in s, ∫ y in t, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := by
        rw [hstep3]
    _ = C1 * ∫ y in t, ∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y) * (g y) ^ 2 := by
        rw [hstep4]
    _ = C1 * ∫ y in t, (∫ x in s, commutatorMajorant m ε (Λ : ℝ) (x - y)) * (g y) ^ 2 := by
        rw [setIntegral_congr_fun htMeas hstep5]
    _ ≤ C1 * ∫ y in t, C1 * (g y) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hRHSfinal hC1nonneg
    _ = C1 * (C1 * ∫ y in t, (g y) ^ 2) := by rw [hstep6]
    _ = C1 ^ 2 * ∫ y in t, (g y) ^ 2 := by ring

end CIV
