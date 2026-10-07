/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Mollifier

/-!
# The commutator of DiPerna and Lions

Mollifying `eq:aniso:comparison:equation` in space produces the commutator
`R_ε = B·∇(η_ε * q) - η_ε * (B·∇q)` of `eq:aniso:comparison:mollified`. Since `B·∇q` means
`div(Bq) - (div B) q`, the convolution `η_ε * (B·∇q)` is the integral of `q` against the
derivative of the kernel, and the commutator is the explicit integral

`R_ε(x) = ∫ q(y) (b(x) - b(y))·(∇η_ε)(x - y) dy + ∫ η_ε(x - y) (div b)(y) q(y) dy`,

taken here as its definition for one time slice `b = B(·, τ)`, `q = q(·, τ)`.

The estimate below is the uniform bound of `eq:aniso:comparison:mollified`: the first
integrand is supported where `|x - y| ≤ ε`, where the Lipschitz bound on `b` gains the factor
`ε` that cancels the `1/ε` of the gradient of the kernel. The constant is explicit,
`Λ M_∞ (C_η + 1)` with `C_η` the gradient constant of the profile.
-/

public section

open CKN MeasureTheory

noncomputable section

namespace CIV

variable {m : ℕ}

/-- The commutator `R_ε` of `eq:aniso:comparison:mollified` for one time slice, written as an
explicit integral against the kernel `η_ε` and its gradient. -/
@[expose] def diPernaLionsCommutator (m : ℕ) (ε : ℝ) (b : Vec m → Vec m) (divb g : Vec m → ℝ)
    (x : Vec m) : ℝ :=
  (∫ y : Vec m, g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
    + ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)

/-- The uniform bound `|R_ε| ≤ C(m, η) Λ M_∞` of `eq:aniso:comparison:mollified`. -/
theorem abs_diPernaLionsCommutator_le {ε M : ℝ} {Λ : NNReal} (hε : 0 < ε) (hM : 0 ≤ M)
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ y, |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) (x : Vec m) :
    |diPernaLionsCommutator m ε b divb g x| ≤ Λ * M * (mollifierGradConst m + 1) := by
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := Λ.coe_nonneg
  have hbcont : Continuous b := hlip.continuous
  -- the coordinate Lipschitz bound in the sup norm of `Vec m`
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
      ‖g y * ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)‖
        ≤ M * ((Λ : ℝ) * ε) *
          ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by
    intro y
    have hsum : |∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ ((Λ : ℝ) * ε) * ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by
      by_cases hxy : ‖x - y‖ ≤ ε
      · calc |∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
            ≤ ∑ i, |(b x i - b y i) *
                fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ((Λ : ℝ) * ε) *
                |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              exact (hcoord y i).trans (mul_le_mul_of_nonneg_left hxy hΛ)
          _ = ((Λ : ℝ) * ε) *
                ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
              (Finset.mul_sum _ _ _).symm
      · have hzero : ∀ i : Fin m,
            fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) = 0 := fun i =>
          fderiv_mollifierKernel_eq_zero hε (lt_of_not_ge hxy) (basisVec i)
        simp [hzero]
    calc ‖g y * ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)‖
        = |g y| * |∑ i, (b x i - b y i) *
            fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ M * (((Λ : ℝ) * ε) *
            ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) :=
          mul_le_mul (hg y) hsum (abs_nonneg _) hM
      _ = M * ((Λ : ℝ) * ε) *
            ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| := by ring
  have hmaj1 : Integrable (fun y : Vec m => M * ((Λ : ℝ) * ε) *
      ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|) volume :=
    (((integrable_sum_abs_fderiv_mollifierKernel hε).comp_sub_left x)).const_mul _
  have hint1 : Integrable (fun y : Vec m => g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume :=
    hmaj1.mono' (hgm.mul hfirstcont.aestronglyMeasurable)
      (Filter.Eventually.of_forall hfirstpt)
  have hintmaj1 : ∫ y : Vec m, M * ((Λ : ℝ) * ε) *
      ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        = M * (Λ : ℝ) * mollifierGradConst m := by
    rw [integral_const_mul, integral_sub_left_eq_self
      (fun w : Vec m => ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)|) volume x,
      integral_sum_abs_fderiv_mollifierKernel hε]
    field_simp
  have hbound1 : |∫ y : Vec m, g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ M * (Λ : ℝ) * mollifierGradConst m := by
    calc |∫ y : Vec m, g y *
          ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)|
        ≤ ∫ y : Vec m, ‖g y *
            ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)‖ := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (volume : Measure (Vec m)))
              (fun y : Vec m => g y *
                ∑ i, (b x i - b y i) *
                  fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      _ ≤ ∫ y : Vec m, M * ((Λ : ℝ) * ε) *
            ∑ i, |fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)| :=
          integral_mono hint1.norm hmaj1 hfirstpt
      _ = M * (Λ : ℝ) * mollifierGradConst m := hintmaj1
  -- the second integrand
  have hsecondpt : ∀ y : Vec m,
      ‖mollifierKernel m ε (x - y) * (divb y * g y)‖
        ≤ (Λ : ℝ) * M * mollifierKernel m ε (x - y) := by
    intro y
    have hker : 0 ≤ mollifierKernel m ε (x - y) := mollifierKernel_nonneg hε _
    calc ‖mollifierKernel m ε (x - y) * (divb y * g y)‖
        = mollifierKernel m ε (x - y) * (|divb y| * |g y|) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hker, abs_mul]
      _ ≤ mollifierKernel m ε (x - y) * ((Λ : ℝ) * M) := by
          refine mul_le_mul_of_nonneg_left ?_ hker
          exact mul_le_mul (hdivb y) (hg y) (abs_nonneg _) hΛ
      _ = (Λ : ℝ) * M * mollifierKernel m ε (x - y) := by ring
  have hmaj2 : Integrable
      (fun y : Vec m => (Λ : ℝ) * M * mollifierKernel m ε (x - y)) volume :=
    ((integrable_mollifierKernel hε).comp_sub_left x).const_mul _
  have hint2 : Integrable
      (fun y : Vec m => mollifierKernel m ε (x - y) * (divb y * g y)) volume :=
    hmaj2.mono' (((contDiff_mollifierKernel (m := m) ε).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul (hdivbm.mul hgm))
      (Filter.Eventually.of_forall hsecondpt)
  have hbound2 : |∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)|
      ≤ (Λ : ℝ) * M := by
    calc |∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y)|
        ≤ ∫ y : Vec m, ‖mollifierKernel m ε (x - y) * (divb y * g y)‖ := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (volume : Measure (Vec m)))
              (fun y : Vec m => mollifierKernel m ε (x - y) * (divb y * g y))
      _ ≤ ∫ y : Vec m, (Λ : ℝ) * M * mollifierKernel m ε (x - y) :=
          integral_mono hint2.norm hmaj2 hsecondpt
      _ = (Λ : ℝ) * M := by
          rw [integral_const_mul, integral_sub_left_eq_self (mollifierKernel m ε) volume x,
            integral_mollifierKernel hε, mul_one]
  have habs := abs_add_le (∫ y : Vec m, g y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
    (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y))
  rw [diPernaLionsCommutator]
  have hfinal : (Λ : ℝ) * M * (mollifierGradConst m + 1)
      = M * (Λ : ℝ) * mollifierGradConst m + (Λ : ℝ) * M := by ring
  rw [hfinal]
  linarith only [habs, hbound1, hbound2]

end CIV
