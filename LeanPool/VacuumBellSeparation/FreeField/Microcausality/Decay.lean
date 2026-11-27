/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Decay

/-!
# Microcausality, stage F: integration by parts for complex linear phases

Stage F of the microcausality proof, independent of the particular
phase.  Let `c : Spacetime →L[ℝ] ℂ` be a real-linear map, i.e. a complex linear form in the four
coordinates.  The plane wave `y ↦ exp(i c(y - x₀))` may grow, but test functions have compact
support, so integration by parts needs no positivity.

* `dirDeriv v F`: the directional derivative `∂_v F = DF(·) v` of a real test function, again a
  real test function, with `tsupport (∂_v F) ⊆ tsupport F` (`tsupport_dirDeriv_subset`,
  `tsupport_iterate_dirDeriv_subset`);
* `integral_expPhase_mul_dirDeriv`:
  `∫ e^{i c(y - x₀)} ∂_v F(y) dy = -i c(v) ∫ e^{i c(y - x₀)} F(y) dy`;
* `pow_mul_integral_expPhase_mul`:
  `(i c(v))^N ∫ e^{i c(y - x₀)} F(y) dy = (-1)^N ∫ e^{i c(y - x₀)} ∂_v^N F(y) dy`;
* `norm_pow_mul_norm_integral_expPhase_le`: if `Im c(y - x₀) ≥ 0` on `tsupport G`, then
  `|c(v)|^N |∫ e^{i c(y - x₀)} G(y) dy| ≤ ‖∂_v^N G‖₁`;
* `norm_pow_mul_norm_doubleIntegral_le`: if `Im c(y - x) ≥ 0` for `x ∈ tsupport F` and
  `y ∈ tsupport G`, then `|c(v)|^N |∫∫ e^{i c(y - x)} F(x) G(y) dy dx| ≤ ‖F‖₁ ‖∂_v^N G‖₁`;
* `coordDir`: the coordinate directions `e 0 = (1, 0)`, `e (i + 1) = (0, 𝐞ᵢ)`;
  `exists_le_norm_coordDir`: `∑_j |c(e_j)|² ≥ K²` implies `|c(e_j)| ≥ K / 2` for some `j`;
* `norm_doubleIntegral_le`: under both hypotheses and `K > 0`,
  `|∫∫ e^{i c(y - x)} F(x) G(y) dy dx| ≤ (2/K)^N ‖F‖₁ max_j ‖∂_{e_j}^N G‖₁`
  (the maximum is `maxCoordDerivNorm G N`);
* `integral_prod_expPhase_eq_iterated`, `norm_integral_prod_expPhase_le`: the double integral
  over the product measure on `Spacetime × Spacetime` is the iterated one (the integrand
  factorizes), so the same bound holds for it.
-/

@[expose] public section

open MeasureTheory

namespace VacuumBellSeparation

/-! ### Directional derivatives of test functions -/

/-- The directional derivative `∂_v F : x ↦ DF(x) v` of a real test function along a spacetime
vector `v`, again a real test function. -/
noncomputable def dirDeriv (v : Spacetime) (F : RealTestFunction) : RealTestFunction :=
  ⟨fun x => fderiv ℝ F.1 x v,
    (contDiff_infty_iff_fderiv.1 F.2.1).2.clm_apply contDiff_const,
    F.2.2.fderiv_apply ℝ v⟩

/-- `(∂_v F)(x) = DF(x) v`. -/
theorem dirDeriv_apply (v : Spacetime) (F : RealTestFunction) (x : Spacetime) :
    (dirDeriv v F).1 x = fderiv ℝ F.1 x v := rfl

/-- `tsupport (∂_v F) ⊆ tsupport F`. -/
theorem tsupport_dirDeriv_subset (v : Spacetime) (F : RealTestFunction) :
    tsupport (dirDeriv v F).1 ⊆ tsupport F.1 := by
  change tsupport (fun x => fderiv ℝ F.1 x v) ⊆ tsupport F.1
  exact tsupport_fderiv_apply_subset ℝ v

/-- `tsupport (∂_v^N F) ⊆ tsupport F`. -/
theorem tsupport_iterate_dirDeriv_subset (v : Spacetime) (F : RealTestFunction) (N : ℕ) :
    tsupport ((dirDeriv v)^[N] F).1 ⊆ tsupport F.1 := by
  induction N with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (tsupport_dirDeriv_subset v _).trans ih

/-! ### Plane waves with a complex linear phase -/

/-- The plane wave `y ↦ exp(i c(y - x₀))` of a complex linear phase is continuous. -/
theorem continuous_expPhase (c : Spacetime →L[ℝ] ℂ) (x₀ : Spacetime) :
    Continuous fun y : Spacetime => Complex.exp (Complex.I * c (y - x₀)) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (c.continuous.comp (continuous_id.sub continuous_const)))

/-- `y ↦ exp(i c(y - x₀)) F(y)` is integrable (continuous with compact support). -/
theorem integrable_expPhase_mul (c : Spacetime →L[ℝ] ℂ) (x₀ : Spacetime) (F : RealTestFunction) :
    Integrable fun y : Spacetime => Complex.exp (Complex.I * c (y - x₀)) * (F.1 y : ℂ) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_expPhase c x₀).mul
      (Complex.continuous_ofReal.comp (continuous_testFunction F))
  · exact (F.2.2.comp_left Complex.ofReal_zero).mul_left

/-- The phase `y ↦ i c(y - x₀)` has derivative `i c`. -/
theorem hasFDerivAt_I_mul_phase (c : Spacetime →L[ℝ] ℂ) (x₀ y : Spacetime) :
    HasFDerivAt (fun y : Spacetime => Complex.I * c (y - x₀)) (Complex.I • c) y := by
  have h1 : HasFDerivAt (fun y : Spacetime => c (y - x₀)) c y :=
    ((c.hasFDerivAt (x := y)).sub_const (c x₀)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => map_sub c z x₀)
  exact h1.const_mul Complex.I

/-- **Integration by parts for a complex linear phase**:
`∫ e^{i c(y - x₀)} ∂_v F(y) dy = -i c(v) ∫ e^{i c(y - x₀)} F(y) dy`. -/
theorem integral_expPhase_mul_dirDeriv (c : Spacetime →L[ℝ] ℂ) (x₀ v : Spacetime)
    (F : RealTestFunction) :
    ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * ((dirDeriv v F).1 y : ℂ) =
      -(Complex.I * c v) * ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (F.1 y : ℂ) := by
  have he : ∀ y : Spacetime, HasFDerivAt (fun y => Complex.exp (Complex.I * c (y - x₀)))
      (Complex.exp (Complex.I * c (y - x₀)) • (Complex.I • c)) y := fun y =>
    (hasFDerivAt_I_mul_phase c x₀ y).cexp
  have hg : ∀ y : Spacetime, HasFDerivAt (fun y => ((F.1 y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ F.1 y)) y := fun y =>
    Complex.ofRealCLM.hasFDerivAt.comp y ((differentiable_testFunction F y).hasFDerivAt)
  have hfd : ∀ y : Spacetime,
      fderiv ℝ (fun y => Complex.exp (Complex.I * c (y - x₀))) y v =
        Complex.I * c v * Complex.exp (Complex.I * c (y - x₀)) := by
    intro y
    rw [(he y).fderiv]
    simp only [smul_apply, smul_eq_mul]
    ring
  have hgd : ∀ y : Spacetime, fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) y v =
      (((dirDeriv v F).1 y : ℝ) : ℂ) := by
    intro y
    rw [(hg y).fderiv]
    rfl
  have hfun1 : (fun y : Spacetime =>
      fderiv ℝ (fun y => Complex.exp (Complex.I * c (y - x₀))) y v * ((F.1 y : ℝ) : ℂ)) =
      fun y => Complex.I * c v * (Complex.exp (Complex.I * c (y - x₀)) * ((F.1 y : ℝ) : ℂ)) := by
    funext y
    rw [hfd]
    ring
  have hfun2 : (fun y : Spacetime =>
      Complex.exp (Complex.I * c (y - x₀)) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) y v) =
      fun y => Complex.exp (Complex.I * c (y - x₀)) * (((dirDeriv v F).1 y : ℝ) : ℂ) := by
    funext y
    rw [hgd]
  have hint1 : Integrable (fun y : Spacetime =>
      fderiv ℝ (fun y => Complex.exp (Complex.I * c (y - x₀))) y v * ((F.1 y : ℝ) : ℂ)) := by
    rw [hfun1]
    exact (integrable_expPhase_mul c x₀ F).const_mul _
  have hint2 : Integrable (fun y : Spacetime =>
      Complex.exp (Complex.I * c (y - x₀)) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) y v) := by
    rw [hfun2]
    exact integrable_expPhase_mul c x₀ (dirDeriv v F)
  have hint3 : Integrable (fun y : Spacetime =>
      Complex.exp (Complex.I * c (y - x₀)) * ((F.1 y : ℝ) : ℂ)) :=
    integrable_expPhase_mul c x₀ F
  have : (volume : Measure Spacetime).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have key : ∫ y : Spacetime,
      Complex.exp (Complex.I * c (y - x₀)) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) y v =
      - ∫ y : Spacetime,
        fderiv ℝ (fun y => Complex.exp (Complex.I * c (y - x₀))) y v * ((F.1 y : ℝ) : ℂ) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint1 hint2 hint3
      (fun y _ => (he y).differentiableAt) (fun y _ => (hg y).differentiableAt)
  calc ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (((dirDeriv v F).1 y : ℝ) : ℂ)
      = ∫ y : Spacetime,
          Complex.exp (Complex.I * c (y - x₀)) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) y v := by
        rw [hfun2]
    _ = - ∫ y : Spacetime,
          fderiv ℝ (fun y => Complex.exp (Complex.I * c (y - x₀))) y v * ((F.1 y : ℝ) : ℂ) :=
        key
    _ = - ∫ y : Spacetime,
          Complex.I * c v * (Complex.exp (Complex.I * c (y - x₀)) * ((F.1 y : ℝ) : ℂ)) := by
        rw [hfun1]
    _ = -(Complex.I * c v) *
          ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * ((F.1 y : ℝ) : ℂ) := by
        rw [integral_const_mul]
        ring

/-- **Iterated integration by parts**:
`(i c(v))^N ∫ e^{i c(y - x₀)} F(y) dy = (-1)^N ∫ e^{i c(y - x₀)} ∂_v^N F(y) dy`. -/
theorem pow_mul_integral_expPhase_mul (c : Spacetime →L[ℝ] ℂ) (x₀ v : Spacetime)
    (F : RealTestFunction) (N : ℕ) :
    (Complex.I * c v) ^ N *
        ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (F.1 y : ℂ) =
      (-1) ^ N * ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x₀)) * (((dirDeriv v)^[N] F).1 y : ℂ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', integral_expPhase_mul_dirDeriv]
    linear_combination (Complex.I * c v) * ih

/-! ### Bounds when the phase has nonnegative imaginary part -/

/-- `|exp(i w)| ≤ 1` when `Im w ≥ 0`. -/
theorem norm_exp_I_mul_le_one_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    ‖Complex.exp (Complex.I * w)‖ ≤ 1 := by
  rw [Complex.norm_exp, Complex.I_mul_re]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hw)

/-- `|F|` is integrable for a real test function `F`. -/
theorem integrable_abs_testFunction (F : RealTestFunction) :
    Integrable fun x : Spacetime => |F.1 x| :=
  ((continuous_testFunction F).integrable_of_hasCompactSupport F.2.2).abs

/-- If `Im c(y - x₀) ≥ 0` on `tsupport G`, then
`|c(v)|^N |∫ e^{i c(y - x₀)} G(y) dy| ≤ ∫ |∂_v^N G|`. -/
theorem norm_pow_mul_norm_integral_expPhase_le (c : Spacetime →L[ℝ] ℂ) (x₀ v : Spacetime)
    (G : RealTestFunction) (N : ℕ) (hc : ∀ y ∈ tsupport G.1, 0 ≤ (c (y - x₀)).im) :
    ‖c v‖ ^ N * ‖∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (G.1 y : ℂ)‖ ≤
      ∫ y : Spacetime, |((dirDeriv v)^[N] G).1 y| := by
  have h := pow_mul_integral_expPhase_mul c x₀ v G N
  have heq : ‖c v‖ ^ N * ‖∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (G.1 y : ℂ)‖ =
      ‖∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x₀)) * (((dirDeriv v)^[N] G).1 y : ℂ)‖ := by
    calc ‖c v‖ ^ N * ‖∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (G.1 y : ℂ)‖
        = ‖(Complex.I * c v) ^ N *
            ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x₀)) * (G.1 y : ℂ)‖ := by
          rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul]
      _ = ‖(-1 : ℂ) ^ N * ∫ y : Spacetime,
            Complex.exp (Complex.I * c (y - x₀)) * (((dirDeriv v)^[N] G).1 y : ℂ)‖ := by
          rw [h]
      _ = ‖∫ y : Spacetime,
            Complex.exp (Complex.I * c (y - x₀)) * (((dirDeriv v)^[N] G).1 y : ℂ)‖ := by
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [heq]
  refine norm_integral_le_of_norm_le (integrable_abs_testFunction _)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hy : y ∈ tsupport G.1
  · exact mul_le_of_le_one_left (abs_nonneg _) (norm_exp_I_mul_le_one_of_im_nonneg (hc y hy))
  · have h0 : ((dirDeriv v)^[N] G).1 y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hy' => hy (tsupport_iterate_dirDeriv_subset v G N hy')
    simp [h0]

/-- **The bound for the double integral**: if `Im c(y - x) ≥ 0` for `x ∈ tsupport F` and
`y ∈ tsupport G`, then `|c(v)|^N |∫∫ e^{i c(y - x)} F(x) G(y) dy dx| ≤ ‖F‖₁ ‖∂_v^N G‖₁`. -/
theorem norm_pow_mul_norm_doubleIntegral_le (c : Spacetime →L[ℝ] ℂ) (v : Spacetime)
    (F G : RealTestFunction) (N : ℕ)
    (hc : ∀ x ∈ tsupport F.1, ∀ y ∈ tsupport G.1, 0 ≤ (c (y - x)).im) :
    ‖c v‖ ^ N * ‖∫ x : Spacetime, ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖ ≤
      (∫ x : Spacetime, |F.1 x|) * ∫ y : Spacetime, |((dirDeriv v)^[N] G).1 y| := by
  set B : ℝ := ∫ y : Spacetime, |((dirDeriv v)^[N] G).1 y|
  have hcv : 0 ≤ ‖c v‖ ^ N := pow_nonneg (norm_nonneg _) N
  have hinner : ∀ x : Spacetime, ∫ y : Spacetime,
      Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ) =
      (F.1 x : ℂ) * ∫ y : Spacetime, Complex.exp (Complex.I * c (y - x)) * (G.1 y : ℂ) := by
    intro x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hpt : ∀ x : Spacetime, ‖((‖c v‖ ^ N : ℝ) : ℂ) * ∫ y : Spacetime,
      Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖ ≤ |F.1 x| * B := by
    intro x
    rw [hinner x, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hcv]
    by_cases hx : x ∈ tsupport F.1
    · have h1 := norm_pow_mul_norm_integral_expPhase_le c x v G N (fun y hy => hc x hx y hy)
      have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (F.1 x))
      calc ‖c v‖ ^ N * (|F.1 x| *
            ‖∫ y : Spacetime, Complex.exp (Complex.I * c (y - x)) * (G.1 y : ℂ)‖)
          = |F.1 x| * (‖c v‖ ^ N *
            ‖∫ y : Spacetime, Complex.exp (Complex.I * c (y - x)) * (G.1 y : ℂ)‖) := by ring
        _ ≤ |F.1 x| * B := h2
    · have h0 : F.1 x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  calc ‖c v‖ ^ N * ‖∫ x : Spacetime, ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖
      = ‖((‖c v‖ ^ N : ℝ) : ℂ) * ∫ x : Spacetime, ∫ y : Spacetime,
          Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcv]
    _ = ‖∫ x : Spacetime, ((‖c v‖ ^ N : ℝ) : ℂ) * ∫ y : Spacetime,
          Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖ := by
        rw [integral_const_mul]
    _ ≤ ∫ x : Spacetime, |F.1 x| * B :=
        norm_integral_le_of_norm_le ((integrable_abs_testFunction F).mul_const B)
          (Filter.Eventually.of_forall hpt)
    _ = (∫ x : Spacetime, |F.1 x|) * B := integral_mul_const B _

/-! ### Choice of a direction -/

/-- The four coordinate directions of spacetime: `e 0 = (1, 0)` (time) and
`e (i + 1) = (0, 𝐞ᵢ)` (space). -/
noncomputable def coordDir : Fin 4 → Spacetime :=
  Fin.cons ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))
    fun i : Fin 3 => ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))

/-- `e 0 = (1, 0)`. -/
@[simp]
theorem coordDir_zero : coordDir 0 = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) :=
  Fin.cons_zero _ _

/-- `e (i + 1) = (0, 𝐞ᵢ)`. -/
@[simp]
theorem coordDir_succ (i : Fin 3) :
    coordDir i.succ = ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) :=
  Fin.cons_succ _ _ _

/-- `∑_j |c(e_j)|² = |c(1, 0)|² + ∑_i |c(0, 𝐞ᵢ)|²`. -/
theorem sum_norm_sq_coordDir (c : Spacetime →L[ℝ] ℂ) :
    ∑ j : Fin 4, ‖c (coordDir j)‖ ^ 2 =
      ‖c ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))‖ ^ 2 +
        ∑ i : Fin 3, ‖c ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  rw [Fin.sum_univ_succ, coordDir_zero]
  simp only [coordDir_succ]

/-- If `∑_j |c(e_j)|² ≥ K²`, then `|c(e_j)| ≥ K / 2` for some coordinate direction `e_j`. -/
theorem exists_le_norm_coordDir {c : Spacetime →L[ℝ] ℂ} {K : ℝ}
    (h : K ^ 2 ≤ ∑ j : Fin 4, ‖c (coordDir j)‖ ^ 2) : ∃ j, K / 2 ≤ ‖c (coordDir j)‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  rw [Fin.sum_univ_four] at h
  have h0 := mul_self_lt_mul_self (norm_nonneg (c (coordDir 0))) (hcon 0)
  have h1 := mul_self_lt_mul_self (norm_nonneg (c (coordDir 1))) (hcon 1)
  have h2 := mul_self_lt_mul_self (norm_nonneg (c (coordDir 2))) (hcon 2)
  have h3 := mul_self_lt_mul_self (norm_nonneg (c (coordDir 3))) (hcon 3)
  linarith

/-- `max_j ‖∂_{e_j}^N G‖₁`: the largest `L¹` norm of the `N`-th derivatives of `G` along the four
coordinate directions. -/
noncomputable def maxCoordDerivNorm (G : RealTestFunction) (N : ℕ) : ℝ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩
    fun j : Fin 4 => ∫ y : Spacetime, |((dirDeriv (coordDir j))^[N] G).1 y|

/-- `‖∂_{e_j}^N G‖₁ ≤ max_k ‖∂_{e_k}^N G‖₁`. -/
theorem le_maxCoordDerivNorm (G : RealTestFunction) (N : ℕ) (j : Fin 4) :
    ∫ y : Spacetime, |((dirDeriv (coordDir j))^[N] G).1 y| ≤ maxCoordDerivNorm G N := by
  unfold maxCoordDerivNorm
  exact Finset.le_sup' (fun j : Fin 4 => ∫ y : Spacetime, |((dirDeriv (coordDir j))^[N] G).1 y|)
    (Finset.mem_univ j)

/-- **Uniform decay bound**: if `Im c(y - x) ≥ 0` for `x ∈ tsupport F`, `y ∈ tsupport G`, and
`∑_j |c(e_j)|² ≥ K²` with `K > 0`, then
`|∫∫ e^{i c(y - x)} F(x) G(y) dy dx| ≤ (2/K)^N ‖F‖₁ max_j ‖∂_{e_j}^N G‖₁`. -/
theorem norm_doubleIntegral_le (c : Spacetime →L[ℝ] ℂ) (F G : RealTestFunction) (N : ℕ)
    {K : ℝ} (hK : 0 < K) (hc : ∀ x ∈ tsupport F.1, ∀ y ∈ tsupport G.1, 0 ≤ (c (y - x)).im)
    (hsum : K ^ 2 ≤ ∑ j : Fin 4, ‖c (coordDir j)‖ ^ 2) :
    ‖∫ x : Spacetime, ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖ ≤
      (2 / K) ^ N * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G N := by
  obtain ⟨j, hj⟩ := exists_le_norm_coordDir hsum
  have h4 := norm_pow_mul_norm_doubleIntegral_le c (coordDir j) F G N hc
  have hA : 0 ≤ ∫ x : Spacetime, |F.1 x| := integral_nonneg fun x => abs_nonneg _
  have hpow : (K / 2) ^ N ≤ ‖c (coordDir j)‖ ^ N :=
    pow_le_pow_left₀ (div_nonneg hK.le zero_le_two) hj N
  have hmax := le_maxCoordDerivNorm G N j
  have hΦ := norm_nonneg (∫ x : Spacetime, ∫ y : Spacetime,
    Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ))
  have h5 : (K / 2) ^ N * ‖∫ x : Spacetime, ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖ ≤
      (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G N :=
    (mul_le_mul_of_nonneg_right hpow hΦ).trans (h4.trans (mul_le_mul_of_nonneg_left hmax hA))
  have hinv : (2 / K) ^ N * (K / 2) ^ N = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm (2 : ℝ) K,
      div_self (mul_ne_zero hK.ne' two_ne_zero), one_pow]
  have h2K : 0 ≤ (2 / K) ^ N := pow_nonneg (div_nonneg zero_le_two hK.le) N
  calc ‖∫ x : Spacetime, ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖
      = (2 / K) ^ N * ((K / 2) ^ N * ‖∫ x : Spacetime, ∫ y : Spacetime,
          Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ)‖) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (2 / K) ^ N * ((∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G N) :=
        mul_le_mul_of_nonneg_left h5 h2K
    _ = (2 / K) ^ N * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G N := by ring

/-! ### The double integral over the product measure -/

/-- For a linear phase the integrand factorizes, so the double integral over the product measure
equals the iterated integral (no integrability hypothesis is needed). -/
theorem integral_prod_expPhase_eq_iterated (c : Spacetime →L[ℝ] ℂ) (F G : RealTestFunction) :
    ∫ z : Spacetime × Spacetime, Complex.exp (Complex.I * c (z.2 - z.1)) * (F.1 z.1 : ℂ) *
        (G.1 z.2 : ℂ) ∂((volume : Measure Spacetime).prod volume) =
      ∫ x : Spacetime, ∫ y : Spacetime,
        Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ) := by
  have hfac : ∀ x y : Spacetime,
      Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ) =
        (Complex.exp (-(Complex.I * c x)) * (F.1 x : ℂ)) *
          (Complex.exp (Complex.I * c y) * (G.1 y : ℂ)) := by
    intro x y
    have h1 : Complex.I * c (y - x) = -(Complex.I * c x) + Complex.I * c y := by
      rw [map_sub]
      ring
    rw [h1, Complex.exp_add]
    ring
  calc ∫ z : Spacetime × Spacetime, Complex.exp (Complex.I * c (z.2 - z.1)) * (F.1 z.1 : ℂ) *
        (G.1 z.2 : ℂ) ∂((volume : Measure Spacetime).prod volume)
      = ∫ z : Spacetime × Spacetime, (Complex.exp (-(Complex.I * c z.1)) * (F.1 z.1 : ℂ)) *
          (Complex.exp (Complex.I * c z.2) * (G.1 z.2 : ℂ))
            ∂((volume : Measure Spacetime).prod volume) := by
        congr 1
        funext z
        exact hfac z.1 z.2
    _ = (∫ x : Spacetime, Complex.exp (-(Complex.I * c x)) * (F.1 x : ℂ)) *
          ∫ y : Spacetime, Complex.exp (Complex.I * c y) * (G.1 y : ℂ) :=
        integral_prod_mul (fun x : Spacetime => Complex.exp (-(Complex.I * c x)) * (F.1 x : ℂ))
          (fun y : Spacetime => Complex.exp (Complex.I * c y) * (G.1 y : ℂ))
    _ = ∫ x : Spacetime, ∫ y : Spacetime,
          Complex.exp (Complex.I * c (y - x)) * (F.1 x : ℂ) * (G.1 y : ℂ) := by
        rw [← integral_mul_const]
        congr 1
        funext x
        rw [← integral_const_mul]
        congr 1
        funext y
        exact (hfac x y).symm

/-- The uniform decay bound of `norm_doubleIntegral_le` for the double integral over the product
measure on `Spacetime × Spacetime`. -/
theorem norm_integral_prod_expPhase_le (c : Spacetime →L[ℝ] ℂ) (F G : RealTestFunction) (N : ℕ)
    {K : ℝ} (hK : 0 < K) (hc : ∀ x ∈ tsupport F.1, ∀ y ∈ tsupport G.1, 0 ≤ (c (y - x)).im)
    (hsum : K ^ 2 ≤ ∑ j : Fin 4, ‖c (coordDir j)‖ ^ 2) :
    ‖∫ z : Spacetime × Spacetime, Complex.exp (Complex.I * c (z.2 - z.1)) * (F.1 z.1 : ℂ) *
        (G.1 z.2 : ℂ) ∂((volume : Measure Spacetime).prod volume)‖ ≤
      (2 / K) ^ N * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G N := by
  rw [integral_prod_expPhase_eq_iterated]
  exact norm_doubleIntegral_le c F G N hK hc hsum

end VacuumBellSeparation
