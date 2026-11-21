/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Barenblatt
public import LeanPool.Cutfast.Asymptotics
public import LeanPool.Cutfast.Elliptic
public import LeanPool.Cutfast.GaussianDensity
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Remark 3.2: Student t-distributions

We write `f_r(y) = Γ((r+d)/2) / (Γ(r/2) (rπ)^{d/2}) (1 + |y|²/r)^{-(r+d)/2}` for the standard
Student density (`Cutfast.Student.stdDensity`). Everything is reduced to this standard case by
the affine change of variables `x = x₀ + √Σ y` (`Cutfast.Student.studentDensity_affine`,
`Cutfast.Student.densityMeasure_studentDensity`).

* The standard law is the Gaussian scale mixture `Y/√(Z/r)`: after the substitution
  `y = √(z/r) x`, Tonelli's theorem and the Gamma integral give `f_r`
  (`Cutfast.Student.map_prod_stdGaussian_gamma`); the density of `stdGaussian` is computed from
  its characteristic function (`Cutfast.Student.stdGaussian_eq_withDensity`).
* Moments come from the radial integrals of `Cutfast.Radial`; the covariance is obtained from
  the invariance of `u ↦ ∫ ⟪y,u⟫² f_r` under reflections, and polarization.
* The limit `r → ∞` is a dominated convergence argument for the unnormalized kernels, the
  normalizing constants being the reciprocals of their integrals (no Gamma asymptotics needed).
* The Fisher–Snedecor law is the image of `f_r` under `y ↦ |y|²/d`, computed radially.
* A normalized profile `(c + b|x|²)^{-(r+d)/2}` is an isotropic Student density
  (`Cutfast.Student.exists_student_of_full`), which gives the Barenblatt identification.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

local notation "𝓛" => Matrix.toEuclideanCLM (𝕜 := ℝ)

namespace Student

variable {d : ℕ}

/-- The unnormalized standard Student kernel `(1 + |y|²/r)^{-(r+d)/2}`. -/
noncomputable def kernel (d : ℕ) (r : ℝ) (y : E d) : ℝ :=
  (1 + r⁻¹ * ‖y‖ ^ 2) ^ (-((r + d) / 2))

/-- The normalizing constant `Γ((r+d)/2) / (Γ(r/2) (rπ)^{d/2})`. -/
noncomputable def stdConst (d : ℕ) (r : ℝ) : ℝ :=
  Gamma ((r + d) / 2) / (Gamma (r / 2) * (r * π) ^ ((d : ℝ) / 2))

/-- The standard Student density (`x₀ = 0`, `Σ = I`). -/
noncomputable def stdDensity (d : ℕ) (r : ℝ) (y : E d) : ℝ := stdConst d r * kernel d r y

lemma kernel_pos (r : ℝ) (hr : 0 < r) (y : E d) : 0 < kernel d r y := by
  unfold kernel; positivity

lemma stdConst_pos {r : ℝ} (hr : 0 < r) : 0 < stdConst d r := by
  unfold stdConst
  have : 0 < Gamma ((r + d) / 2) := Gamma_pos_of_pos (by positivity)
  have : 0 < Gamma (r / 2) := Gamma_pos_of_pos (by positivity)
  positivity

lemma stdDensity_pos {r : ℝ} (hr : 0 < r) (y : E d) : 0 < stdDensity d r y :=
  mul_pos (stdConst_pos hr) (kernel_pos r hr y)

lemma continuous_kernel {r : ℝ} (hr : 0 < r) : Continuous (kernel d r) := by
  unfold kernel
  exact (by fun_prop : Continuous fun y : E d => 1 + r⁻¹ * ‖y‖ ^ 2).rpow_const
    fun y => Or.inl (by positivity)

lemma continuous_stdDensity {r : ℝ} (hr : 0 < r) : Continuous (stdDensity d r) :=
  continuous_const.mul (continuous_kernel hr)

lemma half_lt {r : ℝ} (hr : 0 < r) : (d : ℝ) / 2 < (r + d) / 2 := by linarith

/-- Moments of the kernel:
`∫ |y|^a K = π^{d/2} r^{(d+a)/2} Γ((d+a)/2) Γ((r-a)/2) / (Γ(d/2) Γ(p))`. -/
lemma integral_rpow_norm_mul_kernel (hd : 1 ≤ d) {r a : ℝ} (hr : 0 < r) (ha : -(d : ℝ) < a)
    (har : a < r) :
    Integrable (fun y : E d => ‖y‖ ^ a * kernel d r y) ∧
    ∫ y : E d, ‖y‖ ^ a * kernel d r y =
      r ^ ((d + a) / 2) * (π ^ ((d : ℝ) / 2) * Gamma ((d + a) / 2) * Gamma ((r - a) / 2) /
        (Gamma (d / 2) * Gamma ((r + d) / 2))) := by
  have hap : a + d < 2 * ((r + d) / 2) := by linarith
  refine ⟨integrable_rpow_norm_mul_add_sq_rpow_neg hd ha hap one_pos (inv_pos.2 hr), ?_⟩
  unfold kernel
  rw [integral_rpow_norm_mul_add_sq_rpow_neg hd ha hap one_pos (inv_pos.2 hr), one_rpow,
    one_mul, inv_rpow hr.le, ← rpow_neg hr.le, neg_neg,
    show (r + d) / 2 - (d + a) / 2 = (r - a) / 2 by ring]

lemma integral_kernel (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    Integrable (kernel d r) ∧
    ∫ y : E d, kernel d r y = (r * π) ^ ((d : ℝ) / 2) * Gamma (r / 2) / Gamma ((r + d) / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := integral_rpow_norm_mul_kernel hd hr (a := 0) (by linarith) hr
  simp only [rpow_zero, one_mul, add_zero, sub_zero] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, mul_rpow hr.le pi_pos.le]
  have : 0 < Gamma ((d : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  field_simp

lemma integrable_stdDensity (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) : Integrable (stdDensity d r) :=
  (integral_kernel hd hr).1.const_mul _

lemma integral_stdDensity (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) : ∫ y, stdDensity d r y = 1 := by
  unfold stdDensity stdConst
  rw [integral_const_mul, (integral_kernel hd hr).2]
  have : 0 < Gamma ((r + d) / 2) := Gamma_pos_of_pos (by positivity)
  have : 0 < Gamma (r / 2) := Gamma_pos_of_pos (by positivity)
  field_simp

lemma stdConst_mul_integral_kernel (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    stdConst d r = (∫ y : E d, kernel d r y)⁻¹ := by
  have := integral_stdDensity hd hr
  unfold stdDensity at this
  rw [integral_const_mul] at this
  exact eq_inv_of_mul_eq_one_left this

/-- Second moment of the standard Student law. -/
lemma integral_sq_norm_mul_stdDensity (hd : 1 ≤ d) {r : ℝ} (hr : 2 < r) :
    Integrable (fun y : E d => ‖y‖ ^ 2 * stdDensity d r y) ∧
    ∫ y : E d, ‖y‖ ^ 2 * stdDensity d r y = d * r / (r - 2) := by
  have hr0 : 0 < r := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := integral_rpow_norm_mul_kernel hd hr0 (a := 2) (by linarith) hr
  simp only [rpow_two] at h
  have e : ∀ y : E d, ‖y‖ ^ 2 * stdDensity d r y = stdConst d r * (‖y‖ ^ 2 * kernel d r y) :=
    fun y => by unfold stdDensity; ring
  simp_rw [e]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2]
  unfold stdConst
  have g1 : Gamma ((d + 2) / 2) = (d / 2) * Gamma (d / 2) := by
    rw [show ((d : ℝ) + 2) / 2 = d / 2 + 1 by ring, Gamma_add_one (by positivity)]
  have g2 : Gamma (r / 2) = ((r - 2) / 2) * Gamma ((r - 2) / 2) := by
    have : (r - 2) / 2 ≠ 0 := by intro h; linarith
    rw [show r / 2 = (r - 2) / 2 + 1 by ring, Gamma_add_one this]
  have hG1 : 0 < Gamma ((d : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Gamma ((r - 2) / 2) := Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Gamma ((r + d) / 2) := Gamma_pos_of_pos (by positivity)
  rw [g1, g2, show ((d : ℝ) + 2) / 2 = d / 2 + 1 by ring, rpow_add_one hr0.ne',
    mul_rpow hr0.le pi_pos.le]
  have : 0 < r ^ ((d : ℝ) / 2) := by positivity
  have : 0 < π ^ ((d : ℝ) / 2) := by positivity
  have : r - 2 ≠ 0 := by linarith
  field_simp

/-- Non-integrability of `|y|^a K` for `a ≥ r`. -/
lemma not_integrable_rpow_norm_mul_kernel (hd : 1 ≤ d) {r a : ℝ} (hr : 0 < r)
    (har : r ≤ a) : ¬ Integrable (fun y : E d => ‖y‖ ^ a * kernel d r y) := by
  intro hI
  have h := (Radial.radial hd (fun u => (1 + r⁻¹ * u) ^ (-((r + d) / 2))) a).1.1
    (by simpa [kernel] using hI)
  set p := (r + d) / 2
  -- lower bound on `Ioi (max 1 r)`
  have hsub : Set.Ioi (max 1 r) ⊆ Set.Ioi (0 : ℝ) := fun u hu =>
    lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (le_of_lt hu))
  have h1 := h.mono_set hsub
  have hlow : IntegrableOn (fun u : ℝ => (2 / r) ^ (-p) * u ^ (-1 : ℝ)) (Set.Ioi (max 1 r)) := by
    refine Integrable.mono' h1 (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu1 : 1 < u := lt_of_le_of_lt (le_max_left _ _) hu
    have hur : r < u := lt_of_le_of_lt (le_max_right _ _) hu
    have hu0 : 0 < u := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : 1 + r⁻¹ * u ≤ 2 / r * u := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      field_simp
      linarith
    have hp0 : 0 ≤ p := by positivity
    have e1 : (1 + r⁻¹ * u) ^ (-p) ≥ (2 / r * u) ^ (-p) :=
      rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
    rw [mul_rpow (by positivity) hu0.le] at e1
    have e2 : u ^ (-1 : ℝ) ≤ u ^ ((d + a) / 2 - 1) * u ^ (-p) := by
      rw [← rpow_add hu0]
      apply rpow_le_rpow_of_exponent_le hu1.le
      simp only [p]; linarith
    calc (2 / r) ^ (-p) * u ^ (-1 : ℝ) ≤ (2 / r) ^ (-p) * (u ^ ((d + a) / 2 - 1) * u ^ (-p)) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = u ^ ((d + a) / 2 - 1) * ((2 / r) ^ (-p) * u ^ (-p)) := by ring
      _ ≤ u ^ ((d + a) / 2 - 1) * (1 + r⁻¹ * u) ^ (-p) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
  have := (hlow.const_mul ((2 / r) ^ (-p))⁻¹)
  have hc : (2 / r) ^ (-p) ≠ 0 := by positivity
  simp_rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at this
  have := (integrableOn_Ioi_rpow_iff (s := (-1 : ℝ))
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 r))).1 this
  linarith

/-! ### Symmetries and moments of the standard Student law -/

lemma kernel_isometry (r : ℝ) (U : E d ≃ₗᵢ[ℝ] E d) (y : E d) :
    kernel d r (U y) = kernel d r y := by
  simp [kernel]

lemma stdDensity_isometry (r : ℝ) (U : E d ≃ₗᵢ[ℝ] E d) (y : E d) :
    stdDensity d r (U y) = stdDensity d r y := by
  simp [stdDensity, kernel_isometry]

lemma stdDensity_neg (r : ℝ) (y : E d) : stdDensity d r (-y) = stdDensity d r y := by
  simp [stdDensity, kernel]

/-- The standard Student law is centered. -/
lemma integral_stdDensity_smul (r : ℝ) : ∫ y : E d, stdDensity d r y • y = 0 := by
  have h := integral_neg_eq_self (fun y : E d => stdDensity d r y • y) volume
  simp only [stdDensity_neg, smul_neg, integral_neg] at h
  have : (2 : ℝ) • ∫ y : E d, stdDensity d r y • y = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel _
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

lemma integrable_inner_mul_inner_std (hd : 1 ≤ d) {r : ℝ} (hr : 2 < r) (u v : E d) :
    Integrable (fun y : E d => stdDensity d r y * (⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ)) := by
  have h2 := (integral_sq_norm_mul_stdDensity hd hr).1
  have hr0 : 0 < r := by linarith
  refine (h2.const_mul (‖u‖ * ‖v‖)).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((continuous_stdDensity hr0).mul (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (stdDensity_pos hr0 y)]
    have h1 := abs_real_inner_le_norm y u
    have h2 := abs_real_inner_le_norm y v
    have := stdDensity_pos hr0 y
    calc stdDensity d r y * (|⟪y, u⟫_ℝ| * |⟪y, v⟫_ℝ|)
        ≤ stdDensity d r y * ((‖y‖ * ‖u‖) * (‖y‖ * ‖v‖)) := by gcongr
      _ = ‖u‖ * ‖v‖ * (‖y‖ ^ 2 * stdDensity d r y) := by ring

/-- The quadratic form `u ↦ ∫ ⟪y,u⟫² f_r(y) dy`. -/
noncomputable def quadForm (d : ℕ) (r : ℝ) (u : E d) : ℝ :=
  ∫ y : E d, stdDensity d r y * (⟪y, u⟫_ℝ * ⟪y, u⟫_ℝ)

lemma quadForm_isometry (r : ℝ) (U : E d ≃ₗᵢ[ℝ] E d) (u : E d) :
    quadForm d r (U u) = quadForm d r u := by
  unfold quadForm
  rw [← (U.measurePreserving.integral_comp U.toHomeomorph.measurableEmbedding)]
  congr 1
  ext z
  simp [stdDensity_isometry]

lemma quadForm_eq_of_norm_eq (r : ℝ) {v w : E d} (h : ‖v‖ = ‖w‖) :
    quadForm d r v = quadForm d r w := by
  rw [← Submodule.reflection_sub h, quadForm_isometry]

lemma quadForm_smul (r c : ℝ) (u : E d) : quadForm d r (c • u) = c ^ 2 * quadForm d r u := by
  unfold quadForm
  rw [← integral_const_mul]
  congr 1; ext y
  simp only [inner_smul_right]; ring

lemma quadForm_unit (hd : 1 ≤ d) {r : ℝ} (hr : 2 < r) {e : E d} (he : ‖e‖ = 1) :
    quadForm d r e = r / (r - 2) := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  have hb : ∀ i, quadForm d r (b i) = quadForm d r e := fun i =>
    quadForm_eq_of_norm_eq r (by rw [he]; exact b.orthonormal.1 i)
  have hsum : ∑ i, quadForm d r (b i) = ∫ y : E d, ‖y‖ ^ 2 * stdDensity d r y := by
    unfold quadForm
    rw [← integral_finsetSum _ fun i _ => integrable_inner_mul_inner_std hd hr _ _]
    congr 1; ext y
    rw [← Finset.mul_sum, ← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner y y]
    simp_rw [real_inner_comm (b _) y]; ring
  rw [(integral_sq_norm_mul_stdDensity hd hr).2] at hsum
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have : r - 2 ≠ 0 := by linarith
  field_simp at hsum ⊢
  linarith

lemma quadForm_eq (hd : 1 ≤ d) {r : ℝ} (hr : 2 < r) (u : E d) :
    quadForm d r u = r / (r - 2) * ‖u‖ ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [quadForm]
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have e : u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [e, quadForm_smul, quadForm_unit hd hr, ← e]
  · ring
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

/-- Covariance of the standard Student law: `∫ ⟪y,u⟫⟪y,v⟫ f_r = r/(r-2) ⟪u,v⟫`. -/
lemma integral_inner_mul_inner_std (hd : 1 ≤ d) {r : ℝ} (hr : 2 < r) (u v : E d) :
    ∫ y : E d, stdDensity d r y * (⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ) = r / (r - 2) * ⟪u, v⟫_ℝ := by
  have key : ∀ y : E d, stdDensity d r y * (⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ) =
      (stdDensity d r y * (⟪y, u + v⟫_ℝ * ⟪y, u + v⟫_ℝ) -
        stdDensity d r y * (⟪y, u - v⟫_ℝ * ⟪y, u - v⟫_ℝ)) / 4 := by
    intro y; simp only [inner_add_right, inner_sub_right]; ring
  simp_rw [key]
  rw [integral_div, integral_sub (integrable_inner_mul_inner_std hd hr _ _)
    (integrable_inner_mul_inner_std hd hr _ _)]
  change (quadForm d r (u + v) - quadForm d r (u - v)) / 4 = _
  rw [quadForm_eq hd hr, quadForm_eq hd hr, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_comm u v]
  ring

/-! ### Affine change of variables `x = x₀ + √Σ y` -/

lemma det_toEuclideanCLM (A : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.det ((𝓛 A : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) = A.det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  congr 1
  simp [Matrix.toEuclideanCLM]

variable {S : Matrix (Fin d) (Fin d) ℝ}

lemma sqrt_mul_inv (hS : S.PosDef) : CFC.sqrt S * (CFC.sqrt S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (Elliptic.isUnit_det_sqrt hS)

lemma inv_mul_sqrt (hS : S.PosDef) : (CFC.sqrt S)⁻¹ * CFC.sqrt S = 1 :=
  Matrix.nonsing_inv_mul _ (Elliptic.isUnit_det_sqrt hS)

lemma det_sqrt_pos (hS : S.PosDef) : 0 < (CFC.sqrt S).det := by
  have h0 : 0 ≤ (CFC.sqrt S).det :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).det_nonneg
  exact lt_of_le_of_ne h0 (Elliptic.isUnit_det_sqrt hS).ne_zero.symm

lemma det_sqrt_sq (hS : S.PosDef) : (CFC.sqrt S).det ^ 2 = S.det := by
  rw [sq, ← Matrix.det_mul, Elliptic.sqrt_mul_self_of_posDef hS]

lemma inner_sqrt_inv (hS : S.PosDef) (y : E d) :
    ⟪𝓛 (CFC.sqrt S) y, 𝓛 S⁻¹ (𝓛 (CFC.sqrt S) y)⟫_ℝ = ‖y‖ ^ 2 := by
  rw [Elliptic.inner_toEuclideanCLM_left, Elliptic.star_sqrt, Elliptic.toEuclideanCLM_apply_apply,
    Elliptic.toEuclideanCLM_apply_apply]
  have hS' : S⁻¹ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ := by
    conv_lhs => rw [← Elliptic.sqrt_mul_self_of_posDef hS]
    exact Matrix.mul_inv_rev _ _
  have : CFC.sqrt S * S⁻¹ * CFC.sqrt S = 1 := by
    rw [hS', ← mul_assoc, sqrt_mul_inv hS, one_mul, inv_mul_sqrt hS]
  rw [this, map_one, one_apply_eq_self, real_inner_self_eq_norm_sq]

/-- `√Σ` as a continuous linear equivalence. -/
noncomputable def sqrtEquiv (hS : S.PosDef) : E d ≃L[ℝ] E d :=
  ContinuousLinearEquiv.equivOfInverse (𝓛 (CFC.sqrt S)) (𝓛 (CFC.sqrt S)⁻¹)
    (fun y => by rw [Elliptic.toEuclideanCLM_apply_apply, inv_mul_sqrt hS, map_one]; rfl)
    (fun y => by rw [Elliptic.toEuclideanCLM_apply_apply, sqrt_mul_inv hS, map_one]; rfl)

/-- The affine map `y ↦ x₀ + √Σ y` as a measurable equivalence. -/
noncomputable def affEquiv (x₀ : E d) (hS : S.PosDef) : E d ≃ᵐ E d :=
  ((sqrtEquiv hS).toHomeomorph.trans (Homeomorph.addLeft x₀)).toMeasurableEquiv

@[simp] lemma affEquiv_apply (x₀ : E d) (hS : S.PosDef) (y : E d) :
    affEquiv x₀ hS y = x₀ + 𝓛 (CFC.sqrt S) y := rfl

lemma map_affEquiv (x₀ : E d) (hS : S.PosDef) :
    (volume : Measure (E d)).map (affEquiv x₀ hS) =
      ENNReal.ofReal ((CFC.sqrt S).det)⁻¹ • volume := by
  have hdet : LinearMap.det ((sqrtEquiv hS : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) ≠ 0 := by
    change LinearMap.det ((𝓛 (CFC.sqrt S) : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) ≠ 0
    rw [det_toEuclideanCLM]; exact (det_sqrt_pos hS).ne'
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (E d)) hdet
  have e : (affEquiv x₀ hS : E d → E d) = (fun x => x₀ + x) ∘ (sqrtEquiv hS) := rfl
  rw [e, ← Measure.map_map (measurable_const_add x₀) (sqrtEquiv hS).continuous.measurable]
  change Measure.map (fun x => x₀ + x)
    (Measure.map (((sqrtEquiv hS : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)) volume) = _
  rw [h1, Measure.map_smul, map_add_left_eq_self]
  · congr 2
    change |(LinearMap.det ((𝓛 (CFC.sqrt S) : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d))⁻¹| = _
    rw [det_toEuclideanCLM, abs_of_pos (inv_pos.2 (det_sqrt_pos hS))]
  · exact (measurable_const_add x₀).aemeasurable

lemma lintegral_comp_affEquiv (x₀ : E d) (hS : S.PosDef) (G : E d → ℝ≥0∞) :
    ∫⁻ y, G (x₀ + 𝓛 (CFC.sqrt S) y) =
      ENNReal.ofReal ((CFC.sqrt S).det)⁻¹ * ∫⁻ x, G x := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_affEquiv x₀ hS, lintegral_map_equiv]
  rfl

lemma integral_comp_affEquiv (x₀ : E d) (hS : S.PosDef) (F : E d → ℝ) :
    ∫ y, F (x₀ + 𝓛 (CFC.sqrt S) y) = ((CFC.sqrt S).det)⁻¹ * ∫ x, F x := by
  have h := integral_map_equiv (μ := volume) (affEquiv x₀ hS) F
  rw [map_affEquiv x₀ hS, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.2 (det_sqrt_pos hS)).le, smul_eq_mul] at h
  simp only [affEquiv_apply] at h
  exact h.symm

lemma integral_comp_affEquiv_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x₀ : E d) (hS : S.PosDef) (F : E d → V) :
    ∫ y, F (x₀ + 𝓛 (CFC.sqrt S) y) = ((CFC.sqrt S).det)⁻¹ • ∫ x, F x := by
  have h := integral_map_equiv (μ := volume) (affEquiv x₀ hS) F
  rw [map_affEquiv x₀ hS, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.2 (det_sqrt_pos hS)).le] at h
  simp only [affEquiv_apply] at h
  exact h.symm

lemma integrable_comp_affEquiv_iff (x₀ : E d) (hS : S.PosDef) (F : E d → ℝ) :
    Integrable (fun y => F (x₀ + 𝓛 (CFC.sqrt S) y)) ↔ Integrable F := by
  have h := integrable_map_equiv (μ := volume) (affEquiv x₀ hS) F
  rw [map_affEquiv x₀ hS, integrable_smul_measure (by simpa using det_sqrt_pos hS)
    ENNReal.ofReal_ne_top] at h
  simp only [Function.comp_def, affEquiv_apply] at h
  exact h.symm

/-- The general Student density is an affine image of the standard one. -/
lemma studentDensity_affine (x₀ : E d) (hS : S.PosDef) {r : ℝ} (hr : 0 < r) (y : E d) :
    studentDensity d r x₀ S (x₀ + 𝓛 (CFC.sqrt S) y) =
      ((CFC.sqrt S).det)⁻¹ * stdDensity d r y := by
  have hJ := det_sqrt_pos hS
  unfold studentDensity stdDensity stdConst kernel
  rw [add_sub_cancel_left, inner_sqrt_inv hS, Matrix.det_smul, Fintype.card_fin,
    ← det_sqrt_sq hS, Real.sqrt_mul (by positivity), Real.sqrt_sq hJ.le, Real.sqrt_eq_rpow,
    ← rpow_natCast, ← rpow_mul (by positivity), div_eq_inv_mul (‖y‖ ^ 2) r,
    show (d : ℝ) * (1 / 2) = d / 2 by ring]
  field_simp


lemma integral_mul_studentDensity (x₀ : E d) (hS : S.PosDef) {r : ℝ} (hr : 0 < r)
    (g : E d → ℝ) :
    ∫ x, g x * studentDensity d r x₀ S x =
      ∫ y, g (x₀ + 𝓛 (CFC.sqrt S) y) * stdDensity d r y := by
  have hJ := det_sqrt_pos hS
  have h := integral_comp_affEquiv x₀ hS (fun x => g x * studentDensity d r x₀ S x)
  simp only [studentDensity_affine x₀ hS hr] at h
  simp_rw [mul_left_comm _ ((CFC.sqrt S).det)⁻¹] at h
  rw [integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero hJ.ne') h).symm

lemma integrable_mul_studentDensity_iff (x₀ : E d) (hS : S.PosDef) {r : ℝ} (hr : 0 < r)
    (g : E d → ℝ) :
    Integrable (fun x => g x * studentDensity d r x₀ S x) ↔
      Integrable (fun y => g (x₀ + 𝓛 (CFC.sqrt S) y) * stdDensity d r y) := by
  have hJ := det_sqrt_pos hS
  rw [← integrable_comp_affEquiv_iff x₀ hS]
  simp only [studentDensity_affine x₀ hS hr]
  simp_rw [mul_left_comm _ ((CFC.sqrt S).det)⁻¹]
  exact integrable_const_mul_iff (inv_ne_zero hJ.ne').isUnit _

lemma densityMeasure_studentDensity (x₀ : E d) (hS : S.PosDef) {r : ℝ} (hr : 0 < r) :
    densityMeasure (studentDensity d r x₀ S) =
      (densityMeasure (stdDensity d r)).map (fun y => x₀ + 𝓛 (CFC.sqrt S) y) := by
  have hJ := det_sqrt_pos hS
  ext s hs
  have hm : Measurable (fun y : E d => x₀ + 𝓛 (CFC.sqrt S) y) := (affEquiv x₀ hS).measurable
  rw [Measure.map_apply hm hs, densityMeasure, densityMeasure, withDensity_apply _ hs,
    withDensity_apply _ (hm hs), ← lintegral_indicator hs, ← lintegral_indicator (hm hs)]
  have h := lintegral_comp_affEquiv x₀ hS
    (s.indicator fun x => ENNReal.ofReal (studentDensity d r x₀ S x))
  have e : ∀ y, s.indicator (fun x => ENNReal.ofReal (studentDensity d r x₀ S x))
      (x₀ + 𝓛 (CFC.sqrt S) y) = ENNReal.ofReal ((CFC.sqrt S).det)⁻¹ *
        ((fun y => x₀ + 𝓛 (CFC.sqrt S) y) ⁻¹' s).indicator
          (fun y => ENNReal.ofReal (stdDensity d r y)) y := by
    intro y
    by_cases hy : x₀ + 𝓛 (CFC.sqrt S) y ∈ s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (by exact hy),
        studentDensity_affine x₀ hS hr, ENNReal.ofReal_mul (inv_pos.2 hJ).le]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (by exact hy), mul_zero]
  simp only [e] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact (ENNReal.mul_right_inj (by simpa using hJ) ENNReal.ofReal_ne_top |>.1 h).symm

/-! ### The standard Student law as a Gaussian scale mixture -/

/-- The mixing integrand `γ(z) (z/r)^{d/2} φ(√(z/r) x)`. -/
noncomputable def mixing (d : ℕ) (r : ℝ) (x : E d) (z : ℝ) : ℝ≥0∞ :=
  ProbabilityTheory.gammaPDF (r / 2) (1 / 2) z * ENNReal.ofReal (√(z / r) ^ d) *
    ENNReal.ofReal (gaussDensity d (√(z / r) • x))

lemma mixing_eq_of_pos {r : ℝ} (hr : 0 < r) (x : E d) {z : ℝ} (hz : 0 < z) :
    mixing d r x z = ENNReal.ofReal ((1 / 2) ^ (r / 2) / Gamma (r / 2) *
      ((2 * π) ^ ((d : ℝ) / 2))⁻¹ * (r ^ ((d : ℝ) / 2))⁻¹ *
        (z ^ ((r + d) / 2 - 1) * exp (-((1 + r⁻¹ * ‖x‖ ^ 2) / 2 * z)))) := by
  unfold mixing
  rw [gaussDensity_eq_formula]
  rw [ProbabilityTheory.gammaPDF_of_nonneg hz.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    Real.sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul (by positivity), div_rpow hz.le hr.le,
    show (r + d) / 2 - 1 = (r / 2 - 1) + (d : ℝ) * (1 / 2) by ring, rpow_add hz,
    show -((1 + r⁻¹ * ‖x‖ ^ 2) / 2 * z) = -(1 / 2 * z) + -(1 / 2) * (z / r * ‖x‖ ^ 2) by
      field_simp; ring, exp_add]
  field_simp

lemma lintegral_mixing (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x : E d) :
    ∫⁻ z, mixing d r x z = ENNReal.ofReal (stdDensity d r x) := by
  set c := (1 + r⁻¹ * ‖x‖ ^ 2) / 2 with hc
  have hc0 : 0 < c := by positivity
  set p := (r + d) / 2 with hp
  have hp0 : 0 < p := by positivity
  set C₀ := (1 / 2) ^ (r / 2) / Gamma (r / 2) * ((2 * π) ^ ((d : ℝ) / 2))⁻¹ *
    (r ^ ((d : ℝ) / 2))⁻¹ with hC₀
  set k : ℝ → ℝ := fun z => z ^ (p - 1) * exp (-(c * z)) with hk
  have hkI : ∫ z in Set.Ioi (0 : ℝ), k z = (1 / c) ^ p * Gamma p :=
    integral_rpow_mul_exp_neg_mul_Ioi hp0 hc0
  have hkInt : IntegrableOn k (Set.Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hkI]; have := Gamma_pos_of_pos hp0; positivity)
  set h : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun z => C₀ * k z) with hh
  have hmix : ∀ᵐ z ∂(volume : Measure ℝ), mixing d r x z = ENNReal.ofReal (h z) := by
    have : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [this] with z hz
    rcases lt_or_gt_of_ne hz with hz | hz
    · rw [hh, Set.indicator_of_notMem (by simpa using hz.le), mixing,
        ProbabilityTheory.gammaPDF_of_neg hz]
      simp
    · rw [hh, Set.indicator_of_mem (by exact hz), mixing_eq_of_pos hr x hz]
  rw [lintegral_congr_ae hmix, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [hh, integral_indicator measurableSet_Ioi, integral_const_mul, hkI]
    unfold stdDensity stdConst kernel
    rw [hC₀, show 1 / c = 2 / (1 + r⁻¹ * ‖x‖ ^ 2) by rw [hc]; field_simp,
      div_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 1 + r⁻¹ * ‖x‖ ^ 2),
      one_div (2 : ℝ), inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      mul_rpow (by norm_num) pi_pos.le, mul_rpow hr.le pi_pos.le,
      rpow_neg (by positivity), hp, add_div, rpow_add (by norm_num)]
    have : 0 < Gamma (r / 2) := Gamma_pos_of_pos (by positivity)
    field_simp
  · exact (integrable_indicator_iff measurableSet_Ioi).2 (hkInt.const_mul C₀)
  · refine Eventually.of_forall fun z => ?_
    simp only [hh, Pi.zero_apply]
    by_cases hz : z ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
      have : 0 < Gamma (r / 2) := Gamma_pos_of_pos (by positivity)
      have hz' : 0 < z := hz
      simp only [hC₀, hk]
      positivity
    · rw [Set.indicator_of_notMem hz]

lemma measurable_mixing (r : ℝ) :
    Measurable (Function.uncurry fun (x : E d) (z : ℝ) => mixing d r x z) := by
  change Measurable fun p : E d × ℝ => ProbabilityTheory.gammaPDF (r / 2) (1 / 2) p.2 *
    ENNReal.ofReal (√(p.2 / r) ^ d) * ENNReal.ofReal (gaussDensity d (√(p.2 / r) • p.1))
  have : Measurable (ProbabilityTheory.gammaPDF (r / 2) (1 / 2)) :=
    (ProbabilityTheory.measurable_gammaPDFReal _ _).ennreal_ofReal
  unfold gaussDensity Sphere.gaussProfile
  fun_prop

/-- Inner integral of the mixture after the change of variables `y = √(z/r) x`. -/
lemma lintegral_mixture_inner {r : ℝ} (hr : 0 < r) {B : Set (E d)} {z : ℝ} (hz : 0 < z) :
    ∫⁻ y, B.indicator 1 ((√(z / r))⁻¹ • y) *
        (ENNReal.ofReal (gaussDensity d y) * ProbabilityTheory.gammaPDF (r / 2) (1 / 2) z) =
      ∫⁻ x, B.indicator 1 x * mixing d r x z := by
  set a := √(z / r) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have h := Barenblatt.lintegral_comp_affine (d := d)
    (fun y => B.indicator 1 (a⁻¹ • y) *
      (ENNReal.ofReal (gaussDensity d y) * ProbabilityTheory.gammaPDF (r / 2) (1 / 2) z)) ha0 0
  simp only [add_zero, inv_smul_smul₀ ha0.ne'] at h
  have e : ∀ x, B.indicator 1 x * mixing d r x z = ENNReal.ofReal (a ^ d) *
      (B.indicator 1 x * (ENNReal.ofReal (gaussDensity d (a • x)) *
        ProbabilityTheory.gammaPDF (r / 2) (1 / 2) z)) := by
    intro x; unfold mixing; rw [← ha]; ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_mul]

/-- **The standard Student law.** If `Y ∼ 𝒩(0, I)` and `Z ∼ Gamma(r/2, 1/2)` are independent,
then `Y/√(Z/r)` has density `stdDensity d r`. -/
lemma map_prod_stdGaussian_gamma (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    ((ProbabilityTheory.stdGaussian (E d)).prod
        (ProbabilityTheory.gammaMeasure (r / 2) (1 / 2))).map
        (fun p => (√(p.2 / r))⁻¹ • p.1) = densityMeasure (stdDensity d r) := by
  have hG : Measurable (fun p : E d × ℝ => (√(p.2 / r))⁻¹ • p.1) := by fun_prop
  have hφ : Measurable fun y : E d => ENNReal.ofReal (gaussDensity d y) :=
    continuous_gaussDensity.measurable.ennreal_ofReal
  have hγ : Measurable (ProbabilityTheory.gammaPDF (r / 2) (1 / 2)) :=
    (ProbabilityTheory.measurable_gammaPDFReal _ _).ennreal_ofReal
  ext B hB
  have hGB := hG hB
  rw [Measure.map_apply hG hB, stdGaussian_eq_withDensity, ProbabilityTheory.gammaMeasure,
    prod_withDensity hφ hγ, withDensity_apply _ hGB, ← lintegral_indicator hGB]
  have e1 : ∀ p : E d × ℝ, ((fun p : E d × ℝ => (√(p.2 / r))⁻¹ • p.1) ⁻¹' B).indicator
      (fun p => ENNReal.ofReal (gaussDensity d p.1) * ProbabilityTheory.gammaPDF (r / 2) (1 / 2)
        p.2)
        p = B.indicator 1 ((√(p.2 / r))⁻¹ • p.1) *
          (ENNReal.ofReal (gaussDensity d p.1) * ProbabilityTheory.gammaPDF (r / 2) (1 / 2) p.2)
            := by
    intro p
    by_cases hp : (√(p.2 / r))⁻¹ • p.1 ∈ B
    · rw [Set.indicator_of_mem (by exact hp), Set.indicator_of_mem hp, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem (by exact hp), Set.indicator_of_notMem hp, zero_mul]
  simp_rw [e1]
  rw [lintegral_prod_symm _ (by
    exact ((measurable_one.indicator hB).comp hG).mul ((hφ.comp measurable_fst).mul
      (hγ.comp measurable_snd)) |>.aemeasurable)]
  have e2 : ∀ᵐ z ∂(volume : Measure ℝ), ∫⁻ y, B.indicator 1 ((√(z / r))⁻¹ • y) *
      (ENNReal.ofReal (gaussDensity d y) * ProbabilityTheory.gammaPDF (r / 2) (1 / 2) z) =
        ∫⁻ x, B.indicator 1 x * mixing d r x z := by
    have : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [this] with z hz
    rcases lt_or_gt_of_ne hz with hz | hz
    · simp [mixing, ProbabilityTheory.gammaPDF_of_neg hz]
    · exact lintegral_mixture_inner hr hz
  have hm : Measurable (fun p : ℝ × E d => B.indicator 1 p.2 * mixing d r p.2 p.1) :=
    ((measurable_one.indicator hB).comp measurable_snd).mul
      ((measurable_mixing r).comp measurable_swap)
  rw [lintegral_congr_ae e2, lintegral_lintegral_swap hm.aemeasurable]
  have hfin : ∀ x : E d, B.indicator (1 : E d → ℝ≥0∞) x ≠ ⊤ := fun x => by
    by_cases hx : x ∈ B <;> simp [hx]
  rw [lintegral_congr fun x => by rw [lintegral_const_mul' _ _ (hfin x), lintegral_mixing hd hr],
    densityMeasure, withDensity_apply _ hB, ← lintegral_indicator hB]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ B <;> simp [hx]

lemma integral_smul_studentDensity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x₀ : E d) (hS : S.PosDef) {r : ℝ} (hr : 0 < r) (g : E d → V) :
    ∫ x, studentDensity d r x₀ S x • g x =
      ∫ y, stdDensity d r y • g (x₀ + 𝓛 (CFC.sqrt S) y) := by
  have hJ := det_sqrt_pos hS
  have h := integral_comp_affEquiv_smul x₀ hS (fun x => studentDensity d r x₀ S x • g x)
  simp only [studentDensity_affine x₀ hS hr, mul_smul] at h
  rw [integral_smul] at h
  exact (smul_right_injective V (inv_ne_zero hJ.ne') h).symm

/-- Domination lemma for weighted integrability. -/
lemma integrable_mul_of_le {f g w : E d → ℝ} (hw : Integrable w) (hw0 : ∀ y, 0 ≤ w y)
    (hg : Integrable (fun y => g y * w y)) (hf : AEStronglyMeasurable (fun y => f y * w y))
    {A B : ℝ} (h : ∀ y, |f y| ≤ A * g y + B) : Integrable (fun y => f y * w y) := by
  refine ((hg.const_mul A).add (hw.const_mul B)).mono' hf (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw0 y)]
  calc |f y| * w y ≤ (A * g y + B) * w y := mul_le_mul_of_nonneg_right (h y) (hw0 y)
    _ = A * (g y * w y) + B * w y := by ring

lemma pow_le_of_le {u v A B : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : 0 ≤ v)
    (h : u ≤ A * v + B) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    u ^ k ≤ (2 * A ^ 2 + A) * v ^ k + (2 * B ^ 2 + B) := by
  rcases hk with rfl | rfl
  · nlinarith
  · have : u ^ 2 ≤ (A * v + B) ^ 2 := pow_le_pow_left₀ hu h 2
    nlinarith [sq_nonneg (A * v - B)]

/-- `|x₀ + T y|^k f_r` is integrable iff `|y|^k f_r` is. -/
lemma integrable_norm_affine_pow_iff (hd : 1 ≤ d) (x₀ : E d) (hS : S.PosDef) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k = 1 ∨ k = 2) :
    Integrable (fun y => ‖x₀ + 𝓛 (CFC.sqrt S) y‖ ^ k * stdDensity d r y) ↔
      Integrable (fun y => ‖y‖ ^ k * stdDensity d r y) := by
  have hw := integrable_stdDensity hd hr
  have hw0 : ∀ y, 0 ≤ stdDensity d r y := fun y => (stdDensity_pos hr y).le
  have hc := continuous_stdDensity (d := d) hr
  set L := 𝓛 (CFC.sqrt S)
  set M := 𝓛 (CFC.sqrt S)⁻¹
  have hML : ∀ y, M (L y) = y := fun y => by
    simp only [M, L, Elliptic.toEuclideanCLM_apply_apply, inv_mul_sqrt hS, map_one]; rfl
  constructor
  · intro h
    refine integrable_mul_of_le hw hw0 h (by fun_prop) (A := 2 * ‖M‖ ^ 2 + ‖M‖)
      (B := 2 * ‖M (-x₀)‖ ^ 2 + ‖M (-x₀)‖) fun y => ?_
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_of_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) _ k hk
    have : y = M (x₀ + L y) + M (-x₀) := by rw [← map_add, add_neg_cancel_comm, hML]
    calc ‖y‖ = ‖M (x₀ + L y) + M (-x₀)‖ := by rw [← this]
      _ ≤ ‖M (x₀ + L y)‖ + ‖M (-x₀)‖ := norm_add_le _ _
      _ ≤ ‖M‖ * ‖x₀ + L y‖ + ‖M (-x₀)‖ := by gcongr; exact M.le_opNorm _
  · intro h
    refine integrable_mul_of_le hw hw0 h (by fun_prop) (A := 2 * ‖L‖ ^ 2 + ‖L‖)
      (B := 2 * ‖x₀‖ ^ 2 + ‖x₀‖) fun y => ?_
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_of_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) _ k hk
    calc ‖x₀ + L y‖ ≤ ‖x₀‖ + ‖L y‖ := norm_add_le _ _
      _ ≤ ‖x₀‖ + ‖L‖ * ‖y‖ := by gcongr; exact L.le_opNorm _
      _ = ‖L‖ * ‖y‖ + ‖x₀‖ := by ring

/-- `|y|^k f_r` is integrable iff `k < r`. -/
lemma integrable_norm_pow_mul_stdDensity_iff (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Integrable (fun y : E d => ‖y‖ ^ k * stdDensity d r y) ↔ (k : ℝ) < r := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (fun y : E d => ‖y‖ ^ k * stdDensity d r y) =
      fun y => stdConst d r * (‖y‖ ^ (k : ℝ) * kernel d r y) := by
    ext y; rw [rpow_natCast, stdDensity]; ring
  rw [e, integrable_const_mul_iff (stdConst_pos hr).ne'.isUnit]
  constructor
  · intro h
    by_contra hk
    exact not_integrable_rpow_norm_mul_kernel hd hr (not_lt.1 hk) h
  · intro hk
    exact (integral_rpow_norm_mul_kernel hd hr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      hk).1

end Student

open Student

/-- **Remark 3.2.** The law of `X = x₀ + Y/√(Z/r)`, with `Y ∼ 𝒩(0,Σ)` and `Z ∼ χ²(r) =
Gamma(r/2, 1/2)` independent, is the multivariate Student t-distribution. -/
theorem student_law' {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    ((ProbabilityTheory.multivariateGaussian 0 S).prod
        (ProbabilityTheory.gammaMeasure (r / 2) (1 / 2))).map
        (fun p => x₀ + (√(p.2 / r))⁻¹ • p.1) =
      densityMeasure (studentDensity d r x₀ S) := by
  have hL : Measurable (fun x : E d => 0 + 𝓛 (CFC.sqrt S) x) := by fun_prop
  have hG : Measurable (fun p : E d × ℝ => (√(p.2 / r))⁻¹ • p.1) := by fun_prop
  have hA : Measurable (fun y : E d => x₀ + 𝓛 (CFC.sqrt S) y) := by fun_prop
  have := ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by positivity : 0 < r / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hprod := Measure.map_prod_map (ProbabilityTheory.stdGaussian (E d))
    (ProbabilityTheory.gammaMeasure (r / 2) (1 / 2)) hL measurable_id
  rw [Measure.map_id] at hprod
  rw [densityMeasure_studentDensity x₀ hS hr, ← map_prod_stdGaussian_gamma hd hr,
    Measure.map_map hA hG, ProbabilityTheory.multivariateGaussian, hprod,
    Measure.map_map (by fun_prop) (hL.prodMap measurable_id)]
  congr 1
  ext p : 1
  simp [map_smul]

/-- **Remark 3.2.** The Student t-distribution has a mean iff `r > 1`, equal to `x₀`, and a
covariance iff `r > 2`, equal to `r/(r-2) Σ`. -/
theorem student_moments' {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    (Integrable (fun x => ‖x‖ * studentDensity d r x₀ S x) ↔ 1 < r) ∧
    (1 < r → ∫ x, studentDensity d r x₀ S x • x = x₀) ∧
    (Integrable (fun x => ‖x‖ ^ 2 * studentDensity d r x₀ S x) ↔ 2 < r) ∧
    (2 < r → ∀ u v : E d, ∫ x, studentDensity d r x₀ S x * (⟪x - x₀, u⟫_ℝ * ⟪x - x₀, v⟫_ℝ) =
      r / (r - 2) * ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫_ℝ) := by
  have h1 : Integrable (fun x => ‖x‖ * studentDensity d r x₀ S x) ↔ 1 < r := by
    rw [integrable_mul_studentDensity_iff x₀ hS hr]
    have := integrable_norm_affine_pow_iff hd x₀ hS hr 1 (Or.inl rfl)
    simp only [pow_one] at this
    rw [this]
    simpa using integrable_norm_pow_mul_stdDensity_iff hd hr 1
  have h2 : Integrable (fun x => ‖x‖ ^ 2 * studentDensity d r x₀ S x) ↔ 2 < r := by
    rw [integrable_mul_studentDensity_iff x₀ hS hr (fun x => ‖x‖ ^ 2),
      integrable_norm_affine_pow_iff hd x₀ hS hr 2 (Or.inr rfl)]
    simpa using integrable_norm_pow_mul_stdDensity_iff hd hr 2
  refine ⟨h1, fun hr1 => ?_, h2, fun hr2 u v => ?_⟩
  · have hI : Integrable (fun y : E d => stdDensity d r y • y) := by
      have := (integrable_norm_pow_mul_stdDensity_iff hd hr 1).2 (by simpa using hr1)
      refine this.mono' (by
        exact ((continuous_stdDensity hr).smul continuous_id).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (stdDensity_pos hr y), pow_one, mul_comm]
    rw [integral_smul_studentDensity x₀ hS hr (fun x : E d => x)]
    simp only [smul_add, ← map_smul]
    rw [integral_add ((integrable_stdDensity hd hr).smul_const x₀)
      (by exact (𝓛 (CFC.sqrt S)).integrable_comp hI), integral_smul_const,
      integral_stdDensity hd hr, one_smul, (𝓛 (CFC.sqrt S)).integral_comp_comm hI,
      integral_stdDensity_smul, map_zero, add_zero]
  · have hr0 : 0 < r := hr
    simp_rw [mul_comm (studentDensity d r x₀ S _)]
    rw [integral_mul_studentDensity x₀ hS hr]
    simp only [add_sub_cancel_left, Elliptic.inner_toEuclideanCLM_left, Elliptic.star_sqrt]
    simp_rw [mul_comm _ (stdDensity d r _)]
    rw [integral_inner_mul_inner_std hd hr2, Elliptic.inner_toEuclideanCLM_left,
      Elliptic.star_sqrt, Elliptic.toEuclideanCLM_apply_apply,
      Elliptic.sqrt_mul_self_of_posDef hS]


namespace Student

/-! ### Convergence to the Gaussian as `r → ∞` -/

variable {d : ℕ}

/-- Uniform domination of the Student kernels: for `r + d ≥ 2N ≥ 2`,
`(1 + |y|²/r)^{-(r+d)/2} ≤ (1 + |y|²/(2N))^{-N}`. -/
lemma kernel_le {r N : ℝ} (hr : 0 < r) (hN : 1 ≤ N) (hrN : 2 * N ≤ r + d) (y : E d) :
    kernel d r y ≤ (1 + (2 * N)⁻¹ * ‖y‖ ^ 2) ^ (-N) := by
  unfold kernel
  set t := ‖y‖ ^ 2
  have ht : 0 ≤ t := by positivity
  set s := (r + d) / 2 with hs
  have hsN : 1 ≤ s / N := by rw [le_div_iff₀ (by linarith), hs]; linarith
  have hN0 : 0 < N := by linarith
  have hu : 0 ≤ r⁻¹ * t := by positivity
  have hb := one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ r⁻¹ * t) hsN
  have h1 : 1 + (2 * N)⁻¹ * t ≤ 1 + s / N * (r⁻¹ * t) := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (2 * N)⁻¹ * t ≤ s / N * (r⁻¹ * t) := by
      rw [show s / N * (r⁻¹ * t) = (2 * N)⁻¹ * t * ((r + d) / r) by
        simp only [s]; field_simp]
      exact le_mul_of_one_le_right (by positivity) (by rw [le_div_iff₀ hr]; linarith)
    linarith
  have h2 : (1 + (2 * N)⁻¹ * t) ^ N ≤ (1 + r⁻¹ * t) ^ s := by
    calc (1 + (2 * N)⁻¹ * t) ^ N ≤ ((1 + r⁻¹ * t) ^ (s / N)) ^ N :=
          rpow_le_rpow (by positivity) (h1.trans hb) hN0.le
      _ = (1 + r⁻¹ * t) ^ s := by
          rw [← rpow_mul (by positivity), div_mul_cancel₀ _ hN0.ne']
  rw [rpow_neg (by positivity), rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity) h2

lemma integrable_kernel_bound (hd : 1 ≤ d) :
    Integrable (fun y : E d => (1 + (2 * ((d : ℝ) + 1))⁻¹ * ‖y‖ ^ 2) ^ (-((d : ℝ) + 1))) := by
  have := integrable_rpow_norm_mul_add_sq_rpow_neg (d := d) hd (a := 0) (p := (d : ℝ) + 1)
    (C := 1) (β := (2 * ((d : ℝ) + 1))⁻¹)
    (by simp only [Left.neg_neg_iff, Nat.cast_pos]; omega) (by linarith) one_pos
    (by positivity)
  simpa using this

lemma tendsto_kernel (y : E d) :
    Tendsto (fun r => kernel d r y) atTop (𝓝 (exp (-(1 / 2) * ‖y‖ ^ 2))) := by
  set t := ‖y‖ ^ 2
  have ht : 0 ≤ t := by positivity
  have h1 : Tendsto (fun r : ℝ => ((1 + t / r) ^ r) ^ (-(1 / 2 : ℝ))) atTop
      (𝓝 (exp t ^ (-(1 / 2 : ℝ)))) :=
    (tendsto_one_add_div_rpow_exp t).rpow_const (Or.inl (exp_pos t).ne')
  have h2 : Tendsto (fun r : ℝ => (1 + t / r) ^ (-((d : ℝ) / 2))) atTop
      (𝓝 ((1 + 0) ^ (-((d : ℝ) / 2)))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).rpow_const
      (Or.inl (by norm_num))
  rw [add_zero, one_rpow, ← exp_mul] at *
  have h := h1.mul h2
  rw [mul_one, show t * (-(1 / 2 : ℝ)) = -(1 / 2) * t by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold kernel
  rw [← rpow_mul (by positivity), ← rpow_add (by positivity), div_eq_inv_mul t r]
  congr 1; ring

/-- Dominated convergence for the Student kernels against a bounded continuous weight. -/
lemma tendsto_integral_mul_kernel (hd : 1 ≤ d) {ψ : E d → ℝ} (hψ : Continuous ψ) {C : ℝ}
    (hC : ∀ y, |ψ y| ≤ C) :
    Tendsto (fun r => ∫ y, ψ y * kernel d r y) atTop
      (𝓝 (∫ y, ψ y * exp (-(1 / 2) * ‖y‖ ^ 2))) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => C * (1 + (2 * ((d : ℝ) + 1))⁻¹ * ‖y‖ ^ 2) ^ (-((d : ℝ) + 1))) ?_ ?_
    ((integrable_kernel_bound hd).const_mul C) ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact (hψ.mul (continuous_kernel hr)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (2 * ((d : ℝ) + 1))] with r hr
    refine Eventually.of_forall fun y => ?_
    have hr0 : 0 < r := by linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (kernel_pos r hr0 y)]
    exact mul_le_mul (hC y) (kernel_le hr0 (by linarith) (by linarith) y)
      (kernel_pos r hr0 y).le ((abs_nonneg _).trans (hC y))
  · exact Eventually.of_forall fun y => (tendsto_kernel y).const_mul (ψ y)

lemma integral_gaussian_comp (ψ : E d → ℝ) :
    ∫ y, ψ y ∂(ProbabilityTheory.stdGaussian (E d)) =
      (∫ y, ψ y * exp (-(1 / 2) * ‖y‖ ^ 2)) / ∫ y : E d, exp (-(1 / 2) * ‖y‖ ^ 2) := by
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
      (by exact continuous_gaussDensity.measurable.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_exp_half]
  simp_rw [ENNReal.toReal_ofReal (gaussDensity_pos _).le, smul_eq_mul, gaussDensity_eq_formula]
  rw [eq_div_iff (by positivity), ← integral_mul_const]
  congr 1; ext y; field_simp

end Student

/-- **Remark 3.2.** At fixed `d`, the Student t-distribution tends to `𝒩(x₀, Σ)` as `r → ∞`
(weak convergence: integrals of bounded continuous functions converge). -/
theorem tendsto_student_gaussian' {d : ℕ} (hd : 1 ≤ d) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (φ : E d →ᵇ ℝ) :
    Tendsto (fun r => ∫ x, φ x * studentDensity d r x₀ S x) atTop
      (𝓝 (∫ x, φ x ∂(ProbabilityTheory.multivariateGaussian x₀ S))) := by
  set ψ : E d → ℝ := fun y => φ (x₀ + 𝓛 (CFC.sqrt S) y)
  have hψ : Continuous ψ := φ.continuous.comp (by fun_prop)
  have hC : ∀ y, |ψ y| ≤ ‖φ‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm _
  have hC1 : ∀ y : E d, |(1 : ℝ)| ≤ 1 := fun _ => by simp
  rw [ProbabilityTheory.multivariateGaussian, integral_map (by fun_prop)
    φ.continuous.aestronglyMeasurable, integral_gaussian_comp ψ]
  have hnum := tendsto_integral_mul_kernel hd hψ hC
  have hden := tendsto_integral_mul_kernel hd continuous_const hC1
  simp only [one_mul] at hden
  refine (hnum.div hden (by rw [integral_exp_half]; positivity)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [integral_mul_studentDensity x₀ hS hr]
  unfold stdDensity
  simp_rw [mul_left_comm _ (stdConst d r)]
  rw [integral_const_mul, stdConst_mul_integral_kernel hd hr, inv_mul_eq_div]
  rfl


namespace Student

/-! ### The Fisher–Snedecor distribution and rotation invariance -/

variable {d : ℕ}

/-- Pointwise identity between the radial profile of the Student density and the
Fisher–Snedecor density. -/
lemma fisher_pointwise (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) {v : ℝ} (hv : 0 < v) :
    π ^ ((d : ℝ) / 2) / Gamma (d / 2) * (d * ((d * v) ^ (((d : ℝ) + 0) / 2 - 1) *
      (stdConst d r * (1 + r⁻¹ * (d * v)) ^ (-((r + d) / 2))))) =
      fisherSnedecorDensity d r v := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold fisherSnedecorDensity stdConst
  simp only [hv, ↓reduceIte]
  rw [add_zero, mul_rpow hd0.le hv.le, mul_rpow hr.le pi_pos.le,
    div_rpow hd0.le hr.le, add_comm (d : ℝ) r, show r⁻¹ * (d * v) = d / r * v by ring]
  have h1 : (d : ℝ) * d ^ ((d : ℝ) / 2 - 1) = d ^ ((d : ℝ) / 2) := by
    rw [← rpow_one_add' hd0.le (by intro h; linarith)]; ring_nf
  have : 0 < Gamma ((d : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have : 0 < Gamma (r / 2) := Gamma_pos_of_pos (by positivity)
  have : 0 < Gamma ((r + d) / 2) := Gamma_pos_of_pos (by positivity)
  rw [← h1]
  field_simp

/-- The image of the standard Student law under `y ↦ |y|²/d` is `F(d, r)`. -/
lemma map_stdDensity_fisher (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    (densityMeasure (stdDensity d r)).map (fun y : E d => ‖y‖ ^ 2 / d) =
      volume.withDensity (fun v => ENNReal.ofReal (fisherSnedecorDensity d r v)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hQ : Measurable (fun y : E d => ‖y‖ ^ 2 / d) := by fun_prop
  ext B hB
  set F : ℝ → ℝ := fun u => B.indicator 1 (u / d) * (stdConst d r * (1 + r⁻¹ * u) ^ (-((r + d) /
    2)))
    with hF
  have hF0 : ∀ u, 0 ≤ u → 0 ≤ F u := fun u hu0 => by
    have h1 : 0 ≤ stdConst d r * (1 + r⁻¹ * u) ^ (-((r + d) / 2)) :=
      mul_nonneg (stdConst_pos hr).le (rpow_nonneg (by positivity) _)
    by_cases hu : u / d ∈ B <;> simp [hF, hu, h1]
  -- the integrand on `ℝᵈ`
  have hFi : Integrable (fun y : E d => ‖y‖ ^ (0 : ℝ) * F (‖y‖ ^ 2)) := by
    refine (integrable_stdDensity hd hr).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((((measurable_one.indicator hB).comp hQ).mul
        (continuous_stdDensity hr).measurable)).aestronglyMeasurable.congr
        (Eventually.of_forall fun y => by simp [hF, stdDensity, kernel])
    · rw [rpow_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg (hF0 _ (by positivity))]
      have := stdDensity_pos hr y
      by_cases hu : ‖y‖ ^ 2 / d ∈ B
      · simp [hF, hu, stdDensity, kernel]
      · simpa [hF, hu, stdDensity, kernel] using this.le
  have hrad := Radial.radial hd F 0
  -- integrability on the half-line
  have hIoi := hrad.1.1 hFi
  rw [Radial.integrableOn_Ioi_scale_iff _ hd0] at hIoi
  have hfisher_on : IntegrableOn (fun v => B.indicator 1 v * fisherSnedecorDensity d r v)
      (Set.Ioi 0) := by
    refine (hIoi.const_mul (π ^ ((d : ℝ) / 2) / Gamma (d / 2) * d)).congr
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
    dsimp only
    rw [← fisher_pointwise hd hr hv]
    simp only [hF, mul_div_cancel_left₀ v hd0.ne']
    ring
  have hfisher : Integrable (fun v => B.indicator 1 v * fisherSnedecorDensity d r v) :=
    hfisher_on.integrable_of_forall_notMem_eq_zero fun v hv => by
      simp only [Set.mem_Ioi, not_lt] at hv
      simp [fisherSnedecorDensity, not_lt.2 hv]
  rw [Measure.map_apply hQ hB, densityMeasure, withDensity_apply _ (hQ hB),
    withDensity_apply _ hB, ← lintegral_indicator (hQ hB), ← lintegral_indicator hB]
  have e1 : ∀ y : E d, ((fun y : E d => ‖y‖ ^ 2 / d) ⁻¹' B).indicator
      (fun y => ENNReal.ofReal (stdDensity d r y)) y =
        ENNReal.ofReal (‖y‖ ^ (0 : ℝ) * F (‖y‖ ^ 2)) := by
    intro y
    by_cases hu : ‖y‖ ^ 2 / d ∈ B
    · rw [Set.indicator_of_mem (by exact hu)]; simp [hF, hu, stdDensity, kernel]
    · rw [Set.indicator_of_notMem (by exact hu)]; simp [hF, hu]
  have e2 : ∀ v : ℝ, B.indicator (fun v => ENNReal.ofReal (fisherSnedecorDensity d r v)) v =
      ENNReal.ofReal (B.indicator 1 v * fisherSnedecorDensity d r v) := by
    intro v
    by_cases hv : v ∈ B <;> simp [hv]
  simp_rw [e1, e2]
  have hfisher0 : ∀ v, 0 ≤ B.indicator 1 v * fisherSnedecorDensity d r v := fun v => by
    by_cases hv : v ∈ B
    · simp only [Set.indicator_of_mem hv, Pi.one_apply, one_mul]
      unfold fisherSnedecorDensity
      split_ifs with h
      · have : 0 < Gamma ((d : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
        have : 0 < Gamma (r / 2) := Gamma_pos_of_pos (by positivity)
        have : 0 < Gamma ((d + r) / 2) := Gamma_pos_of_pos (by positivity)
        positivity
      · exact le_rfl
    · simp [hv]
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall fun y => by
      simp only [Pi.zero_apply, rpow_zero, one_mul]; exact hF0 _ (by positivity)),
    ← ofReal_integral_eq_lintegral_ofReal hfisher (Eventually.of_forall hfisher0), hrad.2,
    Radial.integral_Ioi_scale _ hd0, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Set.Ioi 0) (f := fun v => B.indicator 1 v * fisherSnedecorDensity d r v)
      (fun v hv => by
        simp only [Set.mem_Ioi, not_lt] at hv
        simp [fisherSnedecorDensity, not_lt.2 hv]), ← integral_const_mul, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [← fisher_pointwise hd hr hv]
  simp only [hF, mul_div_cancel_left₀ v hd0.ne']
  ring

lemma inv_smul_one {σ2 : ℝ} (hσ : 0 < σ2) :
    (σ2 • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = σ2⁻¹ • 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hσ.ne', one_smul]

lemma inner_smul_one_inv {σ2 : ℝ} (hσ : 0 < σ2) (z : E d) :
    ⟪z, 𝓛 (σ2 • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ z⟫_ℝ = σ2⁻¹ * ‖z‖ ^ 2 := by
  rw [inv_smul_one hσ, map_smul, map_one, smul_apply, one_apply_eq_self,
    real_inner_smul_right, real_inner_self_eq_norm_sq]

end Student

/-- **Remark 3.2.** If `X` follows the Student t-distribution, then `(X-x₀)ᵀΣ⁻¹(X-x₀)/d` follows
the Fisher–Snedecor distribution `F(d, r)` (in the isotropic case `Σ = I`: `|X-x₀|²/d`); the law
of the Student t-distribution with `Σ = σ²I` is rotationally invariant around `x₀`. -/
theorem student_fisherSnedecor' {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    (densityMeasure (studentDensity d r x₀ S)).map
        (fun x => ⟪x - x₀, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ (x - x₀)⟫_ℝ / d) =
      volume.withDensity (fun y => ENNReal.ofReal (fisherSnedecorDensity d r y)) ∧
    ∀ σ2 : ℝ, 0 < σ2 → ∀ U : E d ≃ₗᵢ[ℝ] E d, ∀ x,
      studentDensity d r x₀ (σ2 • 1) (x₀ + U (x - x₀)) = studentDensity d r x₀ (σ2 • 1) x := by
  refine ⟨?_, fun σ2 hσ U x => ?_⟩
  · rw [densityMeasure_studentDensity x₀ hS hr, Measure.map_map (by fun_prop) (by fun_prop),
      ← map_stdDensity_fisher hd hr]
    congr 1
    ext y
    simp [inner_sqrt_inv hS]
  · unfold studentDensity
    rw [add_sub_cancel_left, inner_smul_one_inv hσ, inner_smul_one_inv hσ,
      LinearIsometryEquiv.norm_map]


namespace Student

/-! ### Isotropic Student densities and Barenblatt profiles -/

variable {d : ℕ}

lemma posDef_smul_one {σ2 : ℝ} (hσ : 0 < σ2) : (σ2 • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
  Matrix.PosDef.one.smul hσ

/-- The isotropic Student density `C σ^{-d} (1 + |x|²/(rσ²))^{-(r+d)/2}`. -/
lemma studentDensity_iso {r σ2 : ℝ} (hr : 0 < r) (hσ : 0 < σ2) (x : E d) :
    studentDensity d r 0 (σ2 • 1) x =
      stdConst d r / σ2 ^ ((d : ℝ) / 2) * (1 + (r * σ2)⁻¹ * ‖x‖ ^ 2) ^ (-((r + d) / 2)) := by
  unfold studentDensity stdConst
  rw [sub_zero, inner_smul_one_inv hσ, smul_smul, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin, Real.sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul (by positivity),
    mul_rpow (by positivity) hσ.le, show (d : ℝ) * (1 / 2) = d / 2 by ring]
  field_simp

lemma integral_studentDensity (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) : ∫ x, studentDensity d r x₀ S x = 1 := by
  have := integral_mul_studentDensity x₀ hS hr (fun _ => 1)
  simp only [one_mul] at this
  rw [this, integral_stdDensity hd hr]

/-- A normalized profile `(c + b|x|²)^{-(r+d)/2}` is an isotropic Student density. -/
lemma exists_student_of_full (hd : 1 ≤ d) {r b c : ℝ} (hr : 0 < r) (hb : 0 < b) (hc : 0 < c)
    (hint : ∫ x : E d, (c + b * ‖x‖ ^ 2) ^ (-((r + d) / 2)) = 1) :
    ∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x : E d, (c + b * ‖x‖ ^ 2) ^ (-((r + d) / 2)) =
      studentDensity d r 0 (σ2 • 1) x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set p := (r + d) / 2 with hp
  have hA := stdConst_pos (d := d) hr
  set σ2 := (stdConst d r * c ^ p) ^ (2 / (d : ℝ)) with hσ2
  have hσ : 0 < σ2 := by positivity
  have hσd : σ2 ^ ((d : ℝ) / 2) = stdConst d r * c ^ p := by
    rw [hσ2, ← rpow_mul (by positivity), show 2 / (d : ℝ) * (d / 2) = 1 by field_simp, rpow_one]
  set b' := c / (r * σ2) with hb'
  have hb'0 : 0 < b' := by positivity
  have hstud : ∀ x : E d, studentDensity d r 0 (σ2 • 1) x = (c + b' * ‖x‖ ^ 2) ^ (-p) := by
    intro x
    rw [studentDensity_iso hr hσ, hσd, show c + b' * ‖x‖ ^ 2 = c * (1 + (r * σ2)⁻¹ * ‖x‖ ^ 2) by
      rw [hb']; field_simp, mul_rpow hc.le (by positivity), rpow_neg hc.le, hp]
    field_simp
  have hint' : ∫ x : E d, (c + b' * ‖x‖ ^ 2) ^ (-p) = 1 := by
    simp_rw [← hstud]; exact integral_studentDensity hd hr 0 (posDef_smul_one hσ)
  have hpd : (d : ℝ) / 2 < p := by rw [hp]; linarith
  have hbb : b = b' := by
    rw [← hint', Barenblatt.integral_full hd hpd hb hc, Barenblatt.integral_full hd hpd hb'0 hc]
      at hint
    have hG : 0 < π ^ ((d : ℝ) / 2) * Gamma (d / 2) * Gamma (p - d / 2) /
        (Gamma (d / 2) * Gamma p) := by
      have := Gamma_pos_of_pos (show (0 : ℝ) < d / 2 by positivity)
      have := Gamma_pos_of_pos (show (0 : ℝ) < p - d / 2 by linarith)
      have := Gamma_pos_of_pos (show (0 : ℝ) < p by linarith)
      positivity
    have h1 := mul_left_cancel₀ (by positivity : c ^ ((d : ℝ) / 2 - p) ≠ 0) hint
    have h2 := mul_right_cancel₀ hG.ne' h1
    exact Barenblatt.rpow_inj hb.le hb'0.le (by simp [hd0.ne']) h2
  exact ⟨σ2, hσ, fun x => by rw [hstud, hbb]⟩

/-- Second moment of the isotropic Student density with `x₀ = 0`. -/
lemma integral_sq_norm_mul_studentDensity_iso (hd : 1 ≤ d) {r σ2 : ℝ} (hr : 2 < r)
    (hσ : 0 < σ2) :
    ∫ x : E d, ‖x‖ ^ 2 * studentDensity d r 0 (σ2 • 1) x = d * r / (r - 2) * σ2 := by
  have hr0 : 0 < r := by linarith
  set a := √σ2 with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 hσ
  have hσa : σ2 = a ^ 2 := (Real.sq_sqrt hσ.le).symm
  have h := Barenblatt.integral_comp_affine (d := d)
    (fun x => ‖x‖ ^ 2 * studentDensity d r 0 (σ2 • 1) x) ha0 0
  have had : σ2 ^ ((d : ℝ) / 2) = a ^ d := by
    rw [hσa, ← rpow_natCast a 2, ← rpow_mul ha0.le,
      show ((2 : ℕ) : ℝ) * (d / 2) = d by push_cast; ring, rpow_natCast]
  have e : ∀ y : E d, ‖a • y + 0‖ ^ 2 * studentDensity d r 0 (σ2 • 1) (a • y + 0) =
      a ^ 2 * (a ^ d)⁻¹ * (‖y‖ ^ 2 * stdDensity d r y) := by
    intro y
    rw [add_zero, studentDensity_iso hr0 hσ, had, norm_smul, Real.norm_eq_abs, abs_of_pos ha0,
      hσa, mul_pow]
    unfold stdDensity kernel
    rw [show (r * a ^ 2)⁻¹ * (a ^ 2 * ‖y‖ ^ 2) = r⁻¹ * ‖y‖ ^ 2 by field_simp]
    field_simp
  simp_rw [e] at h
  rw [integral_const_mul, (integral_sq_norm_mul_stdDensity hd hr).2] at h
  have hne : (a ^ d)⁻¹ ≠ 0 := by positivity
  have h' := mul_left_cancel₀ hne (h.symm.trans (by ring :
    a ^ 2 * (a ^ d)⁻¹ * (d * r / (r - 2)) = (a ^ d)⁻¹ * (a ^ 2 * (d * r / (r - 2)))))
  rw [h', hσa]; ring

end Student

/-- **Remark 3.2** (with a real scale `σ²`). In the fast diffusion case, the Barenblatt profile
and the equilibrium are isotropic Student t-densities with `r = 1/(α(1-m))` degrees of freedom. -/
theorem Student.barenblatt_eq_student {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m < 1)
    (hmd : ((d : ℝ) - 2) / d < m) :
    (∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x, barenblatt d m x =
      studentDensity d (1 / (alpha d m * (1 - m))) 0 (σ2 • 1) x) ∧
    ∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x, equilibrium d m x =
      studentDensity d (1 / (alpha d m * (1 - m))) 0 (σ2 • 1) x := by
  have h : Admissible d m := ⟨hd, hm0, hm1.ne, hmd⟩
  have hα := alpha_pos h
  have h1m : 0 < 1 - m := by linarith
  have hr : 0 < 1 / (alpha d m * (1 - m)) := by positivity
  have hp : (1 / (alpha d m * (1 - m)) + d) / 2 = 1 / (1 - m) := by
    have := Barenblatt.alpha_mul h
    field_simp
    linear_combination -this
  obtain ⟨hc, -, hint, -⟩ := barenblattConst_spec' hd hm0 hm1.ne hmd
  have hκ : 0 < alpha d m * (1 - m) / (2 * m) := by positivity
  refine ⟨?_, ?_⟩
  · have hB : ∀ x : E d, barenblatt d m x = (barenblattConst d m +
        alpha d m * (1 - m) / (2 * m) * ‖x‖ ^ 2) ^ (-((1 / (alpha d m * (1 - m)) + d) / 2)) := by
      intro x
      rw [hp]; exact Barenblatt.max_rpow_eq_full hc.le hκ.le x
    obtain ⟨σ2, hσ, hσ'⟩ := Student.exists_student_of_full hd hr hκ hc (by
      simp_rw [← hB]; exact hint)
    exact ⟨σ2, hσ, fun x => by rw [hB, hσ']⟩
  · have hpd : (d : ℝ) / 2 < 1 / (1 - m) := Barenblatt.half_lt_p_full h hm1
    have hb : 0 < (1 - m) / (2 * m) := by positivity
    have hE : ∀ x : E d, equilibrium d m x = (fullBarenblattConst d (1 / (1 - m))
        ((1 - m) / (2 * m)) + (1 - m) / (2 * m) * ‖x‖ ^ 2) ^
          (-((1 / (alpha d m * (1 - m)) + d) / 2)) := by
      intro x
      rw [hp, equilibrium_eq_fullBarenblatt h hm1]; rfl
    obtain ⟨σ2, hσ, hσ'⟩ := Student.exists_student_of_full hd hr hb
      (fullBarenblattConst_pos hpd hb) (by simp_rw [← hE]; exact integral_equilibrium h)
    exact ⟨σ2, hσ, fun x => by rw [hE, hσ']⟩

/-- **Remark 3.2.** In the fast diffusion case, the Barenblatt profile and the equilibrium are
isotropic Student t-densities with `r = 1/(α(1-m))` degrees of freedom. -/
theorem barenblatt_eq_student' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m < 1)
    (hmd : ((d : ℝ) - 2) / d < m) :
    (∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x, barenblatt d m x =
      studentDensity d (1 / (alpha d m * (1 - m))) 0 (σ2 • 1) x) ∧
    ∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x, equilibrium d m x =
      studentDensity d (1 / (alpha d m * (1 - m))) 0 (σ2 • 1) x :=
  Student.barenblatt_eq_student hd hm0 hm1 hmd


namespace Student

lemma admissible_dMinusOne {d : ℕ} (hd : 2 ≤ d) :
    Admissible d (((d : ℝ) - 1) / d) ∧ ((d : ℝ) - 1) / d < 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  refine ⟨⟨by omega, div_pos (by linarith) hd0, ?_, ?_⟩, ?_⟩
  · rw [Ne, div_eq_one_iff_eq hd0.ne']; linarith
  · exact div_lt_div_of_pos_right (by linarith) hd0
  · rw [div_lt_one hd0]; linarith

lemma alpha_dMinusOne {d : ℕ} (hd : 1 ≤ d) : alpha d (((d : ℝ) - 1) / d) = 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold alpha
  rw [show (2 : ℝ) - d * (1 - (d - 1) / d) = 1 by field_simp; ring, div_one]

lemma equilibrium_dMinusOne {d : ℕ} (hd : 1 ≤ d) (x : E d) :
    equilibrium d (((d : ℝ) - 1) / d) x = barenblatt d (((d : ℝ) - 1) / d) x := by
  unfold equilibrium
  rw [alpha_dMinusOne hd]
  simp

lemma tendsto_eqSecondMoment_dMinusOne :
    Tendsto (fun d : ℕ => eqSecondMoment d (((d : ℝ) - 1) / d) / d) atTop
      (𝓝 (2 * π * exp 1)) := by
  have h := (fullBarenblatt_asymptotics' (α := 1) (by norm_num)).1
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hadm, hm⟩ := admissible_dMinusOne hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
  have e1 : 1 / (1 - ((d : ℝ) - 1) / d) = d := by field_simp; ring
  have e2 : (1 - ((d : ℝ) - 1) / d) / (2 * (((d : ℝ) - 1) / d)) = ((d : ℝ) - 2 + 1)⁻¹ * (1 / 2)
    := by
    rw [show (d : ℝ) - 2 + 1 = d - 1 by ring]; field_simp; ring
  unfold eqSecondMoment
  rw [equilibrium_eq_fullBarenblatt hadm hm, e1, e2]

end Student

/-- **Remark 3.2.** For `m = (d-1)/d` (`α = 1`), `B = v_∞` is the isotropic Student
t-density with `r = d` degrees of freedom and scale `σ_d² I`, where `σ_d² → 2πe`. -/
theorem barenblatt_student_dMinusOne' :
    ∃ σ2 : ℕ → ℝ, (∀ᶠ d : ℕ in atTop, 0 < σ2 d ∧ ∀ x : E d,
        barenblatt d ((d - 1) / d) x = studentDensity d d 0 (σ2 d • 1) x ∧
        equilibrium d ((d - 1) / d) x = studentDensity d d 0 (σ2 d • 1) x) ∧
      Tendsto σ2 atTop (𝓝 (2 * π * exp 1)) := by
  refine ⟨fun d => eqSecondMoment d (((d : ℝ) - 1) / d) / d * (((d : ℝ) - 2) / d), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 3] with d hd
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hd1 : 1 ≤ d := by omega
    obtain ⟨hadm, hm⟩ := Student.admissible_dMinusOne (by omega : 2 ≤ d)
    have hr : 1 / (alpha d (((d : ℝ) - 1) / d) * (1 - ((d : ℝ) - 1) / d)) = d := by
      rw [Student.alpha_dMinusOne hd1]; field_simp; ring
    obtain ⟨⟨σ', hσ', hB⟩, -⟩ := Student.barenblatt_eq_student hd1 hadm.2.1 hm hadm.2.2.2
    rw [hr] at hB
    have hM : eqSecondMoment d (((d : ℝ) - 1) / d) = d * d / (d - 2) * σ' := by
      unfold eqSecondMoment
      simp_rw [Student.equilibrium_dMinusOne hd1, hB]
      exact Student.integral_sq_norm_mul_studentDensity_iso hd1 (by linarith) hσ'
    have hσ : eqSecondMoment d (((d : ℝ) - 1) / d) / d * (((d : ℝ) - 2) / d) = σ' := by
      have : (d : ℝ) - 2 ≠ 0 := by linarith
      rw [hM]; field_simp
    simp only [hσ]
    exact ⟨hσ', fun x => ⟨hB x, by rw [Student.equilibrium_dMinusOne hd1, hB x]⟩⟩
  · have h2 : Tendsto (fun d : ℕ => ((d : ℝ) - 2) / d) atTop (𝓝 1) := by
      have : Tendsto (fun d : ℕ => 1 - 2 / (d : ℝ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with d hd
      have : (0 : ℝ) < d := by exact_mod_cast hd
      field_simp
    simpa using Student.tendsto_eqSecondMoment_dMinusOne.mul h2

/-- **Remark 3.2.** The law of `X = x₀ + Y/√(Z/r)`, with `Y ∼ 𝒩(0,Σ)` and `Z ∼ χ²(r) =
Gamma(r/2, 1/2)` independent, is the multivariate Student t-distribution. -/
alias student_law := student_law'

/-- **Remark 3.2.** The Student t-distribution has a mean iff `r > 1`, equal to `x₀`, and a
covariance iff `r > 2`, equal to `r/(r-2) Σ`. -/
alias student_moments := student_moments'

/-- **Remark 3.2.** At fixed `d`, the Student t-distribution tends to `𝒩(x₀, Σ)` as `r → ∞`
(weak convergence: integrals of bounded continuous functions converge). -/
alias tendsto_student_gaussian := tendsto_student_gaussian'

/-- **Remark 3.2.** If `X` follows the Student t-distribution, then `(X-x₀)ᵀΣ⁻¹(X-x₀)/d` follows
the Fisher–Snedecor distribution `F(d, r)` (in the isotropic case `Σ = I`: `|X-x₀|²/d`); the law
of the Student t-distribution with `Σ = σ²I` is rotationally invariant around `x₀`. -/
alias student_fisherSnedecor := student_fisherSnedecor'

/-- **Remark 3.2.** In the fast diffusion case, the Barenblatt profile and the equilibrium are
isotropic Student t-densities with `r = 1/(α(1-m))` degrees of freedom. -/
alias barenblatt_eq_student := barenblatt_eq_student'

/-- **Remark 3.2.** For `m = (d-1)/d` (`α = 1`), `B = v_∞` is the isotropic Student
t-density with `r = d` degrees of freedom and scale `σ_d² I`, where `σ_d² → 2πe`. -/
alias barenblatt_student_dMinusOne := barenblatt_student_dMinusOne'

end Cutfast
