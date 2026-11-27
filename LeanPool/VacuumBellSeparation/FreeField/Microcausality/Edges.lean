/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Strip
public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Decay
public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Algebra

/-!
# Microcausality, stages F and G: continuity at the edges of the strip, and locality

Stages F (continuity at the edges) and G (conclusion) of the microcausality proof.  Notation as
in `FreeField/Microcausality/Phase.lean`:
`ψ = boostPhase m`, `Φ = boostPhaseIntegral m F G`, `ω = ω_m(𝐩)`,
`dν(𝐩) = d³p / (2(2π)³ ω_m(𝐩))`, and `𝒢(ζ) = ∫ Φ(𝐩, ζ) dν(𝐩)`.  The test functions `F`, `G`
are supported in the unit double cones at the origin and at `s 𝐞₁`, `s ≥ 2` (`s > 2` for G).

* `boostPhaseCLM m ζ 𝐩`: the phase `w ↦ ψ(ζ, 𝐩, w)` as a continuous real-linear map
  `Spacetime →L[ℝ] ℂ` (`boostPhaseCLM_apply`);
  `sum_norm_sq_boostPhaseCLM_coordDir`: on the imaginary axis `ζ = iθ`, the coefficients
  `c_j = ψ(iθ, 𝐩, e_j)` satisfy `∑_j |c_j|² = ω² + |𝐩|²`;
  `im_boostPhaseCLM_nonneg`: `Im ψ(iθ, 𝐩, y - x) ≥ 0` for `θ ∈ [0, π]` on the supports.
* `norm_boostPhaseIntegral_mul_I_le` (uniform decay): for `θ ∈ [0, π]`, `m ≠ 0`,
  `|Φ(𝐩, iθ)| ≤ (2/ω)³ ‖F‖₁ max_j ‖∂_{e_j}³ G‖₁` (the bound of
  `Microcausality/Decay.lean` with `N = 3`, `K = ω`).
* `integrable_inv_dispersion_pow_four`: `ω_m(𝐩)⁻⁴` is integrable on `ℝ³` for `m ≠ 0`;
  `norm_boostPhaseIntegral_mul_weight_le`: the resulting integrable majorant of the integrand of
  `𝒢(iθ)`, uniform in `θ ∈ [0, π]`.
* `continuous_boostPhaseIntegral_mul_I`, `continuousOn_boostPhaseIntegral_mul_I`: `Φ(𝐩, iθ)` is
  continuous in `𝐩` (for `θ ∈ [0, π]`) and in `θ ∈ [0, π]` (dominated by `|F(x)| |G(y)|`);
  `continuousOn_integral_boostPhaseIntegral_mul_I`: `θ ↦ 𝒢(iθ)` is continuous on `[0, π]` for
  `m > 0` (dominated convergence), the hypothesis of `im_oneParticleInner_eq_zero_of_continuousOn`
  (`Microcausality/Strip.lean`, stage E: `𝒢` is constant on the open strip).
* `im_oneParticleInner_eq_zero_of_doubleCone` (G): `Im ⟨κ_m F, κ_m G⟩ = 0` for `m > 0`, `s > 2`;
  `locality : Locality` (via `locality_of_im_eq_zero`,
  `Microcausality/Algebra.lean`): the local algebras of the unit double cones at the origin and
  at `s 𝐞₁`, `s > 2`, commute, for every mass `μ > 0` and every vacuum system.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-! ### The phase as a real-linear map of the spacetime point -/

/-- For fixed rapidity `ζ` and momentum `𝐩`, the phase `w ↦ ψ_m(ζ, 𝐩, w)` is real-linear in the
spacetime point `w`. -/
noncomputable def boostPhaseLinearMap (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    Spacetime →ₗ[ℝ] ℂ where
  toFun := boostPhase m ζ p
  map_add' v w := by
    simp only [boostPhase, Prod.fst_add, Prod.snd_add, inner_add_right, Complex.ofReal_add]
    ring
  map_smul' a w := by
    simp only [boostPhase, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right,
      Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul]
    ring

/-- The phase `w ↦ ψ_m(ζ, 𝐩, w)` as a continuous real-linear map `c_{ζ,𝐩} : Spacetime →L[ℝ] ℂ`
(spacetime is finite-dimensional). -/
noncomputable def boostPhaseCLM (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    Spacetime →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (boostPhaseLinearMap m ζ p)

/-- `c_{ζ,𝐩}(w) = ψ_m(ζ, 𝐩, w)`. -/
theorem boostPhaseCLM_apply (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    boostPhaseCLM m ζ p w = boostPhase m ζ p w :=
  rfl

/-- **The coefficients of the phase on the imaginary axis**: for `c = c_{iθ,𝐩}`,
`∑_j |c(e_j)|² = ω_m(𝐩)² + |𝐩|²`, with `c(e₀) = ω cos θ - i p₁ sin θ`,
`c(e₁) = -p₁ cos θ + i ω sin θ`, `c(e₂) = -p₂`, `c(e₃) = -p₃`. -/
theorem sum_norm_sq_boostPhaseCLM_coordDir (m θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ∑ j : Fin 4, ‖boostPhaseCLM m ((θ : ℂ) * Complex.I) p (coordDir j)‖ ^ 2 =
      dispersion m p ^ 2 + ‖p‖ ^ 2 := by
  have h0 : ⟪e₁, p⟫_ℝ = p 0 := by
    rw [real_inner_comm]
    exact inner_euclideanSingle_one p 0
  have e0 : e₁ 0 = 1 := by simp [e₁]
  have e1 : e₁ 1 = 0 := by simp [e₁]
  have e2 : e₁ 2 = 0 := by simp [e₁]
  rw [sum_norm_sq_coordDir, Fin.sum_univ_three, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three]
  simp only [boostPhaseCLM_apply, boostPhase_ofReal_mul_I, Complex.sq_norm,
    Complex.normSq_add_mul_I, inner_zero_right, inner_euclideanSingle_one, h0, e0, e1, e2]
  linear_combination (dispersion m p ^ 2 + p 0 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- **Positivity on the supports**: for `θ ∈ [0, π]`, `F` supported in the unit double cone at
the origin and `G` in the unit double cone at `s 𝐞₁`, `s ≥ 2`, `Im c_{iθ,𝐩}(y - x) ≥ 0` for
`x ∈ tsupport F`, `y ∈ tsupport G`. -/
theorem im_boostPhaseCLM_nonneg {m s θ : ℝ} (hs : 2 ≤ s) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (p : EuclideanSpace ℝ (Fin 3)) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) :
    ∀ x ∈ tsupport F.1, ∀ y ∈ tsupport G.1,
      0 ≤ (boostPhaseCLM m ((θ : ℂ) * Complex.I) p (y - x)).im := by
  intro x hx y hy
  have h := boostPhase_im_nonneg m 0 θ p (y - x) hθ₀ hθπ
    (abs_fst_sub_le_of_mem_doubleCone hs (hF hx) (hG hy))
  rw [Complex.ofReal_zero, zero_add] at h
  rw [boostPhaseCLM_apply]
  exact h

/-! ### Uniform decay in the momentum -/

/-- **Uniform decay of `Φ` on the closed strip**: for `m ≠ 0`, `θ ∈ [0, π]` and test functions
supported in the two unit double cones (`s ≥ 2`),
`|Φ(𝐩, iθ)| ≤ (2/ω_m(𝐩))³ ‖F‖₁ max_j ‖∂_{e_j}³ G‖₁`. -/
theorem norm_boostPhaseIntegral_mul_I_le {m s θ : ℝ} (hm : m ≠ 0) (hs : 2 ≤ s) (hθ₀ : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I)‖ ≤
      (2 / dispersion m p) ^ 3 * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G 3 := by
  have hsum : dispersion m p ^ 2 ≤
      ∑ j : Fin 4, ‖boostPhaseCLM m ((θ : ℂ) * Complex.I) p (coordDir j)‖ ^ 2 := by
    rw [sum_norm_sq_boostPhaseCLM_coordDir]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have h := norm_integral_prod_expPhase_le (boostPhaseCLM m ((θ : ℂ) * Complex.I) p) F G 3
    (dispersion_pos hm p) (im_boostPhaseCLM_nonneg hs hθ₀ hθπ p hF hG) hsum
  simp only [boostPhaseCLM_apply] at h
  unfold boostPhaseIntegral
  exact h

/-- `ω_m(𝐩)⁻⁴` is integrable on `ℝ³` for `m ≠ 0` (it is bounded by
`(1 + m⁻²)² (1 + |𝐩|²)⁻²`, and `3 < 4`). -/
theorem integrable_inv_dispersion_pow_four {m : ℝ} (hm : m ≠ 0) :
    Integrable fun p : EuclideanSpace ℝ (Fin 3) => (dispersion m p ^ 4)⁻¹ := by
  have hm2 : 0 < m ^ 2 := by positivity
  have hint : Integrable fun p : EuclideanSpace ℝ (Fin 3) =>
      ((1 : ℝ) + ‖p‖ ^ 2) ^ (-(4 : ℝ) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine (hint.const_mul ((1 + (m ^ 2)⁻¹) ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (((continuous_dispersion m).pow 4).inv₀ fun p =>
      pow_ne_zero 4 (dispersion_pos hm p).ne').aestronglyMeasurable
  · change ‖(dispersion m p ^ 4)⁻¹‖ ≤ (1 + (m ^ 2)⁻¹) ^ 2 * ((1 : ℝ) + ‖p‖ ^ 2) ^ (-(4 : ℝ) / 2)
    have hω := dispersion_pos hm p
    have hq : 0 < 1 + ‖p‖ ^ 2 := by positivity
    have hW : 0 < dispersion m p ^ 2 := pow_pos hω 2
    have hqW : 1 + ‖p‖ ^ 2 ≤ (1 + (m ^ 2)⁻¹) * dispersion m p ^ 2 := by
      rw [dispersion_sq, add_mul, one_mul, mul_add, inv_mul_cancel₀ hm2.ne']
      have : 0 ≤ (m ^ 2)⁻¹ * ‖p‖ ^ 2 := mul_nonneg (inv_nonneg.2 hm2.le) (sq_nonneg _)
      linarith
    have h1 : (dispersion m p ^ 2)⁻¹ ≤ (1 + (m ^ 2)⁻¹) * (1 + ‖p‖ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      calc (dispersion m p ^ 2)⁻¹ * (1 + ‖p‖ ^ 2)
          ≤ (dispersion m p ^ 2)⁻¹ * ((1 + (m ^ 2)⁻¹) * dispersion m p ^ 2) :=
            mul_le_mul_of_nonneg_left hqW (inv_nonneg.2 hW.le)
        _ = (1 + (m ^ 2)⁻¹) * ((dispersion m p ^ 2)⁻¹ * dispersion m p ^ 2) := by ring
        _ = 1 + (m ^ 2)⁻¹ := by rw [inv_mul_cancel₀ hW.ne', mul_one]
    have h2 := pow_le_pow_left₀ (inv_nonneg.2 hW.le) h1 2
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos hω 4)),
      show -(4 : ℝ) / 2 = -2 by norm_num, Real.rpow_neg hq.le, Real.rpow_two]
    calc (dispersion m p ^ 4)⁻¹ = ((dispersion m p ^ 2)⁻¹) ^ 2 := by ring
      _ ≤ ((1 + (m ^ 2)⁻¹) * (1 + ‖p‖ ^ 2)⁻¹) ^ 2 := h2
      _ = (1 + (m ^ 2)⁻¹) ^ 2 * ((1 + ‖p‖ ^ 2) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]

/-- **The integrable majorant on the closed strip**: for `m ≠ 0`, `θ ∈ [0, π]` and test functions
supported in the two unit double cones (`s ≥ 2`), the integrand of `𝒢(iθ)` is bounded by
`8 ‖F‖₁ max_j ‖∂_{e_j}³ G‖₁ / (2(2π)³) · ω_m(𝐩)⁻⁴`, independently of `θ`. -/
theorem norm_boostPhaseIntegral_mul_weight_le {m s θ : ℝ} (hm : m ≠ 0) (hs : 2 ≤ s)
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)‖ ≤
      8 * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G 3 / (2 * (2 * Real.pi) ^ 3) *
        (dispersion m p ^ 4)⁻¹ := by
  have hω := dispersion_pos hm p
  have hc : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  have hwt : 0 < 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) := one_div_pos.2 (mul_pos hc hω)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwt]
  calc ‖boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I)‖ *
        (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p))
      ≤ (2 / dispersion m p) ^ 3 * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G 3 *
          (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) :=
        mul_le_mul_of_nonneg_right (norm_boostPhaseIntegral_mul_I_le hm hs hθ₀ hθπ hF hG p)
          hwt.le
    _ = 8 * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G 3 / (2 * (2 * Real.pi) ^ 3) *
          (dispersion m p ^ 4)⁻¹ := by
        ring

/-! ### Continuity of `Φ` in the momentum and in `θ ∈ [0, π]` -/

/-- `ζ ↦ ψ_m(ζ, 𝐩, w)` is continuous. -/
theorem continuous_boostPhase_rapidity (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    Continuous fun ζ : ℂ => boostPhase m ζ p w := by
  have hc := Complex.continuous_cosh
  have hs := Complex.continuous_sinh
  unfold boostPhase
  exact (continuous_const.mul ((continuous_const.mul hc).add (continuous_const.mul hs))).sub
    (((continuous_const.mul ((continuous_const.mul hs).add (continuous_const.mul hc))).add
      continuous_const).sub continuous_const)

/-- `θ ↦ ψ_m(iθ, 𝐩, w)` is continuous. -/
theorem continuous_boostPhase_mul_I (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (w : Spacetime) :
    Continuous fun θ : ℝ => boostPhase m ((θ : ℂ) * Complex.I) p w :=
  (continuous_boostPhase_rapidity m p w).comp (Complex.continuous_ofReal.mul continuous_const)

/-- `𝐩 ↦ ψ_m(ζ, 𝐩, w)` is continuous. -/
theorem continuous_boostPhase_momentum (m : ℝ) (ζ : ℂ) (w : Spacetime) :
    Continuous fun p : EuclideanSpace ℝ (Fin 3) => boostPhase m ζ p w := by
  have h4 : Continuous fun p : EuclideanSpace ℝ (Fin 3) => ((dispersion m p : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_dispersion m)
  have h5 : Continuous fun p : EuclideanSpace ℝ (Fin 3) => ((⟪e₁, p⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
  have h3 : Continuous fun p : EuclideanSpace ℝ (Fin 3) => ((⟪p, w.2⟫_ℝ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)
  unfold boostPhase
  exact (h4.mul continuous_const).sub (((h5.mul continuous_const).add h3).sub
    (h5.mul continuous_const))

/-- Pointwise domination of the integrand of `Φ(𝐩, iθ)` for `θ ∈ [0, π]` and test functions
supported in the two unit double cones (`s ≥ 2`):
`|e^{iψ(iθ, 𝐩, y - x)} F(x) G(y)| ≤ |F(x)| |G(y)|`. -/
theorem norm_boostPhaseIntegrand_mul_I_le {m s θ : ℝ} (hs : 2 ≤ s) (hθ₀ : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) (p : EuclideanSpace ℝ (Fin 3))
    (z : Spacetime × Spacetime) :
    ‖Complex.exp (Complex.I * boostPhase m ((θ : ℂ) * Complex.I) p (z.2 - z.1)) *
        ((F.1 z.1 : ℝ) : ℂ) * ((G.1 z.2 : ℝ) : ℂ)‖ ≤ |F.1 z.1| * |G.1 z.2| := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  by_cases hx : z.1 ∈ tsupport F.1
  · by_cases hy : z.2 ∈ tsupport G.1
    · have hw := abs_fst_sub_le_of_mem_doubleCone hs (hF hx) (hG hy)
      have h1 := norm_exp_I_mul_boostPhase_le_one m 0 θ p (z.2 - z.1) hθ₀ hθπ hw
      rw [Complex.ofReal_zero, zero_add] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (F.1 z.1))
      have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (G.1 z.2))
      rwa [one_mul] at h3
    · have h0 : G.1 z.2 = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [h0]
  · have h0 : F.1 z.1 = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [h0]

/-- For `θ ∈ [0, π]` and test functions supported in the two unit double cones (`s ≥ 2`),
`𝐩 ↦ Φ(𝐩, iθ)` is continuous. -/
theorem continuous_boostPhaseIntegral_mul_I {m s θ : ℝ} (hs : 2 ≤ s) (hθ₀ : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) :
    Continuous fun p : EuclideanSpace ℝ (Fin 3) =>
      boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) := by
  unfold boostPhaseIntegral
  refine continuous_of_dominated
    (bound := fun z : Spacetime × Spacetime => |F.1 z.1| * |G.1 z.2|)
    (fun p => (integrable_boostPhaseIntegrand m F G p _).aestronglyMeasurable)
    (fun p => Filter.Eventually.of_forall fun z =>
      norm_boostPhaseIntegrand_mul_I_le hs hθ₀ hθπ hF hG p z)
    ((integrable_abs_testFunction F).mul_prod (integrable_abs_testFunction G))
    (Filter.Eventually.of_forall fun z => ?_)
  exact ((Complex.continuous_exp.comp (continuous_const.mul
    (continuous_boostPhase_momentum m _ (z.2 - z.1)))).mul continuous_const).mul
      continuous_const

/-- For test functions supported in the two unit double cones (`s ≥ 2`), `θ ↦ Φ(𝐩, iθ)` is
continuous on `[0, π]` (continuity of a parametric integral with the majorant `|F(x)| |G(y)|`). -/
theorem continuousOn_boostPhaseIntegral_mul_I {m s : ℝ} (hs : 2 ≤ s) {F G : RealTestFunction}
    (hF : tsupport F.1 ⊆ doubleCone 0 1) (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ContinuousOn (fun θ : ℝ => boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I))
      (Set.Icc 0 Real.pi) := by
  unfold boostPhaseIntegral
  refine continuousOn_of_dominated
    (bound := fun z : Spacetime × Spacetime => |F.1 z.1| * |G.1 z.2|)
    (fun θ _ => (integrable_boostPhaseIntegrand m F G p _).aestronglyMeasurable)
    (fun θ hθ => Filter.Eventually.of_forall fun z =>
      norm_boostPhaseIntegrand_mul_I_le hs hθ.1 hθ.2 hF hG p z)
    ((integrable_abs_testFunction F).mul_prod (integrable_abs_testFunction G))
    (Filter.Eventually.of_forall fun z => ?_)
  exact (((Complex.continuous_exp.comp (continuous_const.mul
    (continuous_boostPhase_mul_I m p (z.2 - z.1)))).mul continuous_const).mul
      continuous_const).continuousOn

/-! ### Continuity of `𝒢(iθ)` on `[0, π]` -/

/-- **Continuity at the edges**: for `m > 0` and test functions supported in the two unit double
cones (`s ≥ 2`), `θ ↦ 𝒢(iθ) = ∫ Φ(𝐩, iθ) dν(𝐩)` is continuous on `[0, π]` (dominated
convergence with the majorant `C ω_m(𝐩)⁻⁴` of `norm_boostPhaseIntegral_mul_weight_le`). -/
theorem continuousOn_integral_boostPhaseIntegral_mul_I {m s : ℝ} (hm : 0 < m) (hs : 2 ≤ s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) :
    ContinuousOn (fun θ : ℝ => ∫ p, boostPhaseIntegral m F G p ((θ : ℂ) * Complex.I) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) (Set.Icc 0 Real.pi) := by
  refine continuousOn_of_dominated
    (bound := fun p : EuclideanSpace ℝ (Fin 3) =>
      8 * (∫ x : Spacetime, |F.1 x|) * maxCoordDerivNorm G 3 / (2 * (2 * Real.pi) ^ 3) *
        (dispersion m p ^ 4)⁻¹)
    (fun θ hθ => ((continuous_boostPhaseIntegral_mul_I hs hθ.1 hθ.2 hF hG).mul
      (continuous_shellWeight hm.ne')).aestronglyMeasurable)
    (fun θ hθ => Filter.Eventually.of_forall fun p =>
      norm_boostPhaseIntegral_mul_weight_le hm.ne' hs hθ.1 hθ.2 hF hG p)
    ((integrable_inv_dispersion_pow_four hm.ne').const_mul _)
    (Filter.Eventually.of_forall fun p =>
      (continuousOn_boostPhaseIntegral_mul_I hs hF hG p).mul continuousOn_const)

/-! ### G. The conclusion -/

/-- **The one-particle inner product is real for test functions in two separated unit double
cones**: for `m > 0`, `s > 2`, `F` supported in the unit double cone at the origin and `G` in the
unit double cone at `s 𝐞₁`, `Im ⟨κ_m F, κ_m G⟩ = 0` (`𝒢` is constant on the open strip, stage E,
and continuous on `[0, π]`, stage F, so `𝒢(0) = 𝒢(iπ)`). -/
theorem im_oneParticleInner_eq_zero_of_doubleCone {m s : ℝ} (hm : 0 < m) (hs : 2 < s)
    {F G : RealTestFunction} (hF : tsupport F.1 ⊆ doubleCone 0 1)
    (hG : tsupport G.1 ⊆ doubleCone (0, s • e₁) 1) :
    (oneParticleInner m F G).im = 0 :=
  im_oneParticleInner_eq_zero_of_continuousOn hm hs hF hG
    (continuousOn_integral_boostPhaseIntegral_mul_I hm hs.le hF hG)

/-- **Microcausality**: `Locality` holds, i.e. for every mass `μ > 0`, every
`s > 2` and every vacuum system of mass `μ`, the local algebras of the unit double cones at the
origin and at `s 𝐞₁` commute. -/
theorem locality : Locality :=
  locality_of_im_eq_zero fun _ _ hμ hs _ _ hF hG =>
    im_oneParticleInner_eq_zero_of_doubleCone hμ hs hF hG

end VacuumBellSeparation
