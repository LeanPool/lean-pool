/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Ideal.GradientOrthogonality

/-!
# The mollifier on the literal three-torus

This module builds the standard mollifier `J_δ` on `L²(T³;ℂ³)`, `T³ = Torus 3`, as an average of
translates,

```
  J_δ f = ∫_{ℝ³} ρ_δ(z) τ_z f dz,     ∂_j J_δ f = ∫_{ℝ³} ∂_jρ_δ(z) τ_z f dz,
```

where `τ_z f = f(· − π z)` is translation by the class `π z` of `z ∈ ℝ³` and
`ρ_δ(z) = δ⁻³ ρ(δ⁻¹ z)` is the rescaling of a fixed smooth bump `ρ` supported in the unit ball
with integral one.

The paper's Remark 1.7 (the strong convergence `e^{tL_{ε,u}} B → 𝒯₀(t) B` as `ε ↓ 0`, uniformly
on bounded time intervals) is derived there from the Trotter–Kato approximation theorem and the
Friedrichs commutator lemma.  The formalisation proves it by an energy estimate for the
difference of the resistive evolution and a mollified ideal evolution, in which `J_δ` and the
Friedrichs commutator `∑_j (∂_j J_δ (u_j ·) − u_j ∂_j J_δ)` enter.  The mollifier is a tool of
that proof and has no counterpart statement in the paper.

## Contents

* `literalTranslate z`, translation as a linear isometry equivalence of `L²(T³;ℂ³)`, its
  representative (`literalTranslate_coe_ae`) and its strong continuity
  (`continuous_literalTranslate_apply`).
* `kernelTranslateIntegral k hk`, the operator `f ↦ ∫ k(z) τ_z f dz` for an integrable kernel,
  with the bound `‖·‖ ≤ ∫ |k|` and its action on Fourier coefficients: the coefficient of
  frequency `m` is multiplied by `∫ k(z) e^{-2πi m·z} dz`.
* `mollifierKernel δ`, `literalMollify δ`, `literalMollifyDeriv δ j` and the Fourier symbol
  `mollifierSymbol δ m = ∫ ρ_δ(z) e^{-2πi m·z} dz`.
* `inner_flatTorus3FourierBasis_literalMollify`,
  `inner_flatTorus3FourierBasis_literalMollifyDeriv`: `J_δ` and `∂_j J_δ` are the Fourier
  multipliers `σ_δ(m)` and `2πi m_j σ_δ(m)`.
* `norm_literalMollify_le`, `tendsto_literalMollify`: `‖J_δ‖ ≤ 1` and `J_δ f → f` as `δ ↓ 0`.
* `exists_bound_sq_mul_mollifierSymbol`: `|m|² |σ_δ(m)|` is bounded for each `δ`.
* `integral_norm_mul_norm_fderiv_mollifierKernel`: `∫ ‖z‖ ‖Dρ_δ(z)‖ dz` does not depend on
  `δ > 0`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped Topology

/-! ## Translations of `L²(T³;ℂ³)` -/

/-- The quotient map `ℝ³ → T³` is continuous. -/
theorem continuous_literalTorusPoint : Continuous literalTorusPoint :=
  continuous_pi fun _ ↦ (AddCircle.continuous_mk' 1).comp (by fun_prop)

/-- Translation of the literal three-torus by the class of `z ∈ ℝ³` preserves the Haar measure. -/
theorem measurePreserving_sub_literalTorusPoint (z : R3) :
    MeasurePreserving (fun x : Torus 3 ↦ x - literalTorusPoint z) volume volume :=
  measurePreserving_sub_right volume (literalTorusPoint z)

/-- Translation `f ↦ f(· − π z)` on `L²(T³;ℂ³)`, `π z` the class of `z ∈ ℝ³`, as a linear
isometry equivalence. -/
def literalTranslate (z : R3) : LiteralC3L2 ≃ₗᵢ[ℂ] LiteralC3L2 :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_sub_literalTorusPoint z)) fun g ↦ by
      refine ⟨Lp.compMeasurePreserving (fun x : Torus 3 ↦ x + literalTorusPoint z)
        (measurePreserving_add_right volume (literalTorusPoint z)) g, ?_⟩
      refine Lp.ext ?_
      have h1 := Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving (fun x : Torus 3 ↦ x + literalTorusPoint z)
          (measurePreserving_add_right volume (literalTorusPoint z)) g)
        (measurePreserving_sub_literalTorusPoint z)
      have h2 := (measurePreserving_sub_literalTorusPoint z).quasiMeasurePreserving.ae
        (Lp.coeFn_compMeasurePreserving g
          (measurePreserving_add_right volume (literalTorusPoint z)))
      filter_upwards [h1, h2] with x hx1 hx2
      refine hx1.trans (hx2.trans ?_)
      simp

/-- The translate is represented by the translated representative. -/
theorem literalTranslate_coe_ae (z : R3) (f : LiteralC3L2) :
    (literalTranslate z f : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ (f : Torus 3 → C3) (x - literalTorusPoint z) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_literalTorusPoint z)

/-- Translation by the origin is the identity. -/
theorem literalTranslate_zero_apply (f : LiteralC3L2) : literalTranslate 0 f = f := by
  refine Lp.ext ?_
  filter_upwards [literalTranslate_coe_ae 0 f] with x hx
  rw [hx, literalTorusPoint_zero, sub_zero]

/-- On the class of a continuous field, translation is precomposition with the translation of the
torus. -/
theorem literalTranslate_toLp (z : R3) (g : C(Torus 3, C3)) :
    literalTranslate z (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) =
      ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
        (g.comp ⟨fun x ↦ x - literalTorusPoint z, by fun_prop⟩) := by
  refine Lp.ext ?_
  have h2 := (measurePreserving_sub_literalTorusPoint z).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (E := C3) (p := 2) (volume : Measure (Torus 3)) (𝕜 := ℂ) g)
  filter_upwards [literalTranslate_coe_ae z
      (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g), h2,
    ContinuousMap.coeFn_toLp (E := C3) (p := 2) (volume : Measure (Torus 3)) (𝕜 := ℂ)
      (g.comp ⟨fun x ↦ x - literalTorusPoint z, by fun_prop⟩)] with x hx hx2 hx3
  rw [hx, hx2, hx3]
  rfl

/-- **Strong continuity of the translations.**  On continuous fields the orbit `z ↦ τ_z g` is
continuous (joint continuity of `(z, x) ↦ g(x − π z)`); continuous fields are dense in `L²`
(`ContinuousMap.toLp_denseRange`) and every `τ_z` is an isometry, so the orbit of every `f` is a
uniform limit of continuous maps. -/
theorem continuous_literalTranslate_apply (f : LiteralC3L2) :
    Continuous fun z : R3 ↦ literalTranslate z f := by
  refine continuous_of_uniform_approx_of_continuous ?_
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (ContinuousMap.toLp_denseRange C3 (volume : Measure (Torus 3)) ℂ (by simp)) f ε hε
  refine ⟨fun z : R3 ↦ literalTranslate z
    (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g), ?_, fun z ↦ hsub ?_⟩
  · let G : C(R3 × Torus 3, C3) :=
      g.comp ⟨fun p ↦ p.2 - literalTorusPoint p.1,
        continuous_snd.sub (continuous_literalTorusPoint.comp continuous_fst)⟩
    have heq : (fun z : R3 ↦ literalTranslate z
        (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)) =
        fun z : R3 ↦ ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ (G.curry z) := by
      funext z
      rw [literalTranslate_toLp]
      rfl
    rw [heq]
    exact (ContinuousMap.toLp (E := C3) 2 (volume : Measure (Torus 3)) ℂ).continuous.comp
      G.curry.continuous
  · rw [dist_eq_norm, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map,
      ← dist_eq_norm]
    exact hg

/-- The phase `e^{-2πi m·z}` of the translate by `z` of the character of frequency `m`. -/
def translationPhase (m : Fin 3 → ℤ) (z : R3) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ∑ j, (m j : ℂ) * (z j : ℂ)))

/-- The phase is the conjugate of the character at the class of `z`. -/
theorem translationPhase_eq (m : Fin 3 → ℤ) (z : R3) :
    translationPhase m z = (starRingEnd ℂ) (UnitAddTorus.mFourier m (literalTorusPoint z)) := by
  rw [mFourier_literalTorusPoint, ← Complex.exp_conj, translationPhase]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_ofNat]
  ring

/-- The phase has modulus one. -/
theorem norm_translationPhase (m : Fin 3 → ℤ) (z : R3) : ‖translationPhase m z‖ = 1 := by
  rw [translationPhase_eq, RCLike.norm_conj, norm_mFourier_apply]

/-- **Translations are diagonal in the Fourier basis**: the coefficient of frequency `m` of each
component of `τ_z f` is that of `f` times `e^{-2πi m·z}`. -/
theorem inner_flatTorus3FourierBasis_literalTranslate (z : R3) (m : Fin 3 → ℤ) (i : Fin 3)
    (f : LiteralC3L2) :
    inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i (literalTranslate z f)) =
      translationPhase m z * inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i f) := by
  rw [inner_flatTorus3FourierBasis, inner_flatTorus3FourierBasis, ← integral_const_mul]
  have hae : (fun x : Torus 3 ↦ (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      (literalCoordL2 i (literalTranslate z f) : Torus 3 → ℂ) x) =ᵐ[volume]
      fun x ↦ (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
        (f : Torus 3 → C3) (x - literalTorusPoint z) i := by
    filter_upwards [literalCoordL2_coe_ae i (literalTranslate z f),
      literalTranslate_coe_ae z f] with x hx hx2
    rw [hx, hx2]
  have hae2 : (fun x : Torus 3 ↦ translationPhase m z * ((starRingEnd ℂ)
      (UnitAddTorus.mFourier m x) * (literalCoordL2 i f : Torus 3 → ℂ) x)) =ᵐ[volume]
      fun x ↦ translationPhase m z * ((starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
        (f : Torus 3 → C3) x i) := by
    filter_upwards [literalCoordL2_coe_ae i f] with x hx
    rw [hx]
  rw [integral_congr_ae hae, integral_congr_ae hae2,
    ← (measurePreserving_add_right volume (literalTorusPoint z)).integral_comp
      (measurableEmbedding_addRight (literalTorusPoint z))]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [add_sub_cancel_right, mFourier_add_point, map_mul, translationPhase_eq]
  ring

/-! ## Averages of translates against an integrable kernel -/

/-- The translates of a fixed field, weighted by an integrable kernel, form an integrable
family. -/
theorem integrable_kernel_smul_literalTranslate {k : R3 → ℝ} (hk : Integrable k)
    (f : LiteralC3L2) :
    Integrable fun z : R3 ↦ (k z : ℂ) • literalTranslate z f := by
  refine (hk.ofReal (𝕜 := ℂ)).smul_of_top_left ?_
  refine memLp_top_of_bound (continuous_literalTranslate_apply f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun z ↦ ?_)
  rw [LinearIsometryEquiv.norm_map]

/-- The operator `f ↦ ∫ k(z) τ_z f dz` of an integrable kernel `k`, bounded by `∫ |k|`. -/
def kernelTranslateIntegral (k : R3 → ℝ) (hk : Integrable k) :
    LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ z, (k z : ℂ) • literalTranslate z f
      map_add' := fun f g ↦ by
        simp only [map_add, smul_add]
        exact integral_add (integrable_kernel_smul_literalTranslate hk f)
          (integrable_kernel_smul_literalTranslate hk g)
      map_smul' := fun c f ↦ by
        simp only [LinearIsometryEquiv.map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        funext z
        rw [smul_comm] }
    (∫ z, |k z|) fun f ↦ by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_smul, LinearIsometryEquiv.norm_map,
        Complex.norm_real, Real.norm_eq_abs]
      exact integral_mul_const _ _

/-- Unfolding `kernelTranslateIntegral`. -/
theorem kernelTranslateIntegral_apply {k : R3 → ℝ} (hk : Integrable k) (f : LiteralC3L2) :
    kernelTranslateIntegral k hk f = ∫ z, (k z : ℂ) • literalTranslate z f :=
  rfl

/-- The operator norm of an average of translates is at most the `L¹` norm of the kernel. -/
theorem norm_kernelTranslateIntegral_le {k : R3 → ℝ} (hk : Integrable k) :
    ‖kernelTranslateIntegral k hk‖ ≤ ∫ z, |k z| :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ abs_nonneg _) _

/-- An average of translates is the Fourier multiplier `m ↦ ∫ k(z) e^{-2πi m·z} dz`. -/
theorem inner_flatTorus3FourierBasis_kernelTranslateIntegral {k : R3 → ℝ} (hk : Integrable k)
    (m : Fin 3 → ℤ) (i : Fin 3) (f : LiteralC3L2) :
    inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i (kernelTranslateIntegral k hk f)) =
      (∫ z, (k z : ℂ) * translationPhase m z) *
        inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i f) := by
  let L : LiteralC3L2 →L[ℂ] ℂ := (innerSL ℂ (flatTorus3FourierBasis m)).comp (literalCoordL2 i)
  have hL : ∀ g, L g = inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i g) := fun _ ↦ rfl
  rw [← hL, kernelTranslateIntegral_apply,
    ← L.integral_comp_comm (integrable_kernel_smul_literalTranslate hk f), ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  dsimp only
  rw [map_smul, hL, inner_flatTorus3FourierBasis_literalTranslate, smul_eq_mul]
  ring

/-! ## The mollifier kernel -/

/-- The smooth bump of radii `1/2` and `1` at the origin of `ℝ³` from which the mollifier is
built. -/
def mollifierBump : ContDiffBump (0 : R3) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The bump has positive integral. -/
theorem integral_mollifierBump_pos : 0 < ∫ w, mollifierBump w := by
  refine (integral_pos_iff_support_of_nonneg mollifierBump.nonneg'
    (mollifierBump.continuous.integrable_of_hasCompactSupport
      mollifierBump.hasCompactSupport)).2 ?_
  rw [mollifierBump.support_eq]
  exact Metric.measure_ball_pos volume 0 mollifierBump.rOut_pos

/-- The standard mollifier `ρ_δ(z) = δ⁻³ ρ(δ⁻¹ z)`, where `ρ = b / ∫ b` is `b = mollifierBump`
normalised to integral one: for `δ > 0` a smooth nonnegative function supported in the closed
ball of radius `δ` with integral one. -/
def mollifierKernel (δ : ℝ) (z : R3) : ℝ :=
  δ⁻¹ ^ 3 / (∫ w, mollifierBump w) * mollifierBump (δ⁻¹ • z)

/-- The mollifier kernel is smooth. -/
theorem contDiff_mollifierKernel (δ : ℝ) {n : ℕ∞} : ContDiff ℝ n (mollifierKernel δ) :=
  contDiff_const.mul (mollifierBump.contDiff.comp (contDiff_const_smul δ⁻¹))

/-- The mollifier kernel has compact support. -/
theorem hasCompactSupport_mollifierKernel (δ : ℝ) : HasCompactSupport (mollifierKernel δ) := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · have h0 : mollifierKernel 0 = 0 := by
      funext z
      simp [mollifierKernel]
    rw [h0]
    exact HasCompactSupport.zero
  · exact (mollifierBump.hasCompactSupport.comp_smul (inv_ne_zero hδ)).mul_left

/-- The mollifier kernel is integrable. -/
theorem integrable_mollifierKernel (δ : ℝ) : Integrable (mollifierKernel δ) :=
  (contDiff_mollifierKernel δ (n := 0)).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_mollifierKernel δ)

/-- A directional derivative of the mollifier kernel is integrable. -/
theorem integrable_fderiv_mollifierKernel_apply (δ : ℝ) (v : R3) :
    Integrable fun z ↦ fderiv ℝ (mollifierKernel δ) z v :=
  (((contDiff_mollifierKernel δ (n := 1)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
    ((hasCompactSupport_mollifierKernel δ).fderiv_apply (𝕜 := ℝ) v)

/-! ## The mollifier and its derivatives -/

/-- The mollifier `J_δ f = ∫ ρ_δ(z) τ_z f dz` on `L²(T³;ℂ³)`. -/
def literalMollify (δ : ℝ) : LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  kernelTranslateIntegral (mollifierKernel δ) (integrable_mollifierKernel δ)

/-- The derivative `∂_j J_δ f = ∫ ∂_jρ_δ(z) τ_z f dz` of the mollified field. -/
def literalMollifyDeriv (δ : ℝ) (j : Fin 3) : LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  kernelTranslateIntegral (fun z ↦ fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1))
    (integrable_fderiv_mollifierKernel_apply δ _)

/-- The Fourier symbol `σ_δ(m) = ∫ ρ_δ(z) e^{-2πi m·z} dz` of the mollifier. -/
def mollifierSymbol (δ : ℝ) (m : Fin 3 → ℤ) : ℂ :=
  ∫ z, (mollifierKernel δ z : ℂ) * translationPhase m z

/-! ## Mass, sign and support of the kernel -/

/-- Rescaling the bump multiplies its integral by `|δ|³`. -/
theorem integral_mollifierBump_comp_inv_smul (δ : ℝ) :
    ∫ z, mollifierBump (δ⁻¹ • z) = |δ ^ 3| * ∫ w, mollifierBump w := by
  rw [Measure.integral_comp_inv_smul, finrank_euclideanSpace_fin, smul_eq_mul]

/-- The `L¹` norm of the mollifier kernel is at most one (it is one for `δ ≠ 0`). -/
theorem integral_abs_mollifierKernel_le (δ : ℝ) : ∫ z, |mollifierKernel δ z| ≤ 1 := by
  have hI := integral_mollifierBump_pos
  have habs : ∀ z, |mollifierKernel δ z| =
      |δ⁻¹ ^ 3| / (∫ w, mollifierBump w) * mollifierBump (δ⁻¹ • z) := fun z ↦ by
    rw [mollifierKernel, abs_mul, abs_div, abs_of_pos hI, abs_of_nonneg (mollifierBump.nonneg' _)]
  simp_rw [habs]
  rw [integral_const_mul, integral_mollifierBump_comp_inv_smul]
  have hval : |δ⁻¹ ^ 3| / (∫ w, mollifierBump w) * (|δ ^ 3| * ∫ w, mollifierBump w) =
      |(δ⁻¹ * δ) ^ 3| := by
    rw [mul_pow, abs_mul]
    field_simp
  rw [hval]
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp
  · rw [inv_mul_cancel₀ hδ]
    simp

/-- For `δ > 0` the mollifier kernel has integral one. -/
theorem integral_mollifierKernel {δ : ℝ} (hδ : 0 < δ) : ∫ z, mollifierKernel δ z = 1 := by
  simp_rw [mollifierKernel]
  rw [integral_const_mul, integral_mollifierBump_comp_inv_smul, abs_of_pos (pow_pos hδ 3)]
  field_simp [integral_mollifierBump_pos.ne']

/-- For `δ ≥ 0` the mollifier kernel is nonnegative. -/
theorem mollifierKernel_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (z : R3) : 0 ≤ mollifierKernel δ z :=
  mul_nonneg (div_nonneg (pow_nonneg (inv_nonneg.2 hδ) 3) integral_mollifierBump_pos.le)
    (mollifierBump.nonneg' _)

/-- For `δ > 0` the mollifier kernel vanishes outside the open ball of radius `δ`. -/
theorem mollifierKernel_eq_zero_of_le_norm {δ : ℝ} (hδ : 0 < δ) {z : R3} (hz : δ ≤ ‖z‖) :
    mollifierKernel δ z = 0 := by
  rw [mollifierKernel, mollifierBump.zero_of_le_dist, mul_zero]
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le]
  change (1 : ℝ) ≤ δ⁻¹ * ‖z‖
  rw [inv_mul_eq_div, one_le_div hδ]
  exact hz

/-! ## Norm bound and convergence of the mollifier -/

/-- **`‖J_δ‖ ≤ 1`.** -/
theorem norm_literalMollify_le (δ : ℝ) : ‖literalMollify δ‖ ≤ 1 :=
  (norm_kernelTranslateIntegral_le _).trans (integral_abs_mollifierKernel_le δ)

/-- **`J_δ f → f` as `δ ↓ 0`.**  Since `ρ_δ ≥ 0` has integral one and is supported in the ball of
radius `δ`, `‖J_δ f − f‖ = ‖∫ ρ_δ(z) (τ_z f − f) dz‖ ≤ sup_{‖z‖<δ} ‖τ_z f − f‖`, which tends to
zero by the strong continuity of the translations. -/
theorem tendsto_literalMollify (f : LiteralC3L2) :
    Tendsto (fun δ : ℝ ↦ literalMollify δ f) (𝓝[>] 0) (𝓝 f) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.1
    ((continuous_literalTranslate_apply f).continuousAt (x := 0)) (ε / 2) (by positivity)
  refine ⟨η, hη, fun δ hδ hδη ↦ ?_⟩
  have hδ : 0 < δ := hδ
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ] at hδη
  have hk := integrable_mollifierKernel δ
  have hrepr : literalMollify δ f - f =
      ∫ z, (mollifierKernel δ z : ℂ) • (literalTranslate z f - f) := by
    have hsub : ∫ z, ((mollifierKernel δ z : ℂ) • literalTranslate z f -
        (mollifierKernel δ z : ℂ) • f) =
        (∫ z, (mollifierKernel δ z : ℂ) • literalTranslate z f) -
          ∫ z, (mollifierKernel δ z : ℂ) • f :=
      integral_sub (integrable_kernel_smul_literalTranslate hk f)
        ((hk.ofReal (𝕜 := ℂ)).smul_const f)
    have hconst : ∫ z, (mollifierKernel δ z : ℂ) • f = f := by
      rw [integral_smul_const, integral_complex_ofReal, integral_mollifierKernel hδ,
        Complex.ofReal_one, one_smul]
    simp_rw [smul_sub]
    rw [hsub, hconst]
    rfl
  rw [dist_eq_norm, hrepr]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le (hk.mul_const (ε / 2))
    (Eventually.of_forall fun z ↦ ?_)) ?_
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mollifierKernel_nonneg hδ.le z)]
    by_cases hz : ‖z‖ < δ
    · refine mul_le_mul_of_nonneg_left ?_ (mollifierKernel_nonneg hδ.le z)
      have h := hη' (x := z) (by rw [dist_zero_right]; linarith)
      rw [literalTranslate_zero_apply, dist_eq_norm] at h
      exact h.le
    · rw [mollifierKernel_eq_zero_of_le_norm hδ (not_lt.1 hz), zero_mul, zero_mul]
  · rw [integral_mul_const, integral_mollifierKernel hδ, one_mul]
    linarith

/-! ## Fourier symbols -/

/-- The phase `z ↦ e^{-2πi m·z}` has derivative `-2πi m_j e^{-2πi m·z}` in the direction of the
`j`-th coordinate vector. -/
theorem fderiv_translationPhase_apply_single (m : Fin 3 → ℤ) (j : Fin 3) (z : R3) :
    fderiv ℝ (translationPhase m) z (EuclideanSpace.single j 1) =
      translationPhase m z * -(2 * Real.pi * Complex.I * (m j : ℂ)) := by
  let L : R3 →L[ℝ] ℂ := (-(2 * Real.pi * Complex.I)) •
    ∑ i : Fin 3, (m i : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj i : R3 →L[ℝ] ℝ))
  have hL : (fun z : R3 ↦ -(2 * Real.pi * Complex.I * ∑ i, (m i : ℂ) * (z i : ℂ))) = L := by
    funext z
    simp [L, Finset.mul_sum]
  have hd : HasFDerivAt (translationPhase m) (translationPhase m z • L) z := by
    have h := (L.hasFDerivAt (x := z)).cexp
    rw [← hL] at h
    exact h
  rw [hd.fderiv, smul_apply, smul_eq_mul]
  congr 1
  simp only [L, smul_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp

/-- The phase is differentiable. -/
theorem differentiable_translationPhase (m : Fin 3 → ℤ) :
    Differentiable ℝ (translationPhase m) := fun z ↦ by
  unfold translationPhase
  fun_prop

/-- **Integration by parts against the phase**: for a `C¹` kernel `k` with compact support,
`∫ ∂_jk(z) e^{-2πi m·z} dz = 2πi m_j ∫ k(z) e^{-2πi m·z} dz`. -/
theorem integral_fderiv_mul_translationPhase {k : R3 → ℝ} (hk : ContDiff ℝ 1 k)
    (hks : HasCompactSupport k) (j : Fin 3) (m : Fin 3 → ℤ) :
    ∫ z, (fderiv ℝ k z (EuclideanSpace.single j 1) : ℂ) * translationPhase m z =
      (2 * Real.pi * Complex.I * (m j : ℂ)) * ∫ z, (k z : ℂ) * translationPhase m z := by
  set v : R3 := EuclideanSpace.single j 1
  have hkd : Differentiable ℝ k := hk.differentiable one_ne_zero
  have hfd : ∀ z, fderiv ℝ (fun w ↦ (k w : ℂ)) z v = (fderiv ℝ k z v : ℂ) := fun z ↦ by
    change fderiv ℝ (Complex.ofRealCLM ∘ k) z v = _
    rw [((Complex.ofRealCLM.hasFDerivAt (x := k z)).comp z (hkd z).hasFDerivAt).fderiv]
    rfl
  have hph := differentiable_translationPhase m
  have hphc : Continuous (translationPhase m) := hph.continuous
  have hkc : Continuous fun z ↦ (k z : ℂ) := Complex.continuous_ofReal.comp hk.continuous
  have hks' : HasCompactSupport fun z ↦ (k z : ℂ) := hks.comp_left Complex.ofReal_zero
  have hdc : Continuous fun z ↦ (fderiv ℝ k z v : ℂ) :=
    Complex.continuous_ofReal.comp ((hk.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)
  have hds : HasCompactSupport fun z ↦ (fderiv ℝ k z v : ℂ) :=
    (hks.fderiv_apply (𝕜 := ℝ) v).comp_left Complex.ofReal_zero
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun w ↦ (k w : ℂ)) (g := translationPhase m) (v := v) (μ := volume)
    (by simp_rw [hfd]; exact (hdc.mul hphc).integrable_of_hasCompactSupport hds.mul_right)
    (by
      simp_rw [v, fderiv_translationPhase_apply_single]
      exact (hkc.mul (hphc.mul continuous_const)).integrable_of_hasCompactSupport
        hks'.mul_right)
    ((hkc.mul hphc).integrable_of_hasCompactSupport hks'.mul_right)
    (fun z _ ↦ (Complex.ofRealCLM.differentiableAt.comp z (hkd z)))
    (fun z _ ↦ hph z)
  simp_rw [hfd, v, fderiv_translationPhase_apply_single] at hibp
  have h2 : ∫ z, (k z : ℂ) * (translationPhase m z * -(2 * Real.pi * Complex.I * (m j : ℂ))) =
      -(2 * Real.pi * Complex.I * (m j : ℂ)) * ∫ z, (k z : ℂ) * translationPhase m z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [h2] at hibp
  linear_combination hibp

/-- **The mollifier is the Fourier multiplier `σ_δ`.** -/
theorem inner_flatTorus3FourierBasis_literalMollify (δ : ℝ) (m : Fin 3 → ℤ) (i : Fin 3)
    (f : LiteralC3L2) :
    inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i (literalMollify δ f)) =
      mollifierSymbol δ m * inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i f) :=
  inner_flatTorus3FourierBasis_kernelTranslateIntegral _ m i f

/-- A directional derivative of the mollifier kernel is again `C¹` with compact support. -/
theorem contDiff_fderiv_mollifierKernel_apply (δ : ℝ) (v : R3) :
    ContDiff ℝ 1 fun z ↦ fderiv ℝ (mollifierKernel δ) z v :=
  ((contDiff_mollifierKernel δ (n := 2)).fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiff_const

/-- **The derivative of the mollifier is the Fourier multiplier `2πi m_j σ_δ`.** -/
theorem inner_flatTorus3FourierBasis_literalMollifyDeriv (δ : ℝ) (j : Fin 3)
    (m : Fin 3 → ℤ) (i : Fin 3) (f : LiteralC3L2) :
    inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i (literalMollifyDeriv δ j f)) =
      (2 * Real.pi * Complex.I * (m j : ℂ)) * mollifierSymbol δ m *
        inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i f) := by
  rw [literalMollifyDeriv, inner_flatTorus3FourierBasis_kernelTranslateIntegral,
    integral_fderiv_mul_translationPhase (contDiff_mollifierKernel δ)
      (hasCompactSupport_mollifierKernel δ)]
  rfl

/-- **Decay of the symbol**: for each `δ`, `|m|² |σ_δ(m)|` is bounded.  Two integrations by parts
give `(2πi m_j)² σ_δ(m) = ∫ ∂_j²ρ_δ(z) e^{-2πi m·z} dz`, whose modulus is at most
`∫ |∂_j²ρ_δ|`. -/
theorem exists_bound_sq_mul_mollifierSymbol (δ : ℝ) :
    ∃ C : ℝ, ∀ m : Fin 3 → ℤ, (∑ j : Fin 3, ((m j : ℝ)) ^ 2) * ‖mollifierSymbol δ m‖ ≤ C := by
  let k₂ : Fin 3 → R3 → ℝ := fun j z ↦ fderiv ℝ (fun w ↦ fderiv ℝ (mollifierKernel δ) w
    (EuclideanSpace.single j 1)) z (EuclideanSpace.single j 1)
  refine ⟨∑ j : Fin 3, (∫ z, |k₂ j z|) / (4 * Real.pi ^ 2), fun m ↦ ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have hsym : (2 * Real.pi * Complex.I * (m j : ℂ)) ^ 2 * mollifierSymbol δ m =
      ∫ z, (k₂ j z : ℂ) * translationPhase m z := by
    rw [integral_fderiv_mul_translationPhase (contDiff_fderiv_mollifierKernel_apply δ _)
      ((hasCompactSupport_mollifierKernel δ).fderiv_apply (𝕜 := ℝ) _),
      integral_fderiv_mul_translationPhase (contDiff_mollifierKernel δ)
      (hasCompactSupport_mollifierKernel δ), mollifierSymbol]
    ring
  have hnorm : ‖(2 * Real.pi * Complex.I * (m j : ℂ)) ^ 2 * mollifierSymbol δ m‖ =
      4 * Real.pi ^ 2 * ((m j : ℝ) ^ 2 * ‖mollifierSymbol δ m‖) := by
    rw [norm_mul, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast, mul_pow, mul_pow, sq_abs]
    norm_num
    ring
  have hle : ‖(2 * Real.pi * Complex.I * (m j : ℂ)) ^ 2 * mollifierSymbol δ m‖ ≤
      ∫ z, |k₂ j z| := by
    rw [hsym]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    congr 1
    funext z
    rw [norm_mul, norm_translationPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hle
  rw [le_div_iff₀ hpi, mul_comm]
  exact hle

/-! ## Scaling of the first moment of `Dρ_δ` -/

/-- The kernel at scale `δ` is the rescaling of the kernel at scale one. -/
theorem mollifierKernel_eq_smul_comp (δ : ℝ) (z : R3) :
    mollifierKernel δ z = δ⁻¹ ^ 3 * mollifierKernel 1 (δ⁻¹ • z) := by
  simp only [mollifierKernel, inv_one, one_pow, one_smul]
  ring

/-- The norm of the derivative of the rescaled kernel. -/
theorem norm_fderiv_mollifierKernel {δ : ℝ} (hδ : 0 < δ) (z : R3) :
    ‖fderiv ℝ (mollifierKernel δ) z‖ =
      δ⁻¹ ^ 3 * (δ⁻¹ * ‖fderiv ℝ (mollifierKernel 1) (δ⁻¹ • z)‖) := by
  have h1 : HasFDerivAt (mollifierKernel 1)
      (fderiv ℝ (mollifierKernel 1) (δ⁻¹ • z)) (δ⁻¹ • z) :=
    ((contDiff_mollifierKernel 1 (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  have h2 : HasFDerivAt (mollifierKernel δ)
      (δ⁻¹ ^ 3 • (fderiv ℝ (mollifierKernel 1) (δ⁻¹ • z)).comp
        (δ⁻¹ • ContinuousLinearMap.id ℝ R3)) z := by
    have h := (h1.comp z ((hasFDerivAt_id z).const_smul δ⁻¹)).const_mul (δ⁻¹ ^ 3)
    have hfun : (fun y ↦ δ⁻¹ ^ 3 * (mollifierKernel 1 ∘ HSMul.hSMul δ⁻¹) y) =
        mollifierKernel δ :=
      funext fun w ↦ (mollifierKernel_eq_smul_comp δ w).symm
    rw [hfun] at h
    exact h
  rw [h2.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul,
    norm_smul, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.2 hδ.le) 3),
    Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]

/-- The first moment `z ↦ ‖z‖ ‖Dρ_δ(z)‖` of the derivative of the kernel is integrable. -/
theorem integrable_norm_mul_norm_fderiv_mollifierKernel (δ : ℝ) :
    Integrable fun z : R3 ↦ ‖z‖ * ‖fderiv ℝ (mollifierKernel δ) z‖ :=
  (continuous_norm.mul ((contDiff_mollifierKernel δ (n := 1)).continuous_fderiv
    one_ne_zero).norm).integrable_of_hasCompactSupport
    ((hasCompactSupport_mollifierKernel δ).fderiv (𝕜 := ℝ)).norm.mul_left

/-- **Scaling of the first moment**: `∫ ‖z‖ ‖Dρ_δ(z)‖ dz` does not depend on `δ > 0`.  With
`ρ_δ(z) = δ⁻³ ρ(δ⁻¹ z)`, `‖z‖ ‖Dρ_δ(z)‖ = δ⁻³ ‖δ⁻¹ z‖ ‖Dρ(δ⁻¹ z)‖`, and the substitution
`w = δ⁻¹ z` contributes `δ³`.  This is the uniform bound behind the Friedrichs commutator
estimate. -/
theorem integral_norm_mul_norm_fderiv_mollifierKernel {δ : ℝ} (hδ : 0 < δ) :
    ∫ z : R3, ‖z‖ * ‖fderiv ℝ (mollifierKernel δ) z‖ =
      ∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖ := by
  have hpt : ∀ z : R3, ‖z‖ * ‖fderiv ℝ (mollifierKernel δ) z‖ =
      δ⁻¹ ^ 3 * (‖δ⁻¹ • z‖ * ‖fderiv ℝ (mollifierKernel 1) (δ⁻¹ • z)‖) := fun z ↦ by
    rw [norm_fderiv_mollifierKernel hδ, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
    ring
  simp_rw [hpt]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun w : R3 ↦ ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖) hδ.le,
    finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hδ.ne',
    one_pow, one_mul]

end

end FastDynamo
