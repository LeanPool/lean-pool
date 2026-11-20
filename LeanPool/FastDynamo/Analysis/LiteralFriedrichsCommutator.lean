/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.LiteralTorusMollifier
public import LeanPool.FastDynamo.Dynamics.IdealWeakForm
public import LeanPool.FastDynamo.Dynamics.Flow.ParticleFlowUniqueness

/-!
# The Friedrichs commutator lemma on the literal three-torus

For a Lipschitz velocity `v` on `T³ = Torus 3` and the mollifier `J_δ` of
`FastDynamo/Analysis/LiteralTorusMollifier.lean`, the **Friedrichs commutator** is the operator

```
  K_δ f = ∑_j (∂_j J_δ (v_j f) − v_j ∂_j J_δ f)
```

on `L²(T³;ℂ³)`, the commutator of the mollifier with the transport term `(v·∇)f = ∑_j v_j ∂_j f`
written in divergence form (for `div v = 0` the two agree).  The Friedrichs commutator lemma
(DiPerna–Lions, Lemma II.1) says that `K_δ` is bounded uniformly in `δ` and that `K_δ f → 0` as
`δ ↓ 0` when `div v = 0`.  The paper derives Remark 1.7 (the strong convergence
`e^{tL_{ε,u}} B → 𝒯₀(t) B` as `ε ↓ 0`, uniformly on bounded time intervals) from the
Trotter–Kato approximation theorem and this lemma; the formalisation uses the lemma in an energy
estimate for the difference of the resistive evolution and a mollified ideal evolution.

## Contents

* `literalComponentMul v hv j`, multiplication by the component `v_j` of a continuous velocity,
  and its representative `literalComponentMul_coe_ae`.
* `friedrichsCommutator v hv δ`, the operator `K_δ`.
* `exists_norm_friedrichsCommutator_le`: `‖K_δ‖ ≤ C` for `0 < δ ≤ 1`.  Writing
  `∂_j J_δ = ∫ ∂_jρ_δ(z) τ_z dz`, `K_δ = ∑_j ∫ ∂_jρ_δ(z) (τ_z v_j − v_j τ_z) dz`, and
  `‖τ_z v_j − v_j τ_z‖ ≤ L ‖z‖`, so `‖K_δ‖ ≤ 3 L ∫ ‖z‖ ‖Dρ_δ(z)‖ dz`, which does not depend on
  `δ`.
* `tendsto_friedrichsCommutator`: if moreover the lift of `v` is differentiable and
  `div v = 0` at every point, `K_δ f → 0` as `δ ↓ 0`, uniformly for `f` in a compact subset of
  `L²`.  For a continuous field `g`,
  `K_δ g(x) = ∑_j ∫ ∂_jρ_δ(z) (v_j(x − z) − v_j(x)) (g(x − z) − g(x)) dz`, because
  `∑_j ∫ ∂_jρ_δ(z) (v_j(x − z) − v_j(x)) dz = ∫ ρ_δ(z) (div v)(x − z) dz = 0` (integration by
  parts in `z`); this is `O(L · sup_{‖z‖ ≤ δ} ‖g(· − z) − g‖_∞)`.  Continuous fields are dense in
  `L²`, and the uniform bound extends the convergence to all of `L²`, uniformly on compact sets.

DiPerna and Lions state the lemma on `ℝ^d`, for Sobolev velocities and `L^p` fields, with
convergence in `L^1_loc`; here it is proved on the torus, for Lipschitz `v` with everywhere
differentiable lift and fields in `L²`, with convergence in `L²`, the case the energy estimate
needs.  The paper only cites the lemma and states no version of its own.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-! ## Multiplication by a component of a continuous velocity -/

/-- The multiplier `x ↦ v_j(x) · id` on `ℂ³` of the `j`-th component of a continuous velocity, as
a continuous operator-valued field. -/
def literalComponentSymbol (v : Torus 3 → R3) (hv : Continuous v) (j : Fin 3) :
    C(Torus 3, C3 →L[ℂ] C3) :=
  ⟨fun x ↦ ((v x j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ C3,
    (Complex.continuous_ofReal.comp ((EuclideanSpace.proj j).continuous.comp hv)).smul
      continuous_const⟩

/-- Multiplication `f ↦ v_j f` by the `j`-th component of a continuous velocity, on
`L²(T³;ℂ³)`. -/
def literalComponentMul (v : Torus 3 → R3) (hv : Continuous v) (j : Fin 3) :
    LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  operatorMulL2 (volume : Measure (Torus 3))
    (ContinuousMap.toLp ∞ (volume : Measure (Torus 3)) ℂ (literalComponentSymbol v hv j))

/-- `literalComponentMul v hv j` is pointwise multiplication by `v_j`. -/
theorem literalComponentMul_coe_ae (v : Torus 3 → R3) (hv : Continuous v) (j : Fin 3)
    (f : LiteralC3L2) :
    (literalComponentMul v hv j f : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ ((v x j : ℝ) : ℂ) • (f : Torus 3 → C3) x := by
  filter_upwards [operatorMulL2_coe_ae (volume : Measure (Torus 3))
      (ContinuousMap.toLp ∞ (volume : Measure (Torus 3)) ℂ (literalComponentSymbol v hv j)) f,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (volume : Measure (Torus 3))
      (literalComponentSymbol v hv j)] with x h1 h2
  rw [literalComponentMul, h1, h2]
  rfl

/-! ## The commutator -/

/-- The Friedrichs commutator `K_δ = ∑_j (∂_j J_δ (v_j ·) − v_j ∂_j J_δ)` of the mollifier with
the transport term in divergence form. -/
def friedrichsCommutator (v : Torus 3 → R3) (hv : Continuous v) (δ : ℝ) :
    LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  ∑ j : Fin 3, ((literalMollifyDeriv δ j).comp (literalComponentMul v hv j) -
    (literalComponentMul v hv j).comp (literalMollifyDeriv δ j))

/-- The commutator as an average of commutators of translations and multiplications:
`K_δ f = ∑_j ∫ ∂_jρ_δ(z) (τ_z (v_j f) − v_j τ_z f) dz`. -/
theorem friedrichsCommutator_apply (v : Torus 3 → R3) (hv : Continuous v) (δ : ℝ)
    (f : LiteralC3L2) :
    friedrichsCommutator v hv δ f =
      ∑ j : Fin 3, ∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
        (literalTranslate z (literalComponentMul v hv j f) -
          literalComponentMul v hv j (literalTranslate z f)) := by
  rw [friedrichsCommutator, sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hk := integrable_fderiv_mollifierKernel_apply δ (EuclideanSpace.single j 1)
  rw [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, literalMollifyDeriv, kernelTranslateIntegral_apply,
    kernelTranslateIntegral_apply,
    ← (literalComponentMul v hv j).integral_comp_comm
      (integrable_kernel_smul_literalTranslate hk f),
    ← integral_sub (integrable_kernel_smul_literalTranslate hk _)]
  · refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only [map_smul, smul_sub]
  · exact ((literalComponentMul v hv j).integrable_comp
      (integrable_kernel_smul_literalTranslate hk f))

/-! ## The uniform bound -/

/-- Translation by the class of `z` moves a point of the torus by at most `‖z‖`. -/
theorem dist_sub_literalTorusPoint_le (x : Torus 3) (z : R3) :
    dist (x - literalTorusPoint z) x ≤ ‖z‖ := by
  rw [dist_self_sub_left]
  simpa [literalTorusPoint_zero] using lipschitzWith_literalTorusPoint.dist_le_mul z 0

/-- A component of an `L`-Lipschitz velocity changes by at most `L ‖z‖` under translation by
`z`. -/
theorem abs_component_sub_le {v : Torus 3 → R3} {L : ℝ≥0} (hv : LipschitzWith L v) (j : Fin 3)
    (x : Torus 3) (z : R3) :
    |v (x - literalTorusPoint z) j - v x j| ≤ L * ‖z‖ := by
  calc |v (x - literalTorusPoint z) j - v x j|
      = ‖(v (x - literalTorusPoint z) - v x) j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖v (x - literalTorusPoint z) - v x‖ := PiLp.norm_apply_le _ j
    _ = dist (v (x - literalTorusPoint z)) (v x) := (dist_eq_norm _ _).symm
    _ ≤ L * dist (x - literalTorusPoint z) x := hv.dist_le_mul _ _
    _ ≤ L * ‖z‖ := mul_le_mul_of_nonneg_left (dist_sub_literalTorusPoint_le x z) L.2

/-- **Translations almost commute with Lipschitz multipliers**:
`‖τ_z (v_j f) − v_j τ_z f‖ ≤ L ‖z‖ ‖f‖`, since pointwise
`τ_z (v_j f) − v_j τ_z f = (v_j(· − z) − v_j) τ_z f`. -/
theorem norm_literalTranslate_componentMul_sub_le {v : Torus 3 → R3} {L : ℝ≥0}
    (hv : LipschitzWith L v) (j : Fin 3) (z : R3) (f : LiteralC3L2) :
    ‖literalTranslate z (literalComponentMul v hv.continuous j f) -
        literalComponentMul v hv.continuous j (literalTranslate z f)‖ ≤ L * ‖z‖ * ‖f‖ := by
  rw [← (literalTranslate z).norm_map f]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (literalTranslate z (literalComponentMul v hv.continuous j f))
      (literalComponentMul v hv.continuous j (literalTranslate z f)),
    literalTranslate_coe_ae z (literalComponentMul v hv.continuous j f),
    (measurePreserving_sub_literalTorusPoint z).quasiMeasurePreserving.ae
      (literalComponentMul_coe_ae v hv.continuous j f),
    literalComponentMul_coe_ae v hv.continuous j (literalTranslate z f),
    literalTranslate_coe_ae z f] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, ← h5, ← sub_smul, norm_smul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_component_sub_le hv j x z) (norm_nonneg _)

/-- A directional derivative of the kernel along a coordinate vector is bounded by the norm of
the derivative. -/
theorem abs_fderiv_mollifierKernel_single_le (δ : ℝ) (j : Fin 3) (z : R3) :
    |fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1)| ≤
      ‖fderiv ℝ (mollifierKernel δ) z‖ := by
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (mollifierKernel δ) z).le_opNorm _).trans_eq ?_
  simp

/-- **The uniform bound, pointwise in `f`**: for `δ > 0`,
`‖K_δ f‖ ≤ 3 (∫ ‖w‖ ‖Dρ₁(w)‖ dw) L ‖f‖`. -/
theorem norm_friedrichsCommutator_apply_le {v : Torus 3 → R3} {L : ℝ≥0}
    (hv : LipschitzWith L v) {δ : ℝ} (hδ : 0 < δ) (f : LiteralC3L2) :
    ‖friedrichsCommutator v hv.continuous δ f‖ ≤
      3 * (∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖) * L * ‖f‖ := by
  rw [friedrichsCommutator_apply]
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j : Fin 3, ‖∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) :
      ℝ) : ℂ) • (literalTranslate z (literalComponentMul v hv.continuous j f) -
        literalComponentMul v hv.continuous j (literalTranslate z f))‖ ≤
      (∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖) * L * ‖f‖ := fun j ↦ by
    refine (norm_integral_le_of_norm_le
      ((integrable_norm_mul_norm_fderiv_mollifierKernel δ).mul_const (L * ‖f‖))
      (Eventually.of_forall fun z ↦ ?_)).trans_eq ?_
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ ‖fderiv ℝ (mollifierKernel δ) z‖ * (L * ‖z‖ * ‖f‖) :=
            mul_le_mul (abs_fderiv_mollifierKernel_single_le δ j z)
              (norm_literalTranslate_componentMul_sub_le hv j z f) (norm_nonneg _)
              (norm_nonneg _)
        _ = ‖z‖ * ‖fderiv ℝ (mollifierKernel δ) z‖ * (L * ‖f‖) := by ring
    · rw [integral_mul_const, integral_norm_mul_norm_fderiv_mollifierKernel hδ, mul_assoc]
  refine (Finset.sum_le_sum fun j _ ↦ hj j).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The constant of the uniform bound is nonnegative. -/
theorem integral_norm_mul_norm_fderiv_mollifierKernel_nonneg :
    0 ≤ ∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖ :=
  integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **The Friedrichs commutators are uniformly bounded**: `‖K_δ‖ ≤ C` for `0 < δ ≤ 1`, with
`C = 3 L ∫ ‖w‖ ‖Dρ₁(w)‖ dw`. -/
theorem exists_norm_friedrichsCommutator_le {v : Torus 3 → R3} {L : ℝ≥0}
    (hv : LipschitzWith L v) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖friedrichsCommutator v hv.continuous δ‖ ≤ C :=
  ⟨3 * (∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖) * L, fun _ hδ _ ↦
    ContinuousLinearMap.opNorm_le_bound _
      (by have := integral_norm_mul_norm_fderiv_mollifierKernel_nonneg; positivity)
      (norm_friedrichsCommutator_apply_le hv hδ)⟩

/-! ## The divergence term -/

/-- **The divergence term vanishes**: if the lift of the Lipschitz velocity `v` is differentiable
and `div v = 0` at every point, then for every `x`,
`∑_j ∫ ∂_jρ_δ(z) (v_j(x − z) − v_j(x)) dz = ∫ ρ_δ(z) (div v)(x − z) dz = 0`, by integration by
parts in `z`. -/
theorem sum_integral_fderiv_mollifierKernel_mul_eq_zero {v : Torus 3 → R3} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hdiff : Differentiable ℝ fun a : R3 ↦ v (literalTorusPoint a))
    (hdiv : ∀ x : Torus 3, ∑ i : Fin 3, literalFDeriv v x (EuclideanSpace.single i 1) i = 0)
    (δ : ℝ) (x : Torus 3) :
    ∑ j : Fin 3, ∫ z, fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
      (v (x - literalTorusPoint z) j - v x j) = 0 := by
  obtain ⟨a₀, hx⟩ : ∃ a₀ : R3, literalTorusPoint a₀ = x :=
    ⟨_, literalTorusPoint_literalIocRepresentative x⟩
  have hpt : ∀ z, x - literalTorusPoint z = literalTorusPoint (a₀ - z) := fun z ↦ by
    rw [sub_eq_add_neg a₀, literalTorusPoint_add, literalTorusPoint_neg, hx, ← sub_eq_add_neg]
  have hℓc : Continuous fun b : R3 ↦ v (literalTorusPoint b) :=
    hv.continuous.comp continuous_literalTorusPoint
  have hℓb : ∀ b, ‖fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) b‖ ≤ L := fun b ↦ by
    simpa [Function.comp_def] using
      norm_fderiv_le_of_lipschitz ℝ (hv.comp lipschitzWith_literalTorusPoint) (x₀ := b)
  have hks := hasCompactSupport_mollifierKernel δ
  have hD : ∀ j : Fin 3, Integrable fun z ↦ mollifierKernel δ z *
      fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) (a₀ - z)
        (EuclideanSpace.single j 1) j := fun j ↦ by
    refine (integrable_mollifierKernel δ).mul_bdd ?_ (c := L) (Eventually.of_forall fun z ↦ ?_)
    · exact ((EuclideanSpace.proj j).continuous.measurable.comp
        ((measurable_fderiv_apply_const ℝ _ _).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
    · calc _ ≤ ‖fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) (a₀ - z)
              (EuclideanSpace.single j 1)‖ := PiLp.norm_apply_le _ j
        _ ≤ ‖fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) (a₀ - z)‖ *
              ‖EuclideanSpace.single j (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L := by simpa using hℓb (a₀ - z)
  have hibp : ∀ j : Fin 3,
      ∫ z, fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
        (v (x - literalTorusPoint z) j - v x j) =
      ∫ z, mollifierKernel δ z * fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) (a₀ - z)
        (EuclideanSpace.single j 1) j := fun j ↦ by
    have hw : ∀ z, HasFDerivAt (fun z : R3 ↦ v (literalTorusPoint (a₀ - z)) j - v x j)
        (-((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).comp
          (fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) (a₀ - z)))) z := fun z ↦ by
      have h := ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp z
        ((hdiff (a₀ - z)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).const_sub a₀))).sub_const (v x j)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun u ↦ ?_)
      simp
    have hwd : ∀ z, fderiv ℝ (fun z : R3 ↦ v (literalTorusPoint (a₀ - z)) j - v x j) z
        (EuclideanSpace.single j 1) = -fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) (a₀ - z)
          (EuclideanSpace.single j 1) j := fun z ↦ by
      rw [(hw z).fderiv]
      rfl
    have hwc : Continuous fun z : R3 ↦ v (literalTorusPoint (a₀ - z)) j - v x j :=
      ((EuclideanSpace.proj j).continuous.comp
        (hℓc.comp (continuous_const.sub continuous_id))).sub continuous_const
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := mollifierKernel δ) (g := fun z : R3 ↦ v (literalTorusPoint (a₀ - z)) j - v x j)
      (v := EuclideanSpace.single j 1)
      ((((contDiff_mollifierKernel δ (n := 1)).continuous_fderiv one_ne_zero).clm_apply
        continuous_const |>.mul hwc).integrable_of_hasCompactSupport
          (hks.fderiv_apply (𝕜 := ℝ) _).mul_right)
      (by simp_rw [hwd, mul_neg]; exact (hD j).neg)
      (((contDiff_mollifierKernel δ (n := 0)).continuous.mul hwc).integrable_of_hasCompactSupport
        hks.mul_right)
      (fun z _ ↦ (contDiff_mollifierKernel δ (n := 1)).differentiable one_ne_zero z)
      (fun z _ ↦ (hw z).differentiableAt)
    simp_rw [hwd, mul_neg, integral_neg, neg_inj] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only [hpt]
  rw [Finset.sum_congr rfl fun j _ ↦ hibp j, ← integral_finsetSum _ fun j _ ↦ hD j]
  simp_rw [← Finset.mul_sum]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z ↦ ?_)
  have h0 := hdiv (literalTorusPoint (a₀ - z))
  rw [literalFDeriv_literalTorusPoint] at h0
  simp [h0]

/-! ## Convergence on continuous fields -/

/-- For `δ > 0` the derivative of the kernel vanishes outside the closed ball of radius `δ`. -/
theorem fderiv_mollifierKernel_eq_zero {δ : ℝ} (hδ : 0 < δ) {z : R3} (hz : δ < ‖z‖) :
    fderiv ℝ (mollifierKernel δ) z = 0 := by
  have h : mollifierKernel δ =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact mollifierKernel_eq_zero_of_le_norm hδ hw.le
  rw [h.fderiv_eq, fderiv_const_apply]

/-- The jointly continuous field `(z, x) ↦ (v_j(x − z) − v_j(x)) g(x − z)`, whose section at `z`
represents `τ_z (v_j g) − v_j τ_z g` (`toLp_componentCommutatorField_curry`). -/
def componentCommutatorField (v : Torus 3 → R3) (hv : Continuous v) (j : Fin 3)
    (g : C(Torus 3, C3)) : C(R3 × Torus 3, C3) :=
  ⟨fun p ↦ ((v (p.2 - literalTorusPoint p.1) j - v p.2 j : ℝ) : ℂ) •
      g (p.2 - literalTorusPoint p.1), by
    have htr : Continuous fun p : R3 × Torus 3 ↦ p.2 - literalTorusPoint p.1 :=
      continuous_snd.sub (continuous_literalTorusPoint.comp continuous_fst)
    exact (Complex.continuous_ofReal.comp
      (((EuclideanSpace.proj j).continuous.comp (hv.comp htr)).sub
        ((EuclideanSpace.proj j).continuous.comp (hv.comp continuous_snd)))).smul
      (g.continuous.comp htr)⟩

/-- On a continuous field, `τ_z (v_j g) − v_j τ_z g` is the class of the section at `z` of
`componentCommutatorField`. -/
theorem toLp_componentCommutatorField_curry (v : Torus 3 → R3) (hv : Continuous v) (j : Fin 3)
    (g : C(Torus 3, C3)) (z : R3) :
    ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
        ((componentCommutatorField v hv j g).curry z) =
      literalTranslate z (literalComponentMul v hv j
          (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)) -
        literalComponentMul v hv j
          (literalTranslate z (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)) := by
  set G := ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g
  refine Lp.ext ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (Torus 3))
      ((componentCommutatorField v hv j g).curry z),
    Lp.coeFn_sub (literalTranslate z (literalComponentMul v hv j G))
      (literalComponentMul v hv j (literalTranslate z G)),
    literalTranslate_coe_ae z (literalComponentMul v hv j G),
    (measurePreserving_sub_literalTorusPoint z).quasiMeasurePreserving.ae
      (literalComponentMul_coe_ae v hv j G),
    (measurePreserving_sub_literalTorusPoint z).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (Torus 3)) g),
    literalComponentMul_coe_ae v hv j (literalTranslate z G),
    literalTranslate_coe_ae z G] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, Pi.sub_apply, h3, h4, h6, h7, h5, ← sub_smul, ← Complex.ofReal_sub]
  rfl

/-- The kernel-weighted sections of a jointly continuous field form an integrable family of
continuous fields. -/
theorem integrable_kernel_smul_curry (δ : ℝ) (j : Fin 3) (H : C(R3 × Torus 3, C3)) :
    Integrable fun z : R3 ↦
      ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) • H.curry z := by
  have hk : Continuous fun z : R3 ↦
      ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (((contDiff_mollifierKernel δ (n := 1)).continuous_fderiv
      one_ne_zero).clm_apply continuous_const)
  have hks : HasCompactSupport fun z : R3 ↦
      ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) :=
    ((hasCompactSupport_mollifierKernel δ).fderiv_apply (𝕜 := ℝ) _).comp_left
      Complex.ofReal_zero
  have hH : Continuous fun z : R3 ↦ H.curry z := H.curry.continuous
  exact (hk.smul hH).integrable_of_hasCompactSupport (hks.smul_right (f' := fun z ↦ H.curry z))

/-- On a continuous field the commutator is the class of a continuous field, the average of the
sections of `componentCommutatorField` taken in the space of continuous fields. -/
theorem friedrichsCommutator_toLp (v : Torus 3 → R3) (hv : Continuous v) (δ : ℝ)
    (g : C(Torus 3, C3)) :
    friedrichsCommutator v hv δ (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) =
      ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ (∑ j : Fin 3, ∫ z,
        ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
          (componentCommutatorField v hv j g).curry z) := by
  rw [friedrichsCommutator_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_kernel_smul_curry δ j _)]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  simp only [map_smul, toLp_componentCommutatorField_curry]

/-- Pointwise values of the average of `componentCommutatorField`. -/
theorem sum_integral_kernel_smul_curry_apply (v : Torus 3 → R3) (hv : Continuous v) (δ : ℝ)
    (g : C(Torus 3, C3)) (x : Torus 3) :
    (∑ j : Fin 3, ∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
        (componentCommutatorField v hv j g).curry z) x =
      ∑ j : Fin 3, ∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
        ((v (x - literalTorusPoint z) j - v x j : ℝ) : ℂ) • g (x - literalTorusPoint z) := by
  rw [ContinuousMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← ContinuousMap.evalCLM_apply (R := ℂ),
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_kernel_smul_curry δ j _)]
  rfl

/-- **The commutator on a continuous field, pointwise.**  If `‖g(x − z) − g(x)‖ ≤ η` for
`‖z‖ < ρ` and `δ < ρ`, then, the divergence term vanishing
(`sum_integral_fderiv_mollifierKernel_mul_eq_zero`),
`‖∑_j ∫ ∂_jρ_δ(z) (v_j(x − z) − v_j(x)) g(x − z) dz‖ ≤ 3 (∫ ‖w‖ ‖Dρ₁(w)‖ dw) L η`. -/
theorem norm_sum_integral_commutatorField_le {v : Torus 3 → R3} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hdiff : Differentiable ℝ fun a : R3 ↦ v (literalTorusPoint a))
    (hdiv : ∀ x : Torus 3, ∑ i : Fin 3, literalFDeriv v x (EuclideanSpace.single i 1) i = 0)
    (g : C(Torus 3, C3)) (x : Torus 3) {δ ρ η : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (hg : ∀ z : R3, ‖z‖ < ρ → ‖g (x - literalTorusPoint z) - g x‖ ≤ η) :
    ‖∑ j : Fin 3, ∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
        ((v (x - literalTorusPoint z) j - v x j : ℝ) : ℂ) • g (x - literalTorusPoint z)‖ ≤
      3 * ((∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖) * (L * η)) := by
  have htr : Continuous fun z : R3 ↦ x - literalTorusPoint z :=
    continuous_const.sub continuous_literalTorusPoint
  have hc : ∀ j : Fin 3, Continuous fun z : R3 ↦
      fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
        (v (x - literalTorusPoint z) j - v x j) := fun j ↦
    (((contDiff_mollifierKernel δ (n := 1)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).mul
      (((EuclideanSpace.proj j).continuous.comp (hv.continuous.comp htr)).sub continuous_const)
  have hcs : ∀ j : Fin 3, HasCompactSupport fun z : R3 ↦
      fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
        (v (x - literalTorusPoint z) j - v x j) := fun j ↦
    ((hasCompactSupport_mollifierKernel δ).fderiv_apply (𝕜 := ℝ) _).mul_right
  have hgc : Continuous fun z : R3 ↦ g (x - literalTorusPoint z) - g x :=
    (g.continuous.comp htr).sub continuous_const
  have hj : ∀ j : Fin 3,
      ∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
        ((v (x - literalTorusPoint z) j - v x j : ℝ) : ℂ) • g (x - literalTorusPoint z) =
      (∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
          (v (x - literalTorusPoint z) j - v x j) : ℝ) : ℂ) •
            (g (x - literalTorusPoint z) - g x)) +
        ((∫ z, fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
          (v (x - literalTorusPoint z) j - v x j) : ℝ) : ℂ) • g x := fun j ↦ by
    have hcc := Complex.continuous_ofReal.comp (hc j)
    have hccs := (hcs j).comp_left Complex.ofReal_zero
    have I1 : Integrable fun z : R3 ↦
        ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
          (v (x - literalTorusPoint z) j - v x j) : ℝ) : ℂ) •
            (g (x - literalTorusPoint z) - g x) :=
      (hcc.smul hgc).integrable_of_hasCompactSupport hccs.smul_right
    have I2 : Integrable fun z : R3 ↦
        ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
          (v (x - literalTorusPoint z) j - v x j) : ℝ) : ℂ) • g x :=
      (hcc.smul continuous_const).integrable_of_hasCompactSupport hccs.smul_right
    rw [← integral_complex_ofReal, ← integral_smul_const, ← integral_add I1 I2]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    dsimp only
    rw [smul_smul, ← Complex.ofReal_mul, ← smul_add, sub_add_cancel]
  rw [Finset.sum_congr rfl fun j _ ↦ hj j, Finset.sum_add_distrib, ← Finset.sum_smul,
    ← Complex.ofReal_sum, sum_integral_fderiv_mollifierKernel_mul_eq_zero hv hdiff hdiv,
    Complex.ofReal_zero, zero_smul, add_zero]
  refine (norm_sum_le _ _).trans ?_
  have hbound : ∀ j : Fin 3,
      ‖∫ z, ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) *
          (v (x - literalTorusPoint z) j - v x j) : ℝ) : ℂ) •
            (g (x - literalTorusPoint z) - g x)‖ ≤
        (∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖) * (L * η) := fun j ↦ by
    refine (norm_integral_le_of_norm_le
      ((integrable_norm_mul_norm_fderiv_mollifierKernel δ).mul_const (L * η))
      (Eventually.of_forall fun z ↦ ?_)).trans_eq ?_
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      by_cases hz : ‖z‖ < ρ
      · calc _ ≤ ‖fderiv ℝ (mollifierKernel δ) z‖ * (L * ‖z‖) * η :=
              mul_le_mul (mul_le_mul (abs_fderiv_mollifierKernel_single_le δ j z)
                (abs_component_sub_le hv j x z) (abs_nonneg _) (norm_nonneg _)) (hg z hz)
                (norm_nonneg _) (by positivity)
          _ = ‖z‖ * ‖fderiv ℝ (mollifierKernel δ) z‖ * (L * η) := by ring
      · rw [fderiv_mollifierKernel_eq_zero hδ (hδρ.trans_le (not_lt.1 hz))]
        simp only [zero_apply, abs_zero, zero_mul, norm_zero, mul_zero]
        positivity
    · rw [integral_mul_const, integral_norm_mul_norm_fderiv_mollifierKernel hδ]
  refine (Finset.sum_le_sum fun j _ ↦ hbound j).trans_eq ?_
  simp

/-- **Convergence on continuous fields**: `K_δ g → 0` as `δ ↓ 0` for every continuous field `g`. -/
theorem tendsto_friedrichsCommutator_toLp {v : Torus 3 → R3} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hdiff : Differentiable ℝ fun a : R3 ↦ v (literalTorusPoint a))
    (hdiv : ∀ x : Torus 3, ∑ i : Fin 3, literalFDeriv v x (EuclideanSpace.single i 1) i = 0)
    (g : C(Torus 3, C3)) :
    Tendsto (fun δ : ℝ ↦ friedrichsCommutator v hv.continuous δ
      (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)) (𝓝[>] 0) (𝓝 0) := by
  set C₁ := ∫ w : R3, ‖w‖ * ‖fderiv ℝ (mollifierKernel 1) w‖
  set T := ‖(ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ :
    C(Torus 3, C3) →L[ℂ] LiteralC3L2)‖
  have hC₁ : 0 ≤ C₁ := integral_norm_mul_norm_fderiv_mollifierKernel_nonneg
  have hT : 0 ≤ T := by positivity
  have hB : 0 ≤ T * (3 * (C₁ * L)) := by positivity
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η := ε / (2 * (T * (3 * (C₁ * L)) + 1))
  have hη : 0 < η := by positivity
  obtain ⟨ρ, hρ, hgρ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous g.continuous) η hη
  refine ⟨ρ, hρ, fun δ hδ hδρ ↦ ?_⟩
  have hδ : 0 < δ := hδ
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ] at hδρ
  rw [dist_zero_right, friedrichsCommutator_toLp]
  have hbound : ‖∑ j : Fin 3, ∫ z,
      ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
        (componentCommutatorField v hv.continuous j g).curry z‖ ≤ 3 * (C₁ * (L * η)) := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ ?_
    rw [sum_integral_kernel_smul_curry_apply]
    refine norm_sum_integral_commutatorField_le hv hdiff hdiv g x hδ hδρ fun z hz ↦ ?_
    rw [← dist_eq_norm]
    exact (hgρ ((dist_sub_literalTorusPoint_le x z).trans_lt hz)).le
  calc _ ≤ T * ‖∑ j : Fin 3, ∫ z,
        ((fderiv ℝ (mollifierKernel δ) z (EuclideanSpace.single j 1) : ℝ) : ℂ) •
          (componentCommutatorField v hv.continuous j g).curry z‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ T * (3 * (C₁ * (L * η))) := mul_le_mul_of_nonneg_left hbound hT
    _ = T * (3 * (C₁ * L)) * ε / (2 * (T * (3 * (C₁ * L)) + 1)) := by
        simp only [η]
        ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

/-! ## The Friedrichs commutator lemma -/

/-- **The Friedrichs commutator lemma** (DiPerna–Lions, Lemma II.1, for `p = 2` on the torus): for
a Lipschitz velocity `v` whose lift is differentiable with `div v = 0` at every point,
`K_δ f → 0` in `L²` as `δ ↓ 0`, uniformly for `f` in a compact set `K`.  It holds on continuous
fields (`tendsto_friedrichsCommutator_toLp`); continuous fields are dense, and the uniform bound
`exists_norm_friedrichsCommutator_le` carries the convergence to a finite cover of `K` by small
balls centred at continuous fields. -/
theorem tendsto_friedrichsCommutator {v : Torus 3 → R3} {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdiff : Differentiable ℝ fun a : R3 ↦ v (literalTorusPoint a))
    (hdiv : ∀ x : Torus 3, ∑ i : Fin 3, literalFDeriv v x (EuclideanSpace.single i 1) i = 0)
    {K : Set LiteralC3L2} (hK : IsCompact K) :
    TendstoUniformlyOn (fun δ f ↦ friedrichsCommutator v hv.continuous δ f) (fun _ ↦ 0)
      (𝓝[>] 0) K := by
  obtain ⟨C, hC⟩ := exists_norm_friedrichsCommutator_le hv
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set r := ε / (2 * (|C| + 1))
  have hr : 0 < r := by positivity
  have hCr : |C| * r ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [abs_nonneg C]
  have hdense := ContinuousMap.toLp_denseRange C3 (volume : Measure (Torus 3)) ℂ
    (p := 2) (by simp)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun g : C(Torus 3, C3) ↦
      Metric.ball (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) r)
    (fun _ ↦ Metric.isOpen_ball) fun f _ ↦ by
      obtain ⟨g, hg⟩ := Metric.denseRange_iff.1 hdense f r hr
      exact Set.mem_iUnion.2 ⟨g, Metric.mem_ball.2 hg⟩
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioc 0 1 ∧ ∀ g ∈ t,
      ‖friedrichsCommutator v hv.continuous δ
        (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)‖ < ε / 2 := by
    have h01 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioc 0 1 := Ioc_mem_nhdsGT one_pos
    refine h01.and ((Finset.eventually_all t).2 fun g _ ↦ ?_)
    filter_upwards [(tendsto_friedrichsCommutator_toLp hv hdiff hdiv g).eventually
      (Metric.ball_mem_nhds 0 (half_pos hε))] with δ hδ
    rwa [dist_zero_right] at hδ
  filter_upwards [hev] with δ hδ f hf
  obtain ⟨g, hgt, hfg⟩ : ∃ g ∈ t,
      f ∈ Metric.ball (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) r := by
    simpa using ht hf
  rw [dist_zero_left]
  have hsplit : friedrichsCommutator v hv.continuous δ f =
      friedrichsCommutator v hv.continuous δ
          (f - ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) +
        friedrichsCommutator v hv.continuous δ
          (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) := by
    rw [map_sub, sub_add_cancel]
  rw [hsplit]
  refine (norm_add_le _ _).trans_lt ?_
  have h1 : ‖friedrichsCommutator v hv.continuous δ
      (f - ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)‖ ≤ |C| * r :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
      ((hC δ hδ.1.1 hδ.1.2).trans (le_abs_self C))
      (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hfg).le) (norm_nonneg _)
      (abs_nonneg C))
  linarith [hδ.2 g hgt]

end

end FastDynamo
