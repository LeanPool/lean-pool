/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Gauss measure and polar decomposition

The density `exp (-π ‖x‖ ^ 2)` of the Gauss measure, the fact that it is a probability density on
a finite-dimensional real inner product space, and the radius of the ball of volume one. These are
the two normalizations Vaaler's cube-slicing theorem compares: Bombieri–Gubler's Lemma C.3.7 says
that the Gauss measure of a symmetric convex set never exceeds the volume of its intersection with
a product of balls of volume one, and the base case of that induction is a comparison, ray by ray,
of these two measures of total mass one.

Alongside them, the polar decomposition of an additive Haar measure as an integral over the unit
sphere, in the `ℝ≥0∞`-valued form the comparison needs.

## Main definitions

* `gaussDensity x = ENNReal.ofReal (exp (-π * ‖x‖ ^ 2))`, the Gauss density, with the defining
  equation `gaussDensity_def`.
* `unitVolumeRadius E`, the radius `ρ` for which the ball of radius `ρ` in `E` has volume `1`.

## Main results

* `lintegral_eq_lintegral_sphere` and `lintegral_eq_lintegral_sphere'`: **polar decomposition** of
  an additive Haar measure, in product and iterated form.
* `lintegral_gaussDensity_eq_one`: `∫⁻ x, exp (-π ‖x‖ ^ 2) = 1` on a finite-dimensional real
  inner product space.
* `volume_closedBall_unitVolumeRadius`: the ball of radius `unitVolumeRadius E` has volume `1`.

## Implementation notes

⚠ **The Gaussian is normalized with `π` in the exponent precisely so that no constant survives.**
`∫_ℝ exp (-π t ^ 2) dt = 1`, so the `n`-dimensional integral is `1` for every `n` by Fubini, and the
comparison in `SliceBound.lean` can cancel the sphere measure between the two total masses instead
of evaluating either radial integral. This is what makes Bombieri–Gubler's Remark C.3.6 — the
closed form `ρ(n) = π ^ (-1/2) * Γ (n/2 + 1) ^ (1/n)` — unnecessary: `unitVolumeRadius` is defined
by the normalization it is used for, and no Gamma function appears anywhere below.

⚠ **Mathlib's polar decomposition is a measure-preserving homeomorphism, not an integral formula.**
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` identifies the Haar measure of
`E \ {0}` with `μ.toSphere.prod (volumeIoiPow (n - 1))`; the only integral formula built on it,
`integral_fun_norm_addHaar`, is for Bochner integrals of *radial* functions. The comparison below
integrates the indicator of a convex set, which is not radial, so the formula is proved here in the
raw `ℝ≥0∞` form, with no hypothesis on the integrand at all.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Remarks C.3.5 and C.3.6.

This is Layer 4.5 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open MeasureTheory Measure Set Metric ENNReal
open scoped Real

/-- The **Gauss density** `exp (-π ‖x‖ ^ 2)`, as an `ℝ≥0∞`-valued function. With `π` in the
exponent it is a probability density for every finite-dimensional real inner product space. -/
@[expose] noncomputable def gaussDensity {E : Type*} [NormedAddCommGroup E] (x : E) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))

theorem gaussDensity_def {E : Type*} [NormedAddCommGroup E] (x : E) :
    gaussDensity x = ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2)) := rfl

@[simp]
theorem gaussDensity_zero {E : Type*} [NormedAddCommGroup E] : gaussDensity (0 : E) = 1 := by
  rw [gaussDensity_def, norm_zero]
  norm_num

@[fun_prop]
theorem measurable_gaussDensity {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] : Measurable (gaussDensity : E → ℝ≥0∞) := by
  unfold gaussDensity; fun_prop

theorem gaussDensity_le_one {E : Type*} [NormedAddCommGroup E] (x : E) : gaussDensity x ≤ 1 := by
  rw [gaussDensity, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, sq_nonneg ‖x‖]

theorem gaussDensity_neg {E : Type*} [NormedAddCommGroup E] (x : E) :
    gaussDensity (-x) = gaussDensity x := by
  rw [gaussDensity, gaussDensity, norm_neg]

/-- **Polar decomposition of an additive Haar measure.** Every `ℝ≥0∞`-valued integral against an
additive Haar measure is an integral over `sphere 0 1 × Ioi 0`, with the radial factor `r ^ (n-1)`
carried by `MeasureTheory.Measure.volumeIoiPow`. No measurability hypothesis is needed. -/
theorem lintegral_eq_lintegral_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ p : sphere (0 : E) 1 × Ioi (0 : ℝ), f ((p.2 : ℝ) • (p.1 : E))
        ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  have h1 : ∫⁻ x, f x ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f x.1 ∂(μ.comap (↑)) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  rw [h1, ← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _) (fun p => f ((p.2 : ℝ) • (p.1 : E)))]
  refine lintegral_congr fun x => ?_
  have hx : (x : E) ≠ 0 := x.2
  have hn : (0 : ℝ) < ‖(x : E)‖ := by simpa using hx
  rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe, smul_smul,
    mul_inv_cancel₀ hn.ne', one_smul]

/-- **Polar decomposition**, iterated form: the inner integral is over the ray. -/
theorem lintegral_eq_lintegral_sphere' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), f ((r : ℝ) • (u : E))
        ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [lintegral_eq_lintegral_sphere μ f, lintegral_prod]
  exact (hf.comp (by fun_prop)).aemeasurable

/-- The Gauss density integrates to `1` over `ι → ℝ`: the one-dimensional Gaussian integral
`∫ exp (-π t ^ 2) = 1` and Fubini. -/
theorem lintegral_gaussian_pi (ι : Type*) [Fintype ι] :
    ∫⁻ y : ι → ℝ, ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2)) = 1 := by
  have hprod : ∀ y : ι → ℝ, Real.exp (-π * ∑ i, (y i) ^ 2) = ∏ i, Real.exp (-π * (y i) ^ 2) := by
    intro y
    rw [← Real.exp_sum, Finset.mul_sum]
  have hint : Integrable (fun y : ι → ℝ => ∏ i, Real.exp (-π * (y i) ^ 2)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq Real.pi_pos)
  have hone : (∫ t : ℝ, Real.exp (-π * t ^ 2)) = 1 := by
    rw [integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]
  have hval : ∫ y : ι → ℝ, ∏ i, Real.exp (-π * (y i) ^ 2) = 1 := by
    rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-π * t ^ 2)), hone, one_pow]
  calc ∫⁻ y : ι → ℝ, ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2))
      = ∫⁻ y : ι → ℝ, ENNReal.ofReal (∏ i, Real.exp (-π * (y i) ^ 2)) :=
        lintegral_congr fun y => by rw [hprod]
    _ = ENNReal.ofReal (∫ y : ι → ℝ, ∏ i, Real.exp (-π * (y i) ^ 2)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (.of_forall fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)).symm
    _ = 1 := by rw [hval, ENNReal.ofReal_one]

theorem lintegral_gaussDensity_euclidean (ι : Type*) [Fintype ι] :
    ∫⁻ x : EuclideanSpace ℝ ι, gaussDensity x = 1 := by
  have hm : Measurable fun y : ι → ℝ => ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2)) := by
    fun_prop
  rw [← lintegral_gaussian_pi ι, ← (PiLp.volume_preserving_ofLp ι).lintegral_comp hm]
  refine lintegral_congr fun x => ?_
  rw [gaussDensity, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp

/-- **The Gauss measure is a probability measure** on a finite-dimensional real inner product
space. -/
theorem lintegral_gaussDensity_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫⁻ x : E, gaussDensity x = 1 := by
  have hm : Measurable (gaussDensity : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞) := by
    unfold gaussDensity; fun_prop
  rw [← lintegral_gaussDensity_euclidean (Fin (Module.finrank ℝ E)),
    ← (stdOrthonormalBasis ℝ E).measurePreserving_repr.lintegral_comp hm]
  exact lintegral_congr fun x => by
    rw [gaussDensity, gaussDensity, (stdOrthonormalBasis ℝ E).repr.norm_map]

/-- The radius `ρ` of the ball of volume `1`: Bombieri–Gubler's `ρ(n)`, defined by the
normalization it is used for rather than by its closed form. -/
@[expose] noncomputable def unitVolumeRadius (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : ℝ :=
  (volume (ball (0 : E) 1)).toReal ^ (-(1 / (Module.finrank ℝ E : ℝ)))

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

theorem volume_ball_one_pos : 0 < (volume (ball (0 : E) 1)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

theorem unitVolumeRadius_pos : 0 < unitVolumeRadius E :=
  Real.rpow_pos_of_pos volume_ball_one_pos _

/-- **The ball of radius `unitVolumeRadius E` has volume one.** -/
theorem volume_closedBall_unitVolumeRadius :
    volume (closedBall (0 : E) (unitVolumeRadius E)) = 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h1 : closedBall (0 : E) (unitVolumeRadius E) = univ := by
      ext x; simp [Subsingleton.elim x (0 : E), unitVolumeRadius_pos.le]
    have hg : ∀ x : E, gaussDensity x = 1 := fun x => by
      rw [Subsingleton.elim x (0 : E), gaussDensity_zero]
    calc volume (closedBall (0 : E) (unitVolumeRadius E)) = ∫⁻ _ : E, 1 := by
          rw [lintegral_one, h1]
      _ = ∫⁻ x : E, gaussDensity x := lintegral_congr fun x => (hg x).symm
      _ = 1 := lintegral_gaussDensity_eq_one
  have hv : 0 < (volume (ball (0 : E) 1)).toReal := volume_ball_one_pos
  have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  rw [Measure.addHaar_closedBall volume 0 unitVolumeRadius_pos.le, unitVolumeRadius,
    ← Real.rpow_natCast ((volume (ball (0 : E) 1)).toReal ^ (-(1 / (Module.finrank ℝ E : ℝ))))
      (Module.finrank ℝ E),
    ← Real.rpow_mul hv.le,
    show -(1 / (Module.finrank ℝ E : ℝ)) * (Module.finrank ℝ E : ℝ) = -1 by field_simp,
    Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos hv,
    ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ENNReal.inv_mul_cancel (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne]

end
