/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Decay
public import LeanPool.VacuumBellSeparation.FreeField.Statements
public import LeanPool.VacuumBellSeparation.Weyl.Existence
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Existence of the free-field vacuum system (non-vacuity)

For every mass `m > 0` a vacuum Weyl system `FreeFieldVacuum m H` exists:

* `RealTestFunction` is an additive commutative group (with the existing `+`);
* `oneParticleMeasure m` is the Lorentz-invariant measure `d³p / (2(2π)³ ω_m(𝐩))` and
  `oneParticleL2 hm F ∈ L²(ℝ³, d𝔪_m)` is the class of the one-particle wave function `κ_m F`;
* `oneParticleL2_add`, `inner_oneParticleL2`: this map is additive and its inner product is
  `oneParticleInner`;
* `freeFieldVacuum_exists : FreeFieldVacuumExists`, from the abstract Weyl-system existence
  theorem `exists_weyl_system` applied to `oneParticleL2 hm`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-! ### The additive group of real test functions -/

instance : Zero RealTestFunction where
  zero := ⟨0, contDiff_const,
    HasCompactSupport.zero⟩

instance : Neg RealTestFunction where
  neg F := ⟨-F.1, F.2.1.neg, F.2.2.neg⟩

instance : AddCommGroup RealTestFunction where
  add_assoc F G K := Subtype.ext (add_assoc F.1 G.1 K.1)
  zero_add F := Subtype.ext (zero_add F.1)
  add_zero F := Subtype.ext (add_zero F.1)
  nsmul := nsmulRec
  neg_add_cancel F := Subtype.ext (neg_add_cancel F.1)
  zsmul := zsmulRec
  add_comm F G := Subtype.ext (add_comm F.1 G.1)

/-! ### The one-particle space `L²(ℝ³, d𝔪_m)` -/

theorem oneParticleWeightReal_pos {m : ℝ} (hm : 0 < m) (p : EuclideanSpace ℝ (Fin 3)) :
    0 < 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) := by
  have hc : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  exact one_div_pos.2 (mul_pos hc (hm.trans_le (le_dispersion hm.le p)))

theorem continuous_oneParticleWeightReal {m : ℝ} (hm : 0 < m) :
    Continuous fun p : EuclideanSpace ℝ (Fin 3) =>
      1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) := by
  have hc : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  exact continuous_const.div (continuous_const.mul (continuous_dispersion m))
    fun p => (mul_pos hc (hm.trans_le (le_dispersion hm.le p))).ne'

/-- The density `1 / (2(2π)³ ω_m(𝐩))` of the Lorentz-invariant measure, `ℝ≥0`-valued. -/
noncomputable def oneParticleWeight (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : NNReal :=
  Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p))

theorem oneParticleWeight_coe {m : ℝ} (hm : 0 < m) (p : EuclideanSpace ℝ (Fin 3)) :
    (oneParticleWeight m p : ℝ) = 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) :=
  Real.coe_toNNReal _ (oneParticleWeightReal_pos hm p).le

theorem measurable_oneParticleWeight {m : ℝ} (hm : 0 < m) :
    Measurable (oneParticleWeight m) :=
  (continuous_real_toNNReal.comp (continuous_oneParticleWeightReal hm)).measurable

/-- The Lorentz-invariant measure `d𝔪_m = d³p / (2(2π)³ ω_m(𝐩))` on momentum space. -/
noncomputable def oneParticleMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  Measure.withDensity (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    fun p => (oneParticleWeight m p : ENNReal)

theorem memLp_oneParticle {m : ℝ} (hm : 0 < m) (F : RealTestFunction) :
    MemLp (oneParticle m F) 2 (oneParticleMeasure m) := by
  have hmeas : AEStronglyMeasurable (oneParticle m F) (oneParticleMeasure m) :=
    (continuous_oneParticle m F).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas, oneParticleMeasure,
    integrable_withDensity_iff_integrable_smul (measurable_oneParticleWeight hm)]
  refine (integrable_oneParticleInner_integrand hm F F).norm.congr
    (Filter.Eventually.of_forall fun p => ?_)
  have hw := oneParticleWeightReal_pos hm p
  change ‖conj (oneParticle m F p) * oneParticle m F p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)‖ =
    oneParticleWeight m p • ‖oneParticle m F p‖ ^ 2
  first
  | (rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw, NNReal.smul_def, smul_eq_mul, oneParticleWeight_coe hm p]
     ring)

/-- The one-particle wave function `κ_m F` as an element of `L²(ℝ³, d𝔪_m)`. -/
noncomputable def oneParticleL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction) :
    Lp ℂ 2 (oneParticleMeasure m) :=
  (memLp_oneParticle hm F).toLp (oneParticle m F)

theorem coeFn_oneParticleL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction) :
    (oneParticleL2 hm F : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[oneParticleMeasure m]
      oneParticle m F :=
  (memLp_oneParticle hm F).coeFn_toLp

/-- `κ_m(F + G) = κ_m F + κ_m G` in `L²(ℝ³, d𝔪_m)`. -/
theorem oneParticleL2_add {m : ℝ} (hm : 0 < m) (F G : RealTestFunction) :
    oneParticleL2 hm (F + G) = oneParticleL2 hm F + oneParticleL2 hm G :=
  (MemLp.toLp_congr (memLp_oneParticle hm (F + G))
      ((memLp_oneParticle hm F).add (memLp_oneParticle hm G))
      (Filter.Eventually.of_forall fun p => oneParticle_add m F G p)).trans
    (MemLp.toLp_add (memLp_oneParticle hm F) (memLp_oneParticle hm G))

/-- The `L²(ℝ³, d𝔪_m)` inner product of one-particle wave functions is `oneParticleInner`. -/
theorem inner_oneParticleL2 {m : ℝ} (hm : 0 < m) (F G : RealTestFunction) :
    ⟪oneParticleL2 hm F, oneParticleL2 hm G⟫_ℂ = oneParticleInner m F G := by
  refine (L2.inner_def (𝕜 := ℂ) _ _).trans ?_
  refine (integral_congr_ae (g := fun p => conj (oneParticle m F p) * oneParticle m G p)
    ?_).trans ?_
  · filter_upwards [coeFn_oneParticleL2 hm F, coeFn_oneParticleL2 hm G] with p hpF hpG
    first
    | (rw [hpF, hpG]; exact RCLike.inner_apply' _ _)
  · rw [oneParticleMeasure,
      integral_withDensity_eq_integral_smul (measurable_oneParticleWeight hm)]
    unfold oneParticleInner
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change oneParticleWeight m p • (conj (oneParticle m F p) * oneParticle m G p) =
      conj (oneParticle m F p) * oneParticle m G p *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)
    first
    | (rw [NNReal.smul_def, Complex.real_smul, oneParticleWeight_coe hm p]; ring)

/-- `‖κ_m F‖² = Re ⟨κ_m F, κ_m F⟩`. -/
theorem norm_oneParticleL2_sq {m : ℝ} (hm : 0 < m) (F : RealTestFunction) :
    ‖oneParticleL2 hm F‖ ^ 2 = (oneParticleInner m F F).re := by
  rw [← inner_oneParticleL2 hm F F]
  first
  | exact (inner_self_eq_norm_sq (𝕜 := ℂ) (oneParticleL2 hm F)).symm

/-! ### Existence of the vacuum system -/

/-- **Non-vacuity**: for every mass `m > 0` a vacuum Weyl system of the free field exists. -/
theorem freeFieldVacuum_exists : FreeFieldVacuumExists := by
  intro m hm
  obtain ⟨H, i1, i2, i3, W, Ω, hU, hmul, hΩ, hvac, hcyc⟩ :=
    exists_weyl_system (X := RealTestFunction) (oneParticleL2 hm) (oneParticleL2_add hm)
  have hmul' : ∀ F G : RealTestFunction, W F * W G =
      Complex.exp (-(Complex.I * ((oneParticleInner m F G).im : ℂ))) • W (F + G) := by
    intro F G
    rw [← inner_oneParticleL2 hm F G]
    exact hmul F G
  have hvac' : ∀ F : RealTestFunction,
      ⟪Ω, W F Ω⟫_ℂ = ((Real.exp (-((oneParticleInner m F F).re / 2)) : ℝ) : ℂ) := by
    intro F
    rw [← norm_oneParticleL2_sq hm F]
    exact hvac F
  exact ⟨H, i1, i2, i3, ⟨⟨W, Ω, hU, hmul', hΩ, hvac', hcyc⟩⟩⟩

end VacuumBellSeparation
