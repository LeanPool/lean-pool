/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.L2.Transport
public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Translation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometric transport of the covariance relaxation

Source: Blueprint `lem:affine-poincare-translation-invariance`, the sentence "translation preserves
covariance and identifies the two intrinsic laws by an `L²` isometry". Read
`Probability.mapLinearIsometryEquiv`,
`Covariance.operator_mapLinearIsometryEquiv`, `gradient_comp_linearIsometryEquiv`, `mapL2`,
`L2.LinearIsometry.variance_pullbackEquiv`,
`Energy.CovarianceGradient.relaxation_mapLinearIsometryEquiv` and
`Poincare.CovarianceGradient.constant_mapLinearIsometryEquiv`.

For a probability law `ν` on a finite-dimensional Euclidean space `V₁` and a linear isometric
equivalence `L : V₁ ≃ₗᵢ[ℝ] V₂`, the image law `Probability.mapLinearIsometryEquiv ν L` lives on
`V₂`. Its covariance operator
is the conjugate `L ∘ Σ ∘ L⁻¹` of the covariance operator `Σ` of `ν`; the gradient of `g ∘ L` is
`L⁻¹ ∇g ∘ L`; composition with `L` is a linear isometric equivalence
`L²(Probability.mapLinearIsometryEquiv ν L) ≃ L²(ν)`
preserving variance; globally Lipschitz covariance tests correspond by composition with equal
covariance energies; hence the covariance relaxations correspond under the isometry and the optimal
`L²` Poincaré constants of the two relaxations coincide.

Together with `Energy/CovarianceGradient/Translation.lean` this covers every affine isometric
change of
intrinsic coordinates, in two steps: a linear isometric equivalence of the direction spaces followed
by a translation. Everything holds for every Borel probability law; no log-concavity, density or
closability is used, and no Poincaré inequality is asserted. The zero-dimensional spaces are
included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities.Energy

open Energy.Euclidean

universe u v

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]

section Gradient

namespace Euclidean

/-- The gradient of a function composed with a linear isometric equivalence is the inverse image
of the gradient at the image point. No differentiability premise is needed: both sides vanish
simultaneously at points of nondifferentiability. -/
theorem gradient_comp_linearIsometryEquiv (g : V₂ → ℝ) (L : V₁ ≃ₗᵢ[ℝ] V₂) (x : V₁) :
    gradient (fun y ↦ g (L y)) x = L.symm (gradient g (L x)) := by
  apply (toDual ℝ V₁).injective
  rw [toDual_gradient]
  have hcomp : fderiv ℝ (fun y ↦ g (L y)) x =
      (fderiv ℝ g (L x)).comp (L.toContinuousLinearEquiv : V₁ →L[ℝ] V₂) := by
    have h := L.toContinuousLinearEquiv.comp_right_fderiv (f := g) (x := x)
    simpa only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h
  rw [hcomp]
  ext v
  change fderiv ℝ g (L x) (L.toContinuousLinearEquiv v) = inner ℝ (L.symm (gradient g (L x))) v
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ← toDual_gradient, toDual_apply_apply]
  calc inner ℝ (gradient g (L x)) (L v)
      = inner ℝ (L (L.symm (gradient g (L x)))) (L v) := by rw [L.apply_symm_apply]
    _ = inner ℝ (L.symm (gradient g (L x))) v := L.inner_map_map _ _

end Euclidean

end Gradient

section Tests

variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  [FiniteDimensional ℝ V₂] {ν₁ : ProbabilityMeasure V₁} {ν₂ : ProbabilityMeasure V₂}
  {L : V₁ ≃ₗᵢ[ℝ] V₂}

namespace CovarianceGradient.Test

/-- Composition of a covariance test with a measure-preserving linear isometric equivalence
between two laws whose covariance quadratic forms correspond under `L`. -/
def compLinearIsometryEquiv
    (hmp : MeasurePreserving L (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) (L.symm w)) (L.symm w))
    (g : Test ν₂) : Test ν₁ where
  toFun := fun x ↦ g (L x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * 1, hK.comp L.lipschitzWith⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.aestronglyMeasurable)
      hmp.aemeasurable).mp this
  integrable := by
    have hdens : density ν₁ (fun x ↦ g (L x)) =
        density ν₂ g.toFun ∘ L := by
      funext x
      simp only [density, Function.comp_apply,
        gradient_comp_linearIsometryEquiv, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this

section IsometricTests

omit [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [SecondCountableTopology V₂]
  [FiniteDimensional ℝ V₂]
/-- The composed test has the same covariance energy. -/
theorem energy_compLinearIsometryEquiv
    (hmp : MeasurePreserving L (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) (L.symm w)) (L.symm w))
    (g : Test ν₂) :
    (g.compLinearIsometryEquiv hmp hcov).energy = g.energy := by
  apply NNReal.eq
  simp only [coe_energy]
  have hdens : density ν₁ (g.compLinearIsometryEquiv hmp hcov).toFun =
      density ν₂ g.toFun ∘ L := by
    funext x
    simp only [compLinearIsometryEquiv, density,
      Function.comp_apply, gradient_comp_linearIsometryEquiv, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl

/-- The composed test realizes the pullback of the original class. -/
theorem toL2_compLinearIsometryEquiv
    (hmp : MeasurePreserving L (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) (L.symm w)) (L.symm w))
    (g : Test ν₂) :
    (g.compLinearIsometryEquiv hmp hcov).toL2 = Lp.compMeasurePreserving L hmp g.toL2 := by
  apply Lp.ext
  refine (g.compLinearIsometryEquiv hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm

end IsometricTests

end CovarianceGradient.Test

end Tests

section Relaxation

variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  [FiniteDimensional ℝ V₂] (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

namespace CovarianceGradient

omit [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂] in
omit [SecondCountableTopology V₁] in
/-- The covariance relaxation of the image law is the covariance relaxation of `ν` pulled back
along `L`. -/
theorem relaxation_mapLinearIsometryEquiv
    (f : Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂)) :
    relaxation (Probability.mapLinearIsometryEquiv ν L) f =
      relaxation ν (L2.LinearIsometry.pullbackEquiv ν L f) := by
  have hcov :
    ∀ w,
      inner ℝ (Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) w) w =
        inner ℝ (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w) :=
    Covariance.inner_operator_mapLinearIsometryEquiv ν L
  have hcov' :
    ∀ w,
      inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
        inner ℝ
          (Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂)
            (L.symm.symm w))
          (L.symm.symm w) := by
    intro w
    rw [LinearIsometryEquiv.symm_symm]
    exact Covariance.inner_operator_mapLinearIsometryEquiv_apply ν L w
  apply le_antisymm
  · have h :=
      (preEnergy ν).sequentialRelaxation_comp_le
        (preEnergy (Probability.mapLinearIsometryEquiv ν L)) (L2.LinearIsometry.pullbackInv ν L)
        (L2.LinearIsometry.pullbackInv ν L).continuous ?_
        (L2.LinearIsometry.pullbackEquiv ν L f)
    · rw [L2.LinearIsometry.pullbackEquiv_apply, L2.LinearIsometry.pullbackInv_pullback] at h
      exact h
    · intro g
      refine
        ⟨g.compLinearIsometryEquiv
            (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L) hcov',
          ?_, le_of_eq ?_⟩
      · exact g.toL2_compLinearIsometryEquiv _ _
      · exact g.energy_compLinearIsometryEquiv _ _
  · have h :=
      (preEnergy (Probability.mapLinearIsometryEquiv ν L)).sequentialRelaxation_comp_le
        (preEnergy ν) (L2.LinearIsometry.pullback ν L)
        (L2.LinearIsometry.pullback ν L).continuous ?_ f
    · exact h
    · intro g
      refine
        ⟨g.compLinearIsometryEquiv (Probability.measurePreserving_mapLinearIsometryEquiv ν L)
            hcov,
          ?_, le_of_eq ?_⟩
      · exact g.toL2_compLinearIsometryEquiv _ _
      · exact g.energy_compLinearIsometryEquiv _ _

end CovarianceGradient

end Relaxation

end FunctionalInequalities.Energy
