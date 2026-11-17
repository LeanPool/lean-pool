/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.L2.Transport
public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Isometry
public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Translation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Linear change of variables for the covariance relaxation

Source: Blueprint `thm:affine-isotropic-reduction`, the sentence "whiten the centered intrinsic law
by `Cov^{-1/2}`; pullback of the isotropic inequality gives the covariance-form inequality". Read
`gradient_comp_continuousLinearEquiv`, `Covariance.operator_map_continuousLinearEquiv`,
`KLS.LogConcave.mapContinuousLinearEquiv`, `L2.ContinuousLinearEquiv.pullbackEquiv`,
`L2.ContinuousLinearEquiv.variance_pullbackEquiv`,
`Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv`,
`Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv` and
`Probability.affineSupport_mapContinuousLinearEquiv`.

For a probability law `ν` on a finite-dimensional Euclidean space `V₁` and a continuous linear
equivalence `T : V₁ ≃L[ℝ] V₂`, the image law `KLS.LogConcave.mapContinuousLinearEquiv ν T` lives on
`V₂`. Its covariance
operator is `T ∘ Σ ∘ T†` with `T†` the adjoint; the gradient of `g ∘ T` is `T† ∇g ∘ T`; composition
with `T` is a linear isometric equivalence `L²(KLS.LogConcave.mapContinuousLinearEquiv ν T) ≃ L²(ν)`
(because `T` is measure
preserving between the two laws) which preserves variance; globally Lipschitz covariance tests
correspond by composition with equal covariance energies, since
`⟪T Σ T† w, w⟫ = ⟪Σ T† w, T† w⟫`; hence the covariance relaxations correspond under the isometry and
the optimal `L²` Poincaré constants of the two relaxations coincide. The affine support of the
image law is the image of the affine support.

This is the non-isometric generalization of `CovarianceGradient/Isometry.lean`; the isometric
module is retained as the certified special case used for translation invariance. Everything holds
for every Borel probability law; no log-concavity, density or closability is used, and no Poincaré
inequality is asserted. The zero-dimensional spaces are included.
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

/-- The gradient of a function composed with a continuous linear equivalence is the adjoint image
of the gradient at the image point. No differentiability premise is needed. -/
theorem gradient_comp_continuousLinearEquiv (g : V₂ → ℝ) (T : V₁ ≃L[ℝ] V₂) (x : V₁) :
    gradient (fun y ↦ g (T y)) x = (T : V₁ →L[ℝ] V₂).adjoint (gradient g (T x)) := by
  apply (toDual ℝ V₁).injective
  rw [toDual_gradient]
  have hcomp : fderiv ℝ (fun y ↦ g (T y)) x = (fderiv ℝ g (T x)).comp (T : V₁ →L[ℝ] V₂) := by
    have h := T.comp_right_fderiv (f := g) (x := x)
    simpa only [Function.comp_def] using h
  rw [hcomp]
  ext v
  change fderiv ℝ g (T x) (T v) = inner ℝ ((T : V₁ →L[ℝ] V₂).adjoint (gradient g (T x))) v
  rw [← toDual_gradient, toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  rfl

end Euclidean

end Gradient

section Tests

variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  [FiniteDimensional ℝ V₂] {ν₁ : ProbabilityMeasure V₁} {ν₂ : ProbabilityMeasure V₂}
  {T : V₁ ≃L[ℝ] V₂}

namespace CovarianceGradient.Test

/-- Composition of a covariance test with a measure-preserving continuous linear equivalence
between two laws whose covariance quadratic forms correspond under the adjoint. -/
def compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : Test ν₂) : Test ν₁ where
  toFun := fun x ↦ g (T x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * ‖(T : V₁ →L[ℝ] V₂)‖₊, hK.comp (T : V₁ →L[ℝ] V₂).lipschitzWith⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.aestronglyMeasurable)
      hmp.aemeasurable).mp this
  integrable := by
    have hdens : density ν₁ (fun x ↦ g (T x)) =
        density ν₂ g.toFun ∘ T := by
      funext x
      simp only [density, Function.comp_apply,
        gradient_comp_continuousLinearEquiv, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this

section EquivalentTests

omit [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [SecondCountableTopology V₂]
  [FiniteDimensional ℝ V₂]
/-- The composed test has the same covariance energy. -/
theorem energy_compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : Test ν₂) :
    (g.compContinuousLinearEquiv hmp hcov).energy = g.energy := by
  apply NNReal.eq
  simp only [coe_energy]
  have hdens : density ν₁ (g.compContinuousLinearEquiv hmp hcov).toFun =
      density ν₂ g.toFun ∘ T := by
    funext x
    simp only [compContinuousLinearEquiv, density,
      Function.comp_apply, gradient_comp_continuousLinearEquiv, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl

/-- The composed test realizes the pullback of the original class. -/
theorem toL2_compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : Test ν₂) :
    (g.compContinuousLinearEquiv hmp hcov).toL2 = Lp.compMeasurePreserving T hmp g.toL2 := by
  apply Lp.ext
  refine (g.compContinuousLinearEquiv hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm

end EquivalentTests

end CovarianceGradient.Test

end Tests

section Relaxation

variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  [FiniteDimensional ℝ V₂] (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

namespace CovarianceGradient

omit [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂] in
omit [SecondCountableTopology V₁] in
/-- The covariance relaxation of the image law is the covariance relaxation of `ν` pulled back
along `T`. -/
theorem relaxation_mapContinuousLinearEquiv
    (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    relaxation (Probability.mapContinuousLinearEquiv ν T) f =
      relaxation ν (L2.ContinuousLinearEquiv.pullbackEquiv ν T f) := by
  have hcov :
    ∀ w,
      inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) w)
          w =
        inner ℝ (Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
          ((T : V₁ →L[ℝ] V₂).adjoint w) :=
    Covariance.inner_operator_mapContinuousLinearEquiv ν T
  have hcov' :
    ∀ w,
      inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
        inner ℝ
          (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂)
            ((T.symm : V₂ →L[ℝ] V₁).adjoint w))
          ((T.symm : V₂ →L[ℝ] V₁).adjoint w) :=
    Covariance.inner_operator_mapContinuousLinearEquiv_symm ν T
  apply le_antisymm
  · have h :=
      (preEnergy ν).sequentialRelaxation_comp_le
        (preEnergy (Probability.mapContinuousLinearEquiv ν T))
        (L2.ContinuousLinearEquiv.pullbackInv ν T)
        (L2.ContinuousLinearEquiv.pullbackInv ν T).continuous ?_
        (L2.ContinuousLinearEquiv.pullbackEquiv ν T f)
    · rw [L2.ContinuousLinearEquiv.pullbackEquiv_apply,
        L2.ContinuousLinearEquiv.pullbackInv_pullback] at h
      exact h
    · intro g
      refine
        ⟨g.compContinuousLinearEquiv
            (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T) hcov',
          ?_, le_of_eq ?_⟩
      · exact g.toL2_compContinuousLinearEquiv _ _
      · exact g.energy_compContinuousLinearEquiv _ _
  · have h :=
      (preEnergy (Probability.mapContinuousLinearEquiv ν T)).sequentialRelaxation_comp_le
        (preEnergy ν) (L2.ContinuousLinearEquiv.pullback ν T)
        (L2.ContinuousLinearEquiv.pullback ν T).continuous ?_ f
    · exact h
    · intro g
      refine
        ⟨g.compContinuousLinearEquiv
            (Probability.measurePreserving_mapContinuousLinearEquiv ν T) hcov,
          ?_, le_of_eq ?_⟩
      · exact g.toL2_compContinuousLinearEquiv _ _
      · exact g.energy_compContinuousLinearEquiv _ _

end CovarianceGradient

end Relaxation

end FunctionalInequalities.Energy
