/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.L2.Transport
public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Basic

/-!
# Translation invariance of the covariance relaxation

Source: Blueprint `thm:affine-covariance-relaxation-closed`, the sentence "changing the affine
origin translates `ν`; pullback by this translation is an `L²` isometry preserving variance and
covariance energy". Read `translateLaw`, `L2.Translation.pullbackEquiv`,
`L2.Translation.variance_pullbackEquiv`,
`Covariance.operator_translateLaw`, `Energy.CovarianceGradient.Test.translate`,
`Energy.CovarianceGradient.relaxation_translateLaw` and
`Poincare.CovarianceGradient.constant_translateLaw`.

For a probability law `ν` on a finite-dimensional Euclidean space and a vector `c`, the translated
law is the image of `ν` under `x ↦ c + x`. Composition with the translation is a linear isometric
equivalence `L²(translated) ≃ L²(ν)` which preserves the intrinsic `L²` variance; the covariance
operator is unchanged; globally Lipschitz tests correspond by composition with the translation,
with equal covariance energies; hence the covariance relaxations correspond under the isometry
and the optimal `L²` Poincaré constants of the two relaxations coincide.

These statements hold for every Borel probability law; no log-concavity, density or closability
is used, and no Poincaré inequality is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities.Energy

open Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

section Tests

namespace Euclidean

/-- The gradient of a translated function is the translated gradient. -/
theorem gradient_comp_const_add (g : V → ℝ) (c x : V) :
    gradient (fun y ↦ g (c + y)) x = gradient g (c + x) := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient]
  exact fderiv_comp_add_left c

omit [InnerProductSpace ℝ V] [CompleteSpace V] in
/-- Translations are `1`-Lipschitz. -/
theorem lipschitzWith_const_add (c : V) : LipschitzWith 1 (fun x : V ↦ c + x) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by simp [dist_eq_norm]

end Euclidean

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν₁ ν₂ : ProbabilityMeasure V} {c : V}

namespace CovarianceGradient.Test

/-- Composition of a covariance test with a measure-preserving translation between two laws with
the same covariance operator. -/
def translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : Test ν₂) : Test ν₁ where
  toFun := fun x ↦ g (c + x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * 1, hK.comp (lipschitzWith_const_add c)⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff
      (hmp.map_eq ▸ g.memLp_two.aestronglyMeasurable) hmp.aemeasurable).mp this
  integrable := by
    have hdens : density ν₁ (fun x ↦ g (c + x)) =
        density ν₂ g.toFun ∘ fun x ↦ c + x := by
      funext x
      simp only [density, Function.comp_apply, gradient_comp_const_add, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this

section TranslatedTests

omit [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The translated test has the same covariance energy. -/
theorem energy_translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : Test ν₂) :
    (g.translate hmp hcov).energy = g.energy := by
  apply NNReal.eq
  simp only [coe_energy]
  have hdens : density ν₁ (g.translate hmp hcov).toFun =
      density ν₂ g.toFun ∘ fun x ↦ c + x := by
    funext x
    simp only [translate, density, Function.comp_apply,
      gradient_comp_const_add, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl

/-- The translated test realizes the pullback of the original class. -/
theorem toL2_translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : Test ν₂) :
    (g.translate hmp hcov).toL2 = Lp.compMeasurePreserving (fun x ↦ c + x) hmp g.toL2 := by
  apply Lp.ext
  refine (g.translate hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm

end TranslatedTests

end CovarianceGradient.Test

end Tests

section Relaxation

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (ν : ProbabilityMeasure V) (c : V)

namespace CovarianceGradient

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The covariance relaxation of the translated law is the covariance relaxation of `ν` pulled
back along the translation isometry. -/
theorem relaxation_translateLaw (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    relaxation (Probability.translateLaw ν c) f =
      relaxation ν (L2.Translation.pullbackEquiv ν c f) := by
  have hcov :
    Covariance.operator (Probability.translateLaw ν c : Measure V) =
      Covariance.operator (ν : Measure V) :=
    Covariance.operator_translateLaw ν c
  apply le_antisymm
  · -- pull tests of `ν` back to the translated law along the inverse translation
    have h :=
      (preEnergy ν).sequentialRelaxation_comp_le (preEnergy (Probability.translateLaw ν c))
        (L2.Translation.pullbackInv ν c) (L2.Translation.pullbackInv ν c).continuous ?_
        (L2.Translation.pullbackEquiv ν c f)
    · rw [L2.Translation.pullbackEquiv_apply, L2.Translation.pullbackInv_pullback] at h
      exact h
    · intro g
      refine
        ⟨g.translate (Probability.measurePreserving_translate_symm ν c) hcov.symm, ?_,
          le_of_eq ?_⟩
      · exact g.toL2_translate _ _
      · exact g.energy_translate _ _
  · have h :=
      (preEnergy (Probability.translateLaw ν c)).sequentialRelaxation_comp_le (preEnergy ν)
        (L2.Translation.pullback ν c) (L2.Translation.pullback ν c).continuous ?_ f
    · exact h
    · intro g
      refine ⟨g.translate (Probability.measurePreserving_translate ν c) hcov, ?_, le_of_eq ?_⟩
      · exact g.toL2_translate _ _
      · exact g.energy_translate _ _

end CovarianceGradient

end Relaxation

end FunctionalInequalities.Energy
