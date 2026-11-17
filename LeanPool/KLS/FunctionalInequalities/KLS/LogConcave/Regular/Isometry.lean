/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Transport
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Poincare

/-!
# Regular potentials under linear isometries

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): regular potentials, their laws, isotropy
and the Poincaré constants transport through linear isometries between (possibly different)
finite-dimensional inner product spaces, with the same curvature constants `a, b`. In particular a
regular law on an abstract space has a regular law in standard coordinates on `ℝⁿ`, so a Poincaré
bound for isotropic regular laws on `ℝⁿ` transfers with the same constant. No non-isometric
invariance of the constant is asserted.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.KLS

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/--
**Regular potentials are preserved by linear isometries** `L : E ≃ F`, with the same constants `a,
b`. -/
theorem RegularPotential.comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) : KLS.RegularPotential (fun y => V (L.symm y)) a b := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨hV.temperate.comp L.symm.toContinuousLinearEquiv.hasTemperateGrowth, hV.pos, ?_, ?_⟩
  · intro y w
    have hh :=
      Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_clm hV2 (L.symm : F →L[ℝ] E) y w w
    simp only [LinearIsometryEquiv.coe_coe''] at hh
    rw [hh]
    simpa only [LinearIsometryEquiv.norm_map] using hV.lower (L.symm y) (L.symm w)
  · intro y w
    have hh :=
      Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_clm hV2 (L.symm : F →L[ℝ] E) y w w
    simp only [LinearIsometryEquiv.coe_coe''] at hh
    rw [hh]
    simpa only [LinearIsometryEquiv.norm_map] using hV.upper (L.symm y) (L.symm w)

/-- The law of `V ∘ L⁻¹` is the image of the law of `V` under `L`. -/
theorem RegularPotential.law_comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) :
    ((RegularPotential.comp_isometry hV L).law : Measure F) = (hV.law : Measure E).map L := by
  have ht := Probability.map_tilted_measurableEquiv L.toMeasurableEquiv
    (volume : Measure E) (-V) hV.temperate.1.continuous.neg.measurable
  change (volume.tilted (-V)).map L =
    ((volume : Measure E).map L).tilted (-fun y => V (L.symm y)) at ht
  rw [L.measurePreserving.map_eq] at ht
  exact ht.symm

/-- The same identity for probability laws. -/
theorem RegularPotential.law_comp_isometry_eq_map {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (L : E ≃ₗᵢ[ℝ] F) :
    (RegularPotential.comp_isometry hV L).law = Probability.mapLinearIsometryEquiv hV.law L := by
  apply ProbabilityMeasure.toMeasure_injective
  exact RegularPotential.law_comp_isometry hV L

omit [CompleteSpace E] [CompleteSpace F] in
/-- The normalizer is invariant under isometries. -/
theorem RegularPotential.integral_exp_neg_comp_isometry (V : E → ℝ) (L : E ≃ₗᵢ[ℝ] F) :
    (∫ y : F, Real.exp (-V (L.symm y)) ∂volume) =
      ∫ x : E, Real.exp (-V x) ∂volume := by
  simpa only using L.symm.measurePreserving.integral_comp
    L.symm.toMeasurableEquiv.measurableEmbedding (fun x => Real.exp (-V x))

/-- Isotropy is preserved. -/
theorem RegularPotential.isotropic_comp_isometry {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (hiso : KLS.Isotropic hV.law) (L : E ≃ₗᵢ[ℝ] F) :
    KLS.Isotropic (RegularPotential.comp_isometry hV L).law := by
  rw [RegularPotential.law_comp_isometry_eq_map]
  exact hiso.map_linearIsometryEquiv L

/-- The smooth-test Poincaré constant is preserved. -/
theorem RegularPotential.smoothTest_constant_comp_isometry {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (L : E ≃ₗᵢ[ℝ] F) :
    Poincare.SmoothTest.optimalConstant ((RegularPotential.comp_isometry hV L).law : Measure F) =
      Poincare.SmoothTest.optimalConstant (hV.law : Measure E) := by
  rw [RegularPotential.law_comp_isometry]
  exact Poincare.SmoothTest.constant_map_linearIsometryEquiv L (hV.law : Measure E)

/-- The literature Poincaré constant is preserved. -/
theorem RegularPotential.localSlope_constant_comp_isometry {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (L : E ≃ₗᵢ[ℝ] F) :
    Poincare.LocalSlope.Intrinsic.optimalConstant (RegularPotential.comp_isometry hV L).law =
      Poincare.LocalSlope.Intrinsic.optimalConstant hV.law := by
  rw [← (RegularPotential.comp_isometry hV L).logConcave_law.smoothTest_constant_eq_localSlope,
    ← hV.logConcave_law.smoothTest_constant_eq_localSlope]
  exact RegularPotential.smoothTest_constant_comp_isometry hV L

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/--
Standard orthonormal coordinates give a regular potential on `ℝⁿ`, `n = dim E`, with the same
constants. -/
theorem RegularPotential.toEuclidean {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    KLS.RegularPotential
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        V ((stdOrthonormalBasis ℝ E).repr.symm y))
      a b :=
  RegularPotential.comp_isometry hV (stdOrthonormalBasis ℝ E).repr

/-- Its law is the coordinate image of the original law, isotropic when the original is. -/
theorem RegularPotential.toEuclidean_law_isotropic {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (hiso : KLS.Isotropic hV.law) :
    (RegularPotential.toEuclidean hV).law =
        Probability.mapLinearIsometryEquiv hV.law (stdOrthonormalBasis ℝ E).repr ∧
      KLS.Isotropic (RegularPotential.toEuclidean hV).law :=
  ⟨RegularPotential.law_comp_isometry_eq_map hV _,
    RegularPotential.isotropic_comp_isometry hV hiso _⟩

/--
A Poincaré bound for isotropic regular laws on `ℝⁿ` (`n > 0`) transfers to every isotropic regular
law
on a finite-dimensional inner product space (dimension zero has constant `0`). No such bound is
asserted. -/
theorem RegularPotential.localSlope_le_of_euclidean_bound {K : NNReal}
    (hK :
      ∀ (n : ℕ),
        0 < n →
          ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
            KLS.Isotropic hV.law →
              Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (K : ENNReal))
    {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) (hiso : KLS.Isotropic hV.law) :
    Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (K : ENNReal) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]
    exact bot_le
  rw [← RegularPotential.localSlope_constant_comp_isometry hV (stdOrthonormalBasis ℝ E).repr]
  exact
    hK (Module.finrank ℝ E) (Nat.pos_of_ne_zero hdim) _ a b (RegularPotential.toEuclidean hV)
      (RegularPotential.isotropic_comp_isometry hV hiso _)

end FunctionalInequalities.KLS
