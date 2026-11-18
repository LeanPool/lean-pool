/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.UpperSemicontinuity
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Intrinsic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Transport
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport

/-!
# Concave tilts of log-concave laws

A continuous concave exponent `φ` with `∫ e^{φ} dμ < ∞` tilts a log-concave probability law to a
log-concave law: on the intrinsic affine support the Borell density is multiplied by the log-concave
weight `e^{φ}/Z`, and the result is pushed forward along the reconstruction isometry. Used for the
BKL
posterior with `Q ≥ 0` (`KLS/BKL/Posterior/Covariance.lean`).
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology FunctionalInequalities

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/--
A continuous concave tilt of a Borell density is a Borell density (zeros of the density allowed). -/
theorem isBorellDensity_of_concave_tilt (μ ν : ProbabilityMeasure E) (m : Measure E) {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) m ρ) (φ : E → ℝ) (hφ : Continuous φ)
    (hconc : ConcaveOn ℝ univ φ) (hν : (ν : Measure E) = (μ : Measure E).tilted φ) :
    KLS.IsBorellDensity (ν : Measure E) m
      (fun x => ρ x * (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂(μ : Measure E))) := by
  have hi : Integrable (fun x => Real.exp (φ x)) (μ : Measure E) := by
    have h :=
      KLS.LogConcave.integrable_exp_neg_of_eq_tilted (ν := ν) (m := (μ : Measure E)) (W := -φ)
        (by simpa using hν)
    simpa using h
  let Z : ℝ := ∫ y, Real.exp (φ y) ∂(μ : Measure E)
  have hZ : 0 < Z := integral_exp_pos hi
  let g : E → ℝ := fun y => Real.exp (φ y) / Z
  have hg : Continuous g := (Real.continuous_exp.comp hφ).div_const _
  have hgp : ∀ y, 0 < g y := fun y => div_pos (Real.exp_pos _) hZ
  refine
    ⟨hρ.measurable.mul hg.measurable, fun x => mul_nonneg (hρ.nonneg x) (hgp x).le,
      FunctionalInequalities.Analysis.upperSemicontinuous_mul_of_continuous_pos
        hρ.upperSemicontinuous hg hgp,
      ?_, ?_⟩
  · intro a b t ht0 ht1
    have hgLC : g a ^ t * g b ^ (1 - t) ≤ g (t • a + (1 - t) • b) := by
      simpa only [g, Pi.neg_apply, neg_neg] using
        KLS.LogConcave.rpow_mul_rpow_le_of_convexOn hconc.neg hZ a b ht0 ht1
    have hρLC := hρ.logConcave a b t ht0 ht1
    change (ρ a * g a) ^ t * (ρ b * g b) ^ (1 - t) ≤ _
    rw [Real.mul_rpow (hρ.nonneg a) (hgp a).le, Real.mul_rpow (hρ.nonneg b) (hgp b).le]
    calc
      ρ a ^ t * g a ^ t * (ρ b ^ (1 - t) * g b ^ (1 - t)) =
          (ρ a ^ t * ρ b ^ (1 - t)) * (g a ^ t * g b ^ (1 - t)) := by
        ring
      _ ≤ _ :=
        mul_le_mul hρLC hgLC
          (mul_nonneg (Real.rpow_nonneg (hgp a).le _) (Real.rpow_nonneg (hgp b).le _))
          (hρ.nonneg _)
  · rw [hν]
    change
      m.withDensity (fun y => ENNReal.ofReal (ρ y * g y)) =
        (μ : Measure E).withDensity (fun y => ENNReal.ofReal (g y))
    have heq :
      (fun y => ENNReal.ofReal (ρ y * g y)) =
        (fun y => ENNReal.ofReal (ρ y)) * fun y => ENNReal.ofReal (g y) := by
      funext y
      exact ENNReal.ofReal_mul (hρ.nonneg y)
    rw [heq, withDensity_mul _ hρ.measurable.ennreal_ofReal hg.measurable.ennreal_ofReal,
      hρ.withDensity_eq]

/--
**A continuous concave tilt of a log-concave law is log-concave** (through the intrinsic Borell
representation; singular laws and dimension zero included). -/
theorem logConcave_of_concave_tilt (μ ν : ProbabilityMeasure E) (hLC : KLS.LogConcave μ)
    (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
    (hν : (ν : Measure E) = (μ : Measure E).tilted φ) : KLS.LogConcave ν := by
  let F := (Probability.affineSupport μ).direction
  let ξ : ProbabilityMeasure F := Probability.intrinsicMeasure μ
  let e : F →ᵃⁱ[ℝ] E := Probability.reconstruct μ
  have he : (ξ : Measure F).map e = (μ : Measure E) :=
    (Probability.measurePreserving_reconstruct μ).map_eq
  have hi : Integrable (fun x => Real.exp (φ x)) (μ : Measure E) := by
    have h :=
      KLS.LogConcave.integrable_exp_neg_of_eq_tilted (ν := ν) (m := (μ : Measure E)) (W := -φ)
        (by simpa using hν)
    simpa using h
  have hi' : Integrable (fun x => Real.exp ((φ ∘ e) x)) (ξ : Measure F) :=
    (Probability.measurePreserving_reconstruct μ).integrable_comp
        (hφ.measurable.exp.aestronglyMeasurable) |>.mpr
      hi
  let η : ProbabilityMeasure F :=
    ⟨(ξ : Measure F).tilted (φ ∘ e), isProbabilityMeasure_tilted hi'⟩
  obtain ⟨ρ, hρ⟩ := hLC.exists_isBorellDensity (volume : Measure F)
  have hconc' : ConcaveOn ℝ univ (φ ∘ e) := by
    simpa only [preimage_univ, AffineIsometry.coe_toAffineMap] using
      hconc.comp_affineMap e.toAffineMap
  have hη : KLS.LogConcave η :=
    (isBorellDensity_of_concave_tilt ξ η volume hρ (φ ∘ e) (hφ.comp e.continuous) hconc'
        rfl).compactLogConcave
  apply LogConcave.map_affineIsometry η hη ν e
  rw [hν]
  change (μ : Measure E).tilted φ = ((ξ : Measure F).tilted (φ ∘ e)).map e
  rw [Probability.map_tilted_comp _ e e.continuous.measurable φ hφ.measurable, he]

end FunctionalInequalities.KLS.LogConcave
