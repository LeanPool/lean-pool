/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Fourier models of whole-plane Sobolev spaces of arbitrary real order

The formalisation uses `H^s(\mathbb R^2; F)` for every real `s` (the paper needs only
`H¹`, `H²` and `H⁻¹`).  Mathlib already
defines membership in these Bessel-potential spaces for tempered
distributions, but does not bundle that predicate as a Hilbert space.  This
file supplies the missing bundled space.

An element stores the `L^2` coefficient

`(1 + |xi|^2)^(s/2) * Fourier(u)(xi)`.

Thus the coefficient map is, by definition, a linear isometric equivalence
with `L^2`.  The physical tempered distribution is reconstructed by inverse
Fourier synthesis followed by the Bessel potential of order `-s`.  The final
range theorem proves that this construction is exactly Mathlib's
`TemperedDistribution.MemSobolev s 2` predicate; it is not a coefficient-only
surrogate.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

/-- The Fourier-weighted Hilbert realization of `H^s(R^2; F)`.  The stored
coefficient is `(1 + |xi|^2)^(s/2) Fourier(u)(xi)`. -/
@[ext]
structure WholePlaneSobolev (s : Real) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace Complex F] [CompleteSpace F] where
  /-- The Fourier coefficient weighted by the order-`s` Bessel factor. -/
  coeff : WholePlaneL2 F

section Instances

variable (s : Real) (F : Type*)
  [NormedAddCommGroup F] [InnerProductSpace Complex F] [CompleteSpace F]

/-- The underlying equivalence between the bundled Sobolev model and its
weighted `L^2` coefficient. -/
def wholePlaneSobolevCoeffEquiv :
    WholePlaneSobolev s F ≃ WholePlaneL2 F where
  toFun := WholePlaneSobolev.coeff
  invFun := WholePlaneSobolev.mk
  left_inv u := by cases u; rfl
  right_inv _ := rfl

/-- Additive group structure on `H^s(ℝ²; F)`, transported from its weighted `L²` coefficient. -/
instance wholePlaneSobolevAddCommGroup : AddCommGroup (WholePlaneSobolev s F) :=
  (wholePlaneSobolevCoeffEquiv s F).addCommGroup

/-- Complex module structure on `H^s(ℝ²; F)`, transported from its weighted `L²` coefficient. -/
instance wholePlaneSobolevModule : Module Complex (WholePlaneSobolev s F) :=
  (wholePlaneSobolevCoeffEquiv s F).addEquiv.module Complex

/-- Norm on `H^s(ℝ²; F)`, transported from the weighted `L²` coefficient; by construction the
coefficient map is norm preserving. -/
instance wholePlaneSobolevNormedAddCommGroup :
    NormedAddCommGroup (WholePlaneSobolev s F) :=
  (wholePlaneSobolevCoeffEquiv s F).normedAddCommGroup

/-- Complex normed-space structure on `H^s(ℝ²; F)`, transported from its weighted `L²`
coefficient. -/
instance wholePlaneSobolevNormedSpace :
    NormedSpace Complex (WholePlaneSobolev s F) :=
  (wholePlaneSobolevCoeffEquiv s F).addEquiv.normedSpace Complex

/-- Inner product on `H^s(ℝ²; F)`, induced from the weighted `L²` coefficient; this is the
Bessel-potential inner product of order `s`. -/
instance wholePlaneSobolevInnerProductSpace :
    InnerProductSpace Complex (WholePlaneSobolev s F) :=
  InnerProductSpace.induced
    ((wholePlaneSobolevCoeffEquiv s F).addEquiv.linearEquiv Complex)

/-- Reading the weighted coefficient is a complex linear isometric
equivalence. -/
def wholePlaneSobolevCoeff :
    WholePlaneSobolev s F ≃ₗᵢ[Complex] WholePlaneL2 F where
  toLinearEquiv := (wholePlaneSobolevCoeffEquiv s F).addEquiv.linearEquiv Complex
  norm_map' _ := rfl

/-- `H^s(ℝ²; F)` is complete, being isometrically equivalent to the complete space `L²`; so the
bundled Sobolev model is a Hilbert space at every real order. -/
instance wholePlaneSobolevCompleteSpace : CompleteSpace (WholePlaneSobolev s F) :=
  (wholePlaneSobolevCoeff s F).toIsometryEquiv.completeSpace

/-- The bundled coefficient isometry reads off the stored weighted Fourier coefficient. -/
@[simp] theorem wholePlaneSobolevCoeff_apply (u : WholePlaneSobolev s F) :
    wholePlaneSobolevCoeff s F u = u.coeff :=
  rfl

/-- Its inverse packages a weighted `L²` coefficient as an element of `H^s(ℝ²; F)`. -/
@[simp] theorem wholePlaneSobolevCoeff_symm_apply (f : WholePlaneL2 F) :
    (wholePlaneSobolevCoeff s F).symm f = WholePlaneSobolev.mk f :=
  rfl

end Instances

section Distribution

variable (s : Real) (F : Type*)
  [NormedAddCommGroup F] [InnerProductSpace Complex F] [CompleteSpace F]

/-- Canonical realization of the bundled Fourier-weighted Sobolev space as a
tempered distribution.  Starting with the weighted coefficient, we synthesize
an `L^2` field and then apply the Bessel potential of order `-s`. -/
def wholePlaneSobolevToTempered :
    WholePlaneSobolev s F →L[Complex] 𝓢'(WholePlane, F) :=
  (TemperedDistribution.besselPotential WholePlane F (-s)).comp
    ((wholePlaneL2ToTempered F).comp
      ((wholePlaneFourierSynthesis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (wholePlaneSobolevCoeff s F).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Unfolding of the distributional realization: synthesize the stored weighted coefficient by
inverse Fourier transform and then apply the Bessel potential of order `-s`. -/
@[simp] theorem wholePlaneSobolevToTempered_apply
    (u : WholePlaneSobolev s F) :
    wholePlaneSobolevToTempered s F u =
      (TemperedDistribution.besselPotential WholePlane F (-s))
        (wholePlaneL2ToTempered F
          (wholePlaneFourierSynthesis F u.coeff)) :=
  rfl

/-- The Sobolev-to-distribution realization is injective. -/
theorem wholePlaneSobolevToTempered_injective :
    Function.Injective (wholePlaneSobolevToTempered s F) := by
  intro u v huv
  apply (wholePlaneSobolevCoeff s F).injective
  apply (wholePlaneFourierSynthesis F).injective
  apply wholePlaneL2ToTempered_injective F
  have h := congrArg
    (TemperedDistribution.besselPotential WholePlane F s) huv
  simpa [TemperedDistribution.besselPotential_besselPotential_apply] using h

/-- Every bundled element represents a Sobolev tempered distribution of the
declared order. -/
theorem wholePlaneSobolevToTempered_memSobolev
    (u : WholePlaneSobolev s F) :
    TemperedDistribution.MemSobolev s 2
      (wholePlaneSobolevToTempered s F u) := by
  refine ⟨wholePlaneFourierSynthesis F u.coeff, ?_⟩
  simp [TemperedDistribution.besselPotential_besselPotential_apply]

/-- Exact range characterization: the bundled Hilbert model represents all
and only Mathlib's order-`s`, exponent-`2` Sobolev tempered distributions. -/
theorem memSobolev_iff_exists_wholePlaneSobolev
    (f : 𝓢'(WholePlane, F)) :
    TemperedDistribution.MemSobolev s 2 f ↔
      ∃ u : WholePlaneSobolev s F,
        wholePlaneSobolevToTempered s F u = f := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(wholePlaneSobolevCoeff s F).symm
      (wholePlaneFourierAnalysis F g), ?_⟩
    rw [wholePlaneSobolevToTempered_apply]
    simp only [wholePlaneSobolevCoeff_symm_apply,
      wholePlaneFourierSynthesis_analysis]
    exact (TemperedDistribution.besselPotential_neg_apply_eq_iff s _ _).2 hg
  · rintro ⟨u, rfl⟩
    exact wholePlaneSobolevToTempered_memSobolev s F u

/-- Fourier transform of the bundled Sobolev realization. -/
theorem fourier_wholePlaneSobolevToTempered
    (s : ℝ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (u : WholePlaneSobolev s F) :
    𝓕 (wholePlaneSobolevToTempered s F u) =
      TemperedDistribution.smulLeftCLM F
        (fun xi : WholePlane =>
          (((1 + ‖xi‖ ^ 2) ^ ((-s) / 2) : ℝ) : ℂ))
        (wholePlaneL2ToTempered F
          (wholePlaneSobolevCoeff s F u)) := by
  rw [wholePlaneSobolevToTempered_apply]
  rw [TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  rw [fourier_wholePlaneL2ToTempered]
  rw [wholePlaneFourierAnalysis_synthesis]
  rfl

end Distribution

end

end FastDynamo
