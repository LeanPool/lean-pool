/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.GalerkinOptimizerReadout
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalCutoffPairingMeasurability
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.MatrixIdentities
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# High-contrast homogenization: Entry.Response.Cutoff.CutoffQuadraticReadout

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-weighted quadratic readout

On a response cell `U` with cutoff weight `φ`, the cutoff-weighted quadratic readout sends a
doubled Hilbert block field `z` to the volume average
`(|U|)^{-1} ∫_U φ(x) ⟪z_1(x), z_2(x)⟫ dx` of its potential and flux slots; this file constructs
that readout as a continuous functional on the Hilbert space of block fields, evaluates it on
the diagonal of the cutoff-weighted energy bilinear form of an elliptic coefficient, and proves
the almost-sure strong measurability of the cutoff pairing for an arbitrary response maximizer
by reducing it, almost everywhere on the response cell, to the readout applied to the Chapter-2
canonical optimizer state.  The labelled result this file serves is the cutoff estimate
`e.response.cutoff.estimate`.
-/

section
/-!
## Measurability of the cutoff pairing in the sample

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the volume average of
the cutoff-weighted product of the gradient defect and the flux defect of the doubled optimizer
state of a response maximizer.  The doubled optimizer state of an arbitrary response maximizer is
determined almost everywhere on the response cell by the Chapter-2 canonical maximizer, by
a.e. gradient uniqueness for response maximizers (AK.HC (2.9)); the canonical selection is the one
whose cell averages depend measurably on the coefficient sample.

The reduction below is the pairing analogue of the canonical identification carried out for the
scale-average seminorm of `e.response.weak.estimate`: for each coefficient sample the two doubled
optimizer fields agree almost everywhere on the cell, so the two cutoff pairings agree, and the
measurability of the pairing transfers from the canonical coefficient family to the arbitrary family
of maximizers.  The measurability of the canonical quadratic readout itself, whose input is the
canonical coefficient object rather than the arbitrary family, is exactly the missing input recorded
as the two hypotheses `hcanonMinus` and `hcanonPlus`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing of `e.response.cutoff.estimate` is almost-everywhere strongly measurable in
the coefficient sample for an arbitrary family of response maximizers, provided the corresponding
quadratic readout of the canonical Chapter-2 optimizer state of the two recentred coefficient
families is measurable.  The arbitrary maximizer is identified with the canonical one almost
everywhere on the cell by a.e. gradient uniqueness (AK.HC (2.9)), so the pairing depends on the
sample only through the canonical selection. -/
theorem aestronglyMeasurable_abs_cutoff_pairing_of_maximizer {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (c : CoeffSpace d → CoeffField d)
    (hc : c = respCoeffMinus F ∨ c = respCoeffPlus F)
    (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a))
    (hcanonMinus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      |volumeAverage (respCell jStar F t) (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffMinusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffMinusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))|) P)
    (hcanonPlus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      |volumeAverage (respCell jStar F t) (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffPlusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffPlusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))|) P) :
    AEStronglyMeasurable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P := by
  classical
  have _ := hφ
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hfin := Book.Ch02.Domain.instIsFiniteMeasureVolumeMeasureOn
      (adaptedDomain (respGrid jStar F) hq t)
    simpa [respCell, adaptedDomain] using hfin
  -- The canonical optimizer state only sees the a.e. class of the coefficient object.
  have hstate_aeeq : ∀ {A B : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t)},
      Book.Ch02.CoeffOn.AEEq A B → ∀ p r : Vec d,
      canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p r
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) B p r := by
    intro A B hAB p r
    have hgrad : (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) A)
          p r).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) B)
          p r).toSolution.toH1.grad := by
      simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
        (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
    filter_upwards [hgrad, hAB] with x hgradx hcoeffx
    simp only [canonicalOptimizerBlockState]
    rw [hgradx, hcoeffx]
  rcases hc with rfl | rfl
  · -- the minus recentring
    have hmain : (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffMinus F a) (u a) x).1 - Y.1)
          ((optimizerField (respCoeffMinus F a) (u a) x).2 - Y.2))|)
        = (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2))|) := by
      funext a
      congr 1
      let hv : ScalarCanonicalMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) :=
        ScalarCanonicalMaximizer.ofIsResponseMaximizer (u a) (hu a)
      obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
        exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
      have hAB : Book.Ch02.CoeffOn.AEEq (coeffOnOfIsEllipticFieldOn (U := adaptedDomain
        (respGrid jStar F) hq t) hlam hle hEll)
          (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) := by
        filter_upwards [hbf.symm] with x hx
        simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
      have hstate := hstate_aeeq hAB p q'
      have hcanon := optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
        (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll hbf p q' hv
      have hfield : optimizerField (respCoeffMinus F a) (u a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)]
          canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' := by
        have hbridge : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U :=
                adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            = canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam
                  hle hEll) p q' := rfl
        have hmid : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U :=
                adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            =ᵐ[volumeMeasureOn (respCell jStar F t)]
            canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' := by
          rw [hbridge]
          exact hstate
        have hgrad_eq : hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad
            = (u a).toH1.grad := by
          funext x
          exact AHarmonicFunction.grad_normalizeMeanZero (u a) x
        have hnorm : optimizerField (respCoeffMinus F a) (u a)
            = optimizerField (respCoeffMinus F a)
                hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
          funext x
          simp only [optimizerField, hgrad_eq]
        rw [hnorm]
        exact hcanon.symm.trans hmid
      unfold volumeAverage
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hfield] with x hx
      rw [hx]
    rw [hmain]
    exact hcanonMinus
  · -- the plus recentring
    have hmain : (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffPlus F a) (u a) x).1 - Y.1)
          ((optimizerField (respCoeffPlus F a) (u a) x).2 - Y.2))|)
        = (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2))|) := by
      funext a
      congr 1
      let hv : ScalarCanonicalMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) :=
        ScalarCanonicalMaximizer.ofIsResponseMaximizer (u a) (hu a)
      obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
        exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
      have hAB : Book.Ch02.CoeffOn.AEEq (coeffOnOfIsEllipticFieldOn (U := adaptedDomain
        (respGrid jStar F) hq t) hlam hle hEll)
          (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) := by
        filter_upwards [hbf.symm] with x hx
        simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
      have hstate := hstate_aeeq hAB p q'
      have hcanon := optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
        (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll hbf p q' hv
      have hfield : optimizerField (respCoeffPlus F a) (u a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)]
          canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' := by
        have hbridge : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U :=
                adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            = canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam
                  hle hEll) p q' := rfl
        have hmid : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U :=
                adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            =ᵐ[volumeMeasureOn (respCell jStar F t)]
            canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' := by
          rw [hbridge]
          exact hstate
        have hgrad_eq : hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad
            = (u a).toH1.grad := by
          funext x
          exact AHarmonicFunction.grad_normalizeMeanZero (u a) x
        have hnorm : optimizerField (respCoeffPlus F a) (u a)
            = optimizerField (respCoeffPlus F a)
                hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
          funext x
          simp only [optimizerField, hgrad_eq]
        rw [hnorm]
        exact hcanon.symm.trans hmid
      unfold volumeAverage
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hfield] with x hx
      rw [hx]
    rw [hmain]
    exact hcanonPlus

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Measurability of the cutoff pairing for an arbitrary maximizer family

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the volume average,
over the response cell `U_t`, of the cutoff-weighted Euclidean pairing of the potential defect and
the flux defect of the doubled optimizer state of a response maximizer.  This file records that the
absolute value of that pairing is almost-everywhere strongly measurable in the coefficient
sample for an arbitrary family of response maximizers.

The doubled optimizer state of an arbitrary response maximizer agrees almost everywhere on the
response cell with the Chapter-2 canonical maximizer, by a.e. gradient uniqueness for response
maximizers (AK.HC (2.9)); the pairing therefore agrees almost everywhere with the canonical pairing.
The canonical pairing is then reduced to its genuinely quadratic term by the pointwise expansion of
the integrand, whose three remaining linear readouts of the canonical optimizer state are
measurable.  Only that quadratic canonical readout is carried as an explicit hypothesis, in the two
recentrings of `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)).
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A volume average over a set `V` is unchanged by an almost-everywhere equality of the integrand
on a larger set `U ⊇ V`.  This is the scalar analogue of `cellAverage_congr_ae`. -/
theorem volumeAverage_congr_ae {d : ℕ} {V U : Set (Vec d)} (hVU : V ⊆ U)
    {f g : Vec d → ℝ} (h : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage V f = volumeAverage V g := by
  have h2 : f =ᵐ[volumeMeasureOn V] g :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae h2

/-- The absolute value of the cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is almost-everywhere strongly measurable in the coefficient sample for an
arbitrary family of response maximizers of the two recentred response coefficient families, provided
the cutoff-weighted volume average of the quadratic self-pairing of the canonical Chapter-2
optimizer
state is measurable in each case.

The arbitrary maximizer is identified with the canonical one almost everywhere on the response cell
by a.e. gradient uniqueness for response maximizers (AK.HC (2.9)), so the pairing depends on the
sample only through the canonically selected optimizer state.  The canonical pairing is expanded
into its quadratic term and the three linear readouts whose measurability is recorded in
`aestronglyMeasurable_abs_canonical_cutoff_pairing_minus_of_quadratic` and its plus twin. -/
theorem aestronglyMeasurable_abs_pairing_of_maximizer {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (c : CoeffSpace d → CoeffField d)
    (hc : c = respCoeffMinus F ∨ c = respCoeffPlus F)
    (p q' : Vec d) (Y : BlockVec d) {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a))
    (hquadMinus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell (respGrid jStar F) t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffMinusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffMinusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2)) P)
    (hquadPlus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell (respGrid jStar F) t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffPlusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffPlusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2)) P) :
    AEStronglyMeasurable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P := by
  refine aestronglyMeasurable_abs_cutoff_pairing_of_maximizer
    P jStar F t hjStar hm φ hφ c hc p q' Y u hu ?_ ?_
  · simpa only [respCell] using
      aestronglyMeasurable_abs_canonical_cutoff_pairing_minus_of_quadratic
        P jStar F t hjStar hm φ hφ p q' Y hquadMinus
  · simpa only [respCell] using
      aestronglyMeasurable_abs_canonical_cutoff_pairing_plus_of_quadratic
        P jStar F t hjStar hm φ hφ p q' Y hquadPlus

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-weighted quadratic readout as a continuous Hilbert functional

On a positive-volume response cell `U` with a cutoff weight `φ`, the cutoff-weighted quadratic
readout sends a doubled Hilbert block field `z` to the volume average

`(|U|)⁻¹ ∫_U φ(x) ⟪z₁(x), z₂(x)⟫ dx`,

where `z₁` and `z₂` are the potential and flux components of `z`.  Because `φ` is bounded, this is
the diagonal of a bounded bilinear form on `HilbertBlockL2 U`, hence continuous; this is the
analytic ingredient behind `e.response.cutoff.estimate`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The pointwise linear map `(p, q) ↦ (q, 0)` on doubled Hilbert vectors, transported from the
algebraic block carrier. -/
@[expose]
def blockFluxProjL (d : ℕ) : HilbertBlockVec d →L[ℝ] HilbertBlockVec d :=
  (HilbertBlockVec.continuousLinearEquivBlockVec d).symm.toContinuousLinearMap ∘L
    (((ContinuousLinearMap.snd ℝ (Vec d) (Vec d)).prod (0 : BlockVec d →L[ℝ] Vec d)) ∘L
      (HilbertBlockVec.continuousLinearEquivBlockVec d).toContinuousLinearMap)

/-- The pointwise action of `blockFluxProjL`: the potential slot is discarded and the flux slot is
paired with zero. -/
@[simp]
theorem blockFluxProjL_apply (X : HilbertBlockVec d) :
    blockFluxProjL d X = HilbertBlockVec.ofBlockVec (X.flux.toVec, 0) :=
  rfl

/-- The pointwise readout of `blockFluxProjL` against `X` is the pairing of the potential and flux
components. -/
theorem inner_blockFluxProjL (X : HilbertBlockVec d) :
    inner ℝ X (blockFluxProjL d X) = vecDot X.potential.toVec X.flux.toVec := by
  rw [blockFluxProjL_apply, HilbertBlockVec.inner_def]
  simp [blockVecDot, vecDot]

/-- The `L²` realization of `blockFluxProjL`. -/
@[expose]
def blockFluxProjL2 (U : Set (Vec d)) : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (blockFluxProjL d).compLpL 2 (volumeMeasureOn U)

/-- The `L²` realization of `blockFluxProjL` acts pointwise. -/
theorem coeFn_blockFluxProjL2 (U : Set (Vec d)) (z : HilbertBlockL2 U) :
    (blockFluxProjL2 U z : Vec d → HilbertBlockVec d) =ᵐ[volumeMeasureOn U]
      fun x => blockFluxProjL d (z x) :=
  (blockFluxProjL d).coeFn_compLpL z

/-- Pointwise multiplication by an a.e. bounded scalar field preserves `L²`. -/
theorem memLp_weighted_smul {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    MemLp (fun x => φ x • (z : Vec d → HilbertBlockVec d) x) 2 (volumeMeasureOn U) := by
  refine MemLp.of_le_mul (c := 2) (Lp.memLp z) (hφm.smul (Lp.aestronglyMeasurable z)) ?_
  filter_upwards [hφb] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- Pointwise multiplication by an a.e. bounded scalar field, as a linear map on the doubled
`L²` space. -/
@[expose]
noncomputable def weightedBlockSMul {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U where
  toFun z := (memLp_weighted_smul hφm hφb z).toLp
    (fun x => φ x • (z : Vec d → HilbertBlockVec d) x)
  map_add' z w := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb (z + w)),
      MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z),
      MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb w),
      Lp.coeFn_add ((memLp_weighted_smul hφm hφb z).toLp _)
        ((memLp_weighted_smul hφm hφb w).toLp _),
      Lp.coeFn_add z w] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' c z := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb (c • z)),
      MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z),
      Lp.coeFn_smul c ((memLp_weighted_smul hφm hφb z).toLp _),
      Lp.coeFn_smul c z] with x h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply]
    rw [smul_comm]

/-- The weighted multiplication map acts pointwise. -/
theorem coeFn_weightedBlockSMul {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    (weightedBlockSMul hφm hφb z : Vec d → HilbertBlockVec d) =ᵐ[volumeMeasureOn U]
      fun x => φ x • z x :=
  MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z)

/-- Pointwise multiplication by an a.e. bounded scalar field, as a continuous linear map on the
doubled `L²` space. -/
@[expose]
noncomputable def weightedBlockSMulL {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (weightedBlockSMul hφm hφb).mkContinuous 2 (by
    intro z
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_weightedBlockSMul hφm hφb z, hφb] with x h1 h2
    rw [h1, norm_smul]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- The continuous weighted multiplication map acts pointwise. -/
theorem coeFn_weightedBlockSMulL {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    (weightedBlockSMulL hφm hφb z : Vec d → HilbertBlockVec d) =ᵐ[volumeMeasureOn U]
      fun x => φ x • z x :=
  MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z)

/-- The cutoff-weighted quadratic readout: the volume average of `φ` against the pointwise
potential-flux pairing of a doubled `L²` block field.  This is the quadratic readout of
`e.response.cutoff.estimate`. -/
@[expose]
noncomputable def cutoffQuadReadout (U : Set (Vec d)) (φ : Vec d → ℝ) :
    HilbertBlockL2 U → ℝ :=
  fun z => volumeAverage U
    (fun x => φ x * vecDot ((z x).potential.toVec) ((z x).flux.toVec))

/-- Under an a.e. bound on `φ`, the readout is the diagonal of the bounded bilinear form induced by
weighted multiplication. -/
theorem cutoffQuadReadout_eq_weighted_inner {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    cutoffQuadReadout U φ z =
      (volume U).toReal⁻¹ * inner ℝ z
        (weightedBlockSMulL hφm hφb (blockFluxProjL2 (d := d) U z)) := by
  rw [cutoffQuadReadout, volumeAverage, MeasureTheory.L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_weightedBlockSMulL hφm hφb (blockFluxProjL2 (d := d) U z),
    coeFn_blockFluxProjL2 (d := d) U z] with x h1 h2
  rw [h1, h2, real_inner_smul_right, inner_blockFluxProjL]

/-- The cutoff-weighted quadratic readout is continuous in the doubled `L²` field, for any cutoff
weight bounded a.e. by `2`; this is the analytic input to `e.response.cutoff.estimate`. -/
theorem continuous_cutoffQuadReadout (U : Set (Vec d))
    (hvol : 0 < (volume U).toReal) {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    Continuous (cutoffQuadReadout U φ) := by
  have _ := hvol
  have heq : cutoffQuadReadout U φ = fun z => (volume U).toReal⁻¹ * inner ℝ z
      (weightedBlockSMulL hφm hφb (blockFluxProjL2 (d := d) U z)) :=
    funext fun z => cutoffQuadReadout_eq_weighted_inner hφm hφb z
  rw [heq]
  exact continuous_const.mul
    (continuous_inner.comp (continuous_id.prodMk
      ((weightedBlockSMulL hφm hφb).continuous.comp
        (blockFluxProjL2 (d := d) U).continuous)))

/-- On a block field promoted to the doubled `L²` space, the readout is the volume average of the
pointwise potential-flux pairing. -/
theorem cutoffQuadReadout_toHilbertBlockL2OfBlockField (U : Set (Vec d)) {φ : Vec d → ℝ}
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    cutoffQuadReadout U φ (toHilbertBlockL2OfBlockField (U := U) hX) =
      volumeAverage U (fun x => φ x * vecDot (X.potential x) (X.flux x)) := by
  simp only [cutoffQuadReadout, volumeAverage]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := U) hX] with x hx
  rw [hx]
  simp [hilbertifyBlockField, BlockState.eval]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-weighted energy functional of the doubled minimizer

For a response cell `U`, a coefficient `a` lying on a quantitative ellipticity slice, and a cutoff
`φ`, the Hilbert `Mu` realization of `a` carries a continuous bilinear energy form.  Multiplying the
first argument pointwise by the cutoff and evaluating the energy on the diagonal gives the
functional `z ↦ ⨍_U φ ⟨z, B_a z⟩`, the cutoff-weighted energy of a doubled field.

The pointwise self-pairing of the canonical optimizer state is the doubled block energy of the
`Mu` minimizer plus twice the potential-flux pairing of the minimizer, so the quadratic term of the
expansion of the cutoff pairing `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) is the value
at the minimizer of the sum of the cutoff-weighted energy and twice the cutoff-weighted
potential-flux readout.  This file records the continuity of that sum in the doubled field, the
analytic half of the measurability of the quadratic term.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The cutoff-weighted energy of a doubled field is continuous in the field.  The energy bilinear
form of the `Mu` realization is continuous, pointwise multiplication by the a.e. bounded cutoff is
continuous linear, and evaluation of a continuous linear functional is continuous.  This is the
analytic input to the cutoff-weighted quadratic term of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)). -/
theorem continuous_energyBilin_weightedBlockSMulL_self {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    Continuous fun z : HilbertBlockL2 U =>
      (responseCellMuHilbert hvol a).energyBilin
        (weightedBlockSMulL (U := U) hφm hφb z) z := by
  have hf : Continuous fun z : HilbertBlockL2 U =>
      (responseCellMuHilbert hvol a).energyBilin
        (weightedBlockSMulL (U := U) hφm hφb z) :=
    (responseCellMuHilbert hvol a).energyBilin.continuous.comp
      (weightedBlockSMulL (U := U) hφm hφb).continuous
  exact hf.clm_apply continuous_id

/-- The sum of the cutoff-weighted energy of a doubled field and twice its cutoff-weighted
potential-flux readout is continuous in the field.  Its value at the `Mu` minimizer is the
quadratic term of the expansion of the cutoff pairing `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)). -/
theorem continuous_weightedEnergy_add_cutoffQuadReadout {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    Continuous fun z : HilbertBlockL2 U =>
      (responseCellMuHilbert hvol a).energyBilin
          (weightedBlockSMulL (U := U) hφm hφb z) z
        + 2 * cutoffQuadReadout U φ z := by
  exact (continuous_energyBilin_weightedBlockSMulL_self hvol a hφm hφb).add
    (continuous_const.mul (continuous_cutoffQuadReadout U hvol hφm hφb))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-weighted quadratic readout of the canonical optimizer state

The cutoff pairing of the response estimate `e.response.cutoff.estimate` expands, in the notation of
AK.HC Lemma A.1, (A.4), into one quadratic term and three linear terms.  The quadratic term is the
cutoff-weighted volume average of the Euclidean pairing of the two slots of the canonical optimizer
state,

`a ↦ ⨍_{adaptedCell} φ · ⟨Z(a).1, Z(a).2⟩`,

where `Z(a)` is the canonical optimizer state of the recentred coefficient.  This is exactly the
`hquadMinus`/`hquadPlus` input of the family reduction of the cutoff pairing.

The second slot of the canonical optimizer state is the coefficient applied to the first, so this
readout is one half of the cutoff-weighted block self-pairing of `Z(a)`.  The block self-pairing of
`Z(a)` is *not* the block self-pairing of the Chapter-2 doubled minimizer `X(a)`: the a.e.
extraction
identity `ae_toFullBlockVec_canonicalOptimizerBlockState` reads

`Z(a).α = X(a).α + (B_a X(a)).α.swap`,

so the two slots of `Z(a)` are the two slots of `X(a)` shifted by the swapped block image of `X(a)`.
This file records the exact algebraic link between the two self-pairings: pointwise,

`⟨Z(a).1, Z(a).2⟩ = ⟨X(a), B_a X(a)⟩ + 2 ⟨X(a).1, X(a).2⟩`.

Consequently the cutoff-weighted quadratic readout is *not* the (manifestly continuous) functional
`z ↦ ⨍ φ ⟨z.1, z.2⟩` of the Hilbert minimizer; the correct functional of the minimizer additionally
carries the weighted energy `⨍ φ ⟨z, B z⟩`, whose coefficients depend on the sample.  The
measurability of the cutoff-weighted quadratic readout therefore does not follow from the
Hilbert-space continuity argument applied to `⨍ φ ⟨z.1, z.2⟩`, and the identity below is the missing
algebraic link in that route.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- For an elliptic matrix `A`, the two slots of the block image `B A X` satisfy
`⟨(B X).2, (B X).1⟩ = ⟨X.1, X.2⟩`.  Writing `s, k` for the symmetric and skew parts of `A` and
`(B X).1 = s p + k s⁻¹ r`, `(B X).2 = s⁻¹ r` with `r = q - k p`, this is the cancellation of the
skew form on `s⁻¹ r` together with the symmetry of `s`.  It is the exact reason the block
self-pairing of the canonical optimizer state differs from that of the doubled minimizer by a cross
pairing. -/
theorem vecDot_blockMatVecMul_snd_fst {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    vecDot (blockMatVecMul (blockMatrixOfCoeff A) X).2
      (blockMatVecMul (blockMatrixOfCoeff A) X).1 = vecDot X.1 X.2 := by
  let s := symmPart A
  let k := skewPart A
  let r := X.2 - matVecMul k X.1
  have hsnd : (blockMatVecMul (blockMatrixOfCoeff A) X).2 = matVecMul s⁻¹ r := by
    simpa only [s, k, r] using blockMatVecMul_blockMatrixOfCoeff_snd A X.1 X.2
  have hfst : (blockMatVecMul (blockMatrixOfCoeff A) X).1 =
      matVecMul s X.1 + matVecMul k (matVecMul s⁻¹ r) := by
    simpa only [s, k, r] using blockMatVecMul_blockMatrixOfCoeff_fst A X.1 X.2
  have hskew : vecDot (matVecMul s⁻¹ r) (matVecMul k (matVecMul s⁻¹ r)) = 0 := by
    simpa only [k] using vecDot_matVecMul_skewPart_self_eq_zero A (matVecMul s⁻¹ r)
  have hsdet : IsUnit s.det := by
    simpa only [s] using isUnit_det_symmPart_of_isEllipticMatrix hA
  have hsym : vecDot (matVecMul s⁻¹ r) (matVecMul s X.1) = vecDot r X.1 := by
    have h1 : vecDot (matVecMul s⁻¹ r) (matVecMul s X.1) =
        vecDot (matVecMul s (matVecMul s⁻¹ r)) X.1 := by
      have h := vecDot_matVecMul_transpose s (matVecMul s⁻¹ r) X.1
      rw [matTranspose_symmPart] at h
      exact h.symm
    rw [h1, matVecMul_mul, Matrix.mul_nonsing_inv s hsdet, matVecMul_one]
  have hr : vecDot r X.1 = vecDot X.1 X.2 := by
    have hk0 : vecDot (matVecMul k X.1) X.1 = 0 := by
      rw [vecDot_comm]
      exact vecDot_matVecMul_skewPart_self_eq_zero A X.1
    simp only [r, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, hk0, neg_zero, add_zero]
    exact vecDot_comm X.2 X.1
  rw [hsnd, hfst, vecDot_add_right, hsym, hskew, add_zero, hr]

/-- Pointwise link between the self-pairing of the canonical optimizer state and the doubled
minimizer energy.  If `Z = X + swap (B X)` is the state whose slots are the shifted slots of the
doubled minimizer `X`, then

`⟨Z.1, Z.2⟩ = ⟨X, B X⟩ + 2 ⟨X.1, X.2⟩`.

The cross term `2 ⟨X.1, X.2⟩` and the block energy `⟨X, B X⟩` are exactly what is lost by reading
the canonical state pairing as the pairing of the minimizer itself. -/
theorem vecDot_canonical_eq_blockVecDot_add_cross {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    vecDot (X.1 + (blockMatVecMul (blockMatrixOfCoeff A) X).2)
        (X.2 + (blockMatVecMul (blockMatrixOfCoeff A) X).1) =
      blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) + 2 * vecDot X.1 X.2 := by
  have hkey := vecDot_blockMatVecMul_snd_fst hA X
  have hcomm : vecDot (blockMatVecMul (blockMatrixOfCoeff A) X).2 X.2 =
      vecDot X.2 (blockMatVecMul (blockMatrixOfCoeff A) X).2 := vecDot_comm _ _
  simp only [vecDot_add_left, vecDot_add_right, blockVecDot]
  rw [hkey, hcomm]
  ring

/-- The same pointwise link, phrased for the coordinatewise extraction of the canonical optimizer
state of `e.response.cutoff.estimate`: almost everywhere on the domain, the pairing of the two slots
of the canonical optimizer state equals the doubled block energy of the minimizer plus twice the
cross pairing of the minimizer slots.  This is the algebraic content of the gap between the
cutoff-weighted quadratic readout and the pairing of the Hilbert minimizer (AK.HC Lemma A.1,
(A.4)). -/
theorem ae_vecDot_canonicalOptimizerBlockState_eq_blockVecDot {U : Book.Ch02.Domain d}
    {lam Lam : ℝ} {aU : Book.Ch02.CoeffOn U}
    (haU : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), IsEllipticMatrix lam Lam (aU.toCoeffField x))
    (p q : Vec d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU (-p, q) X) :
    (fun x => vecDot
        (canonicalOptimizerBlockState U aU p q x).1
        (canonicalOptimizerBlockState U aU p q x).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x => blockVecDot (X.eval x)
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) +
      2 * vecDot (X.eval x).1 (X.eval x).2 := by
  have hcoordP : ∀ i : Fin d,
      (fun x => (canonicalOptimizerBlockState U aU p q x).1 i)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).1 i +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).2 i := by
    intro i
    have h := ae_toFullBlockVec_canonicalOptimizerBlockState (aU := aU) p q (Sum.inl i) hX
    simpa only [toFullBlockVec, Sum.swap_inl] using h
  have hcoordN : ∀ i : Fin d,
      (fun x => (canonicalOptimizerBlockState U aU p q x).2 i)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).2 i +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).1 i := by
    intro i
    have h := ae_toFullBlockVec_canonicalOptimizerBlockState (aU := aU) p q (Sum.inr i) hX
    simpa only [toFullBlockVec, Sum.swap_inr] using h
  have h1 : (fun x => (canonicalOptimizerBlockState U aU p q x).1)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).1 +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).2 := by
    filter_upwards [ae_all_iff.mpr hcoordP] with x hx
    exact funext fun i => hx i
  have h2 : (fun x => (canonicalOptimizerBlockState U aU p q x).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).2 +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).1 := by
    filter_upwards [ae_all_iff.mpr hcoordN] with x hx
    exact funext fun i => hx i
  filter_upwards [haU, h1, h2] with x hEll h1x h2x
  rw [h1x, h2x]
  exact vecDot_canonical_eq_blockVecDot_add_cross hEll (X.eval x)

end

end HCPolySupport.HighContrast.Multiscale
end
