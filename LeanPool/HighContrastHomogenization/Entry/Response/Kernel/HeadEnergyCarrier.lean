/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.HeadCellDeficitInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.QuadraticResponseRecombination

/-!
# High-contrast homogenization: Entry.Response.Kernel.HeadEnergyCarrier

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The head's averaged-energy hypothesis at the estimate's carriers

The finite-window head of the diagonal weak-norm estimate needs, at each depth, the flat average
over the triadic index box of twice the scalar difference energy between the parent and child
response maximizers, bounded by the response load times the operator norm of the averaged
normalized block defect. The recentred coefficient is only an almost-everywhere class and is
never elliptic pointwise, so this file runs the identity at an almost-everywhere-equal elliptic
representative, transporting the maximizers to it and the resulting bound back, leaving no
pointwise ellipticity or coefficient-dependent integrability hypothesis in the conclusion.
It supplies the averaged-energy hypothesis consumed by the cell-average estimate of the
weak-norm bound `e.response.weak.estimate`.
-/

section
/-!
## The averaged-energy hypothesis of the cell-average estimate at the estimate's carriers

The cell-average estimate of the weak-norm bound (`e.response.weak.estimate`) consumes, at each
depth `n`, a per-cell family whose flat average over the triadic index box is bounded by the
printed product of the response load and the operator norm of the averaged normalized block
defect.  The per-cell half of that estimate produces `G w` as twice the scalar difference energy
of the maximizers `u` and `v w` on the aligned subcell
`adaptedCellAtCenter (respGrid jStar F) (t - n) w`:

`G w = 2 ⨍_{V w} (∇u − ∇v_w) · symmPart(a_-) (∇u − ∇v_w)`.

The response identity that turns the flat average of those difference energies into the averaged
response deficit is stated for a coefficient that is pointwise elliptic on the cell.  The
recentred coefficient `a_- = respCoeffMinus F a` is only an almost-everywhere class and is never
elliptic pointwise, so the identity cannot be instantiated at it directly.  This module runs the
identity at an almost-everywhere-equal elliptic representative of `a_-`, transports the
maximizers to that representative, and transports the conclusion back: every quantity in the
conclusion is almost-everywhere invariant in the coefficient.  The result therefore carries none
of the pointwise ellipticity or coefficient-dependent integrability hypotheses that the
representative argument removes.

The algebraic tail is the printed chain: the pointwise identity
`optimizerField b u − optimizerField b v = (∇u − ∇v, b (∇u − ∇v))` turns the doubled optimizer
difference energy into the symmetric scalar difference energy, the recombined quadratic-response
identity rewrites the flat average of the difference energies as twice the deficit of the response
functional, each response value is the coarse-block quadratic form of its cell, and the averaged
response deficit is the quadratic form of the averaged block defect, bounded by the normalized
Loewner comparison through the response load and the operator norm of the averaged normalized
defect.  See `e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The zero harmonic function on a set.  It is used only as a total placeholder for the child
family away from the triadic index box, where the family is never consumed. -/
@[expose]
public def zeroAHarmonic (a : CoeffField d) (U : Set (Vec d)) : AHarmonicFunction a U :=
  { toH1 := 0, isHarmonic := isAHarmonicGradient_zero }

omit [NeZero d] in
/-- **Maximizers transport across an almost-everywhere equality of coefficient fields.**  If `v`
maximizes the response functional for the coefficient `b` on `U`, then the same field, read as an
`f`-harmonic function along `b =ᵐ f`, maximizes the response functional for `f`.  Both response
averages are rewritten by `volumeAverage_scalarResponseIntegrand_congr`. -/
private theorem isResponseMaximizer_of_ae_eq {U : Set (Vec d)} {b f : CoeffField d}
    {p r : Vec d} (hae : b =ᵐ[volumeMeasureOn U] f) {v : AHarmonicFunction b U}
    (hv : IsResponseMaximizer U p r b v) :
    IsResponseMaximizer U p r f (Response.aHarmonicOfAEEq hae v) := by
  intro z
  have key := hv (Response.aHarmonicOfAEEq hae.symm z)
  have h1 : volumeAverage U (scalarResponseIntegrand U f p r z) =
      volumeAverage U (scalarResponseIntegrand U b p r
        (Response.aHarmonicOfAEEq hae.symm z)) :=
    volumeAverage_scalarResponseIntegrand_congr hae.symm p r z _ (fun _ => rfl)
  have h2 : volumeAverage U (scalarResponseIntegrand U b p r v) =
      volumeAverage U (scalarResponseIntegrand U f p r
        (Response.aHarmonicOfAEEq hae v)) :=
    volumeAverage_scalarResponseIntegrand_congr hae p r v _ (fun _ => rfl)
  rw [h1, ← h2]
  exact key

omit [NeZero d] in
/-- **The scalar difference-energy average is an almost-everywhere invariant of the
coefficient.**  Two coefficients that agree almost everywhere on `V` give the same average of
`ξ · symmPart(a) ξ` for any field `ξ`. -/
private theorem volumeAverage_diffEnergy_congr_ae {V : Set (Vec d)} {b f : CoeffField d}
    (hae : b =ᵐ[volumeMeasureOn V] f) (ξ : Vec d → Vec d) :
    volumeAverage V (fun x => vecDot (ξ x) (matVecMul (symmPart (f x)) (ξ x))) =
      volumeAverage V (fun x => vecDot (ξ x) (matVecMul (symmPart (b x)) (ξ x))) := by
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-- At an elliptic representative of the recentred coefficient, the average of the symmetric
scalar difference energies is twice the averaged response deficit.  The proof transports both
maximizers to that representative and uses almost-everywhere invariance to return to the original
coefficient. -/
private theorem headEnergy_response_deficit (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (v : (w : Fin d → ℤ) → AHarmonicFunction (respCoeffMinus F a)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (hv : ∀ w ∈ triadicIndexBox d n,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w))
 :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (fun y => vecDot (u.toH1.grad y - (v w).toH1.grad y)
            (matVecMul (symmPart (respCoeffMinus F a y))
              (u.toH1.grad y - (v w).toH1.grad y)))
      = 2 * (((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
              (respCoeffMinus F a)
            - ResponseJ (HighContrast.adaptedCell (respGrid jStar F) t)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
              (respCoeffMinus F a)) := by
  classical
  let Z : Finset (Fin d → ℤ) := triadicIndexBox d n
  let b : CoeffField d := respCoeffMinus F a
  let p : Vec d := respP (respMean P jStar F t) e
  let r : Vec d := respqMinus P jStar F t e
  let q : Mat d := respGrid jStar F
  -- Step A.  One elliptic representative of the recentred coefficient, on the parent cell and
  -- hence, by monotonicity, on every aligned subcell.
  obtain ⟨lam, Lam, f, _hlam, _hle, hEllU, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hgrid t F a
  have hVU : ∀ w ∈ Z, adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n (by simpa [Z] using hw)
  have hEll : ∀ w ∈ Z, IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f := by
    intro w hw
    exact IsEllipticFieldOn.mono hEllU
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet (hVU w hw)
  have haeW : ∀ w ∈ Z, b =ᵐ[volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)] f := by
    intro w hw
    exact MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono (hVU w hw) le_rfl) hae
  have : ∀ w, IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) :=
    fun w => (isOpenBoundedConvexDomain_adaptedCellAtCenter q hgrid (t - (n : ℤ)) w).isFiniteMeasure_restrict_volume
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    (adaptedCell_isOpenBoundedConvexDomain q hgrid t).isFiniteMeasure_restrict_volume
  -- Step B.  Transport the parent maximizer and each child maximizer to the representative.
  let uT : AHarmonicFunction f (HighContrast.adaptedCell q t) := Response.aHarmonicOfAEEq hae u
  have huT : IsResponseMaximizer (HighContrast.adaptedCell q t) p r f uT :=
    isResponseMaximizer_of_ae_eq hae hu
  let vT : (w : Fin d → ℤ) → AHarmonicFunction f (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w => if hw : w ∈ Z then
        Response.aHarmonicOfAEEq (haeW w hw) (v w)
      else zeroAHarmonic f (adaptedCellAtCenter q (t - (n : ℤ)) w)
  have hvT : ∀ w ∈ Z, IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f (vT w) := by
    intro w hw
    have hvw : vT w = Response.aHarmonicOfAEEq (haeW w hw) (v w) := dite_eq_left hw
    rw [hvw]
    exact isResponseMaximizer_of_ae_eq (haeW w hw) (hv w hw)
  -- Step C.  The response identity at `f`, with its integrability side conditions supplied by the
  -- pointwise elliptic datum through `ResponseLinearIntegrabilityData.of_isEllipticFieldOn`.
  have hIntW : ∀ w ∈ Z, ResponseLinearIntegrabilityData (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    fun w hw => ResponseLinearIntegrabilityData.of_isEllipticFieldOn (hEll w hw)
  have hIntU : ResponseLinearIntegrabilityData (HighContrast.adaptedCell q t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllU
  have huV_int : ∀ w (hw : w ∈ Z),
      weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
        (uT.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hgrid t)
          (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w)
          (hVU w hw) (hEll w hw)) :=
    fun w hw => (hIntW w hw).weakFlux _
  have hv_int : ∀ w ∈ Z, weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f (vT w) :=
    fun w hw => (hIntW w hw).weakFlux (vT w)
  have hresp_v : ∀ w ∈ Z,
      IntegrableOn (scalarResponseIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) f p r (vT w))
        (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w hw => (hIntW w hw).response p r (vT w)
  have hlin : ∀ w (hw : w ∈ Z),
      IntegrableOn (scalarFirstVariationIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) f p r (vT w)
        (AHarmonicFunction.addSMulOfIntegrable
          (uT.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hgrid t)
            (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w)
            (hVU w hw) (hEll w hw)) (vT w)
          (huV_int w hw) (hv_int w hw) (-1)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w hw => (hIntW w hw).firstVariation p r (vT w) _
  have henergy : ∀ w (hw : w ∈ Z),
      IntegrableOn (scalarVariationEnergyIntegrand f
        (AHarmonicFunction.addSMulOfIntegrable
          (uT.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hgrid t)
            (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w)
            (hVU w hw) (hEll w hw)) (vT w)
          (huV_int w hw) (hv_int w hw) (-1)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w hw => (hIntW w hw).energy _
  have hint : IntegrableOn (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r uT)
      (HighContrast.adaptedCell q t) :=
    hIntU.response p r uT
  have hSf : ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun y => vecDot (uT.toH1.grad y - (vT w).toH1.grad y)
            (matVecMul (symmPart (f y)) (uT.toH1.grad y - (vT w).toH1.grad y))))
      = 2 * ((Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
        - ResponseJ (HighContrast.adaptedCell q t) p r f) := by
    exact avg_difference_energy_eq_responseJ_deficit_adaptedCell_ae q hgrid t n
      (a := f) (p := p) (r := r) uT vT hEll hvT huV_int hv_int hresp_v hlin henergy hint huT
  -- Step D.  Transport the identity back to `respCoeffMinus F a`.
  let G' : (Fin d → ℤ) → ℝ := fun w =>
    volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun y => vecDot (u.toH1.grad y - (v w).toH1.grad y)
        (matVecMul (symmPart (b y)) (u.toH1.grad y - (v w).toH1.grad y)))
  have hAS : ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun y => vecDot (uT.toH1.grad y - (vT w).toH1.grad y)
            (matVecMul (symmPart (f y)) (uT.toH1.grad y - (vT w).toH1.grad y))))
      = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G' w := by
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    have hvw : vT w = Response.aHarmonicOfAEEq (haeW w hw) (v w) := dite_eq_left hw
    rw [hvw]
    exact volumeAverage_diffEnergy_congr_ae (haeW w hw)
      (fun y => u.toH1.grad y - (v w).toH1.grad y)
  have hsumJ : (∑ w ∈ Z, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f)
      = ∑ w ∈ Z, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b :=
    Finset.sum_congr rfl
      (fun w hw => (HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq (haeW w hw) p r).symm)
  have hparJ : ResponseJ (HighContrast.adaptedCell q t) p r f
      = ResponseJ (HighContrast.adaptedCell q t) p r b :=
    (HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae p r).symm
  have hBS : ((Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
        - ResponseJ (HighContrast.adaptedCell q t) p r f)
      = ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
        - ResponseJ (HighContrast.adaptedCell q t) p r b) := by
    rw [hsumJ, hparJ]
  have hS : ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G' w)
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
          ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - ResponseJ (HighContrast.adaptedCell q t) p r b) := by
    rw [← hAS, ← hBS]
    exact hSf
  simpa [Z, G', b, q, p, r] using hS

/-- **The averaged-energy hypothesis of the cell-average estimate, with no pointwise ellipticity
hypothesis.**  For the per-cell family that is twice the scalar difference energy of the
maximizers `u` and `v w` on the aligned subcells
`adaptedCellAtCenter (respGrid jStar F) (t - n) w`, the flat average over the triadic index box is
bounded by twice the response load times the operator norm of the averaged normalized block
defect `weakAverageDefect`.

The identity is run at an almost-everywhere-equal representative `f` of `respCoeffMinus F a` that
is pointwise elliptic on the parent adapted cell; the parent and child maximizers are transported
to `f` along the almost-everywhere equality, and the resulting identity is transported back
because both the scalar difference energy and each response value depend on the coefficient only
through its almost-everywhere class.  No pointwise ellipticity and no coefficient-dependent
integrability hypothesis remains.  See `e.response.weak.estimate`. -/
theorem headEnergy_carrier_minus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (v : (w : Fin d → ℤ) → AHarmonicFunction (respCoeffMinus F a)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (hv : ∀ w ∈ triadicIndexBox d n,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w))
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (fun x => vecDot
            (optimizerField (respCoeffMinus F a) u x -
              optimizerField (respCoeffMinus F a) (v w) x).1
            (optimizerField (respCoeffMinus F a) u x -
              optimizerField (respCoeffMinus F a) (v w) x).2))
      ≤ 2 * respLsqMinus P jStar F t e *
          ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
            (respEhatMinus P jStar F t) (respCoeffMinus F a))‖ := by
  classical
  let Z : Finset (Fin d → ℤ) := triadicIndexBox d n
  let b : CoeffField d := respCoeffMinus F a
  let p : Vec d := respP (respMean P jStar F t) e
  let r : Vec d := respqMinus P jStar F t e
  let q : Mat d := respGrid jStar F
  let E : BlockMat d := respEhatMinus P jStar F t
  let x : BlockVec d := (-p, r)
  have hS := headEnergy_response_deficit P jStar F t e hgrid a n u hu v hv
  -- Step E.  The goal's integrand is the symmetric scalar difference energy.
  have hpt : ∀ w, (fun y => vecDot (optimizerField b u y - optimizerField b (v w) y).1
        (optimizerField b u y - optimizerField b (v w) y).2)
      = fun y => vecDot (u.toH1.grad y - (v w).toH1.grad y)
          (matVecMul (symmPart (b y)) (u.toH1.grad y - (v w).toH1.grad y)) := by
    intro w
    funext y
    have hsubmv : matVecMul (b y) (u.toH1.grad y) - matVecMul (b y) ((v w).toH1.grad y)
        = matVecMul (b y) (u.toH1.grad y - (v w).toH1.grad y) := by
      funext i
      simp only [matVecMul, Pi.sub_apply, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [optimizerField, Prod.fst_sub, Prod.snd_sub, hsubmv, vecDot_matVecMul_symmPart]
  have hG : ∀ w ∈ Z, (2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (fun y => vecDot (optimizerField b u y - optimizerField b (v w) y).1
          (optimizerField b u y - optimizerField b (v w) y).2)) = 2 * G' w := by
    intro w _
    exact congrArg (fun g => 2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g) (hpt w)
  -- Step F.  The algebraic tail: response values as coarse-block quadratics, the averaged
  -- response deficit as the quadratic form of the averaged block defect, and the normalized
  -- Loewner comparison.
  let Q : (Fin d → ℤ) → ℝ := fun w =>
    blockVecDot x (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b) x)
  let QU : ℝ := blockVecDot x
    (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q t) b) x)
  have hRespV : ∀ w ∈ Z, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
      = (1 / 2 : ℝ) * Q w - vecDot p r := by
    intro w _
    exact responseJ_adaptedCellAtCenter_respCoeffMinus q hgrid (t - (n : ℤ)) w F a p r
  have hRespU : ResponseJ (HighContrast.adaptedCell q t) p r b
      = (1 / 2 : ℝ) * QU - vecDot p r := by
    exact responseJ_adaptedCell_respCoeffMinus q hgrid t F a p r
  have hcard : (Z.card : ℝ) ≠ 0 := by
    have hne : Z.Nonempty := by
      change (triadicIndexBox d n).Nonempty
      refine ⟨0, ?_⟩
      rw [triadicIndexBox, Fintype.mem_piFinset]
      intro i
      exact Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Int.natCast_nonneg _),
        Int.natCast_nonneg _⟩
    exact_mod_cast (Finset.card_ne_zero.mpr hne)
  have hC : 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
          - ResponseJ (HighContrast.adaptedCell q t) p r b)
      = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (Q w - QU) := by
    rw [hRespU, Finset.sum_congr rfl (fun w _ => hRespV w ‹w ∈ Z›)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
    field_simp [hcard]
    ring
  have hDef : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (Q w - QU)
      = blockVecDot x (blockMatVecMul
          (ofFullBlockMat
            ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z, toFullBlockMat
                (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                  (coarseBlockMatrix (HighContrast.adaptedCell q t) b)))) x) := by
    exact response_deficit_eq_blockQuadratic q t n b x Q QU (fun w _ => rfl) rfl
  have hle : blockVecDot x (blockMatVecMul
        (ofFullBlockMat
          ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z, toFullBlockMat
              (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                (coarseBlockMatrix (HighContrast.adaptedCell q t) b)))) x)
      ≤ ‖toFullBlockMat (weakAverageDefect q t n E b)‖
          * blockVecDot x (blockMatVecMul E x) :=
    average_defect_quadratic_le q t n hEhat b x
  have hLsq : respLsqMinus P jStar F t e = blockVecDot x (blockMatVecMul E x) := by
    rw [respLsqMinus_eq_quadratic]
    rfl
  have hmain : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        (2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun y => vecDot (optimizerField b u y - optimizerField b (v w) y).1
            (optimizerField b u y - optimizerField b (v w) y).2))
      ≤ 2 * respLsqMinus P jStar F t e
          * ‖toFullBlockMat (weakAverageDefect q t n E b)‖ := by
    calc
      (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
          (2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun y => vecDot (optimizerField b u y - optimizerField b (v w) y).1
              (optimizerField b u y - optimizerField b (v w) y).2))
          = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G' w) := by
            rw [Finset.sum_congr rfl hG, ← Finset.mul_sum]
            ring
      _ = 2 * (2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
              ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
                - ResponseJ (HighContrast.adaptedCell q t) p r b)) := by
            rw [hS]
      _ = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (Q w - QU)) := by rw [hC]
      _ = 2 * blockVecDot x (blockMatVecMul
            (ofFullBlockMat
              ((Z.card : ℝ)⁻¹ •
                ∑ w ∈ Z, toFullBlockMat
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b)))) x) := by
            rw [hDef]
      _ ≤ 2 * (‖toFullBlockMat (weakAverageDefect q t n E b)‖
              * blockVecDot x (blockMatVecMul E x)) := by
            linarith only [hle]
      _ = 2 * respLsqMinus P jStar F t e
            * ‖toFullBlockMat (weakAverageDefect q t n E b)‖ := by
            rw [hLsq]
            ring
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end
