/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CutoffQuadraticReadout
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.PathwiseToAnnealedAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantEnergyAndFenchelSlots
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ResponseFieldSize
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing

/-!
# High-contrast homogenization: Entry.Response.Direct.DescendantFenchelProbe

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Fenchel Probe on a Descendant Cell and State Measurability

Each generation increment of the descendant sum pairs the dual variable `Y` with the cell
average, over a descendant cell `V` of the terminal cell `U`, of the doubled state of the
terminal optimizer `u`; restricting `u` to `V` changes neither its gradient nor its flux, so the
Fenchel probe of AK.HC (A.4) applies on `V` with the pathwise coarse block there, bounding the
crossed pairing — and, at the carriers, each of its two crossed slots separately — by the
cell's own two-term head times the square root of twice the cell energy. Because a response
maximizer's doubled optimizer field is determined, up to a null set, by the coefficient sample
alone, every cutoff-weighted average of that field over a measurable subcell is itself measurable
in the sample, for `a_-` and `a_+` alike.  These pathwise bounds on the two crossed slots are
the input of the descendant sum of `p.response.transfer`, and the sample-measurability of the
weighted averages is the companion entering the weak quantity of `e.response.weak.estimate`.
-/

section
/-!
## The crossed pairing of the terminal optimizer on a descendant cell

Each generation increment of the descendant sum of `p.response.transfer` pairs the annealed mean
`Y` with the cell average, over a descendant cell `V` of the terminal cell `U`, of the state of
the terminal optimizer `u`.  Restricting `u` to `V` changes neither its gradient nor its flux, so
the Fenchel probe applies on `V` with the pathwise coarse block of `V`, and both crossed slots
are controlled by the source-load head of `V` times the square root of twice the half cell energy
of `u` on `V`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The state of the restricted optimizer is the state of the optimizer.**  Restricting an
`a`-harmonic function from `U` to an open subset `V` on which the coefficient is elliptic does not
change the doubled optimizer state. -/
theorem optimizerField_restrictOfIsEllipticFieldOn {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (u : AHarmonicFunction a U) :
    optimizerField a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) = optimizerField a u := by
  funext x
  have hgrad : (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simp only [optimizerField, hgrad]

/-- **The crossed pairing of the terminal optimizer on a descendant cell.**  Both crossed slots
of the pairing of the annealed mean `Y` with the cell average of the terminal optimizer state on
a descendant cell are at most the source-load head of that cell times the square root of twice
the half cell energy.  This is the pathwise input of the descendant sum of
`p.response.transfer`. -/
theorem abs_volumeAverage_cross_le_head_mul_sqrt {d : ℕ} [NeZero d] {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    (hConv : IsOpenBoundedConvexDomain V)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (hvol : 0 < (volume V).toReal) (u : AHarmonicFunction a U) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2))
    (hX1 : ∀ i, IntegrableOn (fun x => (optimizerField a u x).1 i) V)
    (hX2 : ∀ i, IntegrableOn (fun x => (optimizerField a u x).2 i) V) :
    |volumeAverage V (fun x => vecDot Y.2 (optimizerField a u x).1)|
          ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2)))
            * Real.sqrt (2 * ((1 / 2 : ℝ) *
                volumeAverage V (scalarVariationEnergyIntegrand a u)))
      ∧ |volumeAverage V (fun x => vecDot Y.1 (optimizerField a u x).2)|
          ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2)))
            * Real.sqrt (2 * ((1 / 2 : ℝ) *
                volumeAverage V (scalarVariationEnergyIntegrand a u))) := by
  have hg : volumeAverage V (fun x => vecDot Y.2 (optimizerField a u x).1)
      = vecDot Y.2 (cellAverage V (optimizerField a u)).1 := by
    rw [volumeAverage_vecDot_left Y.2 (fun x => (optimizerField a u x).1) hX1]
    rfl
  have hf : volumeAverage V (fun x => vecDot Y.1 (optimizerField a u x).2)
      = vecDot Y.1 (cellAverage V (optimizerField a u)).2 := by
    rw [volumeAverage_vecDot_left Y.1 (fun x => (optimizerField a u x).2) hX2]
    rfl
  have hgrad := abs_vecDot_cellAverage_grad_le_head hConv hEll hvol
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) Y hA1 hA2
  have hflux := abs_vecDot_cellAverage_flux_le_head hConv hEll hvol
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) Y hA1 hA2
  rw [scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll u] at hgrad hflux
  rw [optimizerField_restrictOfIsEllipticFieldOn hU hV hVU hEll u] at hgrad hflux
  rw [hg, hf]
  exact ⟨hgrad, hflux⟩

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The crossed pairing of the terminal optimizer on a descendant cell, at the carriers

Each generation increment of the descendant sum of `p.response.transfer` pairs the dual variable
`Y` with the cell average, over a descendant cell of the terminal cell, of the doubled state
`(∇u, a∇u)` of the terminal optimizer `u`.  The Fenchel probe bounds each of the two crossed slots
by the two-term head of that cell times the square root of twice the half cell energy, so their sum
is bounded by the head times the square root of twice the doubled cell energy.  The probe is stated
for a pointwise elliptic coefficient, while the recentred coefficients `a_∓` are elliptic only
almost everywhere; it is therefore run at a pointwise elliptic representative on the terminal cell,
which serves every descendant cell at once, and every quantity is transported back across the
almost-everywhere replacement.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The square root of twice the doubled energy is twice the square root of twice the half energy;
no sign hypothesis is needed, because the square root of a negative number is zero on both
sides. -/
private theorem sqrt_two_mul_two_mul (X : ℝ) :
    Real.sqrt (2 * (2 * X)) = 2 * Real.sqrt (2 * ((1 / 2 : ℝ) * X)) := by
  have h1 : (2 : ℝ) * (2 * X) = 4 * X := by ring
  have h2 : (2 : ℝ) * ((1 / 2 : ℝ) * X) = X := by ring
  rw [h1, h2, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) X,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]

/-- **The crossed pairing of the terminal optimizer on a descendant cell, minus sign.**  On each
depth-`m` aligned descendant cell of the terminal cell, the cell average of the scalar crossed
pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a_-∇u⟩` of the terminal optimizer is at most the pathwise two-term head of
that cell times the square root of twice the doubled cell energy.  This is the pathwise input of
the descendant sum of `p.response.transfer`. -/
theorem abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le
    {d : ℕ} [NeZero d] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m)
    (hX1 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hX2 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY1 : IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY2 : IntegrableOn
      (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) :
    |volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffMinus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffMinus F a)).lowerRight Y.2)))
        * Real.sqrt (2 * (2 * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) u))) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ HighContrast.adaptedCell (respGrid jStar F) t := by
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hConv : IsOpenBoundedConvexDomain V := by
    rw [hVdef]
    exact isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq (t - (m : ℤ)) W
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume V).toReal := by
    rw [hVdef]
    exact volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq (t - (m : ℤ)) W
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u₀ : AHarmonicFunction f (HighContrast.adaptedCell (respGrid jStar F) t) :=
    Response.aHarmonicOfAEEq hae u with hu₀
  have hgrad : u₀.toH1.grad = u.toH1.grad := by
    rw [hu₀]
    exact Response.aHarmonicOfAEEq_grad hae u
  -- the two slots of the state, at the representative and at the recentred coefficient
  have hfst : ∀ x, (optimizerField f u₀ x).1
      = (optimizerField (respCoeffMinus F a) u x).1 := by
    intro x
    simp only [optimizerField, hgrad]
  have hsnd : (fun x => (optimizerField f u₀ x).2)
      =ᵐ[volumeMeasureOn V] fun x => (optimizerField (respCoeffMinus F a) u x).2 := by
    filter_upwards [haeV.symm] with x hx
    simp only [optimizerField, hgrad, hx]
  have hX1' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).1 i) V := by
    intro i
    refine (hX1 i).congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrFun (hfst x).symm i
  have hX2' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).2 i) V := by
    intro i
    refine (hX2 i).congr_fun_ae ?_
    filter_upwards [hsnd] with x hx
    exact congrFun hx.symm i
  have hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V f).upperLeft Y.1) :=
    zero_le_vecDot_coarseBlockMatrix_upperLeft hConv hEllV hvol Y.1
  have hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V f).lowerRight Y.2) :=
    zero_le_vecDot_coarseBlockMatrix_lowerRight hConv hEllV hvol Y.2
  obtain ⟨hg, hf⟩ := abs_volumeAverage_cross_le_head_mul_sqrt hU hVopen hVU hConv hEllV hvol u₀ Y
    hA1 hA2 hX1' hX2'
  -- transport of the coarse block and of the cell energy
  have hC : coarseBlockMatrix V f = coarseBlockMatrix V (respCoeffMinus F a) :=
    (coarseBlockMatrix_congr_of_ae_eq haeV).symm
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  -- transport of the two slot averages
  have hgA : volumeAverage V (fun x => vecDot Y.2 (optimizerField f u₀ x).1)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1) := by
    refine congrArg (volumeAverage V) ?_
    funext x
    rw [hfst x]
  have hfA : volumeAverage V (fun x => vecDot Y.1 (optimizerField f u₀ x).2)
      = volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [hsnd] with x hx
    rw [hx]
  rw [hgA] at hg
  rw [hfA] at hf
  rw [hC, hE] at hg hf
  -- split the average of the sum and collect
  set G : ℝ :=
    Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V (respCoeffMinus F a)).upperLeft Y.1))
      + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V (respCoeffMinus F a)).lowerRight Y.2))
    with hGdef
  set X : ℝ := volumeAverage V (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) with hXdef
  have hsplit : volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
        + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2) := by
    have h := volumeAverage_add (U := V) hY1 hY2
    simpa only [Pi.add_apply] using! h
  rw [hsplit, sqrt_two_mul_two_mul X]
  calc |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)|
      ≤ |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)|
        + |volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)| :=
        abs_add_le _ _
    _ ≤ G * Real.sqrt (2 * ((1 / 2 : ℝ) * X))
        + G * Real.sqrt (2 * ((1 / 2 : ℝ) * X)) := add_le_add hg hf
    _ = G * (2 * Real.sqrt (2 * ((1 / 2 : ℝ) * X))) := by ring

/-- **The crossed pairing of the terminal optimizer on a descendant cell, plus sign.**  The adjoint
twin of `abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le`, for the
recentred
coefficient `a_+ = aᵀ + g` and the dual variable `Y^+`. -/
theorem abs_volumeAverage_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter_le
    {d : ℕ} [NeZero d] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m)
    (hX1 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) u x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hX2 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) u x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY1 : IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY2 : IntegrableOn
      (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) :
    |volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffPlus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffPlus F a)).lowerRight Y.2)))
        * Real.sqrt (2 * (2 * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) u))) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ HighContrast.adaptedCell (respGrid jStar F) t := by
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hConv : IsOpenBoundedConvexDomain V := by
    rw [hVdef]
    exact isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq (t - (m : ℤ)) W
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume V).toReal := by
    rw [hVdef]
    exact volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq (t - (m : ℤ)) W
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u₀ : AHarmonicFunction f (HighContrast.adaptedCell (respGrid jStar F) t) :=
    Response.aHarmonicOfAEEq hae u with hu₀
  have hgrad : u₀.toH1.grad = u.toH1.grad := by
    rw [hu₀]
    exact Response.aHarmonicOfAEEq_grad hae u
  have hfst : ∀ x, (optimizerField f u₀ x).1
      = (optimizerField (respCoeffPlus F a) u x).1 := by
    intro x
    simp only [optimizerField, hgrad]
  have hsnd : (fun x => (optimizerField f u₀ x).2)
      =ᵐ[volumeMeasureOn V] fun x => (optimizerField (respCoeffPlus F a) u x).2 := by
    filter_upwards [haeV.symm] with x hx
    simp only [optimizerField, hgrad, hx]
  have hX1' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).1 i) V := by
    intro i
    refine (hX1 i).congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrFun (hfst x).symm i
  have hX2' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).2 i) V := by
    intro i
    refine (hX2 i).congr_fun_ae ?_
    filter_upwards [hsnd] with x hx
    exact congrFun hx.symm i
  have hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V f).upperLeft Y.1) :=
    zero_le_vecDot_coarseBlockMatrix_upperLeft hConv hEllV hvol Y.1
  have hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V f).lowerRight Y.2) :=
    zero_le_vecDot_coarseBlockMatrix_lowerRight hConv hEllV hvol Y.2
  obtain ⟨hg, hf⟩ := abs_volumeAverage_cross_le_head_mul_sqrt hU hVopen hVU hConv hEllV hvol u₀ Y
    hA1 hA2 hX1' hX2'
  have hC : coarseBlockMatrix V f = coarseBlockMatrix V (respCoeffPlus F a) :=
    (coarseBlockMatrix_congr_of_ae_eq haeV).symm
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  have hgA : volumeAverage V (fun x => vecDot Y.2 (optimizerField f u₀ x).1)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1) := by
    refine congrArg (volumeAverage V) ?_
    funext x
    rw [hfst x]
  have hfA : volumeAverage V (fun x => vecDot Y.1 (optimizerField f u₀ x).2)
      = volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [hsnd] with x hx
    rw [hx]
  rw [hgA] at hg
  rw [hfA] at hf
  rw [hC, hE] at hg hf
  set G : ℝ :=
    Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V (respCoeffPlus F a)).upperLeft Y.1))
      + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V (respCoeffPlus F a)).lowerRight Y.2))
    with hGdef
  set X : ℝ := volumeAverage V (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) with hXdef
  have hsplit : volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
        + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2) := by
    have h := volumeAverage_add (U := V) hY1 hY2
    simpa only [Pi.add_apply] using! h
  rw [hsplit, sqrt_two_mul_two_mul X]
  calc |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)|
      ≤ |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)|
        + |volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)| :=
        abs_add_le _ _
    _ ≤ G * Real.sqrt (2 * ((1 / 2 : ℝ) * X))
        + G * Real.sqrt (2 * ((1 / 2 : ℝ) * X)) := add_le_add hg hf
    _ = G * (2 * Real.sqrt (2 * ((1 / 2 : ℝ) * X))) := by ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Weighted averages of the doubled optimizer field are measurable in the sample

The doubled optimizer field of a response maximizer for the recentred coefficients `a_-` and `a_+`
is determined, up to a null set of the response cell, by the coefficient sample alone: Chapter-2
almost-everywhere gradient uniqueness identifies every response maximizer with the canonical
selection.  Consequently every cutoff-weighted average of a coordinate of the doubled optimizer
field over a measurable subcell is a measurable function of the sample, for an arbitrary family of
maximizers.  This is the linear companion of the weighted energy readout: it gives the
sample-measurability of the cutoff-weighted state mean entering the weak quantity of
`e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The canonical doubled optimizer state depends on the coefficient only through its
almost-everywhere class on the domain. -/
private theorem canonicalOptimizerBlockState_congr_ae {d : ℕ} {U : Book.Ch02.Domain d}
    {A B : Book.Ch02.CoeffOn U} (hAB : Book.Ch02.CoeffOn.AEEq A B) (p r : Vec d) :
    canonicalOptimizerBlockState U A p r
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] canonicalOptimizerBlockState U B p r := by
  have hgrad : (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U A) p r).toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U B) p r).toSolution.toH1.grad := by
    simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
      (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
  filter_upwards [hgrad, hAB] with x hgradx hcoeffx
  simp only [canonicalOptimizerBlockState]
  rw [hgradx, hcoeffx]

/-- An arbitrary response maximizer for the recentred coefficient `a_-` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
theorem optimizerField_ae_eq_canonicalState_respCoeffMinus {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    optimizerField (respCoeffMinus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  let A : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain q hq t) hlam hle hEll
  let v : ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hgrad : optimizerField (respCoeffMinus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffMinus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad x
        = u.toH1.grad x := AHarmonicFunction.grad_normalizeMeanZero u x
    simp only [optimizerField, hg]
  have hcanon : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffMinus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        = optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) := by
      funext x
      rfl
    have hstateEq : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) :=
      Filter.Eventually.of_forall (fun x => congrFun hstate x)
    exact hstateEq.trans (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      (U := adaptedDomain q hq t) hlam hle hEll hbf p r v)
  have hAB : Book.Ch02.CoeffOn.AEEq A (canonicalRespCoeffMinusOn q hq t F a) := by
    filter_upwards [hbf.symm] with x hx
    simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
  have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r :=
    canonicalOptimizerBlockState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- An arbitrary response maximizer for the recentred coefficient `a_+` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
theorem optimizerField_ae_eq_canonicalState_respCoeffPlus {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    optimizerField (respCoeffPlus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  let A : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain q hq t) hlam hle hEll
  let v : ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hgrad : optimizerField (respCoeffPlus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffPlus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad x
        = u.toH1.grad x := AHarmonicFunction.grad_normalizeMeanZero u x
    simp only [optimizerField, hg]
  have hcanon : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffPlus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        = optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) := by
      funext x
      rfl
    have hstateEq : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) :=
      Filter.Eventually.of_forall (fun x => congrFun hstate x)
    exact hstateEq.trans (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      (U := adaptedDomain q hq t) hlam hle hEll hbf p r v)
  have hAB : Book.Ch02.CoeffOn.AEEq A (canonicalRespCoeffPlusOn q hq t F a) := by
    filter_upwards [hbf.symm] with x hx
    simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
  have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r :=
    canonicalOptimizerBlockState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- Every cutoff-weighted average of a coordinate of the doubled optimizer field of an arbitrary
family of response maximizers for the recentred coefficient `a_-` is measurable in the coefficient
sample.  The field need not be measurable in the sample, but its weighted average is determined by
the measurable canonical selection through Chapter-2 a.e. gradient uniqueness, so the weighted
subcell mean entering the weak quantity of `e.response.weak.estimate` is measurable. -/
theorem measurable_volumeAverage_weighted_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) alpha) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) alpha))
      = fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
          toFullBlockVec (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x) alpha) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffMinus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (uM a) (hmax a)
    have hInt : (fun x => eta x *
          toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) alpha)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * toFullBlockVec (canonicalOptimizerBlockState
          (adaptedDomain (respGrid jStar F) hq t)
          (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x) alpha) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffMinus F a) (uM a) x = _ from hx]
    exact volumeAverage_congr_ae hVU hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_canonicalRespCoeffMinus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) alpha hV hVU heta

/-- Every cutoff-weighted average of a coordinate of the doubled optimizer field of an arbitrary
family of response maximizers for the recentred coefficient `a_+` is measurable in the coefficient
sample.  This is the plus twin of
`measurable_volumeAverage_weighted_optimizerField_respCoeffMinus`. -/
theorem measurable_volumeAverage_weighted_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) alpha) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) alpha))
      = fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
          toFullBlockVec (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x) alpha) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffPlus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (uP a) (hmax a)
    have hInt : (fun x => eta x *
          toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) alpha)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * toFullBlockVec (canonicalOptimizerBlockState
          (adaptedDomain (respGrid jStar F) hq t)
          (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x) alpha) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffPlus F a) (uP a) x = _ from hx]
    exact volumeAverage_congr_ae hVU hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_canonicalRespCoeffPlus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) alpha hV hVU heta

end

end HCPolySupport.HighContrast.Multiscale
end
