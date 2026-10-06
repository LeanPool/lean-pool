/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.PathwiseToAnnealedAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantFenchelProbe
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellEnergyIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.SourceLoadHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalHalfEnergyIntegrability

/-!
# High-contrast homogenization: Entry.Response.Rows.CarrierIntegrabilityConditions

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Side Conditions of the Cutoff-Mean Row at the Carriers

Since a response maximizer's doubled optimizer field is determined, up to a null set, by the
coefficient sample alone, every cutoff-weighted average of a coordinate of that field over a
measurable subcell is measurable in the sample, and so is the weighted cell average of the
crossed pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a ∇u⟩` against a deterministic state `Y`.
Recentring by a constant skew matrix is a block congruence, so the entries of the pathwise coarse
block of `a_- = a - g` and `a_+ = a^T + g` are fixed linear combinations of the sample's own
coarse-block entries and inherit its integrability. The two-term head `√(P · b P) + √(Q ·
S_*^{-1} Q)` then inherits, from this and the nonnegativity of its two quadratic forms, the
integrability of its cross term and of its own square; it also records the `P`-integrability of
the annealed cell energy of the terminal optimizer on a descendant cell.  These are the carrier
side conditions of the cutoff-mean row of `p.response.transfer`.
-/

section
/-!
## Weighted cell averages of the crossed pairing are measurable in the sample

The oscillation half of the cutoff-mean row of `p.response.transfer` reads, on each cell `V` of a
triadic refinement of the terminal cell, the weighted cell average of the scalar crossed pairing
`⟨Y₂, ∇u⟩ + ⟨Y₁, a ∇u⟩` of the terminal optimizer against the deterministic dual variable `Y`.
Because `Y` is deterministic, that scalar is a fixed linear combination of the `2d` coordinates of
the doubled optimizer state, so its weighted cell average is the same linear combination of the
`2d` weighted coordinate averages, each of which is measurable in the sample by
`DescendantFenchelProbe`.  The coordinate averages are finite by `TerminalDeficitCarrierBound`,
which needs
only continuity of the weight.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The weighted cell average of the crossed pairing is the `Y`-combination of the `2d` weighted
coordinate averages, for an arbitrary doubled field whose coordinates are integrable on `V`. -/
private theorem volumeAverage_weighted_cross_eq_sum {d : ℕ} {V : Set (Vec d)}
    (eta : Vec d → ℝ) (X : Vec d → BlockVec d) (Y : BlockVec d)
    (h1 : ∀ i : Fin d, IntegrableOn (fun x => eta x * (X x).1 i) V)
    (h2 : ∀ i : Fin d, IntegrableOn (fun x => eta x * (X x).2 i) V) :
    volumeAverage V (fun x => eta x * (vecDot Y.2 (X x).1 + vecDot Y.1 (X x).2))
      = (∑ i : Fin d, Y.2 i * volumeAverage V (fun x => eta x * (X x).1 i))
        + ∑ i : Fin d, Y.1 i * volumeAverage V (fun x => eta x * (X x).2 i) := by
  classical
  have hs1 : ∀ i : Fin d, IntegrableOn (fun x => Y.2 i * (eta x * (X x).1 i)) V :=
    fun i => (h1 i).const_mul (Y.2 i)
  have hs2 : ∀ i : Fin d, IntegrableOn (fun x => Y.1 i * (eta x * (X x).2 i)) V :=
    fun i => (h2 i).const_mul (Y.1 i)
  have hsum1 : IntegrableOn (fun x => ∑ i : Fin d, Y.2 i * (eta x * (X x).1 i)) V :=
    integrable_finsetSum _ fun i _ => hs1 i
  have hsum2 : IntegrableOn (fun x => ∑ i : Fin d, Y.1 i * (eta x * (X x).2 i)) V :=
    integrable_finsetSum _ fun i _ => hs2 i
  have hsplit : (fun x => eta x * (vecDot Y.2 (X x).1 + vecDot Y.1 (X x).2))
      = (fun x => ∑ i : Fin d, Y.2 i * (eta x * (X x).1 i))
        + fun x => ∑ i : Fin d, Y.1 i * (eta x * (X x).2 i) := by
    funext x
    simp only [Pi.add_apply, vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, volumeAverage_add hsum1 hsum2,
    volumeAverage_sum Finset.univ (fun i x => Y.2 i * (eta x * (X x).1 i))
      (fun i _ => hs1 i),
    volumeAverage_sum Finset.univ (fun i x => Y.1 i * (eta x * (X x).2 i))
      (fun i _ => hs2 i)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun x => Y.2 i * (eta x * (X x).1 i))
        = Y.2 i • fun x => eta x * (X x).1 i by funext x; simp [smul_eq_mul]]
    exact volumeAverage_smul V (Y.2 i) _
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun x => Y.1 i * (eta x * (X x).2 i))
        = Y.1 i • fun x => eta x * (X x).2 i by funext x; simp [smul_eq_mul]]
    exact volumeAverage_smul V (Y.1 i) _

/-- **The weighted cell average of the crossed pairing is measurable in the sample, minus sign.**
For a continuous weight whose indicator is square-integrable on the terminal cell and any
measurable subcell `V`, the `V`-average of `eta · (⟨Y₂, ∇u⟩ + ⟨Y₁, a_- ∇u⟩)` is a measurable
function of the coefficient sample, for an arbitrary family of terminal maximizers. -/
theorem measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta)
    (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) := by
  classical
  have hI := fun (a : CoeffSpace d) (i : Fin d) =>
    integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm t uM hV hVU
      hetac a i
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)))
      = fun a : CoeffSpace d =>
        (∑ i : Fin d, Y.2 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) (Sum.inl i)))
          + ∑ i : Fin d, Y.1 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) (Sum.inr i)) := by
    funext a
    exact volumeAverage_weighted_cross_eq_sum eta
      (optimizerField (respCoeffMinus F a) (uM a)) Y (fun i => (hI a i).1) (fun i => (hI a i).2)
  rw [hEq]
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
    (Finset.measurable_sum _ fun i _ => ?_)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffMinus P jStar hjStar F hm t e
      (Sum.inl i) uM hmax hV hVU heta).const_mul (Y.2 i)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffMinus P jStar hjStar F hm t e
      (Sum.inr i) uM hmax hV hVU heta).const_mul (Y.1 i)

/-- **The weighted cell average of the crossed pairing is measurable in the sample, plus sign.**
The adjoint twin of
`measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus`. -/
theorem measurable_volumeAverage_weighted_cross_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta)
    (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) := by
  classical
  have hI := fun (a : CoeffSpace d) (i : Fin d) =>
    integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm t uP hV hVU
      hetac a i
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)))
      = fun a : CoeffSpace d =>
        (∑ i : Fin d, Y.2 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) (Sum.inl i)))
          + ∑ i : Fin d, Y.1 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) (Sum.inr i)) := by
    funext a
    exact volumeAverage_weighted_cross_eq_sum eta
      (optimizerField (respCoeffPlus F a) (uP a)) Y (fun i => (hI a i).1) (fun i => (hI a i).2)
  rw [hEq]
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
    (Finset.measurable_sum _ fun i _ => ?_)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffPlus P jStar hjStar F hm t e
      (Sum.inl i) uP hmax hV hVU heta).const_mul (Y.2 i)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffPlus P jStar hjStar F hm t e
      (Sum.inr i) uP hmax hV hVU heta).const_mul (Y.1 i)

/-- **The unweighted cell average of the crossed pairing is measurable in the sample, minus
sign.**  The constant-weight case of
`measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus`; the indicator of a
measurable subcell by the constant `1` is square-integrable on the terminal cell. -/
theorem measurable_volumeAverage_cross_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  simpa only [one_mul] using
    measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus P jStar hjStar F hm t e
      uM hmax hV hVU (eta := fun _ : Vec d => (1 : ℝ)) continuous_const
      (memScalarL2_indicator_one
        (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t) hV) Y

/-- **The unweighted cell average of the crossed pairing is measurable in the sample, plus
sign.**  The adjoint twin of
`measurable_volumeAverage_cross_optimizerField_respCoeffMinus`. -/
theorem measurable_volumeAverage_cross_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  simpa only [one_mul] using
    measurable_volumeAverage_weighted_cross_optimizerField_respCoeffPlus P jStar hjStar F hm t e
      uP hmax hV hVU (eta := fun _ : Vec d => (1 : ℝ)) continuous_const
      (memScalarL2_indicator_one
        (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t) hV) Y

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Entrywise integrability of the recentred coarse block on an aligned cell

The cell half of the cutoff-mean row of `p.response.transfer` needs, on every coarse subcell, the
`P`-integrability of the individual entries of the pathwise coarse block of the recentred
coefficients `a_- = a - g` and `a_+ = aᵀ + g`.  Recentring by a constant skew matrix is a block
congruence, so those entries are fixed real linear combinations of the entries of the coarse block
of the sample itself, which `HasIntegrableCoarseBlock` supplies.  This module records that
integrability for the four sub-block entries used by the annealed heads, together with the
`AEStronglyMeasurable` forms at the centred cell that the stationarity collapse consumes.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise coarse block of `a_- = a - g` on an aligned adapted cell is the constant shear
congruence `Gᵀ 𝐀(U; a) G` of the sample's coarse block.  The recentring subtracts the constant
skew matrix field `g`, so the variational quantity is recovered by the shear congruence
(`e.annealed.schur`) once quadraticity holds on the cell. -/
private theorem coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter_eq_blockCongr
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q j w) a) := by
  have hquad : HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) := by
    simpa only [adaptedCellAtCenter] using
      hasQuadraticMu_adaptedCellTranslate q hq j (adaptedCellCenter q j w) a
  exact coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
    (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F) hquad

/-- The pathwise coarse block of `a_+ = aᵀ + g` on an aligned adapted cell is the constant
congruence `D Gᵀ 𝐀(U; a) G D` of the sample's coarse block, with `D` the flux-sign block and `G`
the shear of `respG`.  The adjoint recentring is the composition of the flux flip with the shear
congruence, so the two congruences compose to one constant congruence. -/
private theorem coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter_eq_blockCongr
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)
      = blockCongr (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
          (coarseBlock (adaptedCellAtCenter q j w) a) := by
  have hquad : HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) := by
    simpa only [adaptedCellAtCenter] using
      hasQuadraticMu_adaptedCellTranslate q hq j (adaptedCellCenter q j w) a
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  have h1 : respCoeffPlus F a
      = fun y => (adjointCoeffField (⇑a.1 : CoeffField d)) y - (-(respg F)) := by
    funext y
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
    (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
    (hasQuadraticMu_adjointCoeffField hquad)
  have h3 : coarseBlockMatrix (adaptedCellAtCenter q j w)
        (adjointCoeffField (⇑a.1 : CoeffField d))
      = blockCongr (blockD d) (coarseBlock (adaptedCellAtCenter q j w) a) := by
    rw [coarseBlockMatrix_adjointCoeffField_of_exists
      (exists_coarseBlockMatrix_of_hasQuadraticMu hquad), ← blockCongr_blockD]
    rfl
  rw [h1, h2, h3, blockCongr_blockCongr]
  exact congrArg (fun M => blockCongr M (coarseBlock (adaptedCellAtCenter q j w) a))
    (congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F)))

/-- **Integrability of the upper-left block of the recentred coarse block.**  For the unit grid
`q = respGrid jStar F`, a scale `j` and an aligned cell index `w`, if every entry of the coarse
block of the sample is `P`-integrable there, then every entry of the upper-left sub-block of the
pathwise coarse block of `a_- = a - g` is `P`-integrable. -/
theorem integrable_coarseBlockMatrix_upperLeft_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)).upperLeft i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq j w F hint
      (Sum.inl i) (Sum.inl k)

/-- **Integrability of the lower-right block of the recentred coarse block.**  The lower-right twin
of `integrable_coarseBlockMatrix_upperLeft_respCoeffMinus`. -/
theorem integrable_coarseBlockMatrix_lowerRight_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)).lowerRight i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq j w F hint
      (Sum.inr i) (Sum.inr k)

/-- **Integrability of the upper-left block of the adjoint recentred coarse block.**  For the unit
grid `q = respGrid jStar F`, a scale `j` and an aligned cell index `w`, if every entry of the
coarse block of the sample is `P`-integrable there, then every entry of the upper-left sub-block
of the pathwise coarse block of `a_+ = aᵀ + g` is `P`-integrable. -/
theorem integrable_coarseBlockMatrix_upperLeft_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)).upperLeft i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq j w F hint
      (Sum.inl i) (Sum.inl k)

/-- **Integrability of the lower-right block of the adjoint recentred coarse block.**  The
lower-right twin of `integrable_coarseBlockMatrix_upperLeft_respCoeffPlus`. -/
theorem integrable_coarseBlockMatrix_lowerRight_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)).lowerRight i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq j w F hint
      (Sum.inr i) (Sum.inr k)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The side conditions of the two-term head on the carriers

The cell half of the cutoff-mean row of `p.response.transfer` carries, for each coarse cell, the
two-term head `√(P · b P) + √(Q · (S_*)^{-1} Q)` built from the two diagonal blocks of that cell's
pathwise coarse block.  This module discharges the side conditions the head needs on the carriers:
the nonnegativity of its two quadratic forms, their integrability from the entrywise integrability
of the coarse block, and the integrability of the cross term and of the square of the head.  The
last two are consequences of the arithmetic--geometric mean inequality and the nonnegativity of the
two summands: `√α √β ≤ (α + β)/2` and `(√α + √β)^2 ≤ 2(α + β)`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Nonnegativity of the two diagonal coarse-block forms -/

/-! ## Integrability of the two diagonal coarse-block forms -/

/-- **The upper-left diagonal coarse-block form is integrable from its entries.**  If every entry
of the upper-left block of `𝐀(V; b a)` is `P`-integrable, then so is the quadratic form
`Y.1 · (𝐀(V; b a).upperLeft Y.1)`: it is a finite sum of products of entries with the constants
`Y.1 i`, `Y.1 j`.  This is the upper-left integrability input of the two-term head of
`p.response.transfer`. -/
theorem integrable_vecDot_coarseBlockMatrix_upperLeft {d : ℕ} {P : Measure (CoeffSpace d)}
    {V : Set (Vec d)} {b : CoeffSpace d → CoeffField d} (Y : BlockVec d)
    (hint : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).upperLeft i j) P) :
    Integrable (fun a =>
      vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1)) P := by
  have hterm : ∀ i j : Fin d, Integrable (fun a =>
      Y.1 i * ((coarseBlockMatrix V (b a)).upperLeft i j * Y.1 j)) P :=
    fun i j => ((hint i j).mul_const (Y.1 j)).const_mul (Y.1 i)
  have hsum : Integrable (fun a => ∑ i : Fin d, ∑ j : Fin d,
      Y.1 i * ((coarseBlockMatrix V (b a)).upperLeft i j * Y.1 j)) P :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hterm i j
  refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [vecDot, matVecMul, Finset.mul_sum]

/-- **The lower-right diagonal coarse-block form is integrable from its entries.**  The
lower-right twin of `integrable_vecDot_coarseBlockMatrix_upperLeft`: entrywise integrability of
the lower-right block makes the form `Y.2 · (𝐀(V; b a).lowerRight Y.2)` `P`-integrable, the second
integrability input of the two-term head of `p.response.transfer`. -/
theorem integrable_vecDot_coarseBlockMatrix_lowerRight {d : ℕ} {P : Measure (CoeffSpace d)}
    {V : Set (Vec d)} {b : CoeffSpace d → CoeffField d} (Y : BlockVec d)
    (hint : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).lowerRight i j) P) :
    Integrable (fun a =>
      vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2)) P := by
  have hterm : ∀ i j : Fin d, Integrable (fun a =>
      Y.2 i * ((coarseBlockMatrix V (b a)).lowerRight i j * Y.2 j)) P :=
    fun i j => ((hint i j).mul_const (Y.2 j)).const_mul (Y.2 i)
  have hsum : Integrable (fun a => ∑ i : Fin d, ∑ j : Fin d,
      Y.2 i * ((coarseBlockMatrix V (b a)).lowerRight i j * Y.2 j)) P :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hterm i j
  refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [vecDot, matVecMul, Finset.mul_sum]

/-! ## Integrability of the cross term and of the square of the head -/

/-- The arithmetic--geometric mean inequality for two square roots. -/
private theorem two_mul_sqrt_mul_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt x * Real.sqrt y ≤ x + y := by
  have hsq : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy] at hsq
  linarith only [hsq]

/-- **Integrability of the square of the head `(√α + √β)^2` for nonnegative integrable `α`, `β`.**
From `√α √β ≤ (α + β)/2` one gets `(√α + √β)^2 ≤ 2(α + β)`, an integrable domination, with
measurability supplied by continuity of `Real.sqrt`.  This is the squared-head integrability of
the two-term head of `p.response.transfer`. -/
theorem integrable_sq_sqrt_add_sqrt {d : ℕ} {P : Measure (CoeffSpace d)}
    {α β : CoeffSpace d → ℝ} (hα : Integrable α P) (hβ : Integrable β P)
    (hαnn : ∀ a, 0 ≤ α a) (hβnn : ∀ a, 0 ≤ β a) :
    Integrable (fun a => (Real.sqrt (α a) + Real.sqrt (β a)) ^ 2) P := by
  have hsqrtα : AEStronglyMeasurable (fun a => Real.sqrt (α a)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hα.aestronglyMeasurable
  have hsqrtβ : AEStronglyMeasurable (fun a => Real.sqrt (β a)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hβ.aestronglyMeasurable
  refine Integrable.mono' ((hα.add hβ).const_mul 2) ((hsqrtα.add hsqrtβ).pow 2) ?_
  filter_upwards with a
  simp only [Pi.add_apply]
  have hnn : 0 ≤ (Real.sqrt (α a) + Real.sqrt (β a)) ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg hnn]
  have h2 := two_mul_sqrt_mul_sqrt_le (hαnn a) (hβnn a)
  have hexp : (Real.sqrt (α a) + Real.sqrt (β a)) ^ 2
      = α a + β a + 2 * (Real.sqrt (α a) * Real.sqrt (β a)) := by
    rw [add_sq, Real.sq_sqrt (hαnn a), Real.sq_sqrt (hβnn a)]
    ring
  rw [hexp]
  linarith only [h2]

/-- **Integrability of the square of the two-term head on the carriers.**  The square of the head
`√(Y.1 · 𝐀(V; b a).upperLeft Y.1) + √(Y.2 · 𝐀(V; b a).lowerRight Y.2)` is `P`-integrable
whenever its two diagonal coarse-block forms are nonnegative and integrable.  This is the
squared-head side condition of `p.response.transfer`. -/
theorem integrable_sq_sqrt_add_sqrt_coarseBlockMatrix {d : ℕ} {P : Measure (CoeffSpace d)}
    {V : Set (Vec d)} {b : CoeffSpace d → CoeffField d} (Y : BlockVec d)
    (hUL : Integrable (fun a =>
      vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1)) P)
    (hLR : Integrable (fun a =>
      vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2)) P)
    (hULnn : ∀ a, 0 ≤
      vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1))
    (hLRnn : ∀ a, 0 ≤
      vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2)) :
    Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2))) ^ 2) P :=
  integrable_sq_sqrt_add_sqrt hUL hLR hULnn hLRnn

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed cell energy of the terminal optimizer on a descendant cell

The oscillation half of the cutoff-mean row of `p.response.transfer` reads the cell energy of the
terminal optimizer on every descendant cell of the terminal cell.
`TerminalHalfEnergyIntegrability` makes that
readout `P`-integrable on the aligned cells of one fixed generation, from the integrability of the
terminal energy and the measurability of `SubcellEnergyIntegrability`; the descendant generation
`t - (H + n + 1)` is that statement at the shifted scale `s - (n + 1)` and the deeper index box,
because the terminal cell is the same cell either way.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The annealed cell energy on a descendant cell, minus sign.**  The cell energy of the terminal
optimizer on a cell of the generation `t - (H+n+1)` is `P`-integrable. -/
theorem integrable_volumeAverage_energy_descendant_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (n : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d (H + n + 1)) :
    Integrable (fun a => volumeAverage
      (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
  have hshift : t - ((H + n + 1 : ℕ) : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  have ht' : t = (s - ((n + 1 : ℕ) : ℤ)) + ((H + n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  rw [hshift]
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
    (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uM hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar
      hjStar F
      hm (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uM hmax w hw).aestronglyMeasurable)
    W hW

/-- **The annealed cell energy on a descendant cell, plus sign.**  The adjoint twin. -/
theorem integrable_volumeAverage_energy_descendant_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (n : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d (H + n + 1)) :
    Integrable (fun a => volumeAverage
      (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
  have hshift : t - ((H + n + 1 : ℕ) : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  have ht' : t = (s - ((n + 1 : ℕ) : ℤ)) + ((H + n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  rw [hshift]
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
    (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uP hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F
      hm (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uP hmax w hw).aestronglyMeasurable)
    W hW

end

end HCPolySupport.HighContrast.Multiscale
end
