/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellOscillationSplit
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffOscillationAdjointCarrier
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffPairingRowSplit
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.OptimizerMeanRowCarriers

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffMeanDefectIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coordinatewise integrability of the cutoff-mean defect

For the cutoff-mean row of the cutoff estimate in `p.response.transfer`, the annealed cutoff-mean
defect splits, coordinate by coordinate, into a cell part and an oscillation part. Four families of
`P`-integrability feed that split — the terminal cell mean of the optimizer state, its depth-`H`
cell part, the cutoff-weighted mean, and the oscillation part itself — and this file proves all
four, for both the minus and the plus sign, from the integrability established for the oscillation
half of the row. A short auxiliary fact about the vanishing of a pairing against the zero vector
closes one of the coordinate cases.
-/

section
/-!
## The cutoff-mean defect is integrable in every coordinate

The cutoff-mean row of `p.response.transfer` splits the annealed cutoff-mean defect, coordinate by
coordinate, into a cell part and an oscillation part.  Four families of `P`-integrabilities feed
that split: the terminal cell mean, the depth-`H` cell part, the cutoff-weighted mean and the
oscillation part.  All four come from the oscillation half of the row read at the `2d` basis dual
vectors: at `Y = (0, δ_i)` the crossed scalar `⟨Y₂, ∇u⟩ + ⟨Y₁, a ∇u⟩` collapses to `(∇u)_i` and at
`Y = (δ_i, 0)` to `(a ∇u)_i`, so the annealed functional of the half is the `(φ-1)`-weighted mean
of one coordinate, and the Fenchel probe of `CellOscillationSplit` makes the unweighted cell means
integrable on every aligned cell.  The source-load series converges at every dual vector
(`OptimizerMeanRowCarriers`), so the `2d` instantiations are legitimate.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Pairing against the zero vector vanishes. -/
private theorem vecDot_zero_left_local {d : ℕ} (v : Vec d) : vecDot (0 : Vec d) v = 0 := by
  simp [vecDot]

/-- **The four coordinate integrabilities of the cutoff-mean defect, minus sign.**  The terminal
cell mean, the depth-`H` cell part, the cutoff-weighted mean and the oscillation part of each
coordinate of the terminal optimizer state are `P`-integrable. -/
theorem integrable_cutoffMeanDefect_coords_respCoeffMinus {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s)
    (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hsumm : ∀ Y : BlockVec d,
      Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) Y)) :
    (∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
        (optimizerField (respCoeffMinus F a) (uM a))).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
        (optimizerField (respCoeffMinus F a) (uM a))).2 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffMinus F a) (uM a)).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffMinus F a) (uM a)).2 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hst : t - (H : ℤ) = s := by omega
  have hblkAll : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w) := fun k w =>
    hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar hjStar
      F hm k w
  have hUcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 = respCell jStar F
    t := by
    rw [Nat.cast_zero, sub_zero]
    exact adaptedCellAtCenter_zero (respGrid jStar F) t
  have hφc : Continuous φ := hφ.2.2.2.2.2.1.continuous
  -- the crossed cell average is integrable on every aligned cell
  have hcross : ∀ (Y : BlockVec d) (m : ℕ), ∀ W ∈ triadicIndexBox d m, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) P :=
    fun Y m W hW => integrable_volumeAverage_cross_optimizerField_respCoeffMinus P jStar hjStar F
      hm t e uM hmax hJ hblkAll Y m W hW
  -- the unweighted cell means on every aligned cell, read off at the basis dual vectors
  have hmean1 : ∀ (m : ℕ), ∀ W ∈ triadicIndexBox d m, ∀ i : Fin d, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P := by
    intro m W hW i
    refine (hcross (((0 : Vec d), (Pi.single i (1 : ℝ) : Vec d)) : BlockVec d) m W hW).congr
      (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) ?_
    funext x
    change vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffMinus F a) (uM a) x).1
      + vecDot (0 : Vec d) (optimizerField (respCoeffMinus F a) (uM a) x).2 = _
    rw [vecDot_single_left, vecDot_zero_left_local, add_zero]
  have hmean2 : ∀ (m : ℕ), ∀ W ∈ triadicIndexBox d m, ∀ i : Fin d, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P := by
    intro m W hW i
    refine (hcross (((Pi.single i (1 : ℝ) : Vec d), (0 : Vec d)) : BlockVec d) m W hW).congr
      (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) ?_
    funext x
    change vecDot (0 : Vec d) (optimizerField (respCoeffMinus F a) (uM a) x).1
      + vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffMinus F a) (uM a) x).2 = _
    rw [vecDot_single_left, vecDot_zero_left_local, zero_add]
  have hC1 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffMinus F a) (uM a))).1 i) P := by
    intro i
    have h := hmean1 0 0 (zero_mem_triadicIndexBox 0) i
    rwa [hUcell] at h
  have hC2 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffMinus F a) (uM a))).2 i) P := by
    intro i
    have h := hmean2 0 0 (zero_mem_triadicIndexBox 0) i
    rwa [hUcell] at h
  -- the depth-`H` cell parts
  have hCell1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P := by
    intro i
    refine integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
      (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1)
      (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) ?_ 0
    intro n W hW
    have h := hmean1 H W hW i
    rwa [hst] at h
  have hCell2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P := by
    intro i
    refine integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
      (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1)
      (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) ?_ 0
    intro n W hW
    have h := hmean2 H W hW i
    rwa [hst] at h
  -- the `(φ-1)`-weighted means, from the oscillation half at the basis dual vectors
  have hW1 : ∀ i : Fin d, Integrable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P := by
    intro i
    have hY := (integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffMinus_car hd P hstat
      γ E Ψ Kg Src hdag jStar hjStar F hm hq H s t ht hjs e φ hφ
      (((0 : Vec d), (Pi.single i (1 : ℝ) : Vec d)) : BlockVec d) uM hmax hEint hJ
      (hsumm (((0 : Vec d), (Pi.single i (1 : ℝ) : Vec d)) : BlockVec d))).1
    refine hY.congr (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    change (φ x - 1) * (vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffMinus F a) (uM a) x).1
      + vecDot (0 : Vec d) (optimizerField (respCoeffMinus F a) (uM a) x).2) = _
    rw [vecDot_single_left, vecDot_zero_left_local, add_zero]
  have hW2 : ∀ i : Fin d, Integrable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P := by
    intro i
    have hY := (integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffMinus_car hd P hstat
      γ E Ψ Kg Src hdag jStar hjStar F hm hq H s t ht hjs e φ hφ
      (((Pi.single i (1 : ℝ) : Vec d), (0 : Vec d)) : BlockVec d) uM hmax hEint hJ
      (hsumm (((Pi.single i (1 : ℝ) : Vec d), (0 : Vec d)) : BlockVec d))).1
    refine hY.congr (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    change (φ x - 1) * (vecDot (0 : Vec d)
        (optimizerField (respCoeffMinus F a) (uM a) x).1
      + vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffMinus F a) (uM a) x).2) = _
    rw [vecDot_single_left, vecDot_zero_left_local, zero_add]
  -- the pathwise integrabilities on the terminal cell and on the depth-`H` subcells
  have hpathU : ∀ (a : CoeffSpace d) (i : Fin d) (eta : Vec d → ℝ), Continuous eta →
      IntegrableOn (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
          (respCell jStar F t)
        ∧ IntegrableOn (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
          (respCell jStar F t) := fun a i eta hc =>
    integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm t uM
      ((isOpen_adaptedCell_of_isUnit hq t).measurableSet) (fun x hx => hx) hc a i
  have hpathV : ∀ (a : CoeffSpace d) (i : Fin d) (eta : Vec d → ℝ), Continuous eta →
      ∀ w ∈ triadicIndexBox d H,
      IntegrableOn (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
          (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
        ∧ IntegrableOn (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
          (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) := by
    intro a i eta hc w hw
    exact integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm t uM
      ((isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet)
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw) hc a i
  have hG1 : ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
        (respCell jStar F t) := by
    intro a i
    simpa only [one_mul] using (hpathU a i (fun _ => (1 : ℝ)) continuous_const).1
  have hG2 : ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
        (respCell jStar F t) := by
    intro a i
    simpa only [one_mul] using (hpathU a i (fun _ => (1 : ℝ)) continuous_const).2
  -- the cutoff-weighted means
  have hM1 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffMinus F a) (uM a)).1 i) P := by
    intro i
    refine ((hW1 i).add (hC1 i)).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply, cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_add
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).1 (hG1 a i)]
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    simp only [Pi.add_apply]
    ring
  have hM2 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffMinus F a) (uM a)).2 i) P := by
    intro i
    refine ((hW2 i).add (hC2 i)).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply, cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_add
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).2 (hG2 a i)]
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    simp only [Pi.add_apply]
    ring
  -- the oscillation parts, by the coordinate split
  refine ⟨hC1, hC2, hCell1, hCell2, hM1, hM2, ?_, ?_⟩
  · intro i
    refine (((hM1 i).sub (hC1 i)).sub (hCell1 i)).congr
      (Filter.Eventually.of_forall fun a => ?_)
    have hsplit := cutoffStateMeanAux_fst_eq_osc_add_cell (respGrid jStar F) hq t H φ
      (uM a) i (hpathU a i φ hφc).1 (hG1 a i)
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).1
      (fun w hw => (hpathV a i
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
        (hφc.sub continuous_const) w hw).1)
      (fun w hw => (hpathV a i
        (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
        continuous_const w hw).1)
    rw [hst] at hsplit
    simp only [Pi.sub_apply, respCell]
    rw [hsplit]
    ring
  · intro i
    refine (((hM2 i).sub (hC2 i)).sub (hCell2 i)).congr
      (Filter.Eventually.of_forall fun a => ?_)
    have hsplit := cutoffStateMeanAux_snd_eq_osc_add_cell (respGrid jStar F) hq t H φ
      (uM a) i (hpathU a i φ hφc).2 (hG2 a i)
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).2
      (fun w hw => (hpathV a i
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
        (hφc.sub continuous_const) w hw).2)
      (fun w hw => (hpathV a i
        (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
        continuous_const w hw).2)
    rw [hst] at hsplit
    simp only [Pi.sub_apply, respCell]
    rw [hsplit]
    ring

/-- **The four coordinate integrabilities of the cutoff-mean defect, plus sign.**  The adjoint
twin of `integrable_cutoffMeanDefect_coords_respCoeffMinus`. -/
theorem integrable_cutoffMeanDefect_coords_respCoeffPlus {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s)
    (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hsumm : ∀ Y : BlockVec d,
      Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) Y)) :
    (∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
        (optimizerField (respCoeffPlus F a) (uP a))).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
        (optimizerField (respCoeffPlus F a) (uP a))).2 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffPlus F a) (uP a)).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffPlus F a) (uP a)).2 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P)
      ∧ (∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hst : t - (H : ℤ) = s := by omega
  have hblkAll : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w) := fun k w =>
    hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar hjStar
      F hm k w
  have hUcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 = respCell jStar F
    t := by
    rw [Nat.cast_zero, sub_zero]
    exact adaptedCellAtCenter_zero (respGrid jStar F) t
  have hφc : Continuous φ := hφ.2.2.2.2.2.1.continuous
  -- the crossed cell average is integrable on every aligned cell
  have hcross : ∀ (Y : BlockVec d) (m : ℕ), ∀ W ∈ triadicIndexBox d m, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) P :=
    fun Y m W hW => integrable_volumeAverage_cross_optimizerField_respCoeffPlus P jStar hjStar F
      hm t e uP hmax hJ hblkAll Y m W hW
  -- the unweighted cell means on every aligned cell, read off at the basis dual vectors
  have hmean1 : ∀ (m : ℕ), ∀ W ∈ triadicIndexBox d m, ∀ i : Fin d, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P := by
    intro m W hW i
    refine (hcross (((0 : Vec d), (Pi.single i (1 : ℝ) : Vec d)) : BlockVec d) m W hW).congr
      (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) ?_
    funext x
    change vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffPlus F a) (uP a) x).1
      + vecDot (0 : Vec d) (optimizerField (respCoeffPlus F a) (uP a) x).2 = _
    rw [vecDot_single_left, vecDot_zero_left_local, add_zero]
  have hmean2 : ∀ (m : ℕ), ∀ W ∈ triadicIndexBox d m, ∀ i : Fin d, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P := by
    intro m W hW i
    refine (hcross (((Pi.single i (1 : ℝ) : Vec d), (0 : Vec d)) : BlockVec d) m W hW).congr
      (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) ?_
    funext x
    change vecDot (0 : Vec d) (optimizerField (respCoeffPlus F a) (uP a) x).1
      + vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffPlus F a) (uP a) x).2 = _
    rw [vecDot_single_left, vecDot_zero_left_local, zero_add]
  have hC1 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffPlus F a) (uP a))).1 i) P := by
    intro i
    have h := hmean1 0 0 (zero_mem_triadicIndexBox 0) i
    rwa [hUcell] at h
  have hC2 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffPlus F a) (uP a))).2 i) P := by
    intro i
    have h := hmean2 0 0 (zero_mem_triadicIndexBox 0) i
    rwa [hUcell] at h
  -- the depth-`H` cell parts
  have hCell1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P := by
    intro i
    refine integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
      (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1)
      (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) ?_ 0
    intro n W hW
    have h := hmean1 H W hW i
    rwa [hst] at h
  have hCell2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P := by
    intro i
    refine integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
      (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1)
      (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) ?_ 0
    intro n W hW
    have h := hmean2 H W hW i
    rwa [hst] at h
  -- the `(φ-1)`-weighted means, from the oscillation half at the basis dual vectors
  have hW1 : ∀ i : Fin d, Integrable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P := by
    intro i
    have hY := (integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffPlus_car hd P hstat
      γ E Ψ Kg Src hdag jStar hjStar F hm hq H s t ht hjs e φ hφ
      (((0 : Vec d), (Pi.single i (1 : ℝ) : Vec d)) : BlockVec d) uP hmax hEint hJ
      (hsumm (((0 : Vec d), (Pi.single i (1 : ℝ) : Vec d)) : BlockVec d))).1
    refine hY.congr (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    change (φ x - 1) * (vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffPlus F a) (uP a) x).1
      + vecDot (0 : Vec d) (optimizerField (respCoeffPlus F a) (uP a) x).2) = _
    rw [vecDot_single_left, vecDot_zero_left_local, add_zero]
  have hW2 : ∀ i : Fin d, Integrable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P := by
    intro i
    have hY := (integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffPlus_car hd P hstat
      γ E Ψ Kg Src hdag jStar hjStar F hm hq H s t ht hjs e φ hφ
      (((Pi.single i (1 : ℝ) : Vec d), (0 : Vec d)) : BlockVec d) uP hmax hEint hJ
      (hsumm (((Pi.single i (1 : ℝ) : Vec d), (0 : Vec d)) : BlockVec d))).1
    refine hY.congr (Filter.Eventually.of_forall fun a => ?_)
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    change (φ x - 1) * (vecDot (0 : Vec d)
        (optimizerField (respCoeffPlus F a) (uP a) x).1
      + vecDot (Pi.single i (1 : ℝ) : Vec d)
        (optimizerField (respCoeffPlus F a) (uP a) x).2) = _
    rw [vecDot_single_left, vecDot_zero_left_local, zero_add]
  -- the pathwise integrabilities on the terminal cell and on the depth-`H` subcells
  have hpathU : ∀ (a : CoeffSpace d) (i : Fin d) (eta : Vec d → ℝ), Continuous eta →
      IntegrableOn (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
          (respCell jStar F t)
        ∧ IntegrableOn (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
          (respCell jStar F t) := fun a i eta hc =>
    integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm t uP
      ((isOpen_adaptedCell_of_isUnit hq t).measurableSet) (fun x hx => hx) hc a i
  have hpathV : ∀ (a : CoeffSpace d) (i : Fin d) (eta : Vec d → ℝ), Continuous eta →
      ∀ w ∈ triadicIndexBox d H,
      IntegrableOn (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
          (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
        ∧ IntegrableOn (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
          (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) := by
    intro a i eta hc w hw
    exact integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm t uP
      ((isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet)
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw) hc a i
  have hG1 : ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
        (respCell jStar F t) := by
    intro a i
    simpa only [one_mul] using (hpathU a i (fun _ => (1 : ℝ)) continuous_const).1
  have hG2 : ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
        (respCell jStar F t) := by
    intro a i
    simpa only [one_mul] using (hpathU a i (fun _ => (1 : ℝ)) continuous_const).2
  -- the cutoff-weighted means
  have hM1 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffPlus F a) (uP a)).1 i) P := by
    intro i
    refine ((hW1 i).add (hC1 i)).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply, cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_add
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).1 (hG1 a i)]
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    simp only [Pi.add_apply]
    ring
  have hM2 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffPlus F a) (uP a)).2 i) P := by
    intro i
    refine ((hW2 i).add (hC2 i)).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply, cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_add
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).2 (hG2 a i)]
    refine congrArg (volumeAverage (respCell jStar F t)) ?_
    funext x
    simp only [Pi.add_apply]
    ring
  -- the oscillation parts, by the coordinate split
  refine ⟨hC1, hC2, hCell1, hCell2, hM1, hM2, ?_, ?_⟩
  · intro i
    refine (((hM1 i).sub (hC1 i)).sub (hCell1 i)).congr
      (Filter.Eventually.of_forall fun a => ?_)
    have hsplit := cutoffStateMeanAux_fst_eq_osc_add_cell (respGrid jStar F) hq t H φ
      (uP a) i (hpathU a i φ hφc).1 (hG1 a i)
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).1
      (fun w hw => (hpathV a i
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
        (hφc.sub continuous_const) w hw).1)
      (fun w hw => (hpathV a i
        (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
        continuous_const w hw).1)
    rw [hst] at hsplit
    simp only [Pi.sub_apply, respCell]
    rw [hsplit]
    ring
  · intro i
    refine (((hM2 i).sub (hC2 i)).sub (hCell2 i)).congr
      (Filter.Eventually.of_forall fun a => ?_)
    have hsplit := cutoffStateMeanAux_snd_eq_osc_add_cell (respGrid jStar F) hq t H φ
      (uP a) i (hpathU a i φ hφc).2 (hG2 a i)
      (hpathU a i (fun x => φ x - 1) (hφc.sub continuous_const)).2
      (fun w hw => (hpathV a i
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
        (hφc.sub continuous_const) w hw).2)
      (fun w hw => (hpathV a i
        (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
        continuous_const w hw).2)
    rw [hst] at hsplit
    simp only [Pi.sub_apply, respCell]
    rw [hsplit]
    ring

end

end HCPolySupport.HighContrast.Multiscale
end
