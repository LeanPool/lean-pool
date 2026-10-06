/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.SubcellDualPairingIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.AbstractCellPairingBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.AnnealedBlockMeanCancellation
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.ScaleDefectIdentity

/-!
# High-contrast homogenization: Entry.Response.Rows.CellHalfCarrierBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Cell Half of the Cutoff-Mean Row at the Response Carriers

The cell half of the two cutoff-mean rows of `p.response.transfer` asserts that the modulus of the
dual pairing of the
cell part of the cutoff-mean defect against a state `Y^∓` is at most `√(L_s^∓) · √(2
tau^∓)`. This file assembles that bound from its established pieces: the abstract cell-pairing row
supplies the annealed Cauchy-Schwarz estimate and the stationarity collapse of the annealed head,
the per-cell dual pairing discharges its pathwise hypothesis at an almost-everywhere elliptic
response coefficient, the doubled deficit rescaling supplies the annealed flat deficit as `2
tau^∓`, and the linearity of the crossed pairing together with mean cancellation rewrites the
abstract statement back into the pairing of the cell part against `Y^∓`. The result is the
carrier-level form of the cell half of the response-transfer estimate, for each sign.
-/

section
/-!
## The cell half of the cutoff-mean row on the carriers

The cell half of the two cutoff-mean rows of `p.response.transfer` asserts that the modulus of the
dual pairing of the cell part of the cutoff-mean defect against `Y^∓` is at most
`√(L_s^∓) * √(2 tau^∓)`.  This module assembles that statement from the established pieces: the
abstract cell-pairing row `abs_integral_avsum_weighted_pairing_le_respLsMinus` /
`…Plus` supplies the annealed Cauchy--Schwarz estimate and the collapse of the annealed head, the
per-cell pairing bound `abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le` discharges its
pathwise
hypothesis at the almost-everywhere elliptic response coefficient, the deficit rescaling
`integral_avsum_two_subcellDeficit_eq_two_respTauMinus` / `…Plus` discharges the value of the
annealed flat deficit, and the crossed-pairing linearity
`vecDot_avsum_integral_eq_integral_avsum_pairing`
together with the mean cancellation `avsum_weighted_integral_cellAverage_subcellOptimizer_eq_zero`
rewrites the abstract flat average back into the pairing of the cell part `Ncell` against `Y^∓`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- **The per-cell dual pairing bound at the recentred coefficient `a_- = a - g`, in the `hbd`
form of the cell row.**  For each depth-`H` aligned subcell `adaptedCellAtCenter (respGrid jStar
F) s w`
of the terminal cell and each sample `a`, the crossed pairing of `Y^-` with the difference between
the terminal optimizer cell mean and the subcell maximizer cell mean is bounded by the subcell's
two-term head times the square root of twice its deficit.  The pointwise ellipticity is taken from
an a.e.-representative of the carrier coefficient, so only the almost-everywhere datum is used. -/
private theorem abs_cellRow_respCoeffMinus_le {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w a)) :
    ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      |vecDot (respYMinus P jStar F t e).2
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a))).1
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (v w a))).1)
          + vecDot (respYMinus P jStar F t e).1
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a))).2
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (v w a))).2)|
        ≤ (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
                  (respCoeffMinus F a)).upperLeft (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
                  (respCoeffMinus F a)).lowerRight (respYMinus P jStar F t e).2)))
          * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))) := by
  have hs : s = t - (H : ℤ) := by
    rw [ht]
    ring
  subst hs
  intro w hw a
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
    (Geometry.isUnit_roundedGrid hjStar hm) t H hEll hae
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a) hw
    (v w a) (hv w hw a) (respYMinus P jStar F t e)

/-- **The per-cell dual pairing bound at the adjoint recentred coefficient `a_+ = aᵗ + g`.**  The
`Plus` twin of `abs_cellRow_respCoeffMinus_le`, with the adjoint recentred coefficient, the dual
variable `Y^+` and the terminal optimizer family `uP`. -/
private theorem abs_cellRow_respCoeffPlus_le {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) (v w a)) :
    ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      |vecDot (respYPlus P jStar F t e).2
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a))).1
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (v w a))).1)
          + vecDot (respYPlus P jStar F t e).1
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a))).2
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (v w a))).2)|
        ≤ (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
                  (respCoeffPlus F a)).upperLeft (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
                  (respCoeffPlus F a)).lowerRight (respYPlus P jStar F t e).2)))
          * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))) := by
  have hs : s = t - (H : ℤ) := by
    rw [ht]
    ring
  subst hs
  intro w hw a
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
    (Geometry.isUnit_roundedGrid hjStar hm) t H hEll hae
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a) hw
    (v w a) (hv w hw a) (respYPlus P jStar F t e)

/-- **The crossed pairing of a difference of cell means.**  The crossed pairing of `X - Z` against
`Y` is the difference of the crossed pairings of `X` and `Z`. -/
private theorem vecDot_sub_blockVec {d : ℕ} (X Z : BlockVec d) (Y : BlockVec d) :
    vecDot (X - Z).1 Y.2 + vecDot Y.1 (X - Z).2
      = (vecDot X.1 Y.2 + vecDot Y.1 X.2) - (vecDot Z.1 Y.2 + vecDot Y.1 Z.2) := by
  simp only [vecDot, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- **The cell part is the expectation of the pathwise crossed pairings.**  Let `M` be the terminal
optimizer cell means and `Ns` the subcell optimizer cell means.  If `Ncell` is the weighted flat
average of the expectations of `M`, and the weighted flat average of the expectations of `Ns`
vanishes, then the crossed pairing of `Ncell` against `Y` is the sample expectation of the weighted
flat average of the pathwise crossed pairings of the differences `M - Ns`.  This is the
`AnnealedBlockMeanCancellation` exchange followed by the `AnnealedBlockMeanCancellation`
cancellation. -/
private theorem vecDot_cellPart_eq_integral_cellPairing {d : ℕ} {ι α : Type*} [MeasurableSpace α]
    (P : Measure α) (Z : Finset ι) (c : ι → ℝ) (Y : BlockVec d)
    (M Ns : ι → α → BlockVec d) (Ncell : BlockVec d)
    (hNcell : Ncell = (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * (M w a).1 i ∂P,
                        fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * (M w a).2 i ∂P))
    (hNsMean : (fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (Ns w a).1 i ∂P) = 0 ∧
               (fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (Ns w a).2 i ∂P) = 0)
    (hintM1 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (M w a).1 i) P)
    (hintM2 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (M w a).2 i) P)
    (hintNs1 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (Ns w a).1 i) P)
    (hintNs2 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (Ns w a).2 i) P) :
    vecDot Ncell.1 Y.2 + vecDot Y.1 Ncell.2
      = ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          c w * (vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2) ∂P := by
  classical
  let NsMean : BlockVec d :=
    (fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (Ns w a).1 i ∂P,
     fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (Ns w a).2 i ∂P)
  have hNsMean1 : NsMean.1
      = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (Ns w a).1 i ∂P := rfl
  have hNsMean2 : NsMean.2
      = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (Ns w a).2 i ∂P := rfl
  have hNsMean_zero : NsMean = 0 := by
    apply Prod.ext
    · exact hNsMean.1
    · exact hNsMean.2
  have hN1 : Ncell.1
      = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).1 i ∂P := by
    rw [hNcell]
    funext i
    change (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * (M w a).1 i ∂P)
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).1 i ∂P
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum Z (fun w hw => (hintM1 w hw i).const_mul (c w))]
    exact Finset.sum_congr rfl (fun w _ => by rw [integral_const_mul])
  have hN2 : Ncell.2
      = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).2 i ∂P := by
    rw [hNcell]
    funext i
    change (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * (M w a).2 i ∂P)
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).2 i ∂P
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum Z (fun w hw => (hintM2 w hw i).const_mul (c w))]
    exact Finset.sum_congr rfl (fun w _ => by rw [integral_const_mul])
  have hM := vecDot_avsum_integral_eq_integral_avsum_pairing P Z c Y M Ncell hN1 hN2 hintM1 hintM2
  have hNs := vecDot_avsum_integral_eq_integral_avsum_pairing P Z c Y Ns NsMean
    hNsMean1 hNsMean2 hintNs1 hintNs2
  have hpt : ∀ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2)
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2)
        - ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
            c w * (vecDot (Ns w a).1 Y.2 + vecDot Y.1 (Ns w a).2) := by
    intro a
    have hterm : ∀ w ∈ Z, c w * (vecDot ((M w a - Ns w a)).1 Y.2
          + vecDot Y.1 ((M w a - Ns w a)).2)
        = c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2)
          - c w * (vecDot (Ns w a).1 Y.2 + vecDot Y.1 (Ns w a).2) := by
      intro w _
      rw [vecDot_sub_blockVec (M w a) (Ns w a) Y]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    ring
  have hcross_int : ∀ (X : ι → α → BlockVec d),
      (∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (X w a).1 i) P) →
      (∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (X w a).2 i) P) →
      Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot (X w a).1 Y.2 + vecDot Y.1 (X w a).2)) P := by
    intro X hX1 hX2
    refine (integrable_finsetSum Z (fun w hw => ?_)).const_mul _
    have h1 : Integrable (fun a => vecDot (X w a).1 Y.2) P := by
      simp only [vecDot]
      exact integrable_finsetSum _ (fun i _ => (hX1 w hw i).mul_const (Y.2 i))
    have h2 : Integrable (fun a => vecDot Y.1 (X w a).2) P := by
      simp only [vecDot]
      exact integrable_finsetSum _ (fun i _ => (hX2 w hw i).const_mul (Y.1 i))
    exact (h1.add h2).const_mul (c w)
  have hAint := hcross_int M hintM1 hintM2
  have hBint := hcross_int Ns hintNs1 hintNs2
  have hInt_split : (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2) ∂P)
      = (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
            c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2) ∂P)
        - (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
            c w * (vecDot (Ns w a).1 Y.2 + vecDot Y.1 (Ns w a).2) ∂P) := by
    rw [integral_congr_ae (ae_of_all P hpt), integral_sub hAint hBint]
  have hcn : (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot (Ns w a).1 Y.2 + vecDot Y.1 (Ns w a).2) ∂P) = 0 := by
    rw [← hNs, hNsMean_zero]
    change vecDot (0 : Vec d) Y.2 + vecDot Y.1 (0 : Vec d) = 0
    rw [vecDot_zero_left, vecDot_zero_right, add_zero]
  have hcm : (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2) ∂P)
      = vecDot Ncell.1 Y.2 + vecDot Y.1 Ncell.2 := hM.symm
  rw [hInt_split, hcm, hcn, sub_zero]

/-- **The cell half of the cutoff-mean row on the carriers, minus sign.**  Let `Ncell` be the cell
part of the cutoff-mean defect of `p.response.transfer` produced by the centred cutoff
decomposition of the terminal optimizer state of the recentred coefficient `a_- = a - g`, namely
the weighted flat average over the depth-`H` subcells of the subcell mean of `φ - 1` times the
subcell mean of the doubled optimizer field.  Then the modulus of the crossed pairing of `Ncell`
against the dual variable `Y^-` is at most `√(L_s^-) * √(2 tau^-)`.  The proof runs the abstract
cell-pairing row at the concrete crossing of the difference between the terminal and subcell
optimizer means, discharges its pathwise bound by the direct full-dual pairing estimate, discharges
its deficit value by the rescaling of the mean subcell deficit, and rewrites its flat average back
to `Ncell` with the crossed-pairing linearity and the cancellation of the constant cell means. -/
theorem abs_vecDot_cellPart_respYMinus_le {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hmaxV : ∀ w ∈ triadicIndexBox d H, ∀ a,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w a))
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
      (respYMinus P jStar F t e)))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hUL : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1))
    (hLR : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2))
    (hentUL : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        * Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2) P)
    (hFint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                (respYMinus P jStar F t e).2))) ^ 2) P)
    (hDint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 *
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                  (respYMinus P jStar F t e).1))
              + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                  (respYMinus P jStar F t e).2))) ^ 2)
        * Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, 2 *
              (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                  (respqMinus P jStar F t e) (respCoeffMinus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))))) P)
    (hPint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
        (Real.sqrt ((Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                    (respYMinus P jStar F t e).1))
                + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                    (respYMinus P jStar F t e).2))) ^ 2)
          * Real.sqrt (2 *
              (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                  (respqMinus P jStar F t e) (respCoeffMinus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))))) P)
    (hPint' : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
          (vecDot ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a)))
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (v w a)))).1
            (respYMinus P jStar F t e).2
          + vecDot (respYMinus P jStar F t e).1
              ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a)))
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (v w a)))).2)) P)
    (hmeasBlk : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffMinus F a)) α β) P)
    (hintM1 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffMinus F a) (uM a))).1 i) P)
    (hintM2 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffMinus F a) (uM a))).2 i) P)
    (hintNs1 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffMinus F a) (v w a))).1 i) P)
    (hintNs2 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffMinus F a) (v w a))).2 i) P)
    (Ncell : BlockVec d)
    (hNcell : Ncell = ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
      (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P))) :
    |vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  let c : (Fin d → ℤ) → ℝ :=
    fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
  let p : Vec d := respP (respMean P jStar F t) e
  let q : Vec d := respqMinus P jStar F t e
  let Y : BlockVec d := respYMinus P jStar F t e
  let V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter (respGrid jStar F) s w
  let M : (Fin d → ℤ) → CoeffSpace d → BlockVec d := fun w a =>
    cellAverage (V w) (optimizerField (respCoeffMinus F a) (uM a))
  let Ns : (Fin d → ℤ) → CoeffSpace d → BlockVec d := fun w a =>
    cellAverage (V w) (optimizerField (respCoeffMinus F a) (v w a))
  let D : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    ResponseJ (V w) p q (respCoeffMinus F a) - volumeAverage (V w)
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p q (uM a))
  let G : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix (V w) (respCoeffMinus F a)).upperLeft Y.1))
    + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix (V w) (respCoeffMinus F a)).lowerRight Y.2))
  let pairing : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2
  have hc : ∀ w ∈ triadicIndexBox d H, |c w| ≤ 1 := by
    intro w _
    simpa only [c, V] using
      abs_volumeAverage_sub_one_isResponseCutoff_le_one (qq := respGrid jStar F) hq hφ s w
  have hD : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤ D w a := by
    intro w hw a
    have hstH : t - (H : ℤ) = s := by omega
    have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffMinus (jStar := jStar) (F := F)
      hjStar hm t H p q a (uM a) hw).2
    simpa only [D, V, hstH] using h
  have hbd : ∀ w ∈ triadicIndexBox d H, ∀ a, |pairing w a| ≤ G w a * Real.sqrt (2 * D w a) := by
    intro w hw a
    have h := abs_cellRow_respCoeffMinus_le P jStar hjStar F hm H s t ht e uM v hmaxV w hw a
    simp only [pairing]
    rw [vecDot_comm ((M w a - Ns w a)).1 Y.2]
    simpa only [D, G, V, M, Ns, Y, p, q] using! h
  have hDval : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a ∂P) = 2 * respTauMinus P jStar F s t e := by
    simpa only [D, V, p, q] using
      integral_avsum_two_subcellDeficit_eq_two_respTauMinus P hstat jStar hjStar F hm H s t ht hjs e
        uM hmax hblk hrespint hJint hRint hJt hJs
  have hMv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      Ns w a = blockResponseMean (coarseBlockMatrix (V w) (respCoeffMinus F a)) (-p, q) := by
    intro w hw a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have hstH : t - (H : ℤ) = s := by omega
    have hVU : V w ⊆ respCell jStar F t := by
      simpa only [V, hstH, respCell] using
        adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    have hVmeas : MeasurableSet (V w) := (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
    have hEllV : IsEllipticFieldOn lam Lam (V w) f := isEllipticFieldOn_subset hEll hVU hVmeas
    have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn (V w)] f :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
    simpa only [Ns, V] using
      cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean (q := respGrid jStar F)
        hq s w hEllV haeV p q (v w a) (hmaxV w hw a)
  let A : BlockMat d := annealedBlockOf P (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffMinus F)
  have hann : ∀ w ∈ triadicIndexBox d H, annealedBlockOf P (V w) (respCoeffMinus F) = A := by
    intro w hw
    simpa only [A, V, respGrid] using
      annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq_full P hstat jStar (explicitCanonicalMetric F) F s hjs w
        hmeasBlk
  have hquad : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      HasQuadraticMu (V w) (⇑a.1 : CoeffField d) := by
    intro w _ a
    simpa only [V] using hasQuadraticMu_adaptedCellAtCenter (respGrid jStar F) hq s w a
  have hintNs : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (Ns w a).1 i) P ∧ Integrable (fun a => (Ns w a).2 i) P :=
    fun w hw i => ⟨hintNs1 w hw i, hintNs2 w hw i⟩
  have hNsMean : (fun i => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * ∫ a, (Ns w a).1 i ∂P) = 0 ∧
      (fun i => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * ∫ a, (Ns w a).2 i ∂P) = 0 := by
    have hc3 := avsum_weighted_integral_cellAverage_subcellOptimizer_eq_zero P jStar F H s t e φ
      hq hφ ht Ns A hMv hann hintNs (fun w _ => hblk w) hquad
    exact ⟨by simpa only [c] using! funext hc3.1, by simpa only [c] using! funext hc3.2⟩
  have hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffMinus F a)).upperLeft i k) P :=
    fun i k => by simpa only [blockMatEntry] using hmeasBlk (Sum.inl i) (Sum.inl k)
  have hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffMinus F a)).lowerRight i k) P :=
    fun i k => by simpa only [blockMatEntry] using hmeasBlk (Sum.inr i) (Sum.inr k)
  have hmain := abs_integral_avsum_weighted_pairing_le_respLsMinus
    (P := P) (hstat := hstat) (jStar := jStar) (F := F) (H := H) (s := s) (t := t) (e := e)
    (hjs := hjs) (c := c) (hc := hc) (pairing := pairing) (D := D)
    (hsum := hsum) (hD := hD) (hbd := hbd) (hDval := hDval)
    (hUL := hUL) (hLR := hLR) (hentUL := hentUL) (hentLR := hentLR)
    (hqUL := hqUL) (hqLR := hqLR) (hcross := hcross) (hsq := hsq)
    (hmeas := hmeas) (hmeas' := hmeas') (hFint := hFint) (hDint := hDint)
    (hMidint := hMidint) (hPint := hPint) (hPint' := hPint')
  have hmain' : |∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        c w * (vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2) ∂P|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e) := by
    simpa only [pairing] using hmain
  have hrewrite := vecDot_cellPart_eq_integral_cellPairing (P := P)
    (Z := triadicIndexBox d H) (c := c) (Y := Y) (M := M) (Ns := Ns) (Ncell := Ncell)
    (by simpa only [M, V, c, cellAverage] using hNcell)
    hNsMean hintM1 hintM2 hintNs1 hintNs2
  rw [← hrewrite] at hmain'
  simpa only [Y] using hmain'

/-- **The cell half of the cutoff-mean row on the carriers, plus sign.**  The adjoint twin of
`abs_vecDot_cellPart_respYMinus_le`: `Ncell` is the cell part of the cutoff-mean defect for the
adjoint recentred coefficient `a_+ = aᵗ + g`, built from the terminal optimizer family `uP`, and the
modulus of its crossed pairing against `Y^+` is at most `√(L_s^+) * √(2 tau^+)`.  The proof is the
same as for the minus sign, with the adjoint per-cell pairing bound, the adjoint deficit rescaling
and the adjoint mean cancellation. -/
theorem abs_vecDot_cellPart_respYPlus_le {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hmaxV : ∀ w ∈ triadicIndexBox d H, ∀ a,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) (v w a))
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
      (respYPlus P jStar F t e)))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hUL : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1))
    (hLR : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2))
    (hentUL : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        * Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2) P)
    (hFint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                (respYPlus P jStar F t e).2))) ^ 2) P)
    (hDint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 *
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                  (respYPlus P jStar F t e).1))
              + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                  (respYPlus P jStar F t e).2))) ^ 2)
        * Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, 2 *
              (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                  (respqPlus P jStar F t e) (respCoeffPlus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))))) P)
    (hPint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
        (Real.sqrt ((Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                    (respYPlus P jStar F t e).1))
                + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                    (respYPlus P jStar F t e).2))) ^ 2)
          * Real.sqrt (2 *
              (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                  (respqPlus P jStar F t e) (respCoeffPlus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))))) P)
    (hPint' : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
          (vecDot ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a)))
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (v w a)))).1
            (respYPlus P jStar F t e).2
          + vecDot (respYPlus P jStar F t e).1
              ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a)))
              - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (v w a)))).2)) P)
    (hmeasBlk : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffPlus F a)) α β) P)
    (hintM1 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffPlus F a) (uP a))).1 i) P)
    (hintM2 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffPlus F a) (uP a))).2 i) P)
    (hintNs1 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffPlus F a) (v w a))).1 i) P)
    (hintNs2 : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (optimizerField (respCoeffPlus F a) (v w a))).2 i) P)
    (Ncell : BlockVec d)
    (hNcell : Ncell = ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
      (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P))) :
    |vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  let c : (Fin d → ℤ) → ℝ :=
    fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
  let p : Vec d := respP (respMean P jStar F t) e
  let q : Vec d := respqPlus P jStar F t e
  let Y : BlockVec d := respYPlus P jStar F t e
  let V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter (respGrid jStar F) s w
  let M : (Fin d → ℤ) → CoeffSpace d → BlockVec d := fun w a =>
    cellAverage (V w) (optimizerField (respCoeffPlus F a) (uP a))
  let Ns : (Fin d → ℤ) → CoeffSpace d → BlockVec d := fun w a =>
    cellAverage (V w) (optimizerField (respCoeffPlus F a) (v w a))
  let D : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    ResponseJ (V w) p q (respCoeffPlus F a) - volumeAverage (V w)
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p q (uP a))
  let G : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix (V w) (respCoeffPlus F a)).upperLeft Y.1))
    + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix (V w) (respCoeffPlus F a)).lowerRight Y.2))
  let pairing : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2
  have hc : ∀ w ∈ triadicIndexBox d H, |c w| ≤ 1 := by
    intro w _
    simpa only [c, V] using
      abs_volumeAverage_sub_one_isResponseCutoff_le_one (qq := respGrid jStar F) hq hφ s w
  have hD : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤ D w a := by
    intro w hw a
    have hstH : t - (H : ℤ) = s := by omega
    have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffPlus (jStar := jStar) (F := F)
      hjStar hm t H p q a (uP a) hw).2
    simpa only [D, V, hstH] using h
  have hbd : ∀ w ∈ triadicIndexBox d H, ∀ a, |pairing w a| ≤ G w a * Real.sqrt (2 * D w a) := by
    intro w hw a
    have h := abs_cellRow_respCoeffPlus_le P jStar hjStar F hm H s t ht e uP v hmaxV w hw a
    simp only [pairing]
    rw [vecDot_comm ((M w a - Ns w a)).1 Y.2]
    simpa only [D, G, V, M, Ns, Y, p, q] using! h
  have hDval : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a ∂P) = 2 * respTauPlus P jStar F s t e := by
    simpa only [D, V, p, q] using
      integral_avsum_two_subcellDeficit_eq_two_respTauPlus P hstat jStar hjStar F hm H s t ht hjs e
        uP hmax hblk hrespint hJint hRint hJt hJs
  have hMv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      Ns w a = blockResponseMean (coarseBlockMatrix (V w) (respCoeffPlus F a)) (-p, q) := by
    intro w hw a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have hstH : t - (H : ℤ) = s := by omega
    have hVU : V w ⊆ respCell jStar F t := by
      simpa only [V, hstH, respCell] using
        adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    have hVmeas : MeasurableSet (V w) := (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
    have hEllV : IsEllipticFieldOn lam Lam (V w) f := isEllipticFieldOn_subset hEll hVU hVmeas
    have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn (V w)] f :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
    simpa only [Ns, V] using
      cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean (q := respGrid jStar F)
        hq s w hEllV haeV p q (v w a) (hmaxV w hw a)
  let A : BlockMat d := annealedBlockOf P (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffPlus F)
  have hann : ∀ w ∈ triadicIndexBox d H, annealedBlockOf P (V w) (respCoeffPlus F) = A := by
    intro w hw
    simpa only [A, V, respGrid] using
      annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq_full P hstat jStar (explicitCanonicalMetric F) F s hjs w
        hmeasBlk
  have hquad : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      HasQuadraticMu (V w) (⇑a.1 : CoeffField d) := by
    intro w _ a
    simpa only [V] using hasQuadraticMu_adaptedCellAtCenter (respGrid jStar F) hq s w a
  have hintNs : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (Ns w a).1 i) P ∧ Integrable (fun a => (Ns w a).2 i) P :=
    fun w hw i => ⟨hintNs1 w hw i, hintNs2 w hw i⟩
  have hNsMean : (fun i => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * ∫ a, (Ns w a).1 i ∂P) = 0 ∧
      (fun i => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * ∫ a, (Ns w a).2 i ∂P) = 0 := by
    have hc3 := avsum_weighted_integral_cellAverage_subcellOptimizerPlus_eq_zero P jStar F H s t
      e φ hq hφ ht Ns A hMv hann hintNs (fun w _ => hblk w) hquad
    exact ⟨by simpa only [c] using! funext hc3.1, by simpa only [c] using! funext hc3.2⟩
  have hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffPlus F a)).upperLeft i k) P :=
    fun i k => by simpa only [blockMatEntry] using hmeasBlk (Sum.inl i) (Sum.inl k)
  have hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffPlus F a)).lowerRight i k) P :=
    fun i k => by simpa only [blockMatEntry] using hmeasBlk (Sum.inr i) (Sum.inr k)
  have hmain := abs_integral_avsum_weighted_pairing_le_respLsPlus
    (P := P) (hstat := hstat) (jStar := jStar) (F := F) (H := H) (s := s) (t := t) (e := e)
    (hjs := hjs) (c := c) (hc := hc) (pairing := pairing) (D := D)
    (hsum := hsum) (hD := hD) (hbd := hbd) (hDval := hDval)
    (hUL := hUL) (hLR := hLR) (hentUL := hentUL) (hentLR := hentLR)
    (hqUL := hqUL) (hqLR := hqLR) (hcross := hcross) (hsq := hsq)
    (hmeas := hmeas) (hmeas' := hmeas') (hFint := hFint) (hDint := hDint)
    (hMidint := hMidint) (hPint := hPint) (hPint' := hPint')
  have hmain' : |∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        c w * (vecDot ((M w a - Ns w a)).1 Y.2 + vecDot Y.1 ((M w a - Ns w a)).2) ∂P|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e) := by
    simpa only [pairing] using hmain
  have hrewrite := vecDot_cellPart_eq_integral_cellPairing (P := P)
    (Z := triadicIndexBox d H) (c := c) (Y := Y) (M := M) (Ns := Ns) (Ncell := Ncell)
    (by simpa only [M, V, c, cellAverage] using hNcell)
    hNsMean hintM1 hintM2 hintNs1 hintNs2
  rw [← hrewrite] at hmain'
  simpa only [Y] using hmain'

end

end HCPolySupport.HighContrast.Multiscale
end
