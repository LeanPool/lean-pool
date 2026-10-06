/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffPairingRowSplit
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.RecentredResponseEnergyBound

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffEstimateRowClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Closing the cutoff estimate's mean row from its cell and oscillation halves

Once the pathwise cutoff-pairing identity is available for a genuine cutoff of the response class,
the three-row bound on the centred responses `Jtilde^±(e)` holds outright, reducing what the
cutoff estimate still needs to two named analytic obligations: a bound on the energy-defect row and
a bound on the cutoff-mean row, for each sign. The cutoff-mean row bounds the crossed pairing of the
cutoff-mean defect against the dual variable by `C(τ L_s)^{1/2} + C 3^{-H}(E[J_t] L_s)^{1/2}`
(`p.response.transfer`), and this file supplies that bound by splitting the defect into a cell
part, costing `(2 τ L_s)^{1/2}`, and an oscillation part, already of the printed size
`c₂ 3^{-H}(E[J_t] L_s)^{1/2}`. Together the two obligations close the row decomposition down to the
four elementary quantities `τ^±`, `E[J_t^±]`, `L_s^±`, and the expected absolute cutoff pairing.
-/

section
/-!
## The centred response against its three cutoff rows, with the pathwise identity discharged

The centred responses `Jtilde^±(e)` of `e.response.cutoff.estimate` are bounded by the three cutoff
rows of the printed variational calculation once the cutoff pairing is decomposed pathwise into the
cutoff half-energy, the two cutoff-mean pairings and half the self-pairing of the annealed mean.
For a cutoff of the response class — in particular one of cell average one — that decomposition is
not an extra assumption: it follows from the integrability of the cutoff-weighted optimizer state
against the cell.  These two statements therefore replace the pathwise identity of
`RecentredResponseEnergyBound` by the membership of the cutoff and the indicated cell
integrabilities.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), minus carriers, with the pathwise identity discharged from cutoff
membership.  The cutoff `φ` is a response cutoff on the cell `U_t` — so in particular it has cell
average one — and the cutoff-weighted optimizer state is integrable against that cell.  Under these
hypotheses the half-pairing `(1/2) * cutoffPairingOnCellAux` is pathwise the affine combination
of the cutoff half-energy, the two cutoff-mean coordinates and half the self-pairing of the
annealed mean `Y^-`, so `|Jtilde^-(e)|` is bounded by the sum of the expected absolute cutoff
pairing, the absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean
row `(1/2) |<E[M₁] - Y₁^-, Y₂^-> + <Y₁^-, E[M₂] - Y₂^->|`. -/
theorem abs_respCenteredJMinus_le_three_rows_of_cutoff {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
        (respCoeffMinus F a) (uM a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2 i) P)
    (hcut : IsResponseCutoff (respGrid jStar F) t φ)
    (hφint : IntegrableOn φ (respCell jStar F t))
    (hEcell : ∀ a, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2) (respCell jStar F t))
    (h1cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i) (respCell jStar F t))
    (h2cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) (respCell jStar F t)) :
    |respCenteredJMinus P jStar F t e|
      ≤ (1 / 2 : ℝ) * (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ
            (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a)| ∂P)
        + |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
            - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
        + (1 / 2 : ℝ) * |vecDot
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
              (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)| := by
  exact abs_respCenteredJMinus_le_three_rows P jStar F t e φ uM hq hblk hJ hA hW hM1 hM2
    (fun a => cutoff_halfPairing_eq_sub_aux (respCell jStar F t) φ (respYMinus P jStar F t e)
      (uM a) hcut.2.2.2.1 hφint (hEcell a) (h1cell a) (h2cell a))

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), plus carriers, with the pathwise identity discharged from cutoff
membership.  The cutoff `φ` is a response cutoff on the cell `U_t` — so in particular it has cell
average one — and the cutoff-weighted optimizer state is integrable against that cell.  Under these
hypotheses the half-pairing `(1/2) * cutoffPairingOnCellAux` is pathwise the affine combination
of the cutoff half-energy, the two cutoff-mean coordinates and half the self-pairing of the
annealed mean `Y^+`, so `|Jtilde^+(e)|` is bounded by the sum of the expected absolute cutoff
pairing, the absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean
row `(1/2) |<E[M₁] - Y₁^+, Y₂^+> + <Y₁^+, E[M₂] - Y₂^+>|`. -/
theorem abs_respCenteredJPlus_le_three_rows_of_cutoff {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
        (respCoeffPlus F a) (uP a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2 i) P)
    (hcut : IsResponseCutoff (respGrid jStar F) t φ)
    (hφint : IntegrableOn φ (respCell jStar F t))
    (hEcell : ∀ a, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2) (respCell jStar F t))
    (h1cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i) (respCell jStar F t))
    (h2cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) (respCell jStar F t)) :
    |respCenteredJPlus P jStar F t e|
      ≤ (1 / 2 : ℝ) * (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ
            (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a)| ∂P)
        + |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
            - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
        + (1 / 2 : ℝ) * |vecDot
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
              (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)| := by
  exact abs_respCenteredJPlus_le_three_rows P jStar F t e φ uP hq hblk hJ hA hW hM1 hM2
    (fun a => cutoff_halfPairing_eq_sub_aux (respCell jStar F t) φ (respYPlus P jStar F t e)
      (uP a) hcut.2.2.2.1 hφint (hEcell a) (h1cell a) (h2cell a))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The two analytic rows behind the cutoff estimate

The cutoff estimate of `e.response.cutoff.estimate` bounds the centred response `Jtilde^±(e)` by
the sum of its three error rows and the expected absolute cutoff pairing.  The integrated cutoff
decomposition already exhibits those three rows; what the printed proof still supplies are the two
bounds on the energy defect and on the centred cutoff mean.  This module names them as the
predicates `CutoffEnergyDefectRowMinus` and `CutoffMeanRowMinus` (and their `Plus` twins) and shows
that the printed right-hand side of the estimate follows from them together with the decomposition,
by linear arithmetic on the half-weighted pairing row.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The first error row of the estimate, as a named obligation. -/
@[expose]
def CutoffEnergyDefectRowMinus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) :
    Prop :=
  |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
      - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
    ≤ C * (respTauMinus P jStar F s t e
        + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
        + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)

/-- The second and third error rows of the estimate, as a named obligation. -/
@[expose]
def CutoffMeanRowMinus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) :
    Prop :=
  (1 / 2 : ℝ) * |vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
        (respYMinus P jStar F t e).2
      + vecDot (respYMinus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)|
    ≤ C * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
      + C * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))

/-- The three-row decomposition of `e.response.cutoff.estimate` and the two bounds on its error
rows assemble into the printed right-hand side: if the cutoff energy defect obeys its bound and the
centred cutoff mean obeys its two-row bound, then `|Jtilde^-(e)|` is bounded by the two rows, the
half-weighted cutoff pairing, and the expected absolute cutoff pairing carried at coefficient one.
-/
theorem abs_respCenteredJMinus_le_cutoffRows_of_obligations {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
        (respCoeffMinus F a) (uM a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2 i) P)
    (hcut : IsResponseCutoff (respGrid jStar F) t φ)
    (hφint : IntegrableOn φ (respCell jStar F t))
    (hEcell : ∀ a, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2) (respCell jStar F t))
    (h1cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i) (respCell jStar F t))
    (h2cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) (respCell jStar F t))
    (C : ℝ) (H : ℕ) (s : ℤ)
    (hrow1 : CutoffEnergyDefectRowMinus C P jStar F H s t e φ uM)
    (hrow2 : CutoffMeanRowMinus C P jStar F H s t e φ uM) :
    |respCenteredJMinus P jStar F t e|
      ≤ C * (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)
        + C * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
        + C * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))
        + (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ
            (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a)| ∂P) := by
  have hthree := abs_respCenteredJMinus_le_three_rows_of_cutoff P jStar F t e φ uM
    hq hblk hJ hA hW hM1 hM2 hcut hφint hEcell h1cell h2cell
  unfold CutoffEnergyDefectRowMinus at hrow1
  unfold CutoffMeanRowMinus at hrow2
  exact le_cutoffRows_of_two_rows hthree
    (integral_nonneg (fun a => abs_nonneg _)) hrow1 hrow2

/-- The first error row of the adjoint estimate, as a named obligation. -/
@[expose]
def CutoffEnergyDefectRowPlus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) :
    Prop :=
  |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
      - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
    ≤ C * (respTauPlus P jStar F s t e
        + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)

/-- The second and third error rows of the adjoint estimate, as a named obligation. -/
@[expose]
def CutoffMeanRowPlus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) :
    Prop :=
  (1 / 2 : ℝ) * |vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
        (respYPlus P jStar F t e).2
      + vecDot (respYPlus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)|
    ≤ C * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
      + C * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))

/-- The three-row decomposition of `e.response.cutoff.estimate` and the two bounds on its adjoint
error rows assemble into the printed right-hand side: if the adjoint cutoff energy defect obeys its
bound and the adjoint centred cutoff mean obeys its two-row bound, then `|Jtilde^+(e)|` is bounded
by the two rows, the half-weighted cutoff pairing, and the expected absolute cutoff pairing carried
at coefficient one. -/
theorem abs_respCenteredJPlus_le_cutoffRows_of_obligations {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
        (respCoeffPlus F a) (uP a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2 i) P)
    (hcut : IsResponseCutoff (respGrid jStar F) t φ)
    (hφint : IntegrableOn φ (respCell jStar F t))
    (hEcell : ∀ a, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2) (respCell jStar F t))
    (h1cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i) (respCell jStar F t))
    (h2cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) (respCell jStar F t))
    (C : ℝ) (H : ℕ) (s : ℤ)
    (hrow1 : CutoffEnergyDefectRowPlus C P jStar F H s t e φ uP)
    (hrow2 : CutoffMeanRowPlus C P jStar F H s t e φ uP) :
    |respCenteredJPlus P jStar F t e|
      ≤ C * (respTauPlus P jStar F s t e
            + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)
        + C * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
        + C * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))
        + (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ
            (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a)| ∂P) := by
  have hthree := abs_respCenteredJPlus_le_three_rows_of_cutoff P jStar F t e φ uP
    hq hblk hJ hA hW hM1 hM2 hcut hφint hEcell h1cell h2cell
  unfold CutoffEnergyDefectRowPlus at hrow1
  unfold CutoffMeanRowPlus at hrow2
  exact le_cutoffRows_of_two_rows hthree
    (integral_nonneg (fun a => abs_nonneg _)) hrow1 hrow2

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-mean row from its cell and oscillation halves

The cutoff-mean row of `p.response.transfer` bounds the crossed pairing of the cutoff-mean defect
against the dual variable by `C (tau L_s)^{1/2} + C 3^{-H} (E[J_t] L_s)^{1/2}`.  The defect splits
into a cell part and an oscillation part: the cell part costs `(2 tau L_s)^{1/2}`, while the
oscillation part is already of the printed size `c₂ 3^{-H} (E[J_t] L_s)^{1/2}`.  This module is the
purely scalar assembly of the row from those two halves, for both signs, with the coefficient
`max 1 c₂`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff-mean row for the negative sign from its two halves.**  The coordinatewise mean
defect splits as `N = Ncell + Nosc`.  Bilinearity of `vecDot` splits the crossed pairing along the
two coordinates into the cell and oscillation halves; the triangle inequality bounds the total by
the sum of the two half-bounds; `√L √(2τ) = √2 √(τ L)` with `√2 / 2 ≤ 1` absorbs the cell factor;
and `1 ≤ max 1 c₂` together with `(1 / 2) c₂ ≤ max 1 c₂` absorbs the row's factor `1 / 2`. -/
theorem cutoffMeanRowMinus_of_halves {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d)
    (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂) (Ncell Nosc : BlockVec d)
    (hsplit1 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
      = Ncell.1 + Nosc.1)
    (hsplit2 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)
      = Ncell.2 + Nosc.2)
    (hcell : |vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e))
    (hosc : |vecDot Nosc.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) (hL : 0 ≤ respLsMinus P jStar F s t e) :
    CutoffMeanRowMinus (max 1 c₂) P jStar F H s t e φ uM := by
  unfold CutoffMeanRowMinus
  have hsplit_l : vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
        (respYMinus P jStar F t e).2
      = vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2 := by
    rw [hsplit1, vecDot_add_left]
  have hsplit_r : vecDot (respYMinus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)
      = vecDot (respYMinus P jStar F t e).1 Ncell.2
        + vecDot (respYMinus P jStar F t e).1 Nosc.2 := by
    rw [hsplit2, vecDot_add_right]
  rw [hsplit_l, hsplit_r]
  have htri : |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ |vecDot Ncell.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Ncell.2|
        + |vecDot Nosc.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Nosc.2| := by
    have hre : (vecDot Ncell.1 (respYMinus P jStar F t e).2
          + vecDot Nosc.1 (respYMinus P jStar F t e).2)
          + (vecDot (respYMinus P jStar F t e).1 Ncell.2
            + vecDot (respYMinus P jStar F t e).1 Nosc.2)
        = (vecDot Ncell.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Ncell.2)
          + (vecDot Nosc.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Nosc.2) := by ring
    rw [hre]
    exact abs_add_le _ _
  have hpair : |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
    le_trans htri (add_le_add hcell hosc)
  have hhalfpair : (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hcell' : (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e))
      ≤ max 1 c₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) := by
    have hsq : Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        = Real.sqrt 2 * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) := by
      rw [← Real.sqrt_mul hL (2 * respTauMinus P jStar F s t e),
        show respLsMinus P jStar F s t e * (2 * respTauMinus P jStar F s t e)
            = 2 * (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) by ring,
        Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)
          (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)]
    have htwo : Real.sqrt 2 / 2 ≤ 1 := by linarith only [Real.sqrt_two_lt_three_halves]
    have hs : 0 ≤ Real.sqrt (respTauMinus P jStar F s t e
        * respLsMinus P jStar F s t e) := by
      rw [Real.sqrt_mul hτ (respLsMinus P jStar F s t e)]
      positivity
    calc (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e))
        = (Real.sqrt 2 / 2) * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) := by rw [hsq]; ring
      _ ≤ 1 * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right htwo hs
      _ ≤ max 1 c₂ * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) c₂) hs
  have hosp' : (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
      ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e) :=
      mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(H : ℝ)))
        (Real.sqrt_nonneg _)
    have hc₂' : (1 / 2 : ℝ) * c₂ ≤ max 1 c₂ := by
      have : (1 / 2 : ℝ) * c₂ ≤ c₂ := by linarith only [hc₂]
      exact le_trans this (le_max_right (1 : ℝ) c₂)
    calc (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
          * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
        = ((1 / 2 : ℝ) * c₂) * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJMinus P jStar F t e
              * respLsMinus P jStar F s t e)) := by ring
      _ ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJMinus P jStar F t e
              * respLsMinus P jStar F s t e)) :=
          mul_le_mul_of_nonneg_right hc₂' hnonneg
  have hsplitmul : (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
      = (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) := by ring
  calc (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) := hhalfpair
    _ = (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) := hsplitmul
    _ ≤ max 1 c₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
        + max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
          add_le_add hcell' hosp'

/-- **The cutoff-mean row for the positive sign from its two halves.**  The adjoint coordinatewise
mean defect splits as `N = Ncell + Nosc`.  Bilinearity of `vecDot` splits the crossed pairing along
the two coordinates into the cell and oscillation halves; the triangle inequality bounds the total
by the sum of the two half-bounds; `√L √(2τ) = √2 √(τ L)` with `√2 / 2 ≤ 1` absorbs the cell
factor; and `1 ≤ max 1 c₂` together with `(1 / 2) c₂ ≤ max 1 c₂` absorbs the row's factor `1 / 2`.
-/
theorem cutoffMeanRowPlus_of_halves {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d)
    (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂) (Ncell Nosc : BlockVec d)
    (hsplit1 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
      = Ncell.1 + Nosc.1)
    (hsplit2 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)
      = Ncell.2 + Nosc.2)
    (hcell : |vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e))
    (hosc : |vecDot Nosc.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) (hL : 0 ≤ respLsPlus P jStar F s t e) :
    CutoffMeanRowPlus (max 1 c₂) P jStar F H s t e φ uP := by
  unfold CutoffMeanRowPlus
  have hsplit_l : vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
        (respYPlus P jStar F t e).2
      = vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2 := by
    rw [hsplit1, vecDot_add_left]
  have hsplit_r : vecDot (respYPlus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)
      = vecDot (respYPlus P jStar F t e).1 Ncell.2
        + vecDot (respYPlus P jStar F t e).1 Nosc.2 := by
    rw [hsplit2, vecDot_add_right]
  rw [hsplit_l, hsplit_r]
  have htri : |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ |vecDot Ncell.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Ncell.2|
        + |vecDot Nosc.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Nosc.2| := by
    have hre : (vecDot Ncell.1 (respYPlus P jStar F t e).2
          + vecDot Nosc.1 (respYPlus P jStar F t e).2)
          + (vecDot (respYPlus P jStar F t e).1 Ncell.2
            + vecDot (respYPlus P jStar F t e).1 Nosc.2)
        = (vecDot Ncell.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Ncell.2)
          + (vecDot Nosc.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Nosc.2) := by ring
    rw [hre]
    exact abs_add_le _ _
  have hpair : |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
    le_trans htri (add_le_add hcell hosc)
  have hhalfpair : (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hcell' : (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e))
      ≤ max 1 c₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) := by
    have hsq : Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        = Real.sqrt 2 * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) := by
      rw [← Real.sqrt_mul hL (2 * respTauPlus P jStar F s t e),
        show respLsPlus P jStar F s t e * (2 * respTauPlus P jStar F s t e)
            = 2 * (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) by ring,
        Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)
          (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)]
    have htwo : Real.sqrt 2 / 2 ≤ 1 := by linarith only [Real.sqrt_two_lt_three_halves]
    have hs : 0 ≤ Real.sqrt (respTauPlus P jStar F s t e
        * respLsPlus P jStar F s t e) := by
      rw [Real.sqrt_mul hτ (respLsPlus P jStar F s t e)]
      positivity
    calc (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e))
        = (Real.sqrt 2 / 2) * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) := by rw [hsq]; ring
      _ ≤ 1 * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right htwo hs
      _ ≤ max 1 c₂ * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) c₂) hs
  have hosp' : (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
      ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e) :=
      mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(H : ℝ)))
        (Real.sqrt_nonneg _)
    have hc₂' : (1 / 2 : ℝ) * c₂ ≤ max 1 c₂ := by
      have : (1 / 2 : ℝ) * c₂ ≤ c₂ := by linarith only [hc₂]
      exact le_trans this (le_max_right (1 : ℝ) c₂)
    calc (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
          * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
        = ((1 / 2 : ℝ) * c₂) * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJPlus P jStar F t e
              * respLsPlus P jStar F s t e)) := by ring
      _ ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJPlus P jStar F t e
              * respLsPlus P jStar F s t e)) :=
          mul_le_mul_of_nonneg_right hc₂' hnonneg
  have hsplitmul : (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
      = (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) := by ring
  calc (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) := hhalfpair
    _ = (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) := hsplitmul
    _ ≤ max 1 c₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
        + max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
          add_le_add hcell' hosp'

end

end HCPolySupport.HighContrast.Multiscale
end
