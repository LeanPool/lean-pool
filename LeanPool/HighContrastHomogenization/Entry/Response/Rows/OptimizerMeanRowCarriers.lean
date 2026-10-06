/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedMeanDrift
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.OptimizerMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffEstimateRowClosure
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffPairingRowSplit

/-!
# High-contrast homogenization: Entry.Response.Rows.OptimizerMeanRowCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-mean row on the response's own data, and the optimizer-mean identity

The cutoff-mean row of the cutoff estimate is the sum of a cell part, bounded by
`(L_s^∓ 2τ^∓)^{1/2}`, and an oscillation part, bounded by `c₂ 3^{-H}(E[J_t^∓] L_s^∓)^{1/2}`; this
file instantiates that two-piece bound on the response problem's own cell and oscillation data. It
also identifies the annealed mean `Y^∓` of AK.HC (2.32) — defined through the block formula
`Y = (I + R Ehat_t^∓) x^∓` — with the expectation of the cell average of the doubled optimizer
state `X = (∇v, a_∓ ∇v)` on the terminal cell, `E[(X_{u_t})_{U_t}] = Y^∓`, by an affine argument. A
further lemma records that every aligned cell of the response grid is an adapted translate at its
own centre. Separately, the source-load series `L_s^∓`, whose summability at the two annealed
means `Y^±` already follows from the response load bound, is shown summable at an arbitrary dual
vector, needed once the oscillation half of the cutoff-mean row reads the series once per
coordinate direction.  The module serves `e.response.cutoff.estimate` and
`p.response.transfer`.
-/

section
/-!
## The cutoff-mean row on the carriers from its cell and oscillation halves

The cutoff-mean row of `e.response.cutoff.estimate` is the sum of a cell part and an oscillation
part.  `CutoffPairingRowSplit` exhibits those two parts explicitly, and `CutoffEstimateRowClosure`
assembles
the row from a cell-half bound `(L_s^∓ 2 tau^∓)^{1/2}` and an oscillation-half bound
`c₂ 3^{-H} (E[J_t^∓] L_s^∓)^{1/2}`.  This file instantiates the assembly at the two functions that
`CutoffPairingRowSplit` produces, so that a caller holding the standing data of the cutoff-mean
defect,
the cell-half bound and the oscillation-half bound obtains the named obligation
`CutoffMeanRow∓` with constant `max 1 c₂`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff-mean row for the negative sign on the carriers.**  Assume the standing data of
the cutoff-mean defect: `Y^-` is the annealed cell average of the terminal optimizer state for
`respCoeffMinus F`, the grid is invertible, the sample functions are integrable on the terminal cell
and on each depth-`H` subcell, and the two parts of the split are `P`-integrable.  Assume the
cell-half bound for the explicit cell part, the oscillation-half bound `c₂ 3^{-H} (E[J^-]
L^-)^{1/2}`
for the explicit oscillation part, and the nonnegativity of `tau^-` and `L^-`.  Then the named
obligation `CutoffMeanRowMinus` holds with constant `max 1 c₂`.  The cell-half and
oscillation-half bounds remain undischarged inputs. -/
theorem cutoffMeanRowMinus_of_cellSplit {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hY : respYMinus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P)))
    (hgrid : IsUnit (respGrid jStar F))
    (hφG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (respCell jStar F t))
    (hG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) (respCell jStar F t))
    (hint1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (respCell jStar F t))
    (h1_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hφG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (respCell jStar F t))
    (hG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) (respCell jStar F t))
    (hint2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (respCell jStar F t))
    (h1_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hIntM1 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffMinus F a) (uM a)).1 i) P)
    (hIntC1 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffMinus F a) (uM a))).1 i) P)
    (hIntOsc1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P)
    (hIntCell1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P)
    (hIntM2 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffMinus F a) (uM a)).2 i) P)
    (hIntC2 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffMinus F a) (uM a))).2 i) P)
    (hIntOsc2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P)
    (hIntCell2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P)
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hcell : let Ncell : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P));
      |vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e))
    (hosc : let Nosc : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P));
      |vecDot Nosc.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) (hL : 0 ≤ respLsMinus P jStar F s t e) :
    CutoffMeanRowMinus (max 1 c₂) P jStar F H s t e φ uM := by
  have hsplit := integral_cutoffStateMeanAux_sub_respYMinus_eq_cell_add_osc P jStar F H s t ht e
    φ uM hY hgrid hφG1 hG1 hint1 h1_1 h2_1 hφG2 hG2 hint2 h1_2 h2_2
    hIntM1 hIntC1 hIntOsc1 hIntCell1 hIntM2 hIntC2 hIntOsc2 hIntCell2
  let Ncell : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P))
  let Nosc : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P))
  exact cutoffMeanRowMinus_of_halves P jStar F H s t e φ uM c₂ hc₂ Ncell Nosc
    hsplit.1 hsplit.2 hcell hosc hτ hL

/-- **The cutoff-mean row for the positive sign on the carriers.**  The adjoint twin of
`cutoffMeanRowMinus_of_cellSplit`: with `Y^+` the annealed cell average of the terminal optimizer
state for `respCoeffPlus F`, the same standing data and the cell-half and oscillation-half bounds
for the explicit parts of `CutoffPairingRowSplit` give `CutoffMeanRowPlus` with constant `max 1
c₂`. -/
theorem cutoffMeanRowPlus_of_cellSplit {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hY : respYPlus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P)))
    (hgrid : IsUnit (respGrid jStar F))
    (hφG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (respCell jStar F t))
    (hG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) (respCell jStar F t))
    (hint1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (respCell jStar F t))
    (h1_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hφG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (respCell jStar F t))
    (hG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) (respCell jStar F t))
    (hint2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (respCell jStar F t))
    (h1_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hIntM1 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffPlus F a) (uP a)).1 i) P)
    (hIntC1 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffPlus F a) (uP a))).1 i) P)
    (hIntOsc1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P)
    (hIntCell1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P)
    (hIntM2 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffPlus F a) (uP a)).2 i) P)
    (hIntC2 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffPlus F a) (uP a))).2 i) P)
    (hIntOsc2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P)
    (hIntCell2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P)
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hcell : let Ncell : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P));
      |vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e))
    (hosc : let Nosc : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P));
      |vecDot Nosc.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) (hL : 0 ≤ respLsPlus P jStar F s t e) :
    CutoffMeanRowPlus (max 1 c₂) P jStar F H s t e φ uP := by
  have hsplit := integral_cutoffStateMeanAux_sub_respYPlus_eq_cell_add_osc P jStar F H s t ht e
    φ uP hY hgrid hφG1 hG1 hint1 h1_1 h2_1 hφG2 hG2 hint2 h1_2 h2_2
    hIntM1 hIntC1 hIntOsc1 hIntCell1 hIntM2 hIntC2 hIntOsc2 hIntCell2
  let Ncell : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P))
  let Nosc : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P))
  exact cutoffMeanRowPlus_of_halves P jStar F H s t e φ uP c₂ hc₂ Ncell Nosc
    hsplit.1 hsplit.2 hcell hosc hτ hL

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The optimizer-mean identity `E[(X_{u_t})_{U_t}] = Y^∓`

In `p.response.transfer` the annealed mean `Y^∓` of AK.HC (2.32) is *defined* through the block
formula `Y = (I + R Ehat_t^∓) x^∓`.  This module shows that the block formula really is the
expectation of the cell average of the doubled optimizer state `X = (∇v, a_∓ ∇v)` of the
terminal cell: `E[(X_{u_t})_{U_t}] = Y^∓`.

The argument is affine.  Pathwise the cell average of the optimizer state is
`x + R 𝐀(U_t; a_∓) x`, with `𝐀` the set-level coarse block matrix; `blockResponseMean` is
affine in the entries of the block, so integrating the entrywise affine expression reproduces the
same formula with the annealed block `Ehat_t^∓` in place of the pathwise one.  The sample
coefficient `a_∓` is only almost everywhere elliptic, so the pathwise identity is applied to an
elliptic representative and transported back along the almost everywhere agreement of the
optimizer fields and of the coarse block matrices.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-- The annealed mean `Y^-` of AK.HC (2.32) is the expectation of the cell average of the
doubled optimizer state of the terminal cell: `E[(X_{u_t})_{U_t}] = Y^-`, for any measurable
selection `a ↦ u_t(a)` of response maximizers.  The pathwise identity is applied to an
almost everywhere elliptic representative of `a_- = a - g`, and the resulting statement is
transported back along the almost everywhere agreement of the two optimizer fields and of the
two coarse block matrices. -/
theorem respYMinus_eq_integral_cellAverage_optimizerField {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (hF : (toFullBlockMat F).PosDef)
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (huM : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) :
    respYMinus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P)) := by
  have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (respCell jStar F t) (⇑a.1 : CoeffField d) := by
    intro a
    simpa only [respCell, adaptedCellTranslate_zero] using
      hasQuadraticMu_adaptedCellTranslate (respGrid jStar F) hgrid t 0 a
  have hgskew : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hF
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (respCell jStar F t) a) := fun a =>
    coarseBlockMatrix_sub_skew_eq_blockCongr hgskew (hquad a)
  have hA : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix (respCell jStar F t)
        (respCoeffMinus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respG F) hblk hb
  have hpath : ∀ a : CoeffSpace d,
      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) (uM a))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
            (respxMinus P jStar F t e) := by
    intro a
    obtain ⟨lam, Lam, f, -, -, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus (F := F) hjStar hm t a
    have hmax : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f (Response.aHarmonicOfAEEq hae (uM a)) :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (huM a)
    have hB3a : cellAverage (respCell jStar F t)
          (optimizerField f (Response.aHarmonicOfAEEq hae (uM a)))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
            (respxMinus P jStar F t e) := by
      simpa only [respCell, respxMinus] using
        cellAverage_optimizerField_eq_blockResponseMean (respGrid jStar F) hgrid t hEll
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uM a)) hmax
    have hfield : optimizerField (respCoeffMinus F a) (uM a)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
          optimizerField f (Response.aHarmonicOfAEEq hae (uM a)) := by
      filter_upwards [hae] with x hx
      simp only [optimizerField, Response.aHarmonicOfAEEq_grad, hx]
    have hblock : blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
          (respxMinus P jStar F t e)
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
            (respxMinus P jStar F t e) :=
      congrArg (fun A => blockResponseMean A (respxMinus P jStar F t e))
        (coarseBlockMatrix_congr_of_ae_eq hae.symm)
    exact (cellAverage_congr_ae subset_rfl hfield).trans (hB3a.trans hblock)
  have hE : respYMinus P jStar F t e
      = blockResponseMean (annealedBlockOf P (respCell jStar F t) (respCoeffMinus F))
          (respxMinus P jStar F t e) := by
    rw [annealedBlockOf_respCoeffMinus_eq P jStar F t hquad hblk]
    rfl
  rw [hE, ← integral_blockResponseMean P (respCell jStar F t) (respCoeffMinus F)
    (respxMinus P jStar F t e) hA]
  refine Prod.ext ?_ ?_ <;> funext i <;> refine integral_congr_ae ?_ <;>
    filter_upwards [Filter.Eventually.of_forall hpath] with a ha <;> rw [ha]

/-- The adjoint twin of `respYMinus_eq_integral_cellAverage_optimizerField`: the annealed mean
`Y^+` of AK.HC (2.32) is the expectation of the cell average of the doubled optimizer state of
the terminal cell for the adjoint coefficient `a_+ = a^t + g`.  The pathwise identity is
applied to an almost everywhere elliptic representative of `a_+`, and the resulting statement is
transported back along the almost everywhere agreement of the optimizer fields and of the coarse
block matrices. -/
theorem respYPlus_eq_integral_cellAverage_optimizerField {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (hF : (toFullBlockMat F).PosDef)
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (huP : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) :
    respYPlus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P)) := by
  have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (respCell jStar F t) (⇑a.1 : CoeffField d) := by
    intro a
    simpa only [respCell, adaptedCellTranslate_zero] using
      hasQuadraticMu_adaptedCellTranslate (respGrid jStar F) hgrid t 0 a
  have hgskew : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hF
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := matTranspose_neg_of_skew hgskew
  have hbP : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)
        = blockCongr (ofFullBlockMat (toFullBlockMat (blockD d) *
            toFullBlockMat (⟨1, 0, -respg F, 1⟩ : BlockMat d)))
            (coarseBlock (respCell jStar F t) a) := by
    intro a
    have h1 : respCoeffPlus F a
        = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
      funext x
      simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
    have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := respCell jStar F t)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
      (hasQuadraticMu_adjointCoeffField (hquad a))
    have h3 : coarseBlockMatrix (respCell jStar F t)
          (adjointCoeffField (⇑a.1 : CoeffField d))
        = blockCongr (blockD d) (coarseBlock (respCell jStar F t) a) := by
      rw [coarseBlockMatrix_adjointCoeffField_of_exists
        (exists_coarseBlockMatrix_of_hasQuadraticMu (hquad a)), ← blockCongr_blockD]
      rfl
    rw [h1, h2, h3, blockCongr_blockCongr]
  have hA : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix (respCell jStar F t)
        (respCoeffPlus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr _ hblk hbP
  have hpath : ∀ a : CoeffSpace d,
      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) (uP a))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
            (respxPlus P jStar F t e) := by
    intro a
    obtain ⟨lam, Lam, f, -, -, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus (F := F) hjStar hm t a
    have hmax : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) f (Response.aHarmonicOfAEEq hae (uP a)) :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (huP a)
    have hB3a : cellAverage (respCell jStar F t)
          (optimizerField f (Response.aHarmonicOfAEEq hae (uP a)))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
            (respxPlus P jStar F t e) := by
      simpa only [respCell, respxPlus] using
        cellAverage_optimizerField_eq_blockResponseMean (respGrid jStar F) hgrid t hEll
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uP a)) hmax
    have hfield : optimizerField (respCoeffPlus F a) (uP a)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
          optimizerField f (Response.aHarmonicOfAEEq hae (uP a)) := by
      filter_upwards [hae] with x hx
      simp only [optimizerField, Response.aHarmonicOfAEEq_grad, hx]
    have hblock : blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
          (respxPlus P jStar F t e)
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
            (respxPlus P jStar F t e) :=
      congrArg (fun A => blockResponseMean A (respxPlus P jStar F t e))
        (coarseBlockMatrix_congr_of_ae_eq hae.symm)
    exact (cellAverage_congr_ae subset_rfl hfield).trans (hB3a.trans hblock)
  have hE : respYPlus P jStar F t e
      = blockResponseMean (annealedBlockOf P (respCell jStar F t) (respCoeffPlus F))
          (respxPlus P jStar F t e) := by
    rw [annealedBlockOf_respCoeffPlus_eq P jStar F t hquad hblk]
    rfl
  rw [hE, ← integral_blockResponseMean P (respCell jStar F t) (respCoeffPlus F)
    (respxPlus P jStar F t e) hA]
  refine Prod.ext ?_ ?_ <;> funext i <;> refine integral_congr_ae ?_ <;>
    filter_upwards [Filter.Eventually.of_forall hpath] with a ha <;> rw [ha]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Coarse-block integrability on every aligned cell

The terminal-optimizer replacement row averages the subcell responses over the aligned
cells of a fixed generation.  This module records that an aligned cell of the response grid
is the adapted translate at its own centre, and transports the standing stationary-law
integrability of the adapted coarse block to every such aligned cell.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- An aligned cell of the response grid is the adapted translate at its own centre. -/
theorem adaptedCellAtCenter_eq_adaptedCellTranslate {d : ℕ} [NeZero d] (q : Mat d) (j : ℤ)
    (w : Fin d → ℤ) :
    adaptedCellAtCenter q j w
      = HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w) := rfl

/-- **Coarse-block integrability on every aligned cell of the response grid.** -/
theorem hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ) :
    HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w) := by
  rw [adaptedCellAtCenter_eq_adaptedCellTranslate]
  exact Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src hstat hdag
    jStar hjStar (explicitCanonicalMetric F) hm j (adaptedCellCenter (respGrid jStar F) j w)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The source-load series converges at every dual vector

`RespLoadBound` carries the summability of the generation summands of `L_s^∓` only at the two
annealed means `Y^∓`.  The oscillation half of the cutoff-mean row of `p.response.transfer` reads
the same series once per coordinate direction, at the dual vectors `(0, δ_i)` and `(δ_i, 0)`, so it
needs the summability at an arbitrary `Y`.

Nothing in the printed proof of the source-load bound restricts the dual vector: the `Y`-dependence
enters only through the quadratic form `⟨Y, M_0 Y⟩`, which is a finite number for every `Y`.  What
carries the convergence is the scale-wise Loewner envelope
`E[A(V_{s-n,z}; a)] ≤ C Π e(m)^2 3^{γ(j_*-(s-n))_+} E_s` of `annealedBlock_le_adaptedMean`
together with the calibration `Ehat_s^∓ ≤ c M_0`; against the weight `3^{-3n/2}` the resulting
series is geometric of ratio `3^{γ-3/2} < 1`.  This module records that, for both signs.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  annealedBlock aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The source-load series converges at every dual vector, for both signs.**  Under the standing
data of the response window -- stationarity, coarse ellipticity, the source threshold on `j_*`, the
invertible rounded grid, the window inclusion and the calibration of `Ehat_s^∓` against `M_0` -- the
generation summands of the source load are summable at *every* `Y`, not only at the annealed means
`Y^∓` of `RespLoadBound`. -/
theorem exists_summable_respSourceLoadSummand_all (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ)
        (Kg : ℝ) (Src : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ Kg Src →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) →
        ∀ F : BlockMat d, (toFullBlockMat F).PosDef → (explicitCanonicalMetric F).PosDef →
        ∀ s : ℤ, (jStar : ℤ) ≤ s →
          HighContrast.adaptedCell (respGrid jStar F) s ⊆
            HighContrast.centeredCube d (2 * (jStar : ℤ)) →
        ∀ cM : ℝ, 0 ≤ cM →
          BlockMatLoewnerLE (respEhatMinus P jStar F s) (blockScale cM (respM0 F)) →
          BlockMatLoewnerLE (respEhatPlus P jStar F s) (blockScale cM (respM0 F)) →
        ∀ Y : BlockVec d,
          Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) Y) ∧
            Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) Y) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, Cb, hCsrc, hCb, hcell⟩ := annealedBlock_le_adaptedMean d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P hP E Ψ Kg Src hstat hdag jStar hj hthr F hFfull hmF s hjs hwin cM hcM hEsM hEsP Y
  have : IsProbabilityMeasure P := hP
  have hqU : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hmF
  have hM0pd : Book.Ch02.BlockPosDef (respM0 F) := respM0_blockPosDef_of_canonicalMetric_posDef hmF
  have hM0full : (toFullBlockMat (respM0 F)).PosDef :=
    posDef_toFullBlockMat (respM0_isSymm_of_canonicalMetric_posDef hmF) hM0pd
  -- the coarse block is entrywise integrable on every aligned adapted cell
  have hint : ∀ (k : ℤ) (y : Vec d),
      HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate (respGrid jStar F) k y) :=
    fun k y => Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src hstat hdag
      jStar hj (explicitCanonicalMetric F) hmF k y
  have hAsp : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hecc0 : (0 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := by
    positivity
  -- the generation-wise scale factor of the Loewner envelope
  have hA0 : (0 : ℝ) ≤ Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ *
    ‖(explicitCanonicalMetric F)⁻¹‖) :=
    mul_nonneg (mul_nonneg hCb.le (by linarith only [hAsp])) hecc0
  set cfun : ℕ → ℝ := fun n =>
    Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0) * cM with hcfun
  have hcfun0 : ∀ n, 0 ≤ cfun n := by
    intro n
    exact mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg (by norm_num) _)) hcM
  -- the Loewner envelope of the annealed block of each signed family, generation by generation
  have hres : ∀ (G' : BlockMat d) (b : CoeffSpace d → CoeffField d),
      (∀ (k : ℤ) (z : Fin d → ℤ),
          annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) b
            = blockCongr G' (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) →
      BlockMatLoewnerLE (blockCongr G' (respMean P jStar F s)) (blockScale cM (respM0 F)) →
      ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
        BlockMatLoewnerLE
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b)
          (blockScale (cfun n) (respM0 F)) := by
    intro G' b hb hEs n z _
    rw [hb]
    have h1 := hcell P E Ψ Kg Src hstat hdag jStar hj hthr (explicitCanonicalMetric F) hmF s hjs
      hwin
      (s - (n : ℤ)) z
    have step1 := blockCongr_mono G' h1
    rw [blockCongr_blockScale] at step1
    have hfac0 : (0 : ℝ) ≤ Cb * aspectRatio E *
        (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0) :=
      mul_nonneg hA0 (Real.rpow_nonneg (by norm_num) _)
    have step2 := blockScale_mono_of_loewnerLE hEs hfac0
    refine fun V => le_trans (le_trans (step1 V) (step2 V)) ?_
    rw [blockScale_blockScale]
  -- the geometric majorant of the weighted scale factors
  set M : ℝ := max 0 (blockVecDot Y (blockMatVecMul (respM0 F) Y)) with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_left _ _
  have hYle : blockVecDot Y (blockMatVecMul (respM0 F) Y) ≤ M := le_max_right _ _
  have hr2lt : (3 : ℝ) ^ (γ - 3 / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    linarith only [hγ.2]
  have hr2pos : (0 : ℝ) < (3 : ℝ) ^ (γ - 3 / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hsum : Summable fun n : ℕ =>
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (cfun n * M)) := by
    have hgeo : Summable fun n : ℕ =>
        (4 * (Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric
          F)⁻¹‖) * cM * M)) *
          ((3 : ℝ) ^ (γ - 3 / 2)) ^ n :=
      (summable_geometric_of_lt_one hr2pos.le hr2lt).mul_left _
    refine hgeo.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (by norm_num) (mul_nonneg (hcfun0 n) hM0))
    · have hmaxle : max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0 ≤ (n : ℝ) := by
        refine max_le ?_ (Nat.cast_nonneg n)
        have hjsR : ((jStar : ℕ) : ℝ) ≤ ((s : ℤ) : ℝ) := by exact_mod_cast hjs
        push_cast
        linarith only [hjsR]
      have hpowle : (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0)
          ≤ (3 : ℝ) ^ (γ * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        exact mul_le_mul_of_nonneg_left hmaxle hγ.1
      have hstep : cfun n ≤ Cb * aspectRatio E *
          (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * (3 : ℝ) ^ (γ * (n :
            ℝ)) * cM := by
        rw [hcfun]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowle hA0) hcM
      have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hfinal : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (cfun n * M))
          ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
              * (4 * ((Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ *
                ‖(explicitCanonicalMetric F)⁻¹‖) *
                  (3 : ℝ) ^ (γ * (n : ℝ)) * cM) * M)) := by
        refine mul_le_mul_of_nonneg_left ?_ hw0
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right hstep hM0
      refine hfinal.trans (le_of_eq ?_)
      have hmul : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (3 : ℝ) ^ (γ * (n : ℝ))
          = ((3 : ℝ) ^ (γ - 3 / 2)) ^ n := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          show -((3 : ℝ) / 2) * (n : ℝ) + γ * (n : ℝ) = (γ - 3 / 2) * (n : ℝ) by ring,
          pow_eq]
      calc (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
              * (4 * ((Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ *
                ‖(explicitCanonicalMetric F)⁻¹‖) *
                  (3 : ℝ) ^ (γ * (n : ℝ)) * cM) * M))
          = (4 * (Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric
            F)⁻¹‖) *
                cM * M)) *
              ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (3 : ℝ) ^ (γ * (n : ℝ))) := by ring
        _ = (4 * (Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric
          F)⁻¹‖) *
                cM * M)) * ((3 : ℝ) ^ (γ - 3 / 2)) ^ n := by rw [hmul]
  -- the two signed congruences
  have hbMinus : ∀ (k : ℤ) (z : Fin d → ℤ),
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffMinus F)
        = blockCongr (respG F) (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z)) :=
    fun k z => annealedBlockOf_respCoeffMinus_adapted (respGrid jStar F) hqU k
      (adaptedCellCenter (respGrid jStar F) k z) F hFfull (hint k _)
  set Gplus : BlockMat d :=
    ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)) with hGplus
  have hbPlus : ∀ (k : ℤ) (z : Fin d → ℤ),
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F)
        = blockCongr Gplus (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z)) := by
    intro k z
    have h : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F)
        = blockAdjoint (blockCongr (respG F)
            (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) :=
      annealedBlockOf_respCoeffPlus_adapted (respGrid jStar F) hqU k
        (adaptedCellCenter (respGrid jStar F) k z) F hFfull (hint k _)
    rw [h, blockAdjoint, blockCongr_blockCongr, hGplus]
  have hEsPlus : BlockMatLoewnerLE (blockCongr Gplus (respMean P jStar F s))
      (blockScale cM (respM0 F)) := by
    have h := hEsP
    rw [respEhatPlus, blockAdjoint, respEhatMinus, blockCongr_blockCongr] at h
    exact h
  constructor
  · exact (respSourceLoad_le_of_loewner_scalewise P jStar F s (respCoeffMinus F) Y cfun M
      hcfun0 hM0 hmF hYle hsum (hres (respG F) (respCoeffMinus F) hbMinus hEsM)).1
  · exact (respSourceLoad_le_of_loewner_scalewise P jStar F s (respCoeffPlus F) Y cfun M
      hcfun0 hM0 hmF hYle hsum (hres Gplus (respCoeffPlus F) hbPlus hEsPlus)).1

end

end HCPolySupport.HighContrast.Multiscale
end
