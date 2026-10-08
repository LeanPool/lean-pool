/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellOscillationSplit
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffPairingRowSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff pairing splits into a half-energy, two mean pairings, and a cutoff-mean defect

Expanding the two recentred differences inside the cutoff pairing of `e.response.cutoff.estimate`,
distributing the cutoff over the four resulting pieces, and using that the cutoff averages to one
on the cell exhibits half the pairing as the cutoff-weighted half-energy of the optimizer state
minus the two cutoff-mean pairings against the inserted mean `Y^∓`, plus half its self-pairing.
Integrating this pathwise identity against the law of the coefficients splits the resulting
cutoff-mean defect, on the terminal cell, into a cell part and an oscillation part of the annealed
`(φ - 1)`-weighted average of the doubled optimizer state `X = (∇v, b∇v)`. Once the cutoff pairing
row is added with coefficient one, the three rows recombine into the estimate's printed right-hand
side `C(τ + (τ E[J])^{1/2} + g E[J]) + C(τ L)^{1/2} + C g (E[J] L)^{1/2}` (AK.HC (3.45)-(3.54)). A
further fact about the recentring shear `G_g` and the flux flip `D` records that the adjoint of a
sheared block is the sheared adjoint, `D(G_g^T A G_g)D = G_{-g}^T(DAD)G_{-g}`.
-/

section
/-!
## The integrated cutoff-mean defect splits into its cell and oscillation parts

The centred cutoff decomposition of `e.response.cutoff.estimate` leaves the defect of the
annealed cutoff-weighted state mean against the annealed mean `Y^∓`.  On the terminal cell the
mean `Y^∓` is the annealed cell average of the optimizer state `X = (∇v, b ∇v)`, so that defect
is the annealed `(φ - 1)`-weighted average of `X`.  Subdividing the terminal cell into its
depth-`H` triadic subcells splits it, coordinate by coordinate, into a cell part — the subcell
means of `φ - 1` times the subcell means of the state — and an oscillation part — the subcell
averages of `φ` minus their own cell means, weighted by the state.  This file integrates the
pathwise split `cutoffStateMeanAux_fst_eq_osc_add_cell` /
`cutoffStateMeanAux_snd_eq_osc_add_cell` against the law `P`, keeping the two parts as separate
functions so that a later assembly can consume each one.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The integrated cutoff-mean defect splits for the recentred response**
(`e.response.cutoff.estimate`).  Assume that `Y^-` is the annealed cell average of the terminal
optimizer state `X = (∇v, b ∇v)` with `b = respCoeffMinus F` (the hypothesis `hY`), that the
grid `respGrid F` is invertible, and that the sample functions of the split are integrable, both
on the terminal cell and on each depth-`H` triadic subcell, and `P`-integrable as functions of the
coefficient.  Then the annealed cutoff-mean defect
`∫_a (cutoffStateMeanAux U φ (X a)) i - (Y^-) i` splits, in each of the two coordinates, into the
annealed CELL part — the flat average over the depth-`H` subcells of `(⨍ φ - 1)` times the subcell
mean of the coordinate — plus the annealed OSCILLATION part — the flat average over the subcells
of the subcell mean of `(φ - ⨍ φ)` times the coordinate.  The two parts are kept as separate
functions added with `+`, as the row assembly consumes them separately. -/
theorem integral_cutoffStateMeanAux_sub_respYMinus_eq_cell_add_osc {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
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
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P) :
    ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P))
      ∧ ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
            (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)) := by
  have hst : t - (H : ℤ) = s := by omega
  constructor
  · funext i
    have hY1 : (respYMinus P jStar F t e).1
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_fst_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uM a) i (hφG1 a i) (hG1 a i) (hint1 a i) (h1_1 a i) (h2_1 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY1]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffMinus F a) (uM a)).1 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i) ∂P :=
          (integral_sub (hIntM1 i) (hIntC1 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P) :=
          integral_add (hIntOsc1 i) (hIntCell1 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P) :=
          add_comm _ _
  · funext i
    have hY2 : (respYMinus P jStar F t e).2
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_snd_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uM a) i (hφG2 a i) (hG2 a i) (hint2 a i) (h1_2 a i) (h2_2 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY2]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).2 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffMinus F a) (uM a)).2 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i) ∂P :=
          (integral_sub (hIntM2 i) (hIntC2 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P) :=
          integral_add (hIntOsc2 i) (hIntCell2 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P) :=
          add_comm _ _

/-- **The integrated cutoff-mean defect splits for the adjoint recentred response**
(`e.response.cutoff.estimate`).  The adjoint twin of
`integral_cutoffStateMeanAux_sub_respYMinus_eq_cell_add_osc`: with `Y^+` the annealed cell average
of the terminal optimizer state for the adjoint recentred coefficient `respCoeffPlus F`, the
annealed cutoff-mean defect splits, in each coordinate, into the annealed CELL part — the flat
average over the depth-`H` subcells of `(⨍ φ - 1)` times the subcell mean of the coordinate — plus
the annealed OSCILLATION part, the two kept as separate functions. -/
theorem integral_cutoffStateMeanAux_sub_respYPlus_eq_cell_add_osc {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
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
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P) :
    ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P))
      ∧ ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
            (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)) := by
  have hst : t - (H : ℤ) = s := by omega
  constructor
  · funext i
    have hY1 : (respYPlus P jStar F t e).1
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_fst_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uP a) i (hφG1 a i) (hG1 a i) (hint1 a i) (h1_1 a i) (h2_1 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY1]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffPlus F a) (uP a)).1 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i) ∂P :=
          (integral_sub (hIntM1 i) (hIntC1 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P) :=
          integral_add (hIntOsc1 i) (hIntCell1 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P) :=
          add_comm _ _
  · funext i
    have hY2 : (respYPlus P jStar F t e).2
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_snd_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uP a) i (hφG2 a i) (hG2 a i) (hint2 a i) (h1_2 a i) (h2_2 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY2]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).2 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffPlus F a) (uP a)).2 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i) ∂P :=
          (integral_sub (hIntM2 i) (hIntC2 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P) :=
          integral_add (hIntOsc2 i) (hIntCell2 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P) :=
          add_comm _ _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Assembling the cutoff rows of `e.response.cutoff.estimate`

The cutoff energy defect and the centred cutoff-mean row enter the cutoff estimate with the two
bounds `C (τ + (τ E[J])^{1/2} + g E[J])` and `C (τ L)^{1/2} + C g (E[J] L)^{1/2}`, while the
cutoff pairing row enters with coefficient one.  Once the response `J` is split into these three
rows, the printed right-hand side of `e.response.cutoff.estimate` follows by linear arithmetic.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- The response split with half weight on the pairing row: if
`|J| ≤ (1 / 2) * pair + row1 + row2` and the two rows obey their printed bounds, then `|J|` is
bounded by the printed right-hand side of `e.response.cutoff.estimate` with the pairing row
carried at coefficient one.  The half weight is absorbed using the nonnegativity of `pair`. -/
theorem le_cutoffRows_of_two_rows {C τ EJ L g pair row1 row2 J : ℝ}
    (hsplit : |J| ≤ (1 / 2 : ℝ) * pair + row1 + row2)
    (hpair : 0 ≤ pair)
    (hrow1 : row1 ≤ C * (τ + Real.sqrt (τ * EJ) + g * EJ))
    (hrow2 : row2 ≤ C * Real.sqrt (τ * L) + C * (g * Real.sqrt (EJ * L))) :
    |J| ≤ C * (τ + Real.sqrt (τ * EJ) + g * EJ)
        + C * Real.sqrt (τ * L)
        + C * (g * Real.sqrt (EJ * L))
        + pair := by
  linarith only [hsplit, hpair, hrow1, hrow2]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pathwise cutoff decomposition identity on a bare cell

Expanding the two recentred differences inside the cutoff pairing of `e.response.cutoff.estimate`,
distributing the cutoff over the four pieces, and using the unit cell average of the cutoff
exhibits half the pairing as the cutoff-weighted half-energy minus the two cutoff-mean pairings
plus half the self-pairing of the inserted mean.  This is the pathwise identity on which the
integrated three-row decomposition rests, and it needs no ellipticity, no boundedness of the cell
and no positivity of the cutoff, only the indicated integrabilities.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The pathwise cutoff decomposition identity.**  On the bare cell `U`, half the cutoff pairing
of the optimizer state `X = (∇v, b ∇v)` at the inserted mean `Y` equals the cutoff-weighted
half-energy `cutoffHalfEnergyAux` minus half the pairing of the cutoff mean of the first coordinate
with `Y.2`, minus half the pairing of `Y.1` with the cutoff mean of the second coordinate, plus half
the self-pairing of `Y`.  This is the identity consumed by the integrated decomposition of
`e.response.cutoff.estimate`; the cell and the coefficient are arbitrary and the only hypotheses
are the integrabilities of the cutoff, the sample functions and the coordinates of the optimizer
state. -/
theorem cutoff_halfPairing_eq_sub_aux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ)
    (Y : BlockVec d) {b : CoeffField d} (v : AHarmonicFunction b U)
    (hmean : volumeAverage U φ = 1)
    (hφ : IntegrableOn φ U)
    (hE : IntegrableOn
      (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2) U)
    (h1 : ∀ i : Fin d, IntegrableOn (fun x => φ x * (optimizerField b v x).1 i) U)
    (h2 : ∀ i : Fin d, IntegrableOn (fun x => φ x * (optimizerField b v x).2 i) U) :
    (1 / 2 : ℝ) * cutoffPairingOnCellAux U φ Y b v
      = cutoffHalfEnergyAux U φ b v
        - (1 / 2 : ℝ) * vecDot (cutoffStateMeanAux U φ b v).1 Y.2
        - (1 / 2 : ℝ) * vecDot Y.1 (cutoffStateMeanAux U φ b v).2
        + (1 / 2 : ℝ) * vecDot Y.1 Y.2 := by
  classical
  have hpB : (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
      = fun x => vecDot (fun i => φ x * (optimizerField b v x).1 i) Y.2 := by
    funext x
    simp only [vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hpC : (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
      = fun x => vecDot Y.1 (fun i => φ x * (optimizerField b v x).2 i) := by
    funext x
    simp only [vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hB : IntegrableOn (fun x => φ x * vecDot (optimizerField b v x).1 Y.2) U := by
    rw [hpB]
    have h : Integrable
        (fun x => ∑ i, (φ x * (optimizerField b v x).1 i) * Y.2 i)
        (volume.restrict U) :=
      MeasureTheory.integrable_finsetSum (μ := volume.restrict U) Finset.univ
        (f := fun i x => (φ x * (optimizerField b v x).1 i) * Y.2 i)
        (fun i _ => (h1 i).integrable.mul_const (Y.2 i))
    simpa only [IntegrableOn, vecDot] using h
  have hC : IntegrableOn (fun x => φ x * vecDot Y.1 (optimizerField b v x).2) U := by
    rw [hpC]
    have h : Integrable
        (fun x => ∑ i, Y.1 i * (φ x * (optimizerField b v x).2 i))
        (volume.restrict U) :=
      MeasureTheory.integrable_finsetSum (μ := volume.restrict U) Finset.univ
        (f := fun i x => Y.1 i * (φ x * (optimizerField b v x).2 i))
        (fun i _ => (h2 i).integrable.const_mul (Y.1 i))
    simpa only [IntegrableOn, vecDot] using h
  have hD : IntegrableOn (fun x => φ x * vecDot Y.1 Y.2) U :=
    hφ.integrable.mul_const (vecDot Y.1 Y.2)
  have hAB : IntegrableOn
      ((fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)) U :=
    hE.integrable.sub hB.integrable
  have hABC : IntegrableOn
      ((fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
        - (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)) U :=
    hAB.integrable.sub hC.integrable
  have hpt : ∀ x : Vec d,
      φ x * vecDot ((optimizerField b v x).1 - Y.1) ((optimizerField b v x).2 - Y.2)
        = φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - φ x * vecDot (optimizerField b v x).1 Y.2
          - φ x * vecDot Y.1 (optimizerField b v x).2
          + φ x * vecDot Y.1 Y.2 := by
    intro x
    have hvec : vecDot ((optimizerField b v x).1 - Y.1) ((optimizerField b v x).2 - Y.2)
        = vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - vecDot (optimizerField b v x).1 Y.2
          - vecDot Y.1 (optimizerField b v x).2
          + vecDot Y.1 Y.2 := by
      simp only [sub_eq_add_neg, vecDot_add_right, vecDot_add_left, vecDot_neg_left,
        vecDot_neg_right]
      ring
    rw [hvec]
    ring
  have hF2eval : volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
      = vecDot (cutoffStateMeanAux U φ b v).1 Y.2 := by
    rw [hpB,
      volumeAverage_vecDot_right (f := fun x i => φ x * (optimizerField b v x).1 i)
        (v := Y.2) h1]
    rfl
  have hF3eval : volumeAverage U (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
      = vecDot Y.1 (cutoffStateMeanAux U φ b v).2 := by
    rw [hpC,
      volumeAverage_vecDot_left (v := Y.1) (f := fun x i => φ x * (optimizerField b v x).2 i) h2]
    rfl
  have hF4eval : volumeAverage U (fun x => φ x * vecDot Y.1 Y.2) = vecDot Y.1 Y.2 := by
    have heq : (fun x => φ x * vecDot Y.1 Y.2) = (vecDot Y.1 Y.2) • φ := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, volumeAverage_smul, hmean, mul_one]
  have hsplit :
      volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - φ x * vecDot (optimizerField b v x).1 Y.2
          - φ x * vecDot Y.1 (optimizerField b v x).2
          + φ x * vecDot Y.1 Y.2)
        = volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
          - volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
          - volumeAverage U (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
          + volumeAverage U (fun x => φ x * vecDot Y.1 Y.2) := by
    rw [show (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - φ x * vecDot (optimizerField b v x).1 Y.2
          - φ x * vecDot Y.1 (optimizerField b v x).2
          + φ x * vecDot Y.1 Y.2)
        = ((fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
            - (fun x => φ x * vecDot Y.1 (optimizerField b v x).2))
            + (fun x => φ x * vecDot Y.1 Y.2) from rfl]
    rw [volumeAverage_add hABC hD, volumeAverage_sub hAB hC, volumeAverage_sub hE hB]
  have hmain : cutoffPairingOnCellAux U φ Y b v
      = volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - vecDot (cutoffStateMeanAux U φ b v).1 Y.2
        - vecDot Y.1 (cutoffStateMeanAux U φ b v).2
        + vecDot Y.1 Y.2 := by
    calc
      cutoffPairingOnCellAux U φ Y b v
          = volumeAverage U (fun x =>
              φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
                - φ x * vecDot (optimizerField b v x).1 Y.2
                - φ x * vecDot Y.1 (optimizerField b v x).2
                + φ x * vecDot Y.1 Y.2) := by
            unfold cutoffPairingOnCellAux
            apply congrArg (volumeAverage U)
            funext x
            exact hpt x
      _ = volumeAverage U (fun x =>
              φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
            - volumeAverage U (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
            + volumeAverage U (fun x => φ x * vecDot Y.1 Y.2) := hsplit
      _ = volumeAverage U (fun x =>
              φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - vecDot (cutoffStateMeanAux U φ b v).1 Y.2
            - vecDot Y.1 (cutoffStateMeanAux U φ b v).2
            + vecDot Y.1 Y.2 := by
            rw [hF2eval, hF3eval, hF4eval]
  rw [hmain]
  simp only [cutoffHalfEnergyAux]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The adjoint of a sheared block is the sheared adjoint

The recentring shear `G_g = [[Id, 0], [g, Id]]` and the flux flip `D = diag(Id, -Id)` form the
adjoint pair of the response decomposition.  Flipping the flux sign commutes with congruence by
`G_g` up to reversing the shear,

`D (G_gᵀ A G_g) D = G_{-g}ᵀ (D A D) G_{-g}`,

so the adjoint recentred block `Ehat_u^+` is the `(-g)`-shear congruence of the adjoint annealed
block, exactly as `Ehat_u^-` is the `g`-shear congruence of the annealed block itself.  This is the
algebraic identity that places the adjoint row of `e.response.cutoff.estimate` on the same footing
as the primal row of `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Flipping the flux sign commutes with congruence by the recentring shear up to reversing the
shear: `D (G_gᵀ A G_g) D = G_{-g}ᵀ (D A D) G_{-g}`, where `D = blockD d` and
`G_g = ⟨1, 0, g, 1⟩`. -/
theorem blockAdjoint_blockCongr_shear {d : ℕ} (A : BlockMat d) (g : Mat d) :
    blockAdjoint (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A)
      = blockCongr (⟨1, 0, -g, 1⟩ : BlockMat d) (blockAdjoint A) := by
  simp only [blockAdjoint, blockCongr_blockCongr, blockD_mul_shear_neg]

/-- The adjoint recentred block of `e.response.cutoff.estimate` is the `(-g)`-shear congruence of
the adjoint annealed block:
`Ehat_u^+ = G_{-g}ᵀ (D E_u D) G_{-g}`, the adjoint twin of the primal identity
`Ehat_u^- = G_gᵀ E_u G_g` used by `p.response.transfer`. -/
theorem respEhatPlus_eq_blockCongr_shear {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (u : ℤ) :
    respEhatPlus P jStar F u
      = blockCongr (⟨1, 0, -respg F, 1⟩ : BlockMat d) (blockAdjoint (respMean P jStar F u)) := by
  rw [respEhatPlus, respEhatMinus, respG]
  exact blockAdjoint_blockCongr_shear (respMean P jStar F u) (respg F)

end

end HCPolySupport.HighContrast.Multiscale
end
