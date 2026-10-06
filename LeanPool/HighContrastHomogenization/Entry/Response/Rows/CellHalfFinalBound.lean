/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellDeficitIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellEnergyIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.SubcellDualPairingIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellHalfCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalHalfEnergyIntegrability

/-!
# High-contrast homogenization: Entry.Response.Rows.CellHalfFinalBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Cell Half of the Cutoff-Mean Row with No Sample-Side Premises

The carrier-level cell half of the cutoff-mean row is proved subject to eighteen sample-side
integrability premises: the subcell responses and response-integrand averages, the quadratic
readouts of the pathwise coarse block, the flat averages entering the annealed Cauchy-Schwarz
step, and the coordinates of the two optimizer cell means. Every one follows from data the row
already carries, together with the measurability of the subcell average of the terminal
optimizer's energy density obtained from a subcell indicator weight; this file discharges all
eighteen premises and restates the cell half with them removed. It also begins the oscillation
half: the crossed pairing of its `(φ - (φ)_{V_w})`-weighted vector of subcell means against the
dual variable is a scalar annealed average, and the five `P`-integrabilities its dominated form
needs at every depth reduce to three per-cell integrabilities. All of this is the cutoff-mean row
of `p.response.transfer`.
-/

section
/-!
## The cell half of the cutoff-mean row with no sample-side residue

`CellHalfCarrierBound` proves the cell half of the cutoff-mean row of `p.response.transfer` on the
response carriers, but carries eighteen sample-side integrability premises: the subcell responses
and response-integrand averages, the quadratic readouts of the pathwise coarse block, the three
flat averages entering the annealed Cauchy--Schwarz step, and the coordinates of the two optimizer
cell means.  All of them follow from the annealed data the row already carries — the coarse block
is integrable on every aligned cell and the terminal responses at the two scales are integrable —
together with the measurable canonical selection of the optimizer state.

This module discharges them and restates the cell half with those premises removed, and with the
subcell maximizer family constructed internally rather than supplied.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

private theorem integrable_cellHalfAnnealedReadouts {α : Type*} [MeasurableSpace α]
    {P : Measure α} {d : ℕ} (Z : Finset (Fin d → ℤ)) (θ : (Fin d → ℤ) → ℝ)
    (q₁ q₂ D R : (Fin d → ℤ) → α → ℝ)
    (hq₁ : ∀ w a, 0 ≤ q₁ w a) (hq₂ : ∀ w a, 0 ≤ q₂ w a)
    (hq₁I : ∀ w ∈ Z, Integrable (q₁ w) P) (hq₂I : ∀ w ∈ Z, Integrable (q₂ w) P)
    (hDI : ∀ w ∈ Z, Integrable (D w) P) (hRI : ∀ w ∈ Z, Integrable (R w) P) :
    Integrable (fun a => ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (Real.sqrt (q₁ w a) +
      Real.sqrt (q₂ w a)) ^ 2)) P ∧
    Integrable (fun a => ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) P ∧
    Integrable (fun a => Real.sqrt (((Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
      (Real.sqrt (q₁ w a) + Real.sqrt (q₂ w a)) ^ 2)) *
      Real.sqrt (((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a))) P ∧
    Integrable (fun a => ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, θ w *
      (Real.sqrt ((Real.sqrt (q₁ w a) + Real.sqrt (q₂ w a)) ^ 2) *
        Real.sqrt (2 * D w a)))) P ∧
    Integrable (fun a => ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, θ w * R w a)) P := by
  have hsq : ∀ w ∈ Z, Integrable (fun a =>
      (Real.sqrt (q₁ w a) + Real.sqrt (q₂ w a)) ^ 2) P :=
    fun w hw => integrable_sq_sqrt_add_sqrt_gen (hq₁ w) (hq₂ w) (hq₁I w hw) (hq₂I w hw)
  have hFint := integrable_avsum (P := P) Z
    (fun w a => (Real.sqrt (q₁ w a) + Real.sqrt (q₂ w a)) ^ 2) hsq
  have hDint := integrable_avsum (P := P) Z (fun w a => 2 * D w a)
    (fun w hw => (hDI w hw).const_mul 2)
  have hMidint := integrable_sqrt_mul_sqrt_of_integrable hFint hDint
  have hPint := integrable_avsum (P := P) Z
    (fun w a => θ w * (Real.sqrt ((Real.sqrt (q₁ w a) + Real.sqrt (q₂ w a)) ^ 2) *
      Real.sqrt (2 * D w a)))
    (fun w hw => (integrable_sqrt_mul_sqrt_of_integrable (hsq w hw)
      ((hDI w hw).const_mul 2)).const_mul _)
  have hPint' := integrable_avsum (P := P) Z (fun w a => θ w * R w a)
    (fun w hw => (hRI w hw).const_mul _)
  exact ⟨hFint, hDint, hMidint, hPint, hPint'⟩

private theorem integrable_crossedBlockAverageDifference {α : Type*} [MeasurableSpace α]
    {P : Measure α} {d : ℕ} (X Z : α → BlockVec d) (Y : BlockVec d)
    (hX₁ : ∀ i, Integrable (fun a => (X a).1 i) P)
    (hX₂ : ∀ i, Integrable (fun a => (X a).2 i) P)
    (hZ₁ : ∀ i, Integrable (fun a => (Z a).1 i) P)
    (hZ₂ : ∀ i, Integrable (fun a => (Z a).2 i) P) :
    Integrable (fun a => vecDot ((X a).1 - (Z a).1) Y.2
      + vecDot Y.1 ((X a).2 - (Z a).2)) P := by
  have h1 : Integrable (fun a => ∑ i : Fin d,
      ((X a).1 i - (Z a).1 i) * Y.2 i) P :=
    integrable_finsetSum _ fun i _ => ((hX₁ i).sub (hZ₁ i)).mul_const _
  have h2 : Integrable (fun a => ∑ i : Fin d,
      Y.1 i * ((X a).2 i - (Z a).2 i)) P :=
    integrable_finsetSum _ fun i _ => ((hX₂ i).sub (hZ₂ i)).const_mul _
  refine (h1.add h2).congr ?_
  filter_upwards with a
  simp only [Pi.add_apply, vecDot, Pi.sub_apply]

/-- **The cell half of the cutoff-mean row on the carriers with no sample-side residue, minus
sign.**  Under the annealed data of the row — stationarity, the invertible grid, the coarse block
on every aligned subcell of the coarse scale, and the integrability of the two terminal responses —
the modulus of the crossed pairing of the cell part `Ncell` against `Y^-` is at most
`√(L_s^-) √(2 tau^-)`.  No sample-side integrability is assumed. -/
theorem abs_vecDot_cellPart_respYMinus_le_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
      (respYMinus P jStar F t e)))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
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
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- the canonical subcell maximizer family
  let v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e))).toAHarmonicFunctionMeanZero.toAHarmonicFunction
  have hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respCoeffMinus F a) (v w a) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e))).isResponseMaximizer
  -- the subcell energies and deficits
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
      H s t ht e uM hmax w hw).aestronglyMeasurable
  have hE : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm H s t ht e
      uM hmax hJt hmeasEae
  have hDdef : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P :=
    integrable_subcellDeficit_respCoeffMinus P jStar hjStar F hm H s t ht hjs e uM hmax hblk hJt
      hmeasEae
  -- the two optimizer cell means
  have hNs : ∀ w ∈ triadicIndexBox d H,
      (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (v w a))).1 i) P)
        ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (v w a))).2 i) P) :=
    fun w _ => integrable_cellAverage_subcellOptimizer_respCoeffMinus P jStar hjStar F hm s w
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (v w) (hv w) (hblk w)
  have hM := integrable_cellAverage_terminalOptimizer_respCoeffMinus P jStar hjStar F hm H s t ht
    e uM hmax v (fun w _ a => hv w a) hblk hDdef
  -- the subcell response-integrand averages and the subcell responses
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P := by
    intro w hw
    have h1 : Integrable (fun a => -(1 / 2 : ℝ) *
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      + ((∑ i : Fin d, (-(respP (respMean P jStar F t) e)) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i)
        + ∑ i : Fin d, (respqMinus P jStar F t e) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i)) P :=
      ((hE w hw).const_mul _).add
        ((integrable_finsetSum _ fun i _ => (hM.2 w hw i).const_mul _).add
          (integrable_finsetSum _ fun i _ => (hM.1 w hw i).const_mul _))
    refine h1.congr ?_
    filter_upwards with a
    rw [volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffMinus_eq P jStar hjStar F hm
      H s t ht e uM a w hw]
    simp only [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot,
      Pi.neg_apply]
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P := by
    intro w hw
    refine ((hDdef w hw).add (hRint w hw)).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  -- the quadratic readouts of the pathwise coarse block
  have hULLR : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      0 ≤ vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
          (respYMinus P jStar F t e).1)
        ∧ 0 ≤ vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
          (respYMinus P jStar F t e).2) :=
    fun w a => zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm s a
      (respYMinus P jStar F t e) w
  have hent : ∀ w : Fin d → ℤ, ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)) α β) P :=
    fun w => integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq s w F (hblk w)
  have hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).upperLeft) (respYMinus P jStar F t e).1
      (fun i k => hent w (Sum.inl i) (Sum.inl k))
  have hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).lowerRight) (respYMinus P jStar F t e).2
      (fun i k => hent w (Sum.inr i) (Sum.inr k))
  let q1 := fun w a => vecDot (respYMinus P jStar F t e).1 (matVecMul
    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
    (respYMinus P jStar F t e).1)
  let q2 := fun w a => vecDot (respYMinus P jStar F t e).2 (matVecMul
    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
    (respYMinus P jStar F t e).2)
  let D := fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)
    - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
  let θ := fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
  let xCell := fun w a => cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
    (optimizerField (respCoeffMinus F a) (uM a))
  let zCell := fun w a => cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
    (optimizerField (respCoeffMinus F a) (v w a))
  let R := fun w a =>
    vecDot ((xCell w a).1 - (zCell w a).1) (respYMinus P jStar F t e).2
      + vecDot (respYMinus P jStar F t e).1 ((xCell w a).2 - (zCell w a).2)
  have hpair : ∀ w ∈ triadicIndexBox d H, Integrable (R w) P :=
    fun w hw => integrable_crossedBlockAverageDifference (xCell w) (zCell w) (respYMinus P jStar F t e)
      (fun i => hM.1 w hw i) (fun i => hM.2 w hw i)
      (fun i => (hNs w hw).1 i) (fun i => (hNs w hw).2 i)
  obtain ⟨hFint, hDint, hMidint, hPint, hPint'⟩ :=
    integrable_cellHalfAnnealedReadouts (P := P) (triadicIndexBox d H) θ q1 q2 D R
      (fun w a => (hULLR w a).1) (fun w a => (hULLR w a).2) hqUL hqLR hDdef hpair
  have hmeasBlk : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffMinus F a)) α β) P :=
    aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCell P hq s F
  have hrespint : ∀ a : CoeffSpace d, IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq
        t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hvf : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uM a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (Response.aHarmonicOfAEEq hae (uM a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uM a)) hvf
  exact abs_vecDot_cellPart_respYMinus_le P hstat jStar hjStar F hm H s t ht hjs e φ hφ uM hmax
    v (fun w _ a => hv w a) hsum hblk hrespint hJint hRint hJt hJs
    (fun w _ a => (hULLR w a).1) (fun w _ a => (hULLR w a).2)
    (fun w _ i j => hent w (Sum.inl i) (Sum.inl j))
    (fun w _ i j => hent w (Sum.inr i) (Sum.inr j))
    hqUL hqLR hcross hsq hFint hDint hMidint hPint hPint' hmeasBlk
    (fun w hw i => hM.1 w hw i) (fun w hw i => hM.2 w hw i)
    (fun w hw i => (hNs w hw).1 i) (fun w hw i => (hNs w hw).2 i) Ncell hNcell

/-- **The cell half of the cutoff-mean row on the carriers with no sample-side residue, plus
sign.**  The adjoint twin of `abs_vecDot_cellPart_respYMinus_le_clean`, for the adjoint recentred
coefficient `a_+ = aᵀ + g`, the dual load `q^+`, the dual variable `Y^+` and the terminal maximizer
family `uP`. -/
theorem abs_vecDot_cellPart_respYPlus_le_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
      (respYPlus P jStar F t e)))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
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
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- the canonical subcell maximizer family
  let v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e))).toAHarmonicFunctionMeanZero.toAHarmonicFunction
  have hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respCoeffPlus F a) (v w a) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e))).isResponseMaximizer
  -- the subcell energies and deficits
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
      H s t ht e uP hmax w hw).aestronglyMeasurable
  have hE : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm H s t ht e
      uP hmax hJt hmeasEae
  have hDdef : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P :=
    integrable_subcellDeficit_respCoeffPlus P jStar hjStar F hm H s t ht hjs e uP hmax hblk hJt
      hmeasEae
  -- the two optimizer cell means
  have hNs : ∀ w ∈ triadicIndexBox d H,
      (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (v w a))).1 i) P)
        ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (v w a))).2 i) P) :=
    fun w _ => integrable_cellAverage_subcellOptimizer_respCoeffPlus P jStar hjStar F hm s w
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (v w) (hv w) (hblk w)
  have hM := integrable_cellAverage_terminalOptimizer_respCoeffPlus P jStar hjStar F hm H s t ht
    e uP hmax v (fun w _ a => hv w a) hblk hDdef
  -- the subcell response-integrand averages and the subcell responses
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P := by
    intro w hw
    have h1 : Integrable (fun a => -(1 / 2 : ℝ) *
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      + ((∑ i : Fin d, (-(respP (respMean P jStar F t) e)) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i)
        + ∑ i : Fin d, (respqPlus P jStar F t e) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i)) P :=
      ((hE w hw).const_mul _).add
        ((integrable_finsetSum _ fun i _ => (hM.2 w hw i).const_mul _).add
          (integrable_finsetSum _ fun i _ => (hM.1 w hw i).const_mul _))
    refine h1.congr ?_
    filter_upwards with a
    rw [volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffPlus_eq P jStar hjStar F hm
      H s t ht e uP a w hw]
    simp only [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot,
      Pi.neg_apply]
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P := by
    intro w hw
    refine ((hDdef w hw).add (hRint w hw)).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  -- the quadratic readouts of the pathwise coarse block
  have hULLR : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      0 ≤ vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
          (respYPlus P jStar F t e).1)
        ∧ 0 ≤ vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
          (respYPlus P jStar F t e).2) :=
    fun w a => zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm s a
      (respYPlus P jStar F t e) w
  have hent : ∀ w : Fin d → ℤ, ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)) α β) P :=
    fun w => integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq s w F (hblk w)
  have hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).upperLeft) (respYPlus P jStar F t e).1
      (fun i k => hent w (Sum.inl i) (Sum.inl k))
  have hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).lowerRight) (respYPlus P jStar F t e).2
      (fun i k => hent w (Sum.inr i) (Sum.inr k))
  let q1 := fun w a => vecDot (respYPlus P jStar F t e).1 (matVecMul
    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
    (respYPlus P jStar F t e).1)
  let q2 := fun w a => vecDot (respYPlus P jStar F t e).2 (matVecMul
    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
    (respYPlus P jStar F t e).2)
  let D := fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
    - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
  let θ := fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
  let xCell := fun w a => cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
    (optimizerField (respCoeffPlus F a) (uP a))
  let zCell := fun w a => cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
    (optimizerField (respCoeffPlus F a) (v w a))
  let R := fun w a =>
    vecDot ((xCell w a).1 - (zCell w a).1) (respYPlus P jStar F t e).2
      + vecDot (respYPlus P jStar F t e).1 ((xCell w a).2 - (zCell w a).2)
  have hpair : ∀ w ∈ triadicIndexBox d H, Integrable (R w) P :=
    fun w hw => integrable_crossedBlockAverageDifference (xCell w) (zCell w) (respYPlus P jStar F t e)
      (fun i => hM.1 w hw i) (fun i => hM.2 w hw i)
      (fun i => (hNs w hw).1 i) (fun i => (hNs w hw).2 i)
  obtain ⟨hFint, hDint, hMidint, hPint, hPint'⟩ :=
    integrable_cellHalfAnnealedReadouts (P := P) (triadicIndexBox d H) θ q1 q2 D R
      (fun w a => (hULLR w a).1) (fun w a => (hULLR w a).2) hqUL hqLR hDdef hpair
  have hmeasBlk : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffPlus F a)) α β) P :=
    aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCell P hq s F
  have hrespint : ∀ a : CoeffSpace d, IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq
        t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hvf : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uP a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (Response.aHarmonicOfAEEq hae (uP a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uP a)) hvf
  exact abs_vecDot_cellPart_respYPlus_le P hstat jStar hjStar F hm H s t ht hjs e φ hφ uP hmax
    v (fun w _ a => hv w a) hsum hblk hrespint hJint hRint hJt hJs
    (fun w _ a => (hULLR w a).1) (fun w _ a => (hULLR w a).2)
    (fun w _ i j => hent w (Sum.inl i) (Sum.inl j))
    (fun w _ i j => hent w (Sum.inr i) (Sum.inr j))
    hqUL hqLR hcross hsq hFint hDint hMidint hPint hPint' hmeasBlk
    (fun w hw i => hM.1 w hw i) (fun w hw i => hM.2 w hw i)
    (fun w hw i => (hNs w hw).1 i) (fun w hw i => (hNs w hw).2 i) Ncell hNcell

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The crossed pairing of the oscillation part is a scalar annealed average

The oscillation part of the cutoff-mean defect of `p.response.transfer` is the vector whose
coordinates are the annealed flat averages, over the coarse subcells `V_w` of the terminal cell, of
the `(φ - (φ)_{V_w})`-weighted subcell means of the optimizer state.  Because the dual variable `Y`
is deterministic, its crossed pairing with that vector commutes with all three averages — the
expectation, the flat average over the subcells and the subcell mean — so the whole row is a
statement about the single SCALAR field `⟨Y₂, ∇u⟩ + ⟨Y₁, a∇u⟩`, which is the form the Fenchel probe
of AK.HC (A.4) consumes.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The crossed pairing of the oscillation part is a scalar annealed average.**  The pairing of
the deterministic dual variable `Y` with the vector of annealed flat averages of the
`(φ - (φ)_{V_w})`-weighted subcell means of a block field is the annealed flat average of the
`(φ - (φ)_{V_w})`-weighted subcell means of the scalar crossed pairing.  This is the scalar form of
the oscillation half of the cutoff-mean row of `p.response.transfer`. -/
theorem vecDot_avsum_volumeAverage_osc_eq {d : ℕ} {α : Type*} [MeasurableSpace α]
    (P : Measure α) (Z : Finset (Fin d → ℤ)) (V : (Fin d → ℤ) → Set (Vec d))
    (φ : Vec d → ℝ) (X : α → Vec d → BlockVec d) (Y : BlockVec d)
    (hint1 : ∀ i : Fin d, Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
      volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i)) P)
    (hint2 : ∀ i : Fin d, Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
      volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i)) P)
    (hIOn1 : ∀ (a : α), ∀ w ∈ Z, ∀ i : Fin d, IntegrableOn
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) (V w))
    (hIOn2 : ∀ (a : α), ∀ w ∈ Z, ∀ i : Fin d, IntegrableOn
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) (V w)) :
    vecDot (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) ∂P) Y.2
        + vecDot Y.1 (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) ∂P)
      = ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) *
            (vecDot Y.2 (X a x).1 + vecDot Y.1 (X a x).2)) ∂P := by
  classical
  -- the finite-sum bookkeeping that moves the two deterministic vectors through the averages
  have hstep : ∀ (C : (Fin d → ℤ) → Fin d → ℝ) (u : Vec d),
      ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, C w i) * u i
        = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, ∑ i : Fin d, C w i * u i := by
    intro C u
    calc ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, C w i) * u i
        = ∑ i : Fin d, ∑ w ∈ Z, ((Z.card : ℝ))⁻¹ * (C w i * u i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun w _ => by ring)
      _ = ∑ w ∈ Z, ∑ i : Fin d, ((Z.card : ℝ))⁻¹ * (C w i * u i) := Finset.sum_comm
      _ = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, ∑ i : Fin d, C w i * u i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun w _ => by rw [Finset.mul_sum])
  -- the one-cell identity: the two slot sums are the subcell mean of the scalar pairing
  have hcell : ∀ (a : α), ∀ w ∈ Z,
      (∑ i : Fin d, volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) * Y.2 i)
        + ∑ i : Fin d, volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) * Y.1 i
      = volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) *
          (vecDot Y.2 (X a x).1 + vecDot Y.1 (X a x).2)) := by
    intro a w hw
    have h1 : ∀ i : Fin d, volumeAverage (V w)
          (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) * Y.2 i
        = volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i * Y.2 i) := by
      intro i
      rw [mul_comm, ← volumeAverage_smul]
      refine congrArg (volumeAverage (V w)) ?_
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ i : Fin d, volumeAverage (V w)
          (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) * Y.1 i
        = volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i * Y.1 i) := by
      intro i
      rw [mul_comm, ← volumeAverage_smul]
      refine congrArg (volumeAverage (V w)) ?_
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i),
      ← volumeAverage_sum Finset.univ
        (fun i x => (φ x - volumeAverage (V w) φ) * (X a x).1 i * Y.2 i)
        (fun i _ => (hIOn1 a w hw i).mul_const (Y.2 i)),
      ← volumeAverage_sum Finset.univ
        (fun i x => (φ x - volumeAverage (V w) φ) * (X a x).2 i * Y.1 i)
        (fun i _ => (hIOn2 a w hw i).mul_const (Y.1 i)),
      ← volumeAverage_add
        (integrable_finsetSum _ fun i _ => (hIOn1 a w hw i).mul_const (Y.2 i))
        (integrable_finsetSum _ fun i _ => (hIOn2 a w hw i).mul_const (Y.1 i))]
    refine congrArg (volumeAverage (V w)) ?_
    funext x
    simp only [Pi.add_apply]
    rw [vecDot, vecDot, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · exact Finset.sum_congr rfl (fun i _ => by ring)
  -- move both pairings inside the expectation
  have hL1 : vecDot (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) ∂P) Y.2
      = ∫ a, ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i))
            * Y.2 i ∂P := by
    simp only [vecDot]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum Finset.univ (fun i _ => (hint1 i).mul_const (Y.2 i))]
  have hL2 : vecDot Y.1 (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) ∂P)
      = ∫ a, ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i))
            * Y.1 i ∂P := by
    conv_lhs => rw [vecDot_comm]
    simp only [vecDot]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum Finset.univ (fun i _ => (hint2 i).mul_const (Y.1 i))]
  rw [hL1, hL2, ← integral_add
    (integrable_finsetSum _ fun i _ => (hint1 i).mul_const (Y.2 i))
    (integrable_finsetSum _ fun i _ => (hint2 i).mul_const (Y.1 i))]
  refine integral_congr_ae ?_
  filter_upwards with a
  rw [hstep (fun w i => volumeAverage (V w)
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i)) Y.2,
    hstep (fun w i => volumeAverage (V w)
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i)) Y.1,
    ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun w hw => hcell a w hw)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The per-depth annealed readouts of the descendant sum are integrable

The oscillation half of the cutoff-mean row of `p.response.transfer`, in its dominated form, asks
for five `P`-integrabilities at every refinement depth: the flat average of the squared pathwise
head, the flat average of the doubled cell energies, the product of the square roots of those two
flat averages, the weighted flat average of their per-cell product, and the generation increment
itself.  Each is a finite normalized sum of per-cell readouts, and the only non-algebraic step is
the crossed product of square roots, which is dominated by the arithmetic mean of the moduli.

This module records the five reductions once and for all, so that the carrier instantiation has to
supply only the three per-cell integrabilities — the squared head, the cell energy and the crossed
pairing.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α] {P : Measure α} {d : ℕ}

/-- **The flat average of the squared pathwise head is integrable.** -/
theorem integrable_avsum_sq_head (Z : ℕ → Finset (Fin d → ℤ)) (G : ℕ → (Fin d → ℤ) → α → ℝ)
    (hGsqI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => (G n W a) ^ 2) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P :=
  integrable_avsum (Z n) (fun W a => (G n W a) ^ 2) (hGsqI n)

/-- **The flat average of the doubled cell energies is integrable.** -/
theorem integrable_avsum_two_mul_energy (Z : ℕ → Finset (Fin d → ℤ))
    (D : ℕ → (Fin d → ℤ) → α → ℝ)
    (hDI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => D n W a) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P :=
  integrable_avsum (Z n) (fun W a => 2 * D n W a) (fun W hW => (hDI n W hW).const_mul 2)

/-- **The Cauchy--Schwarz middle term is integrable.**  The product of the square roots of the two
flat averages is dominated by the arithmetic mean of their moduli. -/
theorem integrable_sqrt_avsum_mul_sqrt_avsum (Z : ℕ → Finset (Fin d → ℤ))
    (G D : ℕ → (Fin d → ℤ) → α → ℝ)
    (hGsqI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => (G n W a) ^ 2) P)
    (hDI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => D n W a) P) (n : ℕ) :
    Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) P :=
  integrable_sqrt_mul_sqrt_of_integrable (integrable_avsum_sq_head Z G hGsqI n)
    (integrable_avsum_two_mul_energy Z D hDI n)

/-- **The weighted flat average of the per-cell products is integrable.** -/
theorem integrable_avsum_weighted_sqrt_mul_sqrt (Z : ℕ → Finset (Fin d → ℤ))
    (θ : ℕ → (Fin d → ℤ) → ℝ) (G D : ℕ → (Fin d → ℤ) → α → ℝ)
    (hGsqI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => (G n W a) ^ 2) P)
    (hDI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => D n W a) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a))) P :=
  integrable_avsum (Z n)
    (fun W a => θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)))
    (fun W hW => (integrable_sqrt_mul_sqrt_of_integrable (hGsqI n W hW)
      ((hDI n W hW).const_mul 2)).const_mul (θ n W))

/-- **The generation increment is integrable.**  It is the weighted flat average of the per-cell
crossed pairings. -/
theorem integrable_avsum_weighted_pairing (Z : ℕ → Finset (Fin d → ℤ))
    (θ : ℕ → (Fin d → ℤ) → ℝ) (pairing : ℕ → (Fin d → ℤ) → α → ℝ)
    (hPairI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => pairing n W a) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a) P :=
  integrable_avsum (Z n) (fun W a => θ n W * pairing n W a)
    (fun W hW => (hPairI n W hW).const_mul (θ n W))

end

end HCPolySupport.HighContrast.Multiscale
end
