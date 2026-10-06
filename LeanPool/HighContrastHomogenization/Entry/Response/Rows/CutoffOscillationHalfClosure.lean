/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantEnergyAndFenchelSlots
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantEnvelopeBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantFenchelProbe
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantIndexStationarity
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TriadicRefinementIncrement
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Limit.DescendantLimitDomination
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CarrierIntegrabilityConditions
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellHalfFinalBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellOscillationSplit

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffOscillationHalfClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Closing the oscillation half of the cutoff-mean row

This module serves the cutoff estimate `p.response.transfer`.  The oscillation half of the
cutoff-mean row of that estimate is bounded by the source load
once a pathwise vanishing descendant remainder and an increment envelope with four stated
properties are supplied; this file first records that abstract closure, then builds the required
envelope out of data the row already carries — the cutoff weights, the head energies, and the cell
energies. It then supplies that data for the terminal optimizer family of the response problem
itself: the refinement identity at every depth, the cutoff-weight increment, and the pathwise
crossed-pairing bound on each descendant cell. Together the three stages close the oscillation
half of the row for the negative sign directly on the response's own optimizer field, with no
analytic hypothesis left open.
-/

section
/-!
## The oscillation half of the cutoff-mean row, closed by domination

The oscillation half of the second cutoff-mean row of
`p.response.transfer` is bounded by the source load, but the estimate asks for an annealed bound
on the descendant
remainder, and that bound would need the annealed mean of the cell average of a POINTWISE modulus
of the optimizer state, which the standing assumptions do not supply: the ellipticity constants of
a sample are not bounded in the law.

The passage to the limit does not need it.  The remainder tends to zero along every sample from
the pathwise ellipticity alone, and the generation increments see only CELL AVERAGES of the state,
so the scale-average seminorm of those averages is an integrable envelope for the whole series.
This module restates the oscillation half through
`integrable_and_abs_integral_sub_integral_le_of_dominated_descendant`, which replaces the annealed
remainder bound by those two hypotheses, and additionally delivers the `P`-integrability of the
annealed functional.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The oscillation half of the cutoff-mean row is bounded by the source load, by domination.**
The hypotheses of `abs_integral_sub_cellPart_le_descendant_load` with its annealed remainder bound
`|∫ rem N| ≤ C₀ 3^{-N} M` replaced by the pathwise vanishing `rem N a → 0` and an integrable
envelope `env` for the generation increments, and with the integrability of `Phi` replaced by its
almost-everywhere strong measurability.  The conclusion carries that integrability as well as the
bound. -/
theorem integrable_and_abs_integral_sub_cellPart_le_descendant_load {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (Phi Tcell : CoeffSpace d → ℝ) (inc rem : ℕ → CoeffSpace d → ℝ)
    (Z : ℕ → Finset (Fin d → ℤ)) (θ : ℕ → (Fin d → ℤ) → ℝ)
    (pairing G D : ℕ → (Fin d → ℤ) → CoeffSpace d → ℝ)
    (env : ℕ → CoeffSpace d → ℝ) (K EJ : ℝ)
    (hK : 0 ≤ K) (hEJ : 0 ≤ EJ)
    (hdec : ∀ (N : ℕ) (a : CoeffSpace d),
      Phi a = Tcell a + (∑ n ∈ Finset.range N, inc n a) + rem N a)
    (hincdef : ∀ (n : ℕ) (a : CoeffSpace d),
      inc n a = ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a)
    (henv0 : ∀ (n : ℕ) (a : CoeffSpace d), 0 ≤ env n a)
    (henvdom : ∀ (n : ℕ) (a : CoeffSpace d), |inc n a| ≤ env n a)
    (henvsum : ∀ᵐ a ∂P, Summable fun n : ℕ => env n a)
    (henvI : Integrable (fun a => ∑' n : ℕ, env n a) P)
    (hrem0 : ∀ a : CoeffSpace d, Filter.Tendsto (fun N : ℕ => rem N a) Filter.atTop (nhds 0))
    (hθ : ∀ n : ℕ, ∀ W ∈ Z n, |θ n W| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ G n W a)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hbd : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, |pairing n W a| ≤ G n W a * Real.sqrt (2 * D n W a))
    (hGsq : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
      ≤ (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2)
    (hDval : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P) ≤ 2 * EJ)
    (hPhiM : AEStronglyMeasurable Phi P) (hT : Integrable Tcell P)
    (hincI : ∀ n : ℕ, Integrable (inc n) P)
    (hFint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P)
    (hDint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P)
    (hMidint : ∀ n : ℕ, Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) P)
    (hPint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a))) P)
    (hsumm : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2))) :
    Integrable Phi P
      ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P|
          ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
                * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
              * Real.sqrt (2 * EJ) := by
  let L : ℕ → ℝ := fun n =>
    (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d (n + 1),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
              Y.2))) ^ 2
  let g : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2)
  have hL : ∀ n, 0 ≤ L n := by
    intro n
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun z _ => sq_nonneg _)
  have hg : Summable g := by
    simpa only [g] using hsumm
  have hweight : ∀ n : ℕ,
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
        = (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) := by
    intro n
    have hw : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
        = (3 : ℝ) ^ ((3 : ℝ) / 2)
          * (3 : ℝ) ^ (-((3 : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    rw [hw]
    dsimp only [L, g]
    ring
  have hsum : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) := by
    have hg1 : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff 1).2 hg
    have hc : Summable (fun n : ℕ => (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1)) :=
      Summable.mul_left ((3 : ℝ) ^ ((3 : ℝ) / 2)) hg1
    exact Summable.congr hc (fun n => (hweight n).symm)
  have hsum' : Summable (fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :=
    summable_rpow_neg_mul_sqrt_of_summable L hL hsum
  have hPint' : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * pairing n W a) P :=
    fun n => (hincI n).congr (Filter.Eventually.of_forall fun a => hincdef n a)
  let B : ℝ := K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n))
      * Real.sqrt (2 * EJ)
  have hB : ∀ N : ℕ, |∑ n ∈ Finset.range N, ∫ a, inc n a ∂P| ≤ B := by
    intro N
    have h := abs_sum_range_descendant_pairing_le P N Z θ pairing G D L K EJ
      hK hEJ hL hθ hG hD hbd hGsq hDval hFint hDint hMidint hPint hPint' hsum hsum'
    have hcongr : (∑ n ∈ Finset.range N, ∫ a, inc n a ∂P)
        = ∑ n ∈ Finset.range N, ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
            θ n W * pairing n W a ∂P := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => hincdef n a)
    rw [hcongr]
    exact h
  have hpair : Integrable Phi P ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P| ≤ B :=
    integrable_and_abs_integral_sub_integral_le_of_dominated_descendant P Phi Tcell inc rem env B
      hdec henv0 henvdom henvsum henvI hrem0 hB hT hPhiM hincI
  have hsum_le : (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
      ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y :=
    tsum_succ_layer_le_respSourceLoad P jStar F s b Y hsumm
  have hBle : B ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
      * Real.sqrt (2 * EJ) := by
    dsimp only [B]
    have hTle : Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
        ≤ Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y) :=
      Real.sqrt_le_sqrt hsum_le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hTle (Real.sqrt_nonneg _)) hK)
      (Real.sqrt_nonneg _)
  refine ⟨hpair.1, ?_⟩
  calc |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P| ≤ B := hpair.2
    _ ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
          * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
        * Real.sqrt (2 * EJ) := hBle

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The oscillation half of the cutoff-mean row with the envelope supplied

`CutoffOscillationHalfClosure` bounds the oscillation half of the cutoff-mean row of
`p.response.transfer`
by the source load, from a pathwise vanishing remainder and an increment envelope with four
properties.  `DescendantEnvelopeBound` builds that envelope out of the data the row already
carries: the
cutoff weights, the head energies and the cell energies of the generation cells.  This module puts
the two together, so that the oscillation half consumes only the carriers' own inputs and no
envelope has to be exhibited at the call site.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The oscillation half of the cutoff-mean row, with the envelope built in.**  The hypotheses
of `integrable_and_abs_integral_sub_cellPart_le_descendant_load` with its four envelope conditions
removed: the Young splitting of the Cauchy--Schwarz product of the head energy and the cell energy
supplies them from the weight bound `hθ`, the pairing bound `hbd`, the annealed bounds `hGsq` and
`hDval` and the source-load summability `hsumm` that the row already carries. -/
theorem integrable_and_abs_integral_sub_cellPart_le_descendant_load_of_carriers {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (Phi Tcell : CoeffSpace d → ℝ) (inc rem : ℕ → CoeffSpace d → ℝ)
    (Z : ℕ → Finset (Fin d → ℤ)) (θ : ℕ → (Fin d → ℤ) → ℝ)
    (pairing G D : ℕ → (Fin d → ℤ) → CoeffSpace d → ℝ) (K EJ : ℝ)
    (hK : 0 ≤ K) (hEJ : 0 ≤ EJ)
    (hdec : ∀ (N : ℕ) (a : CoeffSpace d),
      Phi a = Tcell a + (∑ n ∈ Finset.range N, inc n a) + rem N a)
    (hincdef : ∀ (n : ℕ) (a : CoeffSpace d),
      inc n a = ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a)
    (hrem0 : ∀ a : CoeffSpace d, Filter.Tendsto (fun N : ℕ => rem N a) Filter.atTop (nhds 0))
    (hθ : ∀ n : ℕ, ∀ W ∈ Z n, |θ n W| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ G n W a)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hbd : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, |pairing n W a| ≤ G n W a * Real.sqrt (2 * D n W a))
    (hGsq : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
      ≤ (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2)
    (hDval : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P) ≤ 2 * EJ)
    (hPhiM : AEStronglyMeasurable Phi P) (hT : Integrable Tcell P)
    (hincI : ∀ n : ℕ, Integrable (inc n) P)
    (hFint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P)
    (hDint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P)
    (hMidint : ∀ n : ℕ, Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) P)
    (hPint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a))) P)
    (hsumm : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2))) :
    Integrable Phi P
      ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P|
          ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
                * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
              * Real.sqrt (2 * EJ) := by
  classical
  set L : ℕ → ℝ := fun n =>
    (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d (n + 1),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
              Y.2))) ^ 2 with hLdef
  set g : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2) with hgdef
  -- The layer weights shift by one generation, so the layer series is summable.
  have hweight : ∀ n : ℕ,
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
        = (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) := by
    intro n
    have hw : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
        = (3 : ℝ) ^ ((3 : ℝ) / 2)
          * (3 : ℝ) ^ (-((3 : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    rw [hw, hLdef, hgdef]
    ring
  have hsumL : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
    have hg1 : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff 1).2 hsumm
    exact Summable.congr (Summable.mul_left ((3 : ℝ) ^ ((3 : ℝ) / 2)) hg1)
      fun n => (hweight n).symm
  have henv := aeSummable_and_integrable_tsum_descendantEnvelope P Z G D L K EJ hK hD
    hGsq hDval hFint hDint hsumL
  refine integrable_and_abs_integral_sub_cellPart_le_descendant_load P jStar F s b Y Phi Tcell
    inc rem Z θ pairing G D (descendantEnvelope Z G D K) K EJ hK hEJ hdec hincdef
    (fun n a => descendantEnvelope_nonneg Z G D K hK hD n a) ?_ henv.1 henv.2 hrem0 hθ hG hD hbd
    hGsq hDval hPhiM hT hincI hFint hDint hMidint hPint hsumm
  intro n a
  rw [hincdef n a]
  exact abs_flat_weighted_pairing_le_descendantEnvelope Z θ pairing G D K hK hθ hG hD hbd n a

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The oscillation half of the cutoff-mean row at the carriers

`CutoffOscillationHalfClosure` bounds the oscillation half of the cutoff-mean row of
`p.response.transfer`
by the source load from the carriers' own data.  This module supplies that data for the terminal
optimizer family of the response cell: the refinement identity at every depth, the cutoff weight
increment, the pathwise crossed pairing bound on each descendant cell, the nonnegativity and the
annealed value of the descendant cell energies, the annealed head of each descendant generation,
and the pathwise vanishing of the remainder.

What is left as a hypothesis is one per-descendant-cell annealed readout, the crossed pairing,
together with the measurability of the annealed functional and the integrability of its cell
part.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

private theorem hasIntegrableCoarseBlock_respGridAdaptedCell {d : ℕ}
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) :
    ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w) := fun k w =>
  hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar hjStar
    F hm k w

private theorem respCoeffMinusCarrierIntegrabilityFacts {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (hq : IsUnit (respGrid jStar F))
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ) (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uP a))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    AEStronglyMeasurable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffMinus F a) (uP a) x).2))) P ∧
    (∀ a : CoeffSpace d, IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffMinus F a) (uP a) x).2)
      (HighContrast.adaptedCell (respGrid jStar F) t)) ∧
    (∀ (k : ℤ) (W : Fin d → ℤ), Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffMinus F a)).upperLeft Y.1)) +
       Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffMinus F a)).lowerRight Y.2)) ^ 2) P) := by
  have hq0 : IsUnit (respGrid jStar F) := hq
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq0 t).measurableSet
  have hPhiM : AEStronglyMeasurable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffMinus F a) (uP a) x).2))) P := by
    have hcont : Continuous (fun x : Vec d => φ x - 1) :=
      hφ.2.2.2.2.2.1.continuous.sub continuous_const
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq0
        t).isFiniteMeasure_restrict_volume
    have hL2 : MemScalarL2 (respCell jStar F t)
        ((respCell jStar F t).indicator (fun x => φ x - 1)) := by
      refine MemLp.of_bound ((hcont.measurable.indicator hUmeas).aestronglyMeasurable) 2
        (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ respCell jStar F t
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
        have h1 := hφ.1 x
        have h2 := hφ.2.1 x
        constructor <;> linarith only [h1, h2]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        norm_num
    exact (measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus P jStar hjStar F
      hm t e uP hmax hUmeas (fun x hx => hx) hcont hL2 Y).aestronglyMeasurable
  have hUcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 =
      respCell jStar F t := by
    rw [Nat.cast_zero, sub_zero]
    exact adaptedCellAtCenter_zero (respGrid jStar F) t
  have hfat : ∀ (a : CoeffSpace d) (m : ℕ), ∀ W ∈ triadicIndexBox d m, IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffMinus F a) (uP a) x).2)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) := fun a m W hW =>
    (integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uP a) Y hW).1
  have hfint : ∀ a : CoeffSpace d, IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffMinus F a) (uP a) x).2)
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    intro a
    have h := hfat a 0 0 (zero_mem_triadicIndexBox 0)
    rwa [hUcell] at h
  have hUL0 : ∀ (k : ℤ) (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W)
        (respCoeffMinus F a)).upperLeft Y.1) := fun k W a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm k a Y W).1
  have hLR0 : ∀ (k : ℤ) (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W)
        (respCoeffMinus F a)).lowerRight Y.2) := fun k W a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm k a Y W).2
  have hheadsq : ∀ (k : ℤ) (W : Fin d → ℤ), Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffMinus F a)).upperLeft Y.1)) +
        Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffMinus F a)).lowerRight Y.2)) ^ 2)
      P := by
    intro k W
    have hblk : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k W) :=
      hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar hjStar
        F hm k W
    exact integrable_sq_sqrt_add_sqrt_coarseBlockMatrix Y
      (integrable_vecDot_coarseBlockMatrix_upperLeft Y
        (integrable_coarseBlockMatrix_upperLeft_respCoeffMinus P jStar hjStar F hm k W hblk))
      (integrable_vecDot_coarseBlockMatrix_lowerRight Y
        (integrable_coarseBlockMatrix_lowerRight_respCoeffMinus P jStar hjStar F hm k W hblk))
      (fun a => hUL0 k W a) (fun a => hLR0 k W a)
  exact ⟨hPhiM, hfint, hheadsq⟩

/-- **The oscillation half of the cutoff-mean row at the carriers, minus sign.**  The
`(φ-1)`-weighted cell average of the crossed pairing of the deterministic dual variable with the
terminal optimizer state is `P`-integrable, and its annealed mean differs from that of its
depth-`H` cell part by at most `32 d² Θ 3^{-H} (3^{3/2} 𝓛_s^-)^{1/2} (8 E[J_t^-])^{1/2}` times the
geometric factor. -/

theorem integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffMinus_car {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (hq : IsUnit (respGrid jStar F))
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s)
    (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (Y : BlockVec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hsumm : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).upperLeft Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).lowerRight Y.2))) ^ 2))) :
    Integrable (fun a => volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))) P
      ∧ |(∫ a, volumeAverage (respCell jStar F t)
              (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
                + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) ∂P)
            - ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                    (fun x => φ x - 1) *
                  volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                    (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
                      + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2) ∂P|
          ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
                  * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) *
                      respSourceLoad P jStar F s (respCoeffMinus F) Y))
              * Real.sqrt (2 * (4 * respEJMinus P jStar F t e)) := by
  classical
  have hblkAll := hasIntegrableCoarseBlock_respGridAdaptedCell hd P γ E Ψ Kg Src hstat hdag
    jStar hjStar F hm
  have hcross : ∀ (m : ℕ), ∀ W ∈ triadicIndexBox d m, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) P :=
    fun m W hW => integrable_volumeAverage_cross_optimizerField_respCoeffMinus P jStar hjStar F hm
      t e uM hmax hJ hblkAll Y m W hW
  have hcellP : ∀ (n : ℕ), ∀ W ∈ triadicIndexBox d (H + n + 1), Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) P :=
    fun n W hW => hcross (H + n + 1) W hW
  have hT : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
            (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
              + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) P :=
    integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
      (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
        (fun x => φ x - 1))
      (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
      (fun _ W hW => hcross H W hW) 0
  obtain ⟨hPhiM, hfint, hheadsq⟩ := respCoeffMinusCarrierIntegrabilityFacts hd P hstat γ E Ψ Kg Src
    hdag jStar hjStar F hm hq t e φ hφ Y uM hmax hJ
  have hcellE : ∀ (n : ℕ), ∀ W ∈ triadicIndexBox d (H + n + 1), Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    fun n W hW => integrable_volumeAverage_energy_descendant_respCoeffMinus P jStar hjStar F hm
      H s t ht e uM hmax hJ n W hW
  refine integrable_and_abs_integral_sub_cellPart_le_descendant_load_of_carriers
    P jStar F s (respCoeffMinus F) Y
    (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
        + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)))
    (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) (fun x => φ x - 1) *
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
    (fun n a => ((triadicIndexBox d (H + n + 1)).card : ℝ)⁻¹ *
      ∑ W ∈ triadicIndexBox d (H + n + 1),
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
              (fun x => φ x - 1)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n : ℕ) : ℤ))
                (Transport.gridParent W)) (fun x => φ x - 1)) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
            (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
              + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
    (fun N a => volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
      - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
              (fun x => φ x - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
              (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
                + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
    (fun n => triadicIndexBox d (H + n + 1))
    (fun n W => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
          (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n : ℕ) : ℤ))
            (Transport.gridParent W)) (fun x => φ x - 1))
    (fun n W a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
        + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
    (fun n W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
          (respCoeffMinus F a)).upperLeft Y.1))
      + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
          (respCoeffMinus F a)).lowerRight Y.2)))
    (fun n W a => 2 * volumeAverage
      (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
    (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
    (4 * respEJMinus P jStar F t e) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hPhiM hT ?_ ?_ ?_ ?_ ?_ hsumm
  · exact mul_nonneg (mul_nonneg (by positivity)
      (by linarith only [one_le_responseCutoffProfileConst])) (by positivity)
  · have := zero_le_respEJMinus P jStar F t e hq
    linarith only [this]
  · intro N a
    exact volumeAverage_sub_one_eq_cellPart_add_sum_range_add_rem hq t H N φ (hfint a)
  · intro n a
    rfl
  · intro a
    exact tendsto_zero_descendantRemainder_respCoeffMinus jStar hjStar F hm t H hφ uM Y a
  · intro n W _
    exact abs_cutoff_weight_increment_le hq hφ H n W
  · intro n W _ a
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · intro n W hW a
    have := zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffMinus_adaptedCellAtCenter
      jStar hjStar F hm t (H + n + 1) a (uM a) hW
    linarith only [this]
  · intro n W hW a
    exact abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le jStar hjStar F
      hm t (H + n + 1) a (uM a) Y hW
      (fun i => (integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hq t F a
        (uM a) (H + n + 1) W hW i).1)
      (fun i => (integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hq t F a
        (uM a) (H + n + 1) W hW i).2)
      ((integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t
        (H + n + 1) a (uM a) hW).1 Y.2)
      ((integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t
        (H + n + 1) a (uM a) hW).2 Y.1)
  · intro n
    have hshift : t - ((H + n + 1 : ℕ) : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by
      rw [ht]; push_cast; ring
    simp only [hshift]
    exact integral_avsum_sq_head_descendant_le_respCoeffMinus_car hd P hstat γ E Ψ Kg Src hdag
      jStar hjStar F hm H (n + 1) s hjs Y
  · intro n
    exact (integral_avsum_two_mul_doubledEnergy_eq_respEJMinus P jStar F t (H + n + 1) e hq uM
      hmax hEint hJ).le
  · intro n
    exact integrable_avsum_weighted_pairing (fun m => triadicIndexBox d (H + m + 1))
      (fun m W => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (fun x => φ x - 1)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m : ℕ) : ℤ))
              (Transport.gridParent W)) (fun x => φ x - 1))
      (fun m W a => volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
      hcellP n
  · intro n
    exact integrable_avsum_sq_head (fun m => triadicIndexBox d (H + m + 1))
      (fun m W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffMinus F a)).lowerRight Y.2)))
      (fun m W _ => hheadsq (t - ((H + m + 1 : ℕ) : ℤ)) W) n
  · intro n
    exact integrable_avsum_two_mul_energy (fun m => triadicIndexBox d (H + m + 1))
      (fun m W a => 2 * volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      (fun m W hW => (hcellE m W hW).const_mul 2) n
  · intro n
    exact integrable_sqrt_avsum_mul_sqrt_avsum (fun m => triadicIndexBox d (H + m + 1))
      (fun m W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffMinus F a)).lowerRight Y.2)))
      (fun m W a => 2 * volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      (fun m W _ => hheadsq (t - ((H + m + 1 : ℕ) : ℤ)) W)
      (fun m W hW => (hcellE m W hW).const_mul 2) n
  · intro n
    exact integrable_avsum_weighted_sqrt_mul_sqrt (fun m => triadicIndexBox d (H + m + 1))
      (fun m W => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (fun x => φ x - 1)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m : ℕ) : ℤ))
              (Transport.gridParent W)) (fun x => φ x - 1))
      (fun m W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffMinus F a)).lowerRight Y.2)))
      (fun m W a => 2 * volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      (fun m W _ => hheadsq (t - ((H + m + 1 : ℕ) : ℤ)) W)
      (fun m W hW => (hcellE m W hW).const_mul 2) n

end

end HCPolySupport.HighContrast.Multiscale
end
