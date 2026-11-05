/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionRoot
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedDivergencePotential

/-!
# SuperposedConclusion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected superposed competitor in the Section 3 conclusion

This file performs the deterministic composition at the superposed affine
competitor.  Its two fields are deliberately different:

* `F = superposedCompetitorSlope ... p`, the slope field of the superposed
  scalar competitor;
* `G = superposedCompetitorDivergence ... q`, the divergence of the
  antisymmetric matrix assembled from the basis-load scalar competitors.

In particular, the `G` leg is never the slope construction rerun at `q`.

The first theorem is the exact conditional `e.sum-of-a-decomp` seam.  The
second composes it with the already assembled Step-3 payload, using the common
collar constant `superposedDivConst d`.  The smaller `F`-leg constant is
weakened by `superposedGradConst_le_superposedDivConst`; the `G`-leg envelope
is the one proved in `Affine.SuperposedDivergence`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The exact conditional decomposition seam -/

/-- The `e.sum-of-a-decomp` inequality at the corrected superposed pair.

The only analytic premises are the two manuscript Sobolev memberships, stated
at the actual global fields consumed by the decomposition.  All cellwise
constancy, bad-cell vanishing, and off-collar normalization clauses are
discharged by the proved superposed slope and divergence A. -/
theorem ofReal_abs_blockVecDot_le_tsum_superposedDivergence
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ} {omega : CutoffSample d}
    (hd : 2 ≤ d) (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (L : ℤ) (p q : Vec d)
    (hF : Ch01.PotentialZeroTraceFieldOn (openCubeSet (originCube d m))
      (fun x => superposedCompetitorSlope m (whitneyScale M m E b k₀ omega)
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) p x - p))
    (hG : Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet (originCube d m))
      (fun x => superposedCompetitorDivergence m (whitneyScale M m E b k₀ omega)
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) q x - q)) :
    ENNReal.ofReal
        |blockVecDot (p, q)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m)))
            (p, q))| ≤
      ∑' T : ↥(simplexPartition (d := d) m (whitneyScale M m E b k₀ omega)),
        (ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            goodCellForm M m (whitneyScale M m E b k₀ omega) L omega p q
              (T : KuhnCell d)) +
          ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            collarCellForm M m (whitneyScale M m E b k₀ omega) L omega
              (superposedCompetitorCellSlope m (whitneyScale M m E b k₀ omega)
                (badFamily M m (whitneyScale M m E b k₀ omega) omega) p)
              (superposedCompetitorCellDivergence m (whitneyScale M m E b k₀ omega)
                (badFamily M m (whitneyScale M m E b k₀ omega) omega) q)
              (T : KuhnCell d))) := by
  have : NeZero d := ⟨by omega⟩
  have hmono : Monotone (whitneyScale M m E b k₀ omega) :=
    whitneyScaleSeq_mono hb0.le (by linarith) _ k₀
  have hwin := badComponents_window_badFamily hb0 hb hk₀ hne
  have hcp := superposedCompetitor_decomp_clauses_badFamily hmono M omega hwin p
  have hcq := superposedCompetitorDivergence_decomp_clauses_badFamily
    hd hmono M omega hwin q
  exact sum_of_a_decomp_cutoff (step_of_monotone hmono) M L omega p q _ _ _ _ hF hG
    (fun T hT => hcp.1 ⟨T, hT⟩) (fun T hT => hcq.1 ⟨T, hT⟩)
    (fun T hT => hcp.2.1 ⟨T, hT⟩) (fun T hT => hcq.2.1 ⟨T, hT⟩)
    (fun T hT => hcp.2.2 ⟨T, hT⟩) (fun T hT => hcq.2.2 ⟨T, hT⟩)

/-- One-premise form of the corrected decomposition seam.  An all-load
potential theorem supplies the `F` leg at `p`; its basis-load specializations
produce the correct solenoidal `G` leg through the antisymmetric-divergence
bridge. -/
theorem ofReal_abs_blockVecDot_le_tsum_superposedDivergence_of_forall
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ} {omega : CutoffSample d}
    (hd : 2 ≤ d) (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (L : ℤ) (p q : Vec d)
    (hF : ∀ r : Vec d,
      Ch01.PotentialZeroTraceFieldOn (openCubeSet (originCube d m))
        (fun x => superposedCompetitorSlope m (whitneyScale M m E b k₀ omega)
          (badFamily M m (whitneyScale M m E b k₀ omega) omega) r x - r)) :
    ENNReal.ofReal
        |blockVecDot (p, q)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m)))
            (p, q))| ≤
      ∑' T : ↥(simplexPartition (d := d) m (whitneyScale M m E b k₀ omega)),
        (ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            goodCellForm M m (whitneyScale M m E b k₀ omega) L omega p q
              (T : KuhnCell d)) +
          ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            collarCellForm M m (whitneyScale M m E b k₀ omega) L omega
              (superposedCompetitorCellSlope m (whitneyScale M m E b k₀ omega)
                (badFamily M m (whitneyScale M m E b k₀ omega) omega) p)
              (superposedCompetitorCellDivergence m (whitneyScale M m E b k₀ omega)
                (badFamily M m (whitneyScale M m E b k₀ omega) omega) q)
              (T : KuhnCell d))) := by
  exact ofReal_abs_blockVecDot_le_tsum_superposedDivergence hd hb0 hb hk₀ hne L p q
    (hF p)
    (superposedCompetitorDivergence_sub_solenoidalZeroNormalTraceFieldOn_of_forall
      hd m (whitneyScale M m E b k₀ omega)
      (badFamily M m (whitneyScale M m E b k₀ omega) omega) q hF)

/-! ## Composition with the assembled payload -/

/-- The corrected superposed branch of the Step-3 conclusion, conditional only
on the two global Sobolev memberships.  Both collar legs are priced with the
common constant `superposedDivConst d`; this is exact for `G` and a monotone
weakening of the `superposedGradConst d` estimate for `F`. -/
theorem abs_blockVecDot_coarseBlockMatrix_originCube_le_payload_superposedDivergence_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {i : ℤ}
    (hmi : m - 1 ≤ i) (hi : i ≤ m0) {L : ℤ} (hmL : m ≤ L) (p q : Vec d)
    {eps : ℝ} (heps : 0 < eps) {t : ℝ} (ht0 : 0 ≤ t) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(Percolation.siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (Percolation.hsepSet M m (E : ℝ) b omega).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n,
        cubeSupBound Q Q.scale L omega.1 ≤
          whitneyWaveLayerScale M m (whitneyScale M m (E : ℝ) b k₀ omega) n L * t) →
      Ch01.PotentialZeroTraceFieldOn (openCubeSet (originCube d m))
        (fun x => superposedCompetitorSlope m (whitneyScale M m (E : ℝ) b k₀ omega)
            (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
            ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p) x -
          (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p) →
      Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet (originCube d m))
        (fun x => superposedCompetitorDivergence m
            (whitneyScale M m (E : ℝ) b k₀ omega)
            (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
            (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) x -
          Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) →
      |blockVecDot
          ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
            Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m)))
            ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
              Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q))| ≤
        layerSumConst beta (2 * M.gamma + eps) kp
            (ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q)
            (collarEnvelopeConst M m i L eps t (superposedDivConst d) p q)
            (6 * (d : ℝ)) *
          ((3 : ℝ) ^ ((2 * M.gamma + eps) *
              ((Percolation.hsep M m (E : ℝ) b omega + k₀ : ℕ) : ℝ)) *
            (1 + (3 : ℝ) ^ (2 * beta *
                ((Percolation.hsep M m (E : ℝ) b omega + k₀ : ℕ) : ℝ)) *
              Real.exp (-((kp : ℝ) / 36)))) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hCgrad : (1 : ℝ) ≤ superposedDivConst d :=
    one_le_superposedDivConst (by omega)
  have hK : (0 : ℝ) ≤ ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q :=
    ktotConst_nonneg hd M m i (by norm_num) _ p q
  have hC : (0 : ℝ) ≤
      collarEnvelopeConst M m i L eps t (superposedDivConst d) p q :=
    collarEnvelopeConst_nonneg hd M m i L eps t (superposedDivConst d) p q
  have hsig : (0 : ℝ) < (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M i).1
  have hs0 : (0 : ℝ) < Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    Real.sqrt_pos.2 hsig
  have hsne : Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ≠ 0 :=
    ne_of_gt hs0
  have hGrad0 : (0 : ℝ) ≤ superposedGradConst d :=
    le_trans zero_le_one (one_le_superposedGradConst (by omega))
  have hDiv0 : (0 : ℝ) ≤ superposedDivConst d := le_trans zero_le_one hCgrad
  have hGradSq : superposedGradConst d ^ 2 ≤ superposedDivConst d ^ 2 :=
    (sq_le_sq₀ hGrad0 hDiv0).2 (superposedGradConst_le_superposedDivConst (by omega))
  filter_upwards [tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload_assembled_ae
    hd M hS m hb0 hb (by omega : 1 ≤ k₀) hmi hi hmL p q heps ht0 hCgrad
    hbeta0 hbeta9 hbetab hgammaWin hcap]
    with omega hpay hne henv hF hG
  have hFv : ∀ (n : ℕ),
      ∀ Q ∈ whitneyLayer (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n,
      ∀ T ∈ whitneySimplexCells (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n Q,
        vecNormSq (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
            superposedCompetitorCellSlope m (whitneyScale M m (E : ℝ) b k₀ omega)
              (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
              ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T -
            p) ≤
          superposedDivConst d ^ 2 *
            (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
              (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) * vecNormSq p := by
    intro n Q hQ T hT
    have hbase := badFamily_vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope
      hb0 hb hk₀ hne
      ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) hQ hT
    have hrw :
        Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
            superposedCompetitorCellSlope m (whitneyScale M m (E : ℝ) b k₀ omega)
              (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
              ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T - p =
          Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
            (superposedCompetitorCellSlope m (whitneyScale M m (E : ℝ) b k₀ omega)
                (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
                ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T -
              (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) := by
      rw [smul_sub, smul_inv_smul₀ hsne]
    rw [hrw, vecNormSq_smul]
    have hsmall :
        Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 *
            vecNormSq
              (superposedCompetitorCellSlope m
                  (whitneyScale M m (E : ℝ) b k₀ omega)
                  (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
                  ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T -
                (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) ≤
          superposedGradConst d ^ 2 *
            (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
              (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) * vecNormSq p := by
      calc
        _ ≤ Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 *
              (superposedGradConst d ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
                  (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) *
                vecNormSq
                  ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p)) :=
            mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
        _ = _ := by
          rw [vecNormSq_smul]
          field_simp
    exact hsmall.trans (by
      have htail : (0 : ℝ) ≤
          (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
            (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) * vecNormSq p :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (vecNormSq_nonneg p)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hGradSq htail)
  have hGv : ∀ (n : ℕ),
      ∀ Q ∈ whitneyLayer (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n,
      ∀ T ∈ whitneySimplexCells (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n Q,
        vecNormSq ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ •
            superposedCompetitorCellDivergence m
              (whitneyScale M m (E : ℝ) b k₀ omega)
              (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
              (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) T - q) ≤
          superposedDivConst d ^ 2 *
            (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
              (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) * vecNormSq q := by
    intro n Q hQ T hT
    have hbase :=
      badFamily_vecNormSq_superposedCompetitorCellDivergence_sub_le_layerEnvelope
        hd hb0 hb hk₀ hne
        (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) hQ hT
    have hrw :
        (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ •
            superposedCompetitorCellDivergence m
              (whitneyScale M m (E : ℝ) b k₀ omega)
              (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
              (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) T - q =
          (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ •
            (superposedCompetitorCellDivergence m
                (whitneyScale M m (E : ℝ) b k₀ omega)
                (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
                (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) T -
              Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) := by
      rw [smul_sub, inv_smul_smul₀ hsne]
    rw [hrw, vecNormSq_smul]
    calc
      _ ≤ (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ ^ 2 *
            (superposedDivConst d ^ 2 *
              (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
                (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) *
              vecNormSq
                (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q)) :=
          mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = _ := by
        rw [vecNormSq_smul]
        field_simp
  have hstep := hpay hne henv
    (fun U => Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
      superposedCompetitorCellSlope m (whitneyScale M m (E : ℝ) b k₀ omega)
        (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
        ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) U)
    (fun U => (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ •
      superposedCompetitorCellDivergence m (whitneyScale M m (E : ℝ) b k₀ omega)
        (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
        (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) U)
    hFv hGv
  simp only [inv_smul_smul₀ hsne, smul_inv_smul₀ hsne] at hstep
  have hdec := ofReal_abs_blockVecDot_le_tsum_superposedDivergence
    hd hb0 hb hk₀ hne L
    ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p)
    (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • q) hF hG
  exact (ENNReal.ofReal_le_ofReal_iff
    (payload_nonneg _ hK hC (by positivity))).1 (le_trans hdec hstep)

end

end Algsuperdiff.Section3.Provider.Multiscale
