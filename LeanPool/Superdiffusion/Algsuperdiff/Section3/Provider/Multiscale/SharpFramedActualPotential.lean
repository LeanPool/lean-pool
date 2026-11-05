/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayers
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialClosure

/-!
# SharpFramedActualPotential

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Framed potential-coordinate layer summation

This file carries the observation-to-layer frame through the existing
potential-coordinate decomposition.  Every declaration here is an internal
conditional proof obligation.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

private theorem probe_superposedCompetitorCellDivergence_zero
    (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d)) (T : KuhnCell d) :
    superposedCompetitorCellDivergence m hn I (0 : Vec d) T = 0 := by
  funext j
  simp [superposedCompetitorCellDivergence_apply]

theorem probeFramedGoodLayerMeanRhs_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (n : ℕ) (i L : ℤ) (omega : CutoffSample d) (p : Vec d) :
    0 ≤ probeFramedGoodLayerMeanRhs M m hn n i L omega p := by
  unfold probeFramedGoodLayerMeanRhs
  have hbase : 0 ≤ probeMeanGoodBaseConst d :=
    probeMeanGoodBaseConst_nonneg hd
  have hwave : 0 ≤ probeMeanGoodWaveConst M :=
    probeMeanGoodWaveConst_nonneg hd M
  have hmass : 0 ≤ ∑ Q ∈ whitneyLayer (d := d) m hn n,
      cubeMassRatio (originCube d m) Q :=
    Finset.sum_nonneg fun Q _ => cubeMassRatio_nonneg _ Q
  exact add_nonneg
    (mul_nonneg (mul_nonneg hbase (vecNormSq_nonneg p)) hmass)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hwave (vecNormSq_nonneg p)) (Real.sqrt_nonneg _))
      (probeFramedLayerWaveFactor_nonneg M m hn n i L omega))

theorem probeFramedCollarLayerMeanRhs_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (n : ℕ) (i L : ℤ) (omega : CutoffSample d) (p : Vec d)
    (Cgrad b : ℝ) :
    0 ≤ probeFramedCollarLayerMeanRhs M m hn n i L omega p Cgrad b := by
  unfold probeFramedCollarLayerMeanRhs
  have hbase : 0 ≤ probeMeanGoodBaseConst d :=
    probeMeanGoodBaseConst_nonneg hd
  have hwave : 0 ≤ probeMeanGoodWaveConst M :=
    probeMeanGoodWaveConst_nonneg hd M
  have hmass : 0 ≤ ∑ Q ∈ collarLayer M m hn n omega,
      cubeMassRatio (originCube d m) Q :=
    Finset.sum_nonneg fun Q _ => cubeMassRatio_nonneg _ Q
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (mul_nonneg (sq_nonneg Cgrad) (Real.rpow_nonneg (by norm_num) _)))
    (add_nonneg
      (mul_nonneg (mul_nonneg hbase (vecNormSq_nonneg p)) hmass)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hwave (vecNormSq_nonneg p)) (Real.sqrt_nonneg _))
        (probeFramedLayerWaveFactor_nonneg M m hn n i L omega)))

private theorem sharpFramedActualPotential_comparisonBounds1 :
    ∀ {d : ℕ} (_ : (2 : ℕ) ≤ d) (M : ABKModel d) {m0 : ℤ} {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (_ : Frozen.Section3.inductionState M m0 E) (m : ℤ) {b : ℝ} (_ : (0 : ℝ) < b) (_ : b ≤ (1 /
        8 : ℝ)) {k₀ : ℕ}
      {i : ℤ} (_ : m - (1 : ℤ) ≤ i) (_ : i ≤ m0) {L : ℤ} (_ : m ≤ L) (p : Vec d),
      √(↑(Annealed.sigmaBar M i) : ℝ) ≠ (0 : ℝ) ∧
        (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∀ (hs n : ℕ),
              ∑ Q ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) n,
                  ∑ T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) n Q,
                    ENNReal.ofReal
                      (cellWeight m T *
                        goodCellForm M m (whitneyScaleSeq b hs k₀) L omega ((√(↑(Annealed.sigmaBar
                          M i) : ℝ))⁻¹ • p)
                          (0 : Vec d) T) ≤
                ENNReal.ofReal (probeFramedGoodLayerMeanRhs M m (whitneyScaleSeq b hs k₀) n i L
                  omega p)) ∧
          ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∀ (hs n : ℕ) (Fv Gv : KuhnCell d → Vec d) (p' : Vec d),
              (∀ Q ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) n,
                  ∀ T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) n Q,
                    vecNormSq (Fv T - p') ≤
                      superposedGradConst d ^ (2 : ℕ) *
                          (3 : ℝ) ^ ((2 : ℝ) * (b * ((↑n : ℝ) + (↑(whitneyScaleSeq b hs k₀ n) :
                            ℝ)))) *
                        vecNormSq p') →
                (∀ Q ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) n,
                    ∀ T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) n Q, vecNormSq (Gv T) ≤
                      (0 : ℝ)) →
                  ∑ Q ∈ collarLayer M m (whitneyScaleSeq b hs k₀) n omega,
                      ∑ T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) n Q,
                        ENNReal.ofReal
                          (cellWeight m T *
                            collarCellForm M m (whitneyScaleSeq b hs k₀) L omega
                              (fun (U : KuhnCell d) => (√(↑(Annealed.sigmaBar M i) : ℝ))⁻¹ • Fv U)
                              (fun (U : KuhnCell d) => √(↑(Annealed.sigmaBar M i) : ℝ) • Gv U) T) ≤
                    ENNReal.ofReal
                      (probeFramedCollarLayerMeanRhs M m (whitneyScaleSeq b hs k₀) n i L omega p'
                        (superposedGradConst d) b) := by
  intro d hd M _ _ hS m b hb0 hb k₀ i hmi hi L hmL p
  have hsigma : 0 < (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M i).1
  have hsqrt : 0 < Real.sqrt
      (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    Real.sqrt_pos.2 hsigma
  have hsne : Real.sqrt
      (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ≠ 0 :=
    ne_of_gt hsqrt
  have hCgrad : 1 ≤ superposedGradConst d :=
    one_le_superposedGradConst (by omega)
  have hgoodAll : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ hs n : ℕ,
        (∑ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
          ∑ T ∈ whitneySimplexCells (d := d) m
              (whitneyScaleSeq b hs k₀) n Q,
            ENNReal.ofReal (cellWeight m T *
              goodCellForm M m (whitneyScaleSeq b hs k₀) L omega
                ((Real.sqrt
                  (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p)
                (0 : Vec d) T)) ≤
          ENNReal.ofReal
            (probeFramedGoodLayerMeanRhs M m
              (whitneyScaleSeq b hs k₀) n i L omega p) :=
    ae_all_iff.2 fun hs => ae_all_iff.2 fun n =>
      probe_sum_ofReal_goodCellForm_layer_le_framedMeanFourth_ae
        hd M hS m (whitneyScaleSeq b hs k₀) n
        (step_of_monotone (whitneyScaleSeq_mono hb0.le (by linarith) hs k₀) n)
        (whitneyScaleSeq_succ_le hb0 hb hs k₀ n) hmi hi hmL p
  have hcolAll : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ hs n : ℕ,
        ∀ (Fv Gv : KuhnCell d → Vec d) (p' : Vec d),
          (∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
            ∀ T ∈ whitneySimplexCells (d := d) m
                (whitneyScaleSeq b hs k₀) n Q,
              vecNormSq (Fv T - p') ≤ superposedGradConst d ^ 2 *
                (3 : ℝ) ^ (2 * (b *
                  ((n : ℝ) + (whitneyScaleSeq b hs k₀ n : ℝ)))) *
                vecNormSq p') →
          (∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
            ∀ T ∈ whitneySimplexCells (d := d) m
                (whitneyScaleSeq b hs k₀) n Q,
              vecNormSq (Gv T) ≤ 0) →
          (∑ Q ∈ collarLayer M m (whitneyScaleSeq b hs k₀) n omega,
            ∑ T ∈ whitneySimplexCells (d := d) m
                (whitneyScaleSeq b hs k₀) n Q,
              ENNReal.ofReal (cellWeight m T *
                collarCellForm M m (whitneyScaleSeq b hs k₀) L omega
                  (fun U => (Real.sqrt
                    (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • Fv U)
                  (fun U => Real.sqrt
                    (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • Gv U) T)) ≤
            ENNReal.ofReal
              (probeFramedCollarLayerMeanRhs M m
                (whitneyScaleSeq b hs k₀) n i L omega p'
                (superposedGradConst d) b) :=
    ae_all_iff.2 fun hs => ae_all_iff.2 fun n =>
      probe_sum_ofReal_collarCellForm_layer_le_framedMeanFourth_ae
        hd M hS m (whitneyScaleSeq b hs k₀) n
        (step_of_monotone (whitneyScaleSeq_mono hb0.le (by linarith) hs k₀) n)
        (whitneyScaleSeq_succ_le hb0 hb hs k₀ n) hmi hi hmL hCgrad hb0.le
  exact ⟨hsne, hgoodAll, hcolAll⟩

private theorem sharpFramedActualPotential_comparisonBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }} (m : ℤ) {b : ℝ} (_ : (0 : ℝ) < b)
      (_ : b ≤ (1 / 8 : ℝ)) {k₀ : ℕ} (_ : (3 : ℕ) ≤ k₀) {i : ℤ} (p : Vec d) (_ : NeZero d)
      (_ : √(↑(Annealed.sigmaBar M i) : ℝ) ≠ (0 : ℝ)) (omega : CutoffSample d)
      (_ : (Percolation.hsepSet M m (↑E : ℝ) b omega).Nonempty),
      Monotone (whitneyScale M m (↑E : ℝ) b k₀ omega) ∧
        (∀ (n : ℕ),
            ∀ Q ∈ whitneyLayer m (whitneyScale M m (↑E : ℝ) b k₀ omega) n,
              ∀ T ∈ whitneySimplexCells m (whitneyScale M m (↑E : ℝ) b k₀ omega) n Q,
                vecNormSq
                    (√(↑(Annealed.sigmaBar M i) : ℝ) •
                        superposedCompetitorCellSlope m (whitneyScale M m (↑E : ℝ) b k₀ omega)
                          (badFamily M m (whitneyScale M m (↑E : ℝ) b k₀ omega) omega)
                          ((√(↑(Annealed.sigmaBar M i) : ℝ))⁻¹ • p) T -
                      p) ≤
                  superposedGradConst d ^ (2 : ℕ) *
                      (3 : ℝ) ^ ((2 : ℝ) * (b * ((↑n : ℝ) + (↑(whitneyScale M m (↑E : ℝ) b k₀
                        omega n) : ℝ)))) *
                    vecNormSq p) ∧
          ∀ (n : ℕ),
            ∀ Q ∈ whitneyLayer m (whitneyScale M m (↑E : ℝ) b k₀ omega) n,
              ∀ T ∈ whitneySimplexCells m (whitneyScale M m (↑E : ℝ) b k₀ omega) n Q,
                vecNormSq ((0 : KuhnCell d → Vec d) T) ≤ (0 : ℝ) := by
  intro d M E m b hb0 hb k₀ hk₀ i p _ hsne omega hne
  have hmono : Monotone (whitneyScale M m (E : ℝ) b k₀ omega) :=
    whitneyScaleSeq_mono hb0.le (by linarith) _ k₀
  have hFv : ∀ (n : ℕ),
      ∀ Q ∈ whitneyLayer (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n,
      ∀ T ∈ whitneySimplexCells (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n Q,
        vecNormSq
          (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
              superposedCompetitorCellSlope m
                (whitneyScale M m (E : ℝ) b k₀ omega)
                (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
                ((Real.sqrt
                  (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T - p) ≤
          superposedGradConst d ^ 2 *
            (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
              (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) *
            vecNormSq p := by
    intro n Q hQ T hT
    have hbase := badFamily_vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope
      hb0 hb hk₀ hne
      ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) hQ hT
    have hrw :
        Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
            superposedCompetitorCellSlope m
              (whitneyScale M m (E : ℝ) b k₀ omega)
              (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
              ((Real.sqrt
                (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T - p =
          Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
            (superposedCompetitorCellSlope m
                (whitneyScale M m (E : ℝ) b k₀ omega)
                (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
                ((Real.sqrt
                  (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) T -
              (Real.sqrt
                (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p) := by
      rw [smul_sub, smul_inv_smul₀ hsne]
    rw [hrw, vecNormSq_smul]
    calc
      _ ≤ Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 *
            (superposedGradConst d ^ 2 *
              (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
                (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) *
              vecNormSq
                ((Real.sqrt
                  (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p)) :=
          mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = _ := by
        rw [vecNormSq_smul]
        field_simp
  have hGv : ∀ (n : ℕ),
      ∀ Q ∈ whitneyLayer (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n,
      ∀ T ∈ whitneySimplexCells (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n Q,
        vecNormSq ((0 : KuhnCell d → Vec d) T) ≤ 0 := by
    intro n Q hQ T hT
    simp [vecNormSq, vecDot]
  exact ⟨hmono, hFv, hGv⟩

theorem probe_ofReal_abs_potentialCoordinate_le_tsum_framedMeanLayers_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (m : ℤ) {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0)
    {L : ℤ} (hmL : m ≤ L) (p : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (Percolation.hsepSet M m (E : ℝ) b omega).Nonempty →
      ENNReal.ofReal
          |blockVecDot
            ((Real.sqrt
                (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p,
              (0 : Vec d))
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
                ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                  (originCube d m)))
              ((Real.sqrt
                  (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p,
                (0 : Vec d)))| ≤
        ∑' n : ℕ, ENNReal.ofReal
          (probeFramedGoodLayerMeanRhs M m
              (whitneyScale M m (E : ℝ) b k₀ omega) n i L omega p +
            probeFramedCollarLayerMeanRhs M m
              (whitneyScale M m (E : ℝ) b k₀ omega) n i L omega p
              (superposedGradConst d) b) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hsne, hgoodAll, hcolAll⟩ :=
    @sharpFramedActualPotential_comparisonBounds1 (d) (hd) (M) (m0) (E) (hS) (m) (b) (hb0) (hb)
      (k₀) (i) (hmi) (hi) (L) (hmL) (p)
  filter_upwards [hgoodAll, hcolAll] with omega hgood hcol
  intro hne
  obtain ⟨hmono, hFv, hGv⟩ :=
    @sharpFramedActualPotential_comparisonBounds2 (d) (M) (E) (m) (b) (hb0) (hb) (k₀) (hk₀) (i)
      (p) (this) (hsne) (omega) (hne)
  let hn := whitneyScale M m (E : ℝ) b k₀ omega
  let q := (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ • p
  let F : KuhnCell d → ENNReal := fun T =>
    ENNReal.ofReal (cellWeight m T * goodCellForm M m hn L omega q (0 : Vec d) T)
  let G : KuhnCell d → ENNReal := fun T =>
    ENNReal.ofReal (cellWeight m T * collarCellForm M m hn L omega
      (superposedCompetitorCellSlope m hn (badFamily M m hn omega) q)
      (superposedCompetitorCellDivergence m hn (badFamily M m hn omega) (0 : Vec d)) T)
  have hlayer : ∀ n : ℕ,
      (∑ Q ∈ whitneyLayer (d := d) m
          hn n,
        ∑ T ∈ whitneySimplexCells (d := d) m
            hn n Q,
          (F T +
            G T)) ≤
        ENNReal.ofReal
          (probeFramedGoodLayerMeanRhs M m
              hn n i L omega p +
            probeFramedCollarLayerMeanRhs M m
              hn n i L omega p
              (superposedGradConst d) b) := by
    intro n
    have hg := hgood (Percolation.hsep M m (E : ℝ) b omega) n
    have hc0 := hcol (Percolation.hsep M m (E : ℝ) b omega) n
      (fun U => Real.sqrt
        (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
          superposedCompetitorCellSlope m
            hn
            (badFamily M m hn omega)
            q U)
      (0 : KuhnCell d → Vec d) p
    have hc := hc0 (by simpa only [hn, q, whitneyScale] using hFv n)
      (by simpa only [hn, q, whitneyScale] using hGv n)
    have hg' := by simpa only [hn, q, whitneyScale] using hg
    have hdivzero :
        superposedCompetitorCellDivergence m
            hn
            (badFamily M m
              hn omega)
            (0 : Vec d) =
          (0 : KuhnCell d → Vec d) := by
      funext T
      exact probe_superposedCompetitorCellDivergence_zero _ _ _ _
    have hc' :
        (∑ Q ∈ collarLayer M m
            hn n omega,
          ∑ T ∈ whitneySimplexCells (d := d) m
              hn n Q,
            G T) ≤
          ENNReal.ofReal
            (probeFramedCollarLayerMeanRhs M m
              hn n i L omega p
              (superposedGradConst d) b) := by
      dsimp only [G]
      rw [hdivzero]
      simpa [G, hn, q, whitneyScale, inv_smul_smul₀ hsne] using! hc
    have hcolrestrict :
        (∑ Q ∈ whitneyLayer (d := d) m
            hn n,
          ∑ T ∈ whitneySimplexCells (d := d) m
              hn n Q,
            G T) =
          ∑ Q ∈ collarLayer M m
              hn n omega,
            ∑ T ∈ whitneySimplexCells (d := d) m
                hn n Q,
              G T := by
      apply (Finset.sum_subset
        (collarLayer_subset M m
          hn n omega) ?_).symm
      intro Q hQ hQcol
      refine Finset.sum_eq_zero fun T hT => ?_
      dsimp only [G]
      rw [collarLayer_zero M m
        hn n L omega
        (superposedCompetitorCellSlope m
          hn
          (badFamily M m
            hn omega)
          q)
        (superposedCompetitorCellDivergence m
          hn
          (badFamily M m
            hn omega)
          (0 : Vec d)) Q hQ hQcol T hT,
        mul_zero, ENNReal.ofReal_zero]
    have hsplit :
        (∑ Q ∈ whitneyLayer (d := d) m
            hn n,
          ∑ T ∈ whitneySimplexCells (d := d) m
              hn n Q,
            (F T +
              G T)) =
          (∑ Q ∈ whitneyLayer (d := d) m
              hn n,
            ∑ T ∈ whitneySimplexCells (d := d) m
                hn n Q,
              F T) +
            ∑ Q ∈ whitneyLayer (d := d) m
                hn n,
              ∑ T ∈ whitneySimplexCells (d := d) m
                  hn n Q,
                G T := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun Q _ => Finset.sum_add_distrib
    rw [hsplit]
    rw [hcolrestrict]
    refine (add_le_add hg' hc').trans ?_
    simpa only [hn, q, whitneyScale] using
      (ENNReal.ofReal_add
        (probeFramedGoodLayerMeanRhs_nonneg hd M m
          hn n i L omega p)
        (probeFramedCollarLayerMeanRhs_nonneg hd M m
          hn n i L omega p
          (superposedGradConst d) b)).symm.le
  have hdec :=
    ofReal_abs_blockVecDot_le_tsum_superposedDivergence_of_forall
      hd hb0 hb hk₀ hne L
      q
      (0 : Vec d)
      (fun r => potentialZeroTraceFieldOn_superposedCompetitorSlope_sub_badFamily
        hb0 hb hk₀ hne r)
  calc
    _ ≤ ∑' T : ↑(simplexPartition (d := d) m
          hn),
        (F (T : KuhnCell d) +
          G (T : KuhnCell d)) := hdec
    _ = ∑' n : ℕ,
        ∑ Q ∈ whitneyLayer (d := d) m
            hn n,
          ∑ T ∈ whitneySimplexCells (d := d) m
              hn n Q,
            (F T +
              G T) :=
      tsum_simplexPartition_eq_tsum_layer (d := d) (m := m)
        (hn := hn) hmono
        (fun T : KuhnCell d =>
          F T +
            G T)
    _ ≤ _ := ENNReal.tsum_le_tsum hlayer

end

end Algsuperdiff.Section3.Provider.Multiscale
