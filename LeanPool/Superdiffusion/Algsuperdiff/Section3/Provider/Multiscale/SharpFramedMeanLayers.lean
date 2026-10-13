/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanCells
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SuperposedConclusion

/-!
# SharpFramedMeanLayers

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Framed potential-only Whitney-layer bounds

The observation-to-cube scale frame from the normalized potential response is
constant across a fixed Whitney layer.  This file keeps that frame outside the
fourth-mass square root when the cellwise estimates are aggregated.

These are internal conditional proof obligations.
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

/-- The observation-to-cube frame on the `n`th Whitney layer. -/
def probeMeanLayerFrame (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (n : ℕ) (i : ℤ) : ℝ :=
  (3 : ℝ) ^
    (-(M.gamma *
      ((i - (m - (n : ℤ) - (hn n : ℤ)) : ℤ) : ℝ)))

/-- The simplex fourth-mass wave factor with the layer frame retained outside
the square root. -/
def probeFramedLayerWaveFactor (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) (n : ℕ) (i L : ℤ) (omega : CutoffSample d) : ℝ :=
  probeMeanLayerFrame M m hn n i *
    (M.gamma * (3 : ℝ) ^ (-(2 * M.gamma *
        ((m - (n : ℤ) - (hn n : ℤ) : ℤ) : ℝ))) *
      Real.sqrt (layerSimplexFourthMass m hn n
        (m - (n : ℤ) - (hn n : ℤ)) L omega))

def probeFramedGoodLayerMeanRhs (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) (n : ℕ) (i L : ℤ) (omega : CutoffSample d)
    (p : Vec d) : ℝ :=
  probeMeanGoodBaseConst d * vecNormSq p *
      (∑ Q ∈ whitneyLayer (d := d) m hn n,
        cubeMassRatio (originCube d m) Q) +
    probeMeanGoodWaveConst M * vecNormSq p *
      Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn n,
        cubeMassRatio (originCube d m) Q) *
      probeFramedLayerWaveFactor M m hn n i L omega

def probeFramedCollarLayerMeanRhs (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) (n : ℕ) (i L : ℤ) (omega : CutoffSample d)
    (p : Vec d) (Cgrad b : ℝ) : ℝ :=
  4 * (Cgrad ^ 2 *
      (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
    (probeMeanGoodBaseConst d * vecNormSq p *
        (∑ Q ∈ collarLayer M m hn n omega,
          cubeMassRatio (originCube d m) Q) +
      probeMeanGoodWaveConst M * vecNormSq p *
        Real.sqrt (∑ Q ∈ collarLayer M m hn n omega,
          cubeMassRatio (originCube d m) Q) *
        probeFramedLayerWaveFactor M m hn n i L omega)

theorem probeMeanLayerFrame_nonneg
    (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) (i : ℤ) :
    0 ≤ probeMeanLayerFrame M m hn n i := by
  rw [probeMeanLayerFrame]
  positivity

theorem probeFramedLayerWaveFactor_nonneg
    (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (i L : ℤ) (omega : CutoffSample d) :
    0 ≤ probeFramedLayerWaveFactor M m hn n i L omega := by
  rw [probeFramedLayerWaveFactor]
  exact mul_nonneg (probeMeanLayerFrame_nonneg M m hn n i)
    (mul_nonneg
      (mul_nonneg M.shellPrefix.gamma_pos.le
        (Real.rpow_nonneg (by norm_num) _))
      (Real.sqrt_nonneg _))

/-- Potential specialization of the framed cell majorant after the geometric
descendant weight is bounded by three. -/
theorem probeFramedMeanCellMajorant_potential_le
    (hd : 2 ≤ d) (M : ABKModel d) (Q : TriadicCube d) (k i L : ℤ)
    (omega : CutoffSample d) (T : KuhnCell d) (p : Vec d)
    (hW : Ch02.multiscaleDescendantWeight Q k (1 / 4) ≤ 3) :
    probeFramedMeanCellMajorant M Q k i L omega T p 0 ≤
      probeMeanGoodBaseConst d * vecNormSq p +
        probeMeanGoodWaveConst M *
          (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
          M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
          matrixOperatorNorm (simplexIncrementValue Q.scale L omega.1 T) ^ 2 *
          vecNormSq p := by
  have hSimp : 0 ≤ simplexCrudeConst d (1 / 4) :=
    simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)
  have hA : 0 ≤ probeSimplexMeanSensitivityConst d :=
    probeSimplexMeanSensitivityConst_nonneg hd
  have hc : 0 ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    inv_nonneg.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
  have hg : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hframe : 0 ≤
      (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow : 0 ≤ (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hinner : 0 ≤
      1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
        probeSimplexMeanSensitivityConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
          (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
          matrixOperatorNorm (simplexIncrementValue Q.scale L omega.1 T) ^ 2 := by
    positivity
  have hcoef : 0 ≤
      640 * simplexCrudeConst d (1 / 4) *
        (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
          probeSimplexMeanSensitivityConst d *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
            (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
            (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
            matrixOperatorNorm
              (simplexIncrementValue Q.scale L omega.1 T) ^ 2) *
        vecNormSq p := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hSimp) hinner)
      (vecNormSq_nonneg p)
  calc
    probeFramedMeanCellMajorant M Q k i L omega T p 0 =
        (640 * simplexCrudeConst d (1 / 4) *
          (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
            probeSimplexMeanSensitivityConst d *
              (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
              (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
              (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
              matrixOperatorNorm
                (simplexIncrementValue Q.scale L omega.1 T) ^ 2) *
          vecNormSq p) * Ch02.multiscaleDescendantWeight Q k (1 / 4) := by
      rw [probeFramedMeanCellMajorant]
      simp only [vecNormSq, vecDot_zero_left, mul_zero, add_zero]
      ring
    _ ≤ (640 * simplexCrudeConst d (1 / 4) *
          (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
            probeSimplexMeanSensitivityConst d *
              (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
              (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
              (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
              matrixOperatorNorm
                (simplexIncrementValue Q.scale L omega.1 T) ^ 2) *
          vecNormSq p) * 3 :=
      mul_le_mul_of_nonneg_left hW hcoef
    _ = probeMeanGoodBaseConst d * vecNormSq p +
        probeMeanGoodWaveConst M *
          (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
          M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
          matrixOperatorNorm (simplexIncrementValue Q.scale L omega.1 T) ^ 2 *
          vecNormSq p := by
      unfold probeMeanGoodBaseConst probeMeanGoodWaveConst
      ring

private theorem probe_framed_sum_ofReal_weight_mul_scaled_affine_sq_le
    {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    (S : Finset (TriadicCube d))
    (hS : S ⊆ whitneyLayer (d := d) m hn n)
    (hstep : hn n ≤ hn (n + 1) + 1)
    (x : KuhnCell d → ℝ) {A B C R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean :
      (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T * x T ^ 2) ≤ R) :
    (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
      ENNReal.ofReal (cellWeight m T * (A * (B + C * x T ^ 2)))) ≤
      ENNReal.ofReal
        (A * (B * (∑ Q ∈ S, cubeMassRatio (originCube d m) Q) + C * R)) := by
  classical
  have hterm : ∀ Q ∈ S, ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
      0 ≤ cellWeight m T * (A * (B + C * x T ^ 2)) := by
    intro Q hQ T hT
    exact mul_nonneg (cellWeight_nonneg m T)
      (mul_nonneg hA (add_nonneg hB (mul_nonneg hC (sq_nonneg _))))
  have hinner : ∀ Q ∈ S,
      0 ≤ ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T * (A * (B + C * x T ^ 2)) := by
    intro Q hQ
    exact Finset.sum_nonneg fun T hT => hterm Q hQ T hT
  have hweight :
      (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T) =
        ∑ Q ∈ S, cubeMassRatio (originCube d m) Q := by
    apply Finset.sum_congr rfl
    intro Q hQ
    exact sum_cellWeight_whitneySimplexCells_eq hstep (hS hQ)
  have hbaseSum :
      (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T * (A * B)) =
        A * (B * (∑ Q ∈ S, cubeMassRatio (originCube d m) Q)) := by
    calc
      _ = ∑ Q ∈ S,
          A * (B * (∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            cellWeight m T)) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = ∑ Q ∈ S, A * (B * cubeMassRatio (originCube d m) Q) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [sum_cellWeight_whitneySimplexCells_eq hstep (hS hQ)]
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have hmeanSum :
      (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T * (A * (C * x T ^ 2))) =
        A * (C * (∑ Q ∈ S,
          ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            cellWeight m T * x T ^ 2)) := by
    calc
      _ = ∑ Q ∈ S,
          A * (C * (∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            cellWeight m T * x T ^ 2)) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have hexpand :
      (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T * (A * (B + C * x T ^ 2))) =
        A * (B * (∑ Q ∈ S, cubeMassRatio (originCube d m) Q) +
          C * (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            cellWeight m T * x T ^ 2)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hbaseSum, hmeanSum]
  calc
    _ = ENNReal.ofReal
        (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
          cellWeight m T * (A * (B + C * x T ^ 2))) := by
      calc
        _ = ∑ Q ∈ S, ENNReal.ofReal
            (∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
              cellWeight m T * (A * (B + C * x T ^ 2))) := by
          apply Finset.sum_congr rfl
          intro Q hQ
          rw [ENNReal.ofReal_sum_of_nonneg (fun T hT => hterm Q hQ T hT)]
        _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun Q hQ => hinner Q hQ)]
    _ = ENNReal.ofReal
        (A * (B * (∑ Q ∈ S, cubeMassRatio (originCube d m) Q) +
          C * (∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            cellWeight m T * x T ^ 2))) := congrArg ENNReal.ofReal hexpand
    _ ≤ ENNReal.ofReal
        (A * (B * (∑ Q ∈ S, cubeMassRatio (originCube d m) Q) + C * R)) := by
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hmean hC)) hA)

/-- Internal conditional aggregation of the framed potential majorant over a
good Whitney layer. -/
theorem probe_sum_ofReal_goodCellForm_layer_le_framedMeanFourth_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (hstep : hn n ≤ hn (n + 1) + 1) (hgap : hn (n + 1) ≤ hn n + 1)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0)
    {L : ℤ} (hmL : m ≤ L) (p : Vec d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (∑ Q ∈ whitneyLayer (d := d) m hn n,
        ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
          ENNReal.ofReal (cellWeight m T * goodCellForm M m hn L omega
            ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
            (0 : Vec d) T)) ≤
        ENNReal.ofReal
          (probeFramedGoodLayerMeanRhs M m hn n i L omega p) := by
  classical
  filter_upwards [probe_goodCellForm_le_framedMeanMajorant_ae hd M hS m hn hmi hi]
    with omega hgood
  let j : ℤ := m - (n : ℤ) - (hn n : ℤ)
  let B : ℝ := probeMeanGoodBaseConst d * vecNormSq p
  let C : ℝ := probeMeanGoodWaveConst M *
    probeMeanLayerFrame M m hn n i * M.gamma *
    (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) * vecNormSq p
  have hB : 0 ≤ B := by
    exact mul_nonneg (probeMeanGoodBaseConst_nonneg hd) (vecNormSq_nonneg p)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M)
            (probeMeanLayerFrame_nonneg M m hn n i))
          M.shellPrefix.gamma_pos.le)
        (Real.rpow_nonneg (by norm_num) _))
      (vecNormSq_nonneg p)
  have hterm : ∀ Q ∈ whitneyLayer (d := d) m hn n,
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
        ENNReal.ofReal (cellWeight m T * goodCellForm M m hn L omega
            ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
            (0 : Vec d) T) ≤
          ENNReal.ofReal (cellWeight m T *
            ((1 : ℝ) * (B + C * matrixOperatorNorm
              (simplexIncrementValue j L omega.1 T) ^ 2))) := by
    intro Q hQ T hT
    have hn1 : 1 ≤ n := (mem_whitneyLayer_iff.mp hQ).1
    have hscale : Q.scale = j := by
      dsimp only [j]
      exact scale_eq_of_mem_whitneyLayer hQ
    have hQL : Q.scale ≤ L := by rw [hscale]; omega
    have hbase := hgood n Q hQ L hQL T hT p 0
    have hmaj := probeFramedMeanCellMajorant_potential_le hd M Q
      (simplexScale m hn n) i L omega T p
      (multiscaleDescendantWeight_le_three_of_mem_whitneyLayer m hn n hgap hQ)
    have hchain := hbase.trans hmaj
    rw [hscale] at hchain
    have hframe_eq : probeMeanLayerFrame M m hn n i =
        (3 : ℝ) ^ (-(M.gamma * ((i - j : ℤ) : ℝ))) := by
      dsimp only [probeMeanLayerFrame, j]
    refine ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ?_ (cellWeight_nonneg m T))
    dsimp only [B, C]
    rw [hframe_eq]
    simp only [smul_zero] at hchain
    convert hchain using 1
    all_goals ring_nf
  have hsum := Finset.sum_le_sum fun Q hQ =>
    Finset.sum_le_sum fun T hT => hterm Q hQ T hT
  have hmean := probeLayerSimplexMeanSq_le_sqrt_mass_mul_sqrt_fourth
    m hn n hstep j L omega
  have hagg := probe_framed_sum_ofReal_weight_mul_scaled_affine_sq_le
    (whitneyLayer (d := d) m hn n) (by exact subset_rfl) hstep
    (fun T => matrixOperatorNorm (simplexIncrementValue j L omega.1 T))
    (A := 1) (B := B) (C := C)
    (R := Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn n,
      cubeMassRatio (originCube d m) Q) *
      Real.sqrt (layerSimplexFourthMass m hn n j L omega))
    (by norm_num) hB hC hmean
  refine hsum.trans ?_
  dsimp only [probeFramedGoodLayerMeanRhs, probeFramedLayerWaveFactor,
    probeMeanLayerFrame, B, C, j] at hagg ⊢
  convert hagg using 2
  all_goals first | rfl | ring

/-- Internal conditional aggregation of the framed potential majorant over a
collar Whitney layer. -/
theorem probe_sum_ofReal_collarCellForm_layer_le_framedMeanFourth_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (hstep : hn n ≤ hn (n + 1) + 1) (hgap : hn (n + 1) ≤ hn n + 1)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) {L : ℤ} (hmL : m ≤ L)
    {b Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad) (hb : 0 ≤ b) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (Fv Gv : KuhnCell d → Vec d) (p : Vec d),
        (∀ Q ∈ whitneyLayer (d := d) m hn n,
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
            vecNormSq (Fv T - p) ≤ Cgrad ^ 2 *
              (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq p) →
        (∀ Q ∈ whitneyLayer (d := d) m hn n,
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
            vecNormSq (Gv T) ≤ 0) →
        (∑ Q ∈ collarLayer M m hn n omega,
          ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ENNReal.ofReal (cellWeight m T * collarCellForm M m hn L omega
              (fun U => (Real.sqrt
                ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
              (fun U => Real.sqrt
                ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U) T)) ≤
          ENNReal.ofReal
            (probeFramedCollarLayerMeanRhs M m hn n i L omega p Cgrad b) := by
  classical
  filter_upwards [probe_collarCellForm_le_framedMeanMajorant_ae
    hd M hS m hn hmi hi hCgrad hb] with omega hcol
  intro Fv Gv p hFv hGv
  let j : ℤ := m - (n : ℤ) - (hn n : ℤ)
  let A : ℝ := 4 * (Cgrad ^ 2 *
    (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))))
  let B : ℝ := probeMeanGoodBaseConst d * vecNormSq p
  let C : ℝ := probeMeanGoodWaveConst M *
    probeMeanLayerFrame M m hn n i * M.gamma *
    (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) * vecNormSq p
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by
    exact mul_nonneg (probeMeanGoodBaseConst_nonneg hd) (vecNormSq_nonneg p)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M)
            (probeMeanLayerFrame_nonneg M m hn n i))
          M.shellPrefix.gamma_pos.le)
        (Real.rpow_nonneg (by norm_num) _))
      (vecNormSq_nonneg p)
  have hterm : ∀ Q ∈ collarLayer M m hn n omega,
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
        ENNReal.ofReal (cellWeight m T * collarCellForm M m hn L omega
            (fun U => (Real.sqrt
              ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
            (fun U => Real.sqrt
              ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U) T) ≤
          ENNReal.ofReal (cellWeight m T *
            (A * (B + C * matrixOperatorNorm
              (simplexIncrementValue j L omega.1 T) ^ 2))) := by
    intro Q hQ T hT
    have hQ' := collarLayer_subset M m hn n omega hQ
    have hn1 : 1 ≤ n := (mem_whitneyLayer_iff.mp hQ').1
    have hscale : Q.scale = j := by
      dsimp only [j]
      exact scale_eq_of_mem_whitneyLayer hQ'
    have hQL : Q.scale ≤ L := by rw [hscale]; omega
    have hGzero : vecNormSq (Gv T - (0 : Vec d)) ≤ Cgrad ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) *
          vecNormSq (0 : Vec d) := by
      simpa [vecNormSq, vecDot] using hGv Q hQ' T hT
    have h1 := hcol n Q hQ' L hQL T hT Fv Gv p 0
      (hFv Q hQ' T hT) hGzero
    have h2 := probeFramedMeanCellMajorant_potential_le hd M Q
      (simplexScale m hn n) i L omega T p
      (multiscaleDescendantWeight_le_three_of_mem_whitneyLayer m hn n hgap hQ')
    rw [hscale] at h2
    have hchain := h1.trans (mul_le_mul_of_nonneg_left h2 hA)
    have hframe_eq : probeMeanLayerFrame M m hn n i =
        (3 : ℝ) ^ (-(M.gamma * ((i - j : ℤ) : ℝ))) := by
      dsimp only [probeMeanLayerFrame, j]
    refine ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ?_ (cellWeight_nonneg m T))
    dsimp only [A, B, C]
    rw [hframe_eq]
    convert hchain using 1
    all_goals ring_nf
  have hsum := Finset.sum_le_sum fun Q hQ =>
    Finset.sum_le_sum fun T hT => hterm Q hQ T hT
  have hmean := probe_sum_collarLayer_meanSq_le_sqrt_mass_mul_sqrt_fourth
    M m hn n hstep j L omega
  have hagg := probe_framed_sum_ofReal_weight_mul_scaled_affine_sq_le
    (collarLayer M m hn n omega) (collarLayer_subset M m hn n omega) hstep
    (fun T => matrixOperatorNorm (simplexIncrementValue j L omega.1 T))
    (A := A) (B := B) (C := C)
    (R := Real.sqrt (∑ Q ∈ collarLayer M m hn n omega,
      cubeMassRatio (originCube d m) Q) *
      Real.sqrt (layerSimplexFourthMass m hn n j L omega))
    hA hB hC hmean
  refine hsum.trans ?_
  dsimp only [probeFramedCollarLayerMeanRhs, probeFramedLayerWaveFactor,
    probeMeanLayerFrame, A, B, C, j] at hagg ⊢
  convert hagg using 2
  all_goals first | rfl | ring

end

end Algsuperdiff.Section3.Provider.Multiscale
