/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedSimplexMean

/-!
# SharpFramedMeanCells

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Cellwise carriers for the framed simplex-mean majorant

This file transports `probeFramedMeanCellMajorant` through the Whitney
good-cell and collar carriers.  Every result below is an internal conditional
proof obligation.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

private theorem probe_framed_ae_imp_of_imp_ae
    {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {P : Prop} {R : alpha → Prop}
    (h : P → ∀ᵐ a ∂mu, R a) : ∀ᵐ a ∂mu, P → R a := by
  by_cases hP : P
  · filter_upwards [h hP] with a ha
    exact fun _ => ha
  · exact Filter.Eventually.of_forall fun _ hPa => absurd hPa hP

private theorem probe_framed_ae_forall_cube_two_scales
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {R : alpha → TriadicCube d → ℤ → ℤ → Prop}
    (h : ∀ (Q : TriadicCube d) (k i : ℤ), ∀ᵐ a ∂mu, R a Q k i) :
    ∀ᵐ a ∂mu, ∀ (Q : TriadicCube d) (k i : ℤ), R a Q k i :=
  ae_all_iff.2 fun Q => ae_all_iff.2 fun k => ae_all_iff.2 fun i => h Q k i

/-- Internal conditional A for uniformizing the framed simplex-domain bound over
all cubes and two running scales. -/
theorem probe_blockVecDot_simplexDomain_le_framedMeanMajorant_ae_uniform
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (Q : TriadicCube d) (k i : ℤ), Q.scale ≤ i → i ≤ m₀ →
        omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
          ∀ T : KuhnCell d, T.supportCube ∈ descendantsAtScale Q k →
            ∀ p q : Vec d,
              blockVecDot
                  ((Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                    Real.sqrt
                      ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
                  (blockMatVecMul
                    (Ch02.coarseBlockMatrix (simplexDomain T)
                      (simplexCoeffOn
                        (coefficientCutoffTriadicCoeffFamily M L omega) T))
                    ((Real.sqrt
                      ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                      Real.sqrt
                        ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)) ≤
                probeFramedMeanCellMajorant M Q k i L omega T p q :=
  probe_framed_ae_forall_cube_two_scales fun Q k _ =>
    probe_framed_ae_imp_of_imp_ae fun hji =>
      probe_framed_ae_imp_of_imp_ae fun hi =>
      probe_blockVecDot_coarseBlockMatrix_simplexDomain_le_framedMeanMajorant_ae
        hd M hS Q (hji.trans hi) k hji hi

/-- Internal conditional A for applying the framed cell majorant to Whitney simplex
cells. -/
theorem probe_blockVecDot_whitneySimplexCells_le_framedMeanMajorant_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (m : ℤ) (hn : ℕ → ℕ) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m₀) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        omega ∉ BadEvents.bad M Q → ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ∀ p q : Vec d,
            blockVecDot
                ((Real.sqrt
                  ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                  Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (simplexDomain T)
                    (simplexCoeffOn
                      (coefficientCutoffTriadicCoeffFamily M L omega) T))
                  ((Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                    Real.sqrt
                      ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)) ≤
              probeFramedMeanCellMajorant M Q
                (simplexScale m hn n) i L omega T p q := by
  filter_upwards
    [probe_blockVecDot_simplexDomain_le_framedMeanMajorant_ae_uniform hd M hS]
    with omega huniform n Q hQ hbad L hL T hT p q
  have hn1 : 1 ≤ n := (mem_whitneyLayer_iff.mp hQ).1
  have hscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) :=
    scale_eq_of_mem_whitneyLayer hQ
  have hQi : Q.scale ≤ i := by omega
  have hosc : omega ∉ badOsc M Q := fun h => hbad (Set.mem_union_left _ h)
  have hloc : omega ∉ badLoc M Q := fun h => hbad (Set.mem_union_right _ h)
  exact huniform Q (simplexScale m hn n) i hQi hi hosc hloc L hL T
    (mem_whitneySimplexCells_iff.mp hT) p q

/-- Internal conditional A for the framed majorant on `goodCellForm`. -/
theorem probe_goodCellForm_le_framedMeanMajorant_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (m : ℤ) (hn : ℕ → ℕ) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m₀) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ∀ p q : Vec d,
            goodCellForm M m hn L omega
                ((Real.sqrt
                  ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
                (Real.sqrt
                  ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) T ≤
              probeFramedMeanCellMajorant M Q
                (simplexScale m hn n) i L omega T p q := by
  classical
  filter_upwards
    [probe_blockVecDot_whitneySimplexCells_le_framedMeanMajorant_ae
      hd M hS m hn hmi hi]
    with omega hgood n Q hQ L hL T hT p q
  have hcube : whitneyCubeOf m hn T = Q :=
    whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
  by_cases hbad : Q ∈ badFamily M m hn omega
  · have hzero : notBadIndicator M m hn omega T = 0 :=
      notBadIndicator_of_bad (by rw [hcube]; exact hbad)
    rw [goodCellForm, hzero, mul_zero]
    exact probeFramedMeanCellMajorant_nonneg
      hd M Q (simplexScale m hn n) i L omega T p q
  · have hnb : omega ∉ BadEvents.bad M Q :=
      fun h => hbad ⟨⟨n, hQ⟩, h⟩
    have hone : notBadIndicator M m hn omega T = 1 :=
      notBadIndicator_of_not_bad (by rw [hcube]; exact hbad)
    rw [goodCellForm, hone, mul_one, coarseBlockMatrix_cellCutoffCoeffOn]
    exact hgood n Q hQ hnb L hL T hT p q

/-- Internal conditional A for the framed majorant on the collar simplex quadratic
form. -/
theorem probe_blockVecDot_collar_simplexDomain_le_framedMeanMajorant_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (m : ℤ) (hn : ℕ → ℕ) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m₀)
    {b Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad) (hb : 0 ≤ b) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        omega ∉ BadEvents.bad M Q → ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ∀ p q Fv Gv : Vec d,
              vecNormSq (Fv - p) ≤ Cgrad ^ 2 *
                  (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq p →
              vecNormSq (Gv - q) ≤ Cgrad ^ 2 *
                  (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq q →
              blockVecDot
                  ((Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv,
                    Real.sqrt
                      ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv)
                  (blockMatVecMul
                    (Ch02.coarseBlockMatrix (simplexDomain T)
                      (simplexCoeffOn
                        (coefficientCutoffTriadicCoeffFamily M L omega) T))
                    ((Real.sqrt
                      ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv,
                      Real.sqrt
                        ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv)) ≤
                4 * (Cgrad ^ 2 *
                    (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
                  probeFramedMeanCellMajorant M Q
                    (simplexScale m hn n) i L omega T p q := by
  filter_upwards
    [probe_blockVecDot_simplexDomain_le_framedMeanMajorant_ae_uniform hd M hS]
    with omega huniform n Q hQ hgood L hL T hT p q Fv Gv hFv hGv
  have hn1 : 1 ≤ n := (mem_whitneyLayer_iff.mp hQ).1
  have hscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) :=
    scale_eq_of_mem_whitneyLayer hQ
  have hQi : Q.scale ≤ i := by omega
  have hosc : omega ∉ badOsc M Q := fun h => hgood (Set.mem_union_left _ h)
  have hloc : omega ∉ badLoc M Q := fun h => hgood (Set.mem_union_right _ h)
  have hform := huniform Q (simplexScale m hn n) i hQi hi hosc hloc L hL T
    (mem_whitneySimplexCells_iff.mp hT) Fv Gv
  let Kp : ℝ :=
    640 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
        probeSimplexMeanSensitivityConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
          (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
          matrixOperatorNorm
            (simplexIncrementValue Q.scale L omega.1 T) ^ 2)
  let Kq : ℝ :=
    320 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ)))
  have hKp : 0 ≤ Kp := by
    dsimp only [Kp]
    have hSnn : 0 ≤ simplexCrudeConst d (1 / 4) :=
      simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)
    have hW :=
      multiscaleDescendantWeight_nonneg Q (simplexScale m hn n) (1 / 4)
    have hA := probeSimplexMeanSensitivityConst_nonneg hd
    have hc := inv_nonneg.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
    have hg := M.shellPrefix.gamma_pos.le
    positivity
  have hKq : 0 ≤ Kq := by
    dsimp only [Kq]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
        (multiscaleDescendantWeight_nonneg Q (simplexScale m hn n) (1 / 4)))
      (Real.rpow_nonneg (by norm_num) _)
  have ht : (1 : ℝ) ≤
      (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) := by
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hform' :
      blockVecDot
          ((Real.sqrt
            ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv,
            Real.sqrt
              ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (simplexDomain T)
              (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T))
            ((Real.sqrt
              ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv,
              Real.sqrt
                ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv)) ≤
        Kp * vecNormSq Fv + Kq * vecNormSq Gv := by
    simpa [Kp, Kq, probeFramedMeanCellMajorant] using hform
  have htrade := quadratic_form_le_of_slope_bounds hform' hKp hKq
    (vecNormSq_le_four_mul_of_slope_error hCgrad ht hFv)
    (vecNormSq_le_four_mul_of_slope_error hCgrad ht hGv)
  simpa [Kp, Kq, probeFramedMeanCellMajorant] using htrade

/-- Internal conditional A for the framed majorant on `collarCellForm`. -/
theorem probe_collarCellForm_le_framedMeanMajorant_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (m : ℤ) (hn : ℕ → ℕ) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m₀)
    {b Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad) (hb : 0 ≤ b) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ∀ Fv Gv : KuhnCell d → Vec d, ∀ p q : Vec d,
              vecNormSq (Fv T - p) ≤ Cgrad ^ 2 *
                  (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq p →
              vecNormSq (Gv T - q) ≤ Cgrad ^ 2 *
                  (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq q →
              collarCellForm M m hn L omega
                  (fun U => (Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
                  (fun U => Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U) T ≤
                4 * (Cgrad ^ 2 *
                    (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
                  probeFramedMeanCellMajorant M Q
                    (simplexScale m hn n) i L omega T p q := by
  classical
  filter_upwards
    [probe_blockVecDot_collar_simplexDomain_le_framedMeanMajorant_ae
      hd M hS m hn hmi hi hCgrad hb]
    with omega hraw n Q hQ L hL T hT Fv Gv p q hFv hGv
  have hcube : whitneyCubeOf m hn T = Q :=
    whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
  have hRhs : 0 ≤ 4 * (Cgrad ^ 2 *
      (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
        probeFramedMeanCellMajorant M Q
          (simplexScale m hn n) i L omega T p q :=
    mul_nonneg (by positivity)
      (probeFramedMeanCellMajorant_nonneg
        hd M Q (simplexScale m hn n) i L omega T p q)
  by_cases hbad : Q ∈ badFamily M m hn omega
  · rw [collarCellForm,
      notBadIndicator_of_bad (by rw [hcube]; exact hbad), mul_zero, zero_mul]
    exact hRhs
  · by_cases hcol : Q ∈ whitneyNeighborhood m hn (badFamily M m hn omega)
    · have hgood : omega ∉ BadEvents.bad M Q :=
        fun h => hbad ⟨⟨n, hQ⟩, h⟩
      rw [collarCellForm,
        notBadIndicator_of_not_bad (by rw [hcube]; exact hbad),
        collarIndicator_of_mem (by rw [hcube]; exact hcol),
        mul_one, mul_one, coarseBlockMatrix_cellCutoffCoeffOn]
      exact hraw n Q hQ hgood L hL T hT p q (Fv T) (Gv T) hFv hGv
    · rw [collarCellForm,
        collarIndicator_of_notMem (by rw [hcube]; exact hcol), mul_zero]
      exact hRhs

end

end Algsuperdiff.Section3.Provider.Multiscale
