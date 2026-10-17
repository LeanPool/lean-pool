/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedActualPotential
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayerEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpPotentialNorm

/-!
# SharpFramedPotentialRoot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Framed sharp potential estimate at an origin cube

This file combines the framed coordinatewise potential estimate with the
finite-coordinate pure-potential reduction.  Its theorem is an internal
conditional proof obligation; the displayed bad-event inequalities remain
caller-supplied A inputs.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Affine
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The normalized cutoff upper block at an origin cube, bounded almost surely
by the sharp layer envelope with its observation-to-cube frame retained. -/
theorem probe_ofReal_cutoffBBlockFamily_inv_le_sum_tsum_sharpFramedMeanLayerEnvelope_ae
    (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (m : ℤ) {sigma b : ℝ}
    (hd : 2 ≤ d) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ (E : ℝ))
    (hE4 : 4 ≤ (E : ℝ))
    (hunit : BadEvents.unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ (E : ℝ))
    (hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {i : ℤ}
    (hmi : m - 1 ≤ i) (hi : i ≤ m₀)
    {L : ℤ} (hmL : m ≤ L) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (CoarseEllipticity.cutoffBBlockFamily M L
            (Annealed.sigmaBar M i : ℝ)⁻¹ (originCube d m) omega) ≤
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M m (E : ℝ) b k₀ n i L omega
            (basisVec j) (superposedGradConst d)) := by
  classical
  let sig : ℝ := (Annealed.sigmaBar M i : ℝ)
  have hsig : 0 < sig :=
    (Annealed.sigmaBar_characterization M i).1
  have hm_local : m - 1 ≤ m₀ := hmi.trans hi
  have hSlocal : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E :=
    ⟨fun j hj => hS.1 j (hj.trans hm_local),
      fun j hj => hS.2 j (hj.trans hm_local)⟩
  have hsepReal : (cutoffSampleLaw M).toMeasure.real
      {omega : CutoffSample d |
        ¬ (hsepSet M m (E : ℝ) b omega).Nonempty} = 0 := by
    simpa using
      (measureReal_hsepSet_not_nonempty_of_gates M hd E.property hSlocal
        hsigma0 hsigma hb0 hb hEexp hE4 hunit hgamma20 hinvSq hEb hgamma)
  have hsepAe : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (hsepSet M m (E : ℝ) b omega).Nonempty := by
    rw [ae_iff]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hsepReal
  have hcoord : ∀ j : Fin d, ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          |blockVecDot
            ((Real.sqrt sig)⁻¹ • basisVec j, (0 : Vec d))
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
                ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                  (originCube d m)))
              ((Real.sqrt sig)⁻¹ • basisVec j, (0 : Vec d)))| ≤
        ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M m (E : ℝ) b k₀ n i L omega
            (basisVec j) (superposedGradConst d)) := by
    intro j
    filter_upwards
        [probe_ofReal_abs_potentialCoordinate_le_tsum_framedMeanLayers_ae
          hd M hS m hb0 hb hk₀ hmi hi hmL (basisVec j), hsepAe]
      with omega hraw hne
    refine (hraw hne).trans (ENNReal.tsum_le_tsum fun n => ?_)
    exact ENNReal.ofReal_le_ofReal
      (probe_framedGood_add_collar_layer_rhs_le_sharpEnvelope
        M hd hb0 hb (by omega) i hmL n omega hne (basisVec j)
          (superposedGradConst d))
  filter_upwards [ae_all_iff.2 hcoord] with omega hall
  have hreal := probe_cutoffBBlockFamily_inv_le_sum_abs_purePotential
    M L hsig (originCube d m) omega
  calc
    ENNReal.ofReal
        (cutoffBBlockFamily M L sig⁻¹ (originCube d m) omega)
        ≤ ENNReal.ofReal
            (∑ j : Fin d,
              |blockVecDot (((Real.sqrt sig)⁻¹ • basisVec j, 0) : BlockVec d)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
                    ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                      (originCube d m)))
                  ((Real.sqrt sig)⁻¹ • basisVec j, 0))|) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = ∑ j : Fin d, ENNReal.ofReal
          |blockVecDot (((Real.sqrt sig)⁻¹ • basisVec j, 0) : BlockVec d)
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
                ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                  (originCube d m)))
              ((Real.sqrt sig)⁻¹ • basisVec j, 0))| := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro j _
        exact abs_nonneg _
    _ ≤ ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M m (E : ℝ) b k₀ n i L omega
            (basisVec j) (superposedGradConst d)) :=
      Finset.sum_le_sum fun j _ => hall j

end

end Algsuperdiff.Section3.Provider.Multiscale
