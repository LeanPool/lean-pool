/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerRepresentative

/-!
# SuperposedFluxLowerAmplitude

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A uniform depth-amplitude majorant for the sharp lower lane

This file replaces the exact grid-net amplitude of the pointwise
representative by a single dimension-only prefactor times
`(n+1)^4 3^(gamma n) exp(-c E⁻² gamma⁻¹)`.  It is the quantitative input
shared by the finite `q < 2`, finite `2 ≤ q`, and endpoint branches.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Filter MeasureTheory Topology
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- Uniform grid-net constant once the tail exponent is at least `1/4`. -/
def superposedFluxGridNetConst (d : ℕ) : ℝ :=
  (3 * (d : ℝ) * Real.log 3) ^ (4 : ℝ)

theorem superposedFluxGridNetConst_pos (hd : 2 ≤ d) :
    0 < superposedFluxGridNetConst d := by
  unfold superposedFluxGridNetConst
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  exact Real.rpow_pos_of_pos
    (mul_pos (mul_pos (by norm_num) hdR) (lt_trans zero_lt_one one_lt_log_three)) _

private theorem gridNetConst_le_superposedFluxGridNetConst (hd : 2 ≤ d)
    {tau : ℝ} (htau : 1 / 4 ≤ tau) :
    gridNetConst d tau ≤ superposedFluxGridNetConst d := by
  have htau0 : 0 < tau := lt_of_lt_of_le (by norm_num) htau
  have hinv : tau⁻¹ ≤ (4 : ℝ) :=
    (inv_le_iff_one_le_mul₀ htau0).2 (by nlinarith)
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hbase : 1 ≤ 3 * (d : ℝ) * Real.log 3 := by
    have hlog : 1 < Real.log 3 := one_lt_log_three
    nlinarith
  unfold gridNetConst superposedFluxGridNetConst
  exact Real.rpow_le_rpow_of_exponent_le hbase hinv

/-- Dimension-only prefactor of the depth-amplitude majorant. -/
def superposedFluxDepthAmpConst (d : ℕ) : ℝ :=
  superposedFluxGridNetConst d * superposedFluxBfaConst d

theorem superposedFluxDepthAmpConst_pos (hd : 2 ≤ d) :
    0 < superposedFluxDepthAmpConst d :=
  mul_pos (superposedFluxGridNetConst_pos hd) (superposedFluxBfaConst_pos hd)

/-- Uniform depth-amplitude majorant used by all lower exponent branches. -/
def superposedFluxDepthAmpProfile (M : ABKModel d) (E : ℝ) (n : ℕ) : ℝ :=
  superposedFluxDepthAmpConst d * (((n : ℝ) + 1) ^ (4 : ℕ)) *
    (3 : ℝ) ^ (M.gamma * (n : ℝ)) *
    Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))

theorem superposedFluxDepthAmpProfile_pos (hd : 2 ≤ d)
    (M : ABKModel d) (E : ℝ) (n : ℕ) :
    0 < superposedFluxDepthAmpProfile M E n := by
  unfold superposedFluxDepthAmpProfile
  exact mul_pos (mul_pos
    (mul_pos (superposedFluxDepthAmpConst_pos hd) (by positivity))
      (Real.rpow_pos_of_pos (by norm_num) _)) (Real.exp_pos _)

/-- The exact representative amplitude is bounded by the uniform depth
profile.  Every scalar gate is discharged from the frozen max/fifth-root
hypotheses. -/
theorem superposedFluxSharpDepthAmp_le_profile [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ)
    (E : {E : ℝ // 1 ≤ E}) {sigma : ℝ}
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (n : ℕ) :
    superposedFluxSharpDepthAmp M m E sigma n.pred ≤
      superposedFluxDepthAmpProfile M E n := by
  obtain ⟨_, _, _, _, _, _, _, _, hlocalEq, _, htau⟩ :=
    superposedFluxRateCompatible_allParameterGates_of_profileAuxiliaryMaxGate
      hd M E.property hsigma hsigmaHalf hmax hEgamma
  have htail : 1 / 4 ≤ (1 - sigma) / 2 := by linarith
  have htauQuarter : 1 / 4 ≤
      bfaTau (bfaProfileSigma sigma)
        (superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M)) bfaProfileB :=
    htail.trans htau
  have htau0 : 0 < bfaTau (bfaProfileSigma sigma)
      (superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M)) bfaProfileB :=
    lt_of_lt_of_le (by norm_num) htauQuarter
  have hinv : (bfaTau (bfaProfileSigma sigma)
      (superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M)) bfaProfileB)⁻¹ ≤
      (4 : ℝ) := (inv_le_iff_one_le_mul₀ htau0).2 (by nlinarith)
  have hlane := bfaLaneScale_sharp_le_exp_profile hd M m n.pred E.property
    hsigma hsigmaHalf hmax hEgamma
  rw [← hlocalEq] at hlane
  have hlane' : bfaLaneScale (bfaProfileSigma sigma) bfaProfileB
      (superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M))
      (superposedFluxSharpDepthConst M m E n.pred)
      (superposedFluxSharpDepthRare M E) ≤
    superposedFluxBfaConst d * (3 : ℝ) ^ (M.gamma * (n.pred : ℝ)) *
      Real.exp (-(superposedFluxBfaRate d *
        (((E : ℝ))⁻¹ ^ 2 * M.gamma⁻¹))) := by
    simpa [superposedFluxSharpDepthConst, superposedFluxSharpDepthRare] using hlane
  have hlane0 : 0 ≤ bfaLaneScale (bfaProfileSigma sigma) bfaProfileB
      (superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M))
      (superposedFluxSharpDepthConst M m E n.pred)
      (superposedFluxSharpDepthRare M E) :=
    (bfaLaneScale_pos
      (superposedFluxSharpConst_pos hd M _ _ _ _ _ _)
      (superposedFluxSharpRare_pos _ _ _)).le
  have hgrid := gridBlockAmp_le_natPow (d := d) hlane0 4 hinv n.pred
  have hnet := gridNetConst_le_superposedFluxGridNetConst hd htauQuarter
  have hpred : n.pred ≤ n := Nat.pred_le n
  have hpoly : (((n.pred : ℝ) + 1) ^ (4 : ℕ)) ≤
      (((n : ℝ) + 1) ^ (4 : ℕ)) := by
    exact pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hpred) 4
  have hgeom : (3 : ℝ) ^ (M.gamma * (n.pred : ℝ)) ≤
      (3 : ℝ) ^ (M.gamma * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hpred)
        M.shellPrefix.gamma_pos.le)
  unfold superposedFluxSharpDepthAmp superposedFluxDepthAmpProfile
  calc
    gridBlockAmp d
          (bfaTau (bfaProfileSigma sigma)
            (superposedFluxLocalExponent M bfaProfileB
              (superposedFluxRateEps M) (superposedFluxRateBeta M)) bfaProfileB)
          (bfaLaneScale (bfaProfileSigma sigma) bfaProfileB
            (superposedFluxLocalExponent M bfaProfileB
              (superposedFluxRateEps M) (superposedFluxRateBeta M))
            (superposedFluxSharpDepthConst M m E n.pred)
            (superposedFluxSharpDepthRare M E)) n.pred ≤
        gridNetConst d
            (bfaTau (bfaProfileSigma sigma)
              (superposedFluxLocalExponent M bfaProfileB
                (superposedFluxRateEps M) (superposedFluxRateBeta M)) bfaProfileB) *
          (bfaLaneScale (bfaProfileSigma sigma) bfaProfileB
            (superposedFluxLocalExponent M bfaProfileB
              (superposedFluxRateEps M) (superposedFluxRateBeta M))
            (superposedFluxSharpDepthConst M m E n.pred)
            (superposedFluxSharpDepthRare M E)) *
          (((n.pred : ℝ) + 1) ^ (4 : ℕ)) := hgrid
    _ ≤ superposedFluxGridNetConst d *
          (superposedFluxBfaConst d *
            (3 : ℝ) ^ (M.gamma * (n.pred : ℝ)) *
            Real.exp (-(superposedFluxBfaRate d *
              (((E : ℝ))⁻¹ ^ 2 * M.gamma⁻¹)))) *
          (((n.pred : ℝ) + 1) ^ (4 : ℕ)) := by
      have hpair := mul_le_mul hnet hlane' hlane0
        (superposedFluxGridNetConst_pos hd).le
      exact mul_le_mul_of_nonneg_right hpair (by positivity)
    _ ≤ superposedFluxDepthAmpConst d * (((n : ℝ) + 1) ^ (4 : ℕ)) *
          (3 : ℝ) ^ (M.gamma * (n : ℝ)) *
          Real.exp (-(superposedFluxBfaRate d *
            (((E : ℝ))⁻¹ ^ 2 * M.gamma⁻¹))) := by
      unfold superposedFluxDepthAmpConst
      have hnonneg : 0 ≤ superposedFluxGridNetConst d *
          superposedFluxBfaConst d :=
        mul_nonneg (superposedFluxGridNetConst_pos hd).le
          (superposedFluxBfaConst_pos hd).le
      have hPG : (((n.pred : ℝ) + 1) ^ (4 : ℕ)) *
          (3 : ℝ) ^ (M.gamma * (n.pred : ℝ)) ≤
        (((n : ℝ) + 1) ^ (4 : ℕ)) *
          (3 : ℝ) ^ (M.gamma * (n : ℝ)) :=
        mul_le_mul hpoly hgeom (Real.rpow_nonneg (by norm_num) _)
          (by positivity)
      have hC0 : 0 ≤ superposedFluxGridNetConst d *
          superposedFluxBfaConst d *
          Real.exp (-(superposedFluxBfaRate d *
            (((E : ℝ))⁻¹ ^ 2 * M.gamma⁻¹))) :=
        mul_nonneg hnonneg (Real.exp_pos _).le
      calc
        _ = (superposedFluxGridNetConst d * superposedFluxBfaConst d *
              Real.exp (-(superposedFluxBfaRate d *
                (((E : ℝ))⁻¹ ^ 2 * M.gamma⁻¹)))) *
            ((((n.pred : ℝ) + 1) ^ (4 : ℕ)) *
              (3 : ℝ) ^ (M.gamma * (n.pred : ℝ))) := by ring
        _ ≤ (superposedFluxGridNetConst d * superposedFluxBfaConst d *
              Real.exp (-(superposedFluxBfaRate d *
                (((E : ℝ))⁻¹ ^ 2 * M.gamma⁻¹)))) *
            ((((n : ℝ) + 1) ^ (4 : ℕ)) *
              (3 : ℝ) ^ (M.gamma * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hPG hC0
        _ = _ := by ring
    _ = _ := by ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
