/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenFlushAssembly

/-!
# StepSevenFlushHgradSlot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 4. The abstract assembly core -/

/-- Pure-algebra core of the flush `hgrad` assembly; every quantity is an
abstract real.  See the module docstring. -/
private theorem flush_assembly_core
    {gl gc v c0 r14 r12 r34 K1 K2 Cosc CG CH sq sqi sqmI aosc oscHi oscData
      XKhol XKh : ℝ}
    (hv0 : 0 ≤ v) (hc00 : 0 ≤ c0) (hr140 : 0 ≤ r14) (hr120 : 0 ≤ r12)
    (hr340 : 0 ≤ r34) (hK10 : 0 ≤ K1) (hK20 : 0 ≤ K2) (hCosc0 : 0 ≤ Cosc)
    (hCG0 : 0 ≤ CG) (hCH0 : 0 ≤ CH) (hsq0 : 0 ≤ sq)
    (hsqmI0 : 0 ≤ sqmI) (hoscHi0 : 0 ≤ oscHi)
    (hoscData0 : 0 ≤ oscData) (hXg0 : 0 ≤ XKhol) (hXh0 : 0 ≤ XKh)
    (h1 : gl ≤ v * gc)
    (h2 : gc ≤ K1 * (3 * (1 + K2) * (sq * aosc) + CG * (sqi * XKhol) +
      CH * (sq * XKh)))
    (h3 : aosc ≤ Cosc * r12 * oscHi + Cosc * r12 * oscData)
    (h4 : v ≤ c0 * r14)
    (h5 : sqi ≤ 2 * r14 * sqmI)
    (h6 : r14 * r12 = r34) (h7 : r14 * r14 = r12)
    (h8 : r12 ≤ r34) (h9 : r14 ≤ r34) :
    gl ≤ c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) * sq * r34 * oscHi +
      c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) * r34 *
        (sq * (oscData + XKh) + sqmI * XKhol) := by
  -- substitute the oscillation bound and the bridge into the bracket
  have hA : 3 * (1 + K2) * (sq * aosc) ≤
      3 * (1 + K2) * (sq * (Cosc * r12 * oscHi + Cosc * r12 * oscData)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hK20])
    exact mul_le_mul_of_nonneg_left h3 hsq0
  have hB : CG * (sqi * XKhol) ≤ CG * (2 * r14 * sqmI * XKhol) := by
    refine mul_le_mul_of_nonneg_left ?_ hCG0
    exact mul_le_mul_of_nonneg_right h5 hXg0
  have h2' : gc ≤ K1 *
      (3 * (1 + K2) * (sq * (Cosc * r12 * oscHi + Cosc * r12 * oscData)) +
        CG * (2 * r14 * sqmI * XKhol) + CH * (sq * XKh)) := by
    refine le_trans h2 (mul_le_mul_of_nonneg_left ?_ hK10)
    linarith only [hA, hB]
  -- the substituted bracket is nonnegative
  have hbr0 : 0 ≤ K1 *
      (3 * (1 + K2) * (sq * (Cosc * r12 * oscHi + Cosc * r12 * oscData)) +
        CG * (2 * r14 * sqmI * XKhol) + CH * (sq * XKh)) := by
    have t0 : (0 : ℝ) ≤ Cosc * r12 * oscHi + Cosc * r12 * oscData := by
      have u1 := mul_nonneg (mul_nonneg hCosc0 hr120) hoscHi0
      have u2 := mul_nonneg (mul_nonneg hCosc0 hr120) hoscData0
      linarith only [u1, u2]
    have t1' : (0 : ℝ) ≤ 3 * (1 + K2) *
        (sq * (Cosc * r12 * oscHi + Cosc * r12 * oscData)) :=
      mul_nonneg (by linarith only [hK20]) (mul_nonneg hsq0 t0)
    have t2 : (0 : ℝ) ≤ CG * (2 * r14 * sqmI * XKhol) :=
      mul_nonneg hCG0 (mul_nonneg (mul_nonneg
        (by linarith only [hr140]) hsqmI0) hXg0)
    have t3 : (0 : ℝ) ≤ CH * (sq * XKh) :=
      mul_nonneg hCH0 (mul_nonneg hsq0 hXh0)
    exact mul_nonneg hK10 (by linarith only [t1', t2, t3])
  -- pass through the volume factor
  have hglA : gl ≤ (c0 * r14) * (K1 *
      (3 * (1 + K2) * (sq * (Cosc * r12 * oscHi + Cosc * r12 * oscData)) +
        CG * (2 * r14 * sqmI * XKhol) + CH * (sq * XKh))) :=
    le_trans h1 (le_trans (mul_le_mul_of_nonneg_left h2' hv0)
      (mul_le_mul_of_nonneg_right h4 hbr0))
  -- ring-expand and regroup on the exponent identities
  have hEq : (c0 * r14) * (K1 *
      (3 * (1 + K2) * (sq * (Cosc * r12 * oscHi + Cosc * r12 * oscData)) +
        CG * (2 * r14 * sqmI * XKhol) + CH * (sq * XKh))) =
      c0 * K1 * (3 * (1 + K2)) * Cosc * (r14 * r12) * (sq * oscHi) +
        c0 * K1 * (3 * (1 + K2)) * Cosc * (r14 * r12) * (sq * oscData) +
        2 * (c0 * K1 * CG) * (r14 * r14) * (sqmI * XKhol) +
        c0 * K1 * CH * r14 * (sq * XKh) := by ring
  rw [h6, h7] at hEq
  rw [hEq] at hglA
  -- the coefficient dominations
  have hc0K1 : (0 : ℝ) ≤ c0 * K1 := mul_nonneg hc00 hK10
  have hrest : (0 : ℝ) ≤ c0 * K1 * (2 * CG + CH) :=
    mul_nonneg hc0K1 (by linarith only [hCG0, hCH0])
  have hrestG : (0 : ℝ) ≤ c0 * K1 * (3 * (1 + K2) * Cosc + CH) := by
    have u1 : (0 : ℝ) ≤ 3 * (1 + K2) * Cosc :=
      mul_nonneg (by linarith only [hK20]) hCosc0
    exact mul_nonneg hc0K1 (by linarith only [u1, hCH0])
  have hrestH : (0 : ℝ) ≤ c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG) := by
    have u1 : (0 : ℝ) ≤ 3 * (1 + K2) * Cosc :=
      mul_nonneg (by linarith only [hK20]) hCosc0
    exact mul_nonneg hc0K1 (by linarith only [u1, hCG0])
  have hco1 : c0 * K1 * (3 * (1 + K2)) * Cosc ≤
      c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) := by
    have hr : c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) =
        c0 * K1 * (3 * (1 + K2)) * Cosc + c0 * K1 * (2 * CG + CH) := by ring
    linarith only [hr, hrest]
  have hco3 : 2 * (c0 * K1 * CG) ≤
      c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) := by
    have hr : c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) =
        2 * (c0 * K1 * CG) + c0 * K1 * (3 * (1 + K2) * Cosc + CH) := by ring
    linarith only [hr, hrestG]
  have hco4 : c0 * K1 * CH ≤
      c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) := by
    have hr : c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) =
        c0 * K1 * CH + c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG) := by ring
    linarith only [hr, hrestH]
  set CF : ℝ := c0 * K1 * (3 * (1 + K2) * Cosc + 2 * CG + CH) with hCFdef
  have hCF0 : 0 ≤ CF := by
    have u1 : (0 : ℝ) ≤ 3 * (1 + K2) * Cosc :=
      mul_nonneg (by linarith only [hK20]) hCosc0
    rw [hCFdef]
    exact mul_nonneg hc0K1 (by linarith only [u1, hCG0, hCH0])
  -- the four monomial bounds
  have b1 : c0 * K1 * (3 * (1 + K2)) * Cosc * r34 * (sq * oscHi) ≤
      CF * r34 * (sq * oscHi) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hsq0 hoscHi0)
    exact mul_le_mul_of_nonneg_right hco1 hr340
  have b2 : c0 * K1 * (3 * (1 + K2)) * Cosc * r34 * (sq * oscData) ≤
      CF * r34 * (sq * oscData) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hsq0 hoscData0)
    exact mul_le_mul_of_nonneg_right hco1 hr340
  have b3 : 2 * (c0 * K1 * CG) * r12 * (sqmI * XKhol) ≤
      CF * r34 * (sqmI * XKhol) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hsqmI0 hXg0)
    calc 2 * (c0 * K1 * CG) * r12 ≤ 2 * (c0 * K1 * CG) * r34 := by
          refine mul_le_mul_of_nonneg_left h8 ?_
          exact mul_nonneg (by norm_num) (mul_nonneg hc0K1 hCG0)
      _ ≤ CF * r34 := mul_le_mul_of_nonneg_right hco3 hr340
  have b4 : c0 * K1 * CH * r14 * (sq * XKh) ≤ CF * r34 * (sq * XKh) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hsq0 hXh0)
    calc c0 * K1 * CH * r14 ≤ c0 * K1 * CH * r34 := by
          refine mul_le_mul_of_nonneg_left h9 ?_
          exact mul_nonneg hc0K1 hCH0
      _ ≤ CF * r34 := mul_le_mul_of_nonneg_right hco4 hr340
  have hT : CF * sq * r34 * oscHi + CF * r34 * (sq * (oscData + XKh) +
      sqmI * XKhol) =
      CF * r34 * (sq * oscHi) + CF * r34 * (sq * oscData) +
        CF * r34 * (sqmI * XKhol) + CF * r34 * (sq * XKh) := by ring
  linarith only [hglA, b1, b2, b3, b4, hT.ge, hT.le]

/-! ## 5. The flush branch's `hgrad` slot -/

/-- **The flush branch, in the Step-7 chain's `hgrad` slot.**

The unit-D window energy (priced through §3), the Step-6 oscillation bound and
the print's volume passage, assembled into the shape
`StepSevenMean.exists_stepSevenEnd_chain_of_lambda_hmeanFree` consumes, at
`shomNp := σ_{n+3}`, `dataOsc := oscData + 3^{m/2}K_h` and `dataM:=
√σ_m^{-1}·3^{m/2}·K_g`. -/
theorem stepSevenFlushHgrad (d : ℕ) {M : ABKModel d}
    {nroot n m : ℤ} {z : Vec d}
    (uglob : H1Function (openCubeSet (originCube d m)))
    {K1 K2 Khol Kh Cosc oscHi oscData C1 alpha delta : ℝ} {B : ℕ}
    (hz : z ∈ openCubeSet (originCube d m)) (hnrootm : nroot ≤ m)
    (hcore : nroot + 1 ≤ n) (hn3m : n + 3 ≤ m)
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hdelta : delta ≤ C1⁻¹ * (1 - alpha)) (hgap : n + 2 - nroot ≤ (B : ℤ) + 6)
    (hbudget : (B : ℝ) ≤ delta * (((m - nroot).toNat : ℝ) + 1))
    (h2gamma : 2 * M.gamma ≤ 1 - alpha)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hKhol : 0 ≤ Khol) (hKh : 0 ≤ Kh)
    (hCosc : 0 ≤ Cosc) (hoscHi : 0 ≤ oscHi) (hoscData : 0 ≤ oscData)
    (hbrG : ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ≤
      rootClauseBTopKs M.gamma m (n + 3) * ((Annealed.sigmaBar M m : ℝ))⁻¹)
    (hDD : stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m n) uglob.grad ≤
      K1 * (3 * (1 + K2) *
          (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
            ((3 : ℝ) ^ (-(n + 3)) *
              normalizedL2On (truncatedWindow z m (n + 3))
                (fun y => uglob.toFun y -
                  volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))) +
        stepSevenFlushCG d K2 *
          (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) +
        stepSevenFlushCH d K2 *
          (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))))
    (hosc : (3 : ℝ) ^ (-(n + 3)) *
        normalizedL2On (truncatedWindow z m (n + 3))
          (fun y => uglob.toFun y -
            volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun) ≤
      Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha nroot m) * oscHi +
        Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha nroot m) *
          oscData) :
    stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (nroot + 1)) uglob.grad ≤
      stepSevenFlushCg d K1 K2 Cosc *
          Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha nroot m) * oscHi +
        stepSevenFlushCg d K1 K2 Cosc *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha nroot m) *
          (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
              (oscData + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) +
            Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
              (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) := by
  have hgamma0 : (0 : ℝ) ≤ M.gamma := (M.shellPrefix.gamma_pos).le
  -- the volume passage
  have hvol := stepSevenNuGradNorm_le_volumeRatio d (n' := n + 2)
    (le_of_lt M.nu_pos) hz hnrootm (by omega) uglob
  rw [show (n + 2 - 2 : ℤ) = n by ring] at hvol
  have hvolB := three_rpow_stepSevenVolume_le d (n' := n + 2) hC1 halpha0 halpha1
    hnrootm hdelta hgap hbudget
  -- the σ bridge with the budget absorption
  have hbridge : Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ≤
      2 * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m) *
        Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ := by
    calc Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹
        ≤ Real.sqrt (rootClauseBTopKs M.gamma m (n + 3) *
            ((Annealed.sigmaBar M m : ℝ))⁻¹) := Real.sqrt_le_sqrt hbrG
      _ = Real.sqrt (rootClauseBTopKs M.gamma m (n + 3)) *
            Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
          Real.sqrt_mul (rootClauseBTopKs_nonneg _ _ _) _
      _ ≤ 2 * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m) *
            Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right
            (sqrt_rootClauseBTopKs_le_budget hgamma0 h2gamma (by omega) hn3m)
            (Real.sqrt_nonneg _)
  -- the exponent identities
  have hE0 : (0 : ℝ) ≤ stepSixExponent alpha nroot m :=
    stepSixExponent_nonneg halpha1 hnrootm
  have h6 : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m) *
      Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha nroot m) =
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha nroot m) := by
    rw [rpow_three_stepSixExponent_mul]
    norm_num
  have h7 : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m) *
      Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m) =
      Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha nroot m) := by
    rw [rpow_three_stepSixExponent_mul]
    norm_num
  have h8 : Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha nroot m) ≤
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha nroot m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hE0])
  have h9 : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m) ≤
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha nroot m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hE0])
  -- the core, instantiated
  have hcoreRes := flush_assembly_core
    (gl := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (nroot + 1))
      uglob.grad)
    (gc := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m n) uglob.grad)
    (v := Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((((n + 2 : ℤ)) : ℝ) - (nroot : ℝ))))
    (c0 := Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4))
    (r14 := Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha nroot m))
    (r12 := Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha nroot m))
    (r34 := Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha nroot m))
    (K1 := K1) (K2 := K2) (Cosc := Cosc)
    (CG := stepSevenFlushCG d K2) (CH := stepSevenFlushCH d K2)
    (sq := Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)))
    (sqi := Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹)
    (sqmI := Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹)
    (aosc := (3 : ℝ) ^ (-(n + 3)) *
      normalizedL2On (truncatedWindow z m (n + 3))
        (fun y => uglob.toFun y -
          volumeAverage (truncatedWindow z m (n + 3)) uglob.toFun))
    (oscHi := oscHi) (oscData := oscData)
    (XKhol := Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)
    (XKh := Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by norm_num) _) hK1 hK2 hCosc
    (stepSevenFlushCG_nonneg d hK2) (stepSevenFlushCH_nonneg d hK2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hoscHi hoscData
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKhol)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh)
    hvol hDD hosc hvolB hbridge h6 h7 h8 h9
  rw [stepSevenFlushCg]
  exact hcoreRes

end

end Algsuperdiff.Section4.Provider.Regularity
