/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.GridCellCenter
public import LeanPool.ApollonianSuperharmonic.GridSegmentLogLiftDelta
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# GridVerticalUpLogLiftDelta

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: GridVerticalUpLogLiftDelta]
theorem GridVerticalUpLogLiftDelta (q a : GaussianInt)
    (L : Set.Icc (0 : Real) 1 → ℂ) (hL : Continuous L)
    (hexp : ∀ t, Complex.exp (L t) =
      (1 - (t : Real)) * ((a : ℂ) - GridCellCenter q) +
        (t : Real) * ((a + ⟨0, 1⟩ : GaussianInt) - GridCellCenter q)) :
    L ⟨1, by norm_num⟩ - L ⟨0, by norm_num⟩ =
      Complex.log ((a + ⟨0, 1⟩ : GaussianInt) - GridCellCenter q) -
        Complex.log ((a : ℂ) - GridCellCenter q) -
        (if a.im = q.im ∧ a.re ≤ q.re then 2 * Real.pi * Complex.I else 0) := by
-- BODY
  have neg_log_delta_up (z0 z1 : ℂ)
      (hre0 : z0.re < 0) (him0 : z0.im < 0)
      (hre1 : z1.re < 0) (him1 : 0 < z1.im)
      (hnorm : ‖z1‖ = ‖z0‖) :
      Complex.log (-z1) - Complex.log (-z0) =
        Complex.log z1 - Complex.log z0 - 2 * Real.pi * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re, hnorm]
    · simp only [Complex.log_im, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
        mul_one, mul_zero]
      rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him1,
        Complex.arg_neg_eq_arg_add_pi_of_im_neg him0]
      norm_num
      ring
  by_cases hcross : a.im = q.im ∧ a.re ≤ q.re
  · rw [ite_eq_left hcross]
    let z0 := (a : ℂ) - GridCellCenter q
    let z1 := (a + ⟨0, 1⟩ : GaussianInt) - GridCellCenter q
    let M : Set.Icc (0 : Real) 1 → ℂ := fun t ↦ L t - Real.pi * Complex.I
    have hM : Continuous M := hL.sub continuous_const
    have hMexp : ∀ t, Complex.exp (M t) =
        (1 - (t : Real)) * (-z0) + (t : Real) * (-z1) := by
      intro t
      rw [show M t = L t - Real.pi * Complex.I by rfl,
        Complex.exp_sub_pi_mul_I, hexp]
      dsimp [z0, z1]
      ring
    have hslit : ∀ t : Set.Icc (0 : Real) 1,
        (1 - (t : Real)) * (-z0) + (t : Real) * (-z1) ∈ Complex.slitPlane := by
      intro t
      rw [Complex.mem_slitPlane_iff]
      left
      dsimp [z0, z1, GridCellCenter]
      simp only [Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im,
        ]
      norm_num
      have ha : ((a.re : Int) : Real) ≤ (q.re : Int) := by
        exact_mod_cast hcross.2
      have haC : (a : ℂ).re ≤ (q : ℂ).re := by simpa using ha
      have ht0 : 0 ≤ (t : Real) := t.2.1
      have ht1 : (t : Real) ≤ 1 := t.2.2
      linarith
    have hd := GridSegmentLogLiftDelta (-z0) (-z1) hslit M hM hMexp
    have hre0 : z0.re < 0 := by
      dsimp [z0, GridCellCenter]
      simp
      have ha : ((a.re : Int) : Real) ≤ (q.re : Int) := by
        exact_mod_cast hcross.2
      have haC : (a : ℂ).re ≤ (q : ℂ).re := by simpa using ha
      linarith
    have him0 : z0.im < 0 := by
      dsimp [z0, GridCellCenter]
      have hi : ((a.im : Int) : Real) = (q.im : Int) := by
        exact_mod_cast hcross.1
      have hiC : (a : ℂ).im = (q : ℂ).im := by simpa using hi
      rw [hiC]
      norm_num
    have hre1 : z1.re < 0 := by
      dsimp [z1, GridCellCenter]
      simp
      have ha : ((a.re : Int) : Real) ≤ (q.re : Int) := by
        exact_mod_cast hcross.2
      have haC : (a : ℂ).re ≤ (q : ℂ).re := by simpa using ha
      linarith
    have him1 : 0 < z1.im := by
      dsimp [z1, GridCellCenter]
      have hi : ((a.im : Int) : Real) = (q.im : Int) := by
        exact_mod_cast hcross.1
      have hiC : (a : ℂ).im = (q : ℂ).im := by simpa using hi
      norm_num
      rw [hiC]
      norm_num
    have hnorm : ‖z1‖ = ‖z0‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
      rw [Complex.sq_norm, Complex.sq_norm]
      dsimp [z0, z1, GridCellCenter]
      simp? [Complex.normSq_apply]
      have hi : ((a.im : Int) : Real) = (q.im : Int) := by
        exact_mod_cast hcross.1
      have hiC : (a : ℂ).im = (q : ℂ).im := by simpa using hi
      rw [hiC]
      ring
    rw [show M ⟨1, by norm_num⟩ - M ⟨0, by norm_num⟩ =
        L ⟨1, by norm_num⟩ - L ⟨0, by norm_num⟩ by simp [M]] at hd
    rw [neg_log_delta_up z0 z1 hre0 him0 hre1 him1 hnorm] at hd
    simpa [z0, z1] using hd
  · rw [ite_eq_right hcross, sub_zero]
    apply GridSegmentLogLiftDelta _ _ _ L hL hexp
    intro t
    rw [Complex.mem_slitPlane_iff]
    by_cases hre : 0 <
        ((1 - (t : Real)) * ((a : ℂ) - GridCellCenter q) +
          (t : Real) * ((a + ⟨0, 1⟩ : GaussianInt) - GridCellCenter q)).re
    · exact Or.inl hre
    · right
      intro him
      apply hcross
      constructor
      · dsimp [GridCellCenter] at him
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero,
          add_zero, Complex.sub_im] at him
        norm_num at him
        rw [← GaussianInt.intCast_im, ← GaussianInt.intCast_im] at him
        have hloR : (-1 : Real) < ((a.im : Int) : Real) - (q.im : Int) := by
          linarith [t.2.1, t.2.2]
        have hhiR : ((a.im : Int) : Real) - (q.im : Int) < 1 := by
          linarith [t.2.1, t.2.2]
        have hlo : (-1 : Int) < a.im - q.im := by exact_mod_cast hloR
        have hhi : a.im - q.im < (1 : Int) := by exact_mod_cast hhiR
        omega
      · dsimp [GridCellCenter] at hre
        simp only [Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im,
          ] at hre
        norm_num at hre
        rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_re] at hre
        have hltR : ((a.re : Int) : Real) - (q.re : Int) < 1 := by linarith
        have hlt : a.re - q.re < (1 : Int) := by exact_mod_cast hltR
        omega

end

end ApollonianSuperharmonic

end
