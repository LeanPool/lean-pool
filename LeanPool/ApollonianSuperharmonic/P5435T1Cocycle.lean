/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.QuadraticCocycleSubgroup

public import LeanPool.ApollonianSuperharmonic.DiamondExceptionalLattice
public import LeanPool.ApollonianSuperharmonic.DiamondOdometer
public import LeanPool.ApollonianSuperharmonic.DiamondPeakMatrix
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

-- [TABLET NODE: P5435T1Cocycle]

/-!
# P5435T1Cocycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5435T1Cocycle (K : DiamondParameter) :
    ∀ v, v ∈ DiamondExceptionalLattice K → ∃ a : GaussianInt,
      Matrix.mulVec (DiamondPeakMatrix K)
        ![(v.re : Real), (v.im : Real)] =
          ![(a.re : Real), (a.im : Real)] ∧
      ∀ x, DiamondOdometer K (x + v) = DiamondOdometer K x +
        x.re * a.re + x.im * a.im + DiamondOdometer K v := by
-- BODY
  classical
  let g := DiamondOdometer K
  let k : Int := K.1
  have hk : (k : Real) ≠ 0 := by
    have h : 0 < k := by dsimp [k]; exact_mod_cast K.2
    exact_mod_cast ne_of_gt h
  have hk1 : (k : Real) + 1 ≠ 0 := by
    have h : 0 < k := by dsimp [k]; exact_mod_cast K.2
    have h' : (0 : Real) < k := by exact_mod_cast h
    linarith
  obtain ⟨ha, hb, _, hf⟩ := (Classical.choose_spec (DiamondOdometerExistsUnique K)).1
  change (∀ x, g (x + ⟨0, -(2 * K.1 : Int)⟩) = g x +
    (-(K.1 : Int))*x.re + ((K.1 : Int)-1)*x.im -
      (K.1 : Int)*((K.1 : Int)-2)) at ha
  change (∀ x, g (x + ⟨(K.1+1 : Int), (K.1 : Int)⟩) = g x +
    (K.1 : Int)*x.re + x.im + (K.1 : Int)*(K.1+1)/2) at hb
  have hF : ∀ x, x ∈ DiamondVertexDomains K false →
      g x = (Int.natAbs x.re : Int)*((Int.natAbs x.re : Int)-1)/2 -
        (x.re-x.im)^2/4 := hf
  have hzero : g 0 = 0 := by
    have hmem : (0 : GaussianInt) ∈ DiamondVertexDomains K false := by
      change max (Int.natAbs (0 : GaussianInt).re)
        (max (Int.natAbs ((0 : GaussianInt).im - (K.1 : Int)))
          (Int.natAbs (0 : GaussianInt).re +
            Int.natAbs ((0 : GaussianInt).im - (K.1 : Int)) - 1)) ≤ K.1
      norm_num
    have h := hF 0 hmem
    norm_num at h
    exact h
  let H := quadraticCocycleSubgroup (DiamondPeakMatrix K) g hzero
  have hgen : {v : GaussianInt | v = ⟨0, -(2 * K.1 : Int)⟩ ∨
      v = ⟨(K.1 + 1 : Int), (K.1 : Int)⟩} ⊆ H := by
    intro v hv
    rcases hv with rfl | rfl
    · refine ⟨⟨-k, k-1⟩, ?_, ?_⟩
      · dsimp [DiamondPeakMatrix]
        ext i; fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, k]
        all_goals
          try field_simp [show (K.1 : Real) ≠ 0 by simpa [k] using hk,
            show (K.1 : Real)+1 ≠ 0 by simpa [k] using hk1]
          ring
      · intro x
        have h := ha x
        have h0 := ha 0
        simp only [Zsqrtd.re_zero, Zsqrtd.im_zero, zero_add, mul_zero, add_zero,
          hzero] at h0
        change g _ = g x + x.re*(-k) + x.im*(k-1) + g _
        rw [h0]
        change g _ = g x + (-k)*x.re + (k-1)*x.im - k*(k-2) at h
        linarith
    · refine ⟨⟨k, 1⟩, ?_, ?_⟩
      · dsimp [DiamondPeakMatrix]
        ext i; fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, k]
        all_goals
          try field_simp [show (K.1 : Real) ≠ 0 by simpa [k] using hk,
            show (K.1 : Real)+1 ≠ 0 by simpa [k] using hk1]
          ring
      · intro x
        have h := hb x
        have h0 := hb 0
        simp only [Zsqrtd.re_zero, Zsqrtd.im_zero, zero_add, mul_zero, add_zero,
          hzero] at h0
        change g _ = g x + x.re*k + x.im*1 + g _
        rw [h0]
        change g _ = g x + k*x.re + x.im + k*(k+1)/2 at h
        linarith
  intro v hv
  exact ((AddSubgroup.closure_le H).mpr hgen) hv

end ApollonianSuperharmonic

end
