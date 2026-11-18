/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.QuadraticCocycleSubgroup

public import LeanPool.ApollonianSuperharmonic.FordExceptionalLattice
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordPeakMatrix

-- [TABLET NODE: P5442T1Cocycle]

/-!
# P5442T1Cocycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5442T1Cocycle (P : FordFareyParameter) :
    ∀ v, v ∈ FordExceptionalLattice P → ∃ a : GaussianInt,
      Matrix.mulVec (FordPeakMatrix P.p P.q P.q_pos P.reduced)
        ![(v.re : Real), (v.im : Real)] =
          ![(a.re : Real), (a.im : Real)] ∧
      ∀ x, FordOdometer P (x + v) = FordOdometer P x +
        x.re * a.re + x.im * a.im + FordOdometer P v := by
-- BODY
  classical
  let g := FordOdometer P
  obtain ⟨_, hbdy, ha, hb, _, _⟩ :=
    (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change ∀ R x, x ∈ FordDoubledBoundary R.q → FordOdometer R x = _ at hbdy
  change ∀ R x, FordOdometer R (x + ⟨0, -(R.q : Int)⟩) = _ at ha
  change ∀ R x, FordOdometer R (x + ⟨(R.q : Int), (R.q₁ : Int)⟩) = _ at hb
  have hzero : g 0 = 0 := by
    have hz : (0 : GaussianInt) ∈ FordDoubledBoundary P.q := by
      simp [FordDoubledBoundary, FordVertexDomain]
    simpa [g, IntegerCeilDiv] using hbdy P 0 hz
  let H := quadraticCocycleSubgroup (FordPeakMatrix P.p P.q P.q_pos P.reduced) g hzero
  have hq : (P.q : Real) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  have hdet : (P.p₁ : Real) * P.q - (P.q₁ : Real) * P.p = 1 := by
    exact_mod_cast P.det₁
  have hgen : {v : GaussianInt | v = ⟨0, -(P.q : Int)⟩ ∨
      v = ⟨(P.q : Int), (P.q₁ : Int)⟩} ⊆ H := by
    intro v hv
    rcases hv with rfl | rfl
    · refine ⟨⟨-P.p, 0⟩, ?_, ?_⟩
      · dsimp [FordPeakMatrix]
        ext i; fin_cases i <;> simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        · push_cast
          change (1 / (P.q : Real)^2) * 1 * 0 +
            (1 / (P.q : Real)^2) * ((P.p : Real) * P.q) * (-(P.q : Real)) = -(P.p : Real)
          field_simp [hq]; ring
        · push_cast
          change (1 / (P.q : Real)^2) * ((P.p : Real) * P.q) * 0 +
            (1 / (P.q : Real)^2) * 0 * (-(P.q : Real)) = 0
          ring
      · intro x
        have h := ha P x
        have h0 := ha P 0
        change g _ = g _ - _ at h h0
        simp only [Zsqrtd.re_zero, zero_add, mul_zero, sub_zero, hzero] at h0
        change g _ = g x + x.re * (-P.p) + x.im * 0 + g _
        rw [h0]
        linarith only [h]
    · refine ⟨⟨P.p₁, P.p⟩, ?_, ?_⟩
      · dsimp [FordPeakMatrix]
        ext i; fin_cases i <;> simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        · push_cast
          change (1 / (P.q : Real)^2) * 1 * (P.q : Real) +
            (1 / (P.q : Real)^2) * ((P.p : Real) * P.q) * (P.q₁ : Real) = (P.p₁ : Real)
          field_simp [hq]
          nlinarith only [hdet]
        · push_cast
          change (1 / (P.q : Real)^2) * ((P.p : Real) * P.q) * (P.q : Real) +
            (1 / (P.q : Real)^2) * 0 * (P.q₁ : Real) = (P.p : Real)
          field_simp [hq]; ring
      · intro x
        have h := hb P x
        have h0 := hb P 0
        change g _ = g _ + _ + _ + _ at h h0
        simp only [Zsqrtd.re_zero, Zsqrtd.im_zero, zero_add,
          mul_zero, add_zero, hzero] at h0
        change g _ = g x + x.re * P.p₁ + x.im * P.p + g _
        rw [h0]
        linarith only [h]
  intro v hv
  exact ((AddSubgroup.closure_le H).mpr hgen) hv

end ApollonianSuperharmonic

end
