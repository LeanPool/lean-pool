/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv

-- [TABLET NODE: P5188T1CeilingStability]

/-!
# P5188T1CeilingStability

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5188T1CeilingStability (N M d q E : Int) (hd : 0 < d) (hdq : d < q)
    (hE0 : 0 ≤ E) (hEd : E ≤ d) (hrel : M * d = N * q - E) :
    IntegerCeilDiv M q (by omega) = IntegerCeilDiv N d (by omega) := by
-- BODY
  let k := N / d
  let r := N % d
  have hdecomp : N = d * k + r := by
    dsimp [k, r]
    have := Int.mul_ediv_add_emod N d
    nlinarith
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrd : r < d := Int.emod_lt_of_pos _ hd
  by_cases hr : r = 0
  · have hMlo : k * q - q < M := by
      have := hrel
      rw [hdecomp, hr] at this
      nlinarith [hdq, hd]
    have hMhi : M ≤ k * q := by
      rw [hdecomp, hr] at hrel
      nlinarith [hEd, hE0]
    have hdivN : (-N) / d = -k := by
      rw [Int.ediv_eq_iff_of_pos hd]
      rw [hdecomp, hr]
      constructor <;> nlinarith
    have hdivM : (-M) / q = -k := by
      rw [Int.ediv_eq_iff_of_pos (by omega)]
      constructor <;> nlinarith [hMlo, hMhi]
    change -((-M) / q) = -((-N) / d)
    rw [hdivM, hdivN]
  · have hrpos : 0 < r := by omega
    have hdivN : (-N) / d = -(k + 1) := by
      rw [Int.ediv_eq_iff_of_pos hd]
      rw [hdecomp]
      constructor <;> nlinarith [hrpos, hrd]
    have hMlo : k * q < M := by
      rw [hdecomp] at hrel
      nlinarith [hdq, hrpos, hEd]
    have hMhi : M < k * q + q := by
      rw [hdecomp] at hrel
      nlinarith [hdq, hrpos, hrd, hEd]
    have hdivM : (-M) / q = -(k + 1) := by
      rw [Int.ediv_eq_iff_of_pos (by omega)]
      constructor <;> nlinarith [hMlo, hMhi]
    change -((-M) / q) = -((-N) / d)
    rw [hdivM, hdivN]

end ApollonianSuperharmonic

end
