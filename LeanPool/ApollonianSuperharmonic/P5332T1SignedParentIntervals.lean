/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


-- [TABLET NODE: P5332T1SignedParentIntervals]

/-!
# P5332T1SignedParentIntervals

Adapted from Wesley Pegden’s Apache - 2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1SignedParentIntervals (A p d q v σ : Int)
    (hd : 0 < d) (hdq : d < q) (hv : 0 < v) (hvd : v < d)
    (hσ : σ = 1 ∨ σ = -1) (hdet : A * q - p * d = σ) :
    let K := A * v / d;
    -((-(A * v)) / d) = K + 1 ∧
    p * v / q = K ∧ -((-(p * v)) / q) = K + 1 ∧
    (p * v + σ) / q = K ∧ -((-(p * v + σ)) / q) = K + 1 := by
-- BODY
  dsimp only
  let K := A * v / d
  let R := A * v % d
  have hq : 0 < q := lt_trans hd hdq
  have hR0 : 0 ≤ R := Int.emod_nonneg _ (by omega)
  have hRd : R < d := Int.emod_lt_of_pos _ hd
  have heq : A * v = K * d + R := by
    dsimp [K, R]
    have := Int.emod_add_mul_ediv (A * v) d
    nlinarith
  have hRn : R ≠ 0 := by
    intro hz
    have hdiv : d ∣ σ * v := by
      refine ⟨K * q - p * v, ?_⟩
      have hm := congrArg (fun z : Int => z * v) hdet
      rw [hz] at heq
      nlinarith [hm]
    have hdv : d ∣ v := by
      rcases hσ with rfl | rfl
      · simpa using hdiv
      · simpa using hdiv
    have := Int.le_of_dvd hv hdv
    omega
  have hRp : 0 < R := by omega
  have lower : K * q < p * v := by
    have hh := congrArg (fun z : Int => z * v) hdet
    rcases hσ with hs | hs <;> rw [hs] at hh <;> nlinarith
  have upper : p * v < K * q + q := by
    have hh := congrArg (fun z : Int => z * v) hdet
    rcases hσ with hs | hs <;> rw [hs] at hh <;> nlinarith
  have lower' : K * q < p * v + σ := by
    have hh := congrArg (fun z : Int => z * v) hdet
    rcases hσ with hs | hs <;> rw [hs] at hh ⊢ <;> nlinarith
  have upper' : p * v + σ < K * q + q := by
    have hh := congrArg (fun z : Int => z * v) hdet
    rcases hσ with hs | hs <;> rw [hs] at hh ⊢ <;> nlinarith
  have ceil (N D : Int) (hD : 0 < D) (hlo : K * D < N) (hhi : N < K * D + D) :
      -((-N) / D) = K + 1 := by
    have hh : (-N) / D = -(K + 1) := by
      apply (Int.ediv_eq_iff_of_pos hD).mpr
      constructor <;> nlinarith
    rw [hh]
    ring
  refine ⟨ceil (A * v) d hd (by nlinarith) (by nlinarith), ?_,
    ceil (p * v) q hq lower upper, ?_, ceil (p * v + σ) q hq lower' upper'⟩
  · change p * v / q = K
    apply (Int.ediv_eq_iff_of_pos hq).mpr
    constructor <;> omega
  · change (p * v + σ) / q = K
    apply (Int.ediv_eq_iff_of_pos hq).mpr
    constructor <;> omega

end ApollonianSuperharmonic

end
