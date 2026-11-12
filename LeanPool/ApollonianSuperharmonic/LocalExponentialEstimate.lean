/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.RealFourNeighborLaplacian

-- [TABLET NODE: LocalExponentialEstimate]

/-!
# LocalExponentialEstimate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem LocalExponentialEstimate
    (w : GaussianInt -> Real) (M : Real)
    (hw : forall x, 0 <= w x)
    (hlap : forall x, RealFourNeighborLaplacian w x <= M) :
    forall x : GaussianInt,
      w x <= (4 : Real) ^ (x.re.natAbs + x.im.natAbs) * w 0 +
        M * (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3) := by
-- BODY
  intro x
  have hright (z : GaussianInt) : w (z + 1) <= 4 * w z + M := by
    have h := hlap z
    simp [RealFourNeighborLaplacian] at h
    linarith [hw (z - 1), hw (z + ⟨0, 1⟩), hw (z - ⟨0, 1⟩)]
  have hleft (z : GaussianInt) : w (z - 1) <= 4 * w z + M := by
    have h := hlap z
    simp [RealFourNeighborLaplacian] at h
    linarith [hw (z + 1), hw (z + ⟨0, 1⟩), hw (z - ⟨0, 1⟩)]
  have hup (z : GaussianInt) : w (z + ⟨0, 1⟩) <= 4 * w z + M := by
    have h := hlap z
    simp [RealFourNeighborLaplacian] at h
    linarith [hw (z + 1), hw (z - 1), hw (z - ⟨0, 1⟩)]
  have hdown (z : GaussianInt) : w (z - ⟨0, 1⟩) <= 4 * w z + M := by
    have h := hlap z
    simp [RealFourNeighborLaplacian] at h
    linarith [hw (z + 1), hw (z - 1), hw (z + ⟨0, 1⟩)]
  have growth (k : ℕ) :
      4 * ((4 : Real) ^ k * w 0 + M * (((4 : Real) ^ k - 1) / 3)) + M =
        (4 : Real) ^ (k + 1) * w 0 + M * (((4 : Real) ^ (k + 1) - 1) / 3) := by
    rw [pow_succ]
    ring
  have decrementPositive (a : ℤ) (ha : 0 < a.natAbs) (haeq : a = (a.natAbs : ℤ)) :
      (a - 1).natAbs = a.natAbs - 1 := by
    have hnon : 0 ≤ a - 1 := by omega
    have hc := Int.natAbs_of_nonneg hnon
    have hc' := Int.natAbs_of_nonneg (a := (a.natAbs : ℤ) - 1) (by omega)
    omega
  have incrementNegative (a : ℤ) (ha : 0 < a.natAbs) (haeq : a = -(a.natAbs : ℤ)) :
      (a + 1).natAbs = a.natAbs - 1 := by
    have hc' := Int.natAbs_of_nonneg (a := (a.natAbs : ℤ) - 1) (by omega)
    have hrel : (- (a.natAbs : ℤ) + 1).natAbs = a.natAbs - 1 := by
      rw [show - (a.natAbs : ℤ) + 1 = -((a.natAbs : ℤ) - 1) by ring,
        Int.natAbs_neg]
      omega
    rw [haeq, Int.natAbs_neg]
    exact hrel
  have main : ∀ n : ℕ, ∀ z : GaussianInt,
      z.re.natAbs + z.im.natAbs = n →
      w z <= (4 : Real) ^ n * w 0 + M * (((4 : Real) ^ n - 1) / 3) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hz
      by_cases hn : n = 0
      · have hz0 : z.re = 0 := by omega
        have hz1 : z.im = 0 := by omega
        have ze : z = 0 := by ext <;> simp [hz0, hz1]
        subst z
        subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hr : z.re = 0
        · have hi : 0 < z.im.natAbs := by omega
          rcases Int.natAbs_eq z.im with hi' | hi'
          · have hprev : (z - ⟨0, 1⟩).re.natAbs + (z - ⟨0, 1⟩).im.natAbs = n - 1 := by
              have hre : (z - ⟨0, 1⟩).re = z.re := by simp
              have him : (z - ⟨0, 1⟩).im = z.im - 1 := by simp
              rw [hre, him]
              have hdec := decrementPositive z.im hi hi'
              rw [hdec]
              rw [hr, hi']
              omega
            have hh := ih (n - 1) (by omega) (z - ⟨0, 1⟩) hprev
            have hstep := hup (z - ⟨0, 1⟩)
            have zeq : (z - ⟨0, 1⟩) + ⟨0, 1⟩ = z := by abel
            rw [zeq] at hstep
            have hg := growth (n - 1)
            rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at hg
            nlinarith [hh, hstep, hg]
          · have hprev : (z + ⟨0, 1⟩).re.natAbs + (z + ⟨0, 1⟩).im.natAbs = n - 1 := by
              have hre : (z + ⟨0, 1⟩).re = z.re := by simp
              have him : (z + ⟨0, 1⟩).im = z.im + 1 := by simp
              rw [hre, him]
              have hinc := incrementNegative z.im hi hi'
              rw [hinc]
              rw [hr, hi']
              omega
            have hh := ih (n - 1) (by omega) (z + ⟨0, 1⟩) hprev
            have hstep := hdown (z + ⟨0, 1⟩)
            have zeq : (z + ⟨0, 1⟩) - ⟨0, 1⟩ = z := by abel
            rw [zeq] at hstep
            have hg := growth (n - 1)
            rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at hg
            nlinarith [hh, hstep, hg]
        · have hrpos : 0 < z.re.natAbs := by omega
          rcases Int.natAbs_eq z.re with hr' | hr'
          · have hprev : (z - 1).re.natAbs + (z - 1).im.natAbs = n - 1 := by
              have hre : (z - 1).re = z.re - 1 := by simp
              have him : (z - 1).im = z.im := by simp
              rw [hre, him]
              have hdec := decrementPositive z.re hrpos hr'
              rw [hdec]
              rw [hr']
              omega
            have hh := ih (n - 1) (by omega) (z - 1) hprev
            have hstep := hright (z - 1)
            have zeq : (z - 1) + 1 = z := by abel
            rw [zeq] at hstep
            have hg := growth (n - 1)
            rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at hg
            nlinarith [hh, hstep, hg]
          · have hprev : (z + 1).re.natAbs + (z + 1).im.natAbs = n - 1 := by
              have hre : (z + 1).re = z.re + 1 := by simp
              have him : (z + 1).im = z.im := by simp
              rw [hre, him]
              have hinc := incrementNegative z.re hrpos hr'
              rw [hinc]
              rw [hr']
              omega
            have hh := ih (n - 1) (by omega) (z + 1) hprev
            have hstep := hleft (z + 1)
            have zeq : (z + 1) - 1 = z := by abel
            rw [zeq] at hstep
            have hg := growth (n - 1)
            rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at hg
            nlinarith [hh, hstep, hg]
  apply main (x.re.natAbs + x.im.natAbs) x rfl

end ApollonianSuperharmonic

end
