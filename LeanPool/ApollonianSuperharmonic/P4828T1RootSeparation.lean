/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1LeftRootGeometry
public import LeanPool.ApollonianSuperharmonic.P4828T1RightRootGeometry

-- [TABLET NODE: P4828T1RootSeparation]

/-!
# P4828T1RootSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1RootSeparation (a b : GaussianInt) (e f : Bool)
    (hne : (a, e) ≠ (b, f)) :
    Disjoint (P4828T1Gap (2 * (a.re : Real)) (P4828T1Root a e))
      (P4828T1Gap (2 * (b.re : Real)) (P4828T1Root b f)) := by
-- BODY
  have bounds : ∀ (z : GaussianInt) (side : Bool) (p : Complex),
      p ∈ P4828T1Gap (2 * (z.re : Real)) (P4828T1Root z side) →
      2 * (z.re : Real) < p.re ∧ p.re < 2 * (z.re : Real) + 2 ∧
      2 * (z.im : Real) < p.im ∧ p.im < 2 * (z.im : Real) + 2 := by
    intro z side p hp
    cases side
    · rw [(P4828T1LeftRootGeometry z).2.2.2] at hp
      exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.1, hp.2.2.2.1⟩
    · rw [(P4828T1RightRootGeometry z).2.2.2] at hp
      exact ⟨by linarith [hp.1], hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  apply Set.disjoint_left.2
  intro p hp hp'
  obtain ⟨ax, ax', ay, ay'⟩ := bounds a e p hp
  obtain ⟨bx, bx', by_, by'⟩ := bounds b f p hp'
  have hre : a.re = b.re := by
    have h1 : a.re < b.re + 1 := by
      exact_mod_cast (show (a.re : Real) < (b.re : Real) + 1 by linarith)
    have h2 : b.re < a.re + 1 := by
      exact_mod_cast (show (b.re : Real) < (a.re : Real) + 1 by linarith)
    omega
  have him : a.im = b.im := by
    have h1 : a.im < b.im + 1 := by
      exact_mod_cast (show (a.im : Real) < (b.im : Real) + 1 by linarith)
    have h2 : b.im < a.im + 1 := by
      exact_mod_cast (show (b.im : Real) < (a.im : Real) + 1 by linarith)
    omega
  have hab : a = b := by ext <;> assumption
  subst b
  have hef : e = f := by
    cases e <;> cases f
    · rfl
    · rw [(P4828T1LeftRootGeometry a).2.2.2] at hp
      rw [(P4828T1RightRootGeometry a).2.2.2] at hp'
      linarith [hp.2.1, hp'.1]
    · rw [(P4828T1RightRootGeometry a).2.2.2] at hp
      rw [(P4828T1LeftRootGeometry a).2.2.2] at hp'
      linarith [hp.1, hp'.2.1]
    · rfl
  exact hne (by rw [hef])

end ApollonianSuperharmonic

end
