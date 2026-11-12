/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1Root
public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate

-- [TABLET NODE: P5455T2RootAlignment]

/-!
# P5455T2RootAlignment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2RootAlignment (z z' : GaussianInt) (s s' : Bool)
    (r r' : Fin 3)
    (h : P4828T1Rotate (P4828T1Root z s) r =
      P4828T1Rotate (P4828T1Root z' s') r') :
    z = z' ∧ s = s' ∧ r = r' := by
-- BODY
  have hc := congrArg (fun q => (q 0).2) h
  have parameters : z = z' ∧ s = s' := by
    cases s <;> cases s'
    all_goals norm_num [P4828T1Rotate, P4828T1Root, Zsqrtd.ext_iff] at hc
    · exact ⟨by ext <;> omega, rfl⟩
    · omega
    · omega
    · exact ⟨by ext <;> omega, rfl⟩
  obtain ⟨rfl, rfl⟩ := parameters
  refine ⟨rfl, rfl, ?_⟩
  have h1 := congrArg (fun q => (q 1).1) h
  have h2 := congrArg (fun q => (q 2).1) h
  cases s <;> fin_cases r <;> fin_cases r'
  all_goals first
    | rfl
    | (change (0 : ℤ) = 1 at h1; omega)
    | (change (1 : ℤ) = 0 at h1; omega)
    | (change (0 : ℤ) = 1 at h2; omega)
    | (change (1 : ℤ) = 0 at h2; omega)

end ApollonianSuperharmonic

end
