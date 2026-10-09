/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Reference

/-!
# Executable semantic helpers

Fuel monotonicity for the Nat-level `evalN` reference.
-/

@[expose] public section

namespace Nock

theorem evalN_succ {n : Nat} {s form r : Noun}
    (h : evalN n s form = some r) : evalN (n + 1) s form = some r := by
  induction n, s, form using evalN.induct generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalN, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalN, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalN]

theorem evalN_mono {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalN n s form = some r) : evalN m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalN_succ ih

-- main.tex:1156–1158  (fuel-indexed shadow of `Thm:deterministic_Trace`)
/-- **`evalN` is a partial function (output uniqueness).**  Two successful evaluations of the
    same `subject`/`formula`, at any fuel budgets, return the same noun.  Fuel controls only
    whether evaluation finishes, never the result.  Proof: bump both to the common fuel
    `max n m` by `evalN_mono`, then `some` is injective. -/
theorem evalN_deterministic {n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalN n s form = some r₁) (h₂ : evalN m s form = some r₂) : r₁ = r₂ :=
  Option.some.inj ((evalN_mono (Nat.le_max_left n m) h₁).symm.trans
    (evalN_mono (Nat.le_max_right n m) h₂))

end Nock
