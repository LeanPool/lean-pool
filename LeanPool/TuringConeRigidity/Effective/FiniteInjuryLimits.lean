/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteInjuryLimits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteInjury

/-!
# Finite Injury Limits
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FiniteInjury
open CodingForcing

def leftLimit (p : ℕ → Condition) : Oracle := fun n => (p (n+1)).left.getD n false

def rightLimit (p : ℕ → Condition) : Oracle := fun n => (p (n+1)).right.getD n false

theorem word_prefix {p : ℕ → Condition}
    (h : ∀ s, (p s).left <+: (p (s + 1)).left ∧ (p s).right <+: (p (s + 1)).right)
    {s u : ℕ} (hsu : s ≤ u) : (p s).left <+: (p u).left ∧ (p s).right <+: (p u).right := by
  induction u, hsu using Nat.le_induction with
  | base => exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | succ u hu ih => exact ⟨ih.1.trans (h u).1, ih.2.trans (h u).2⟩

theorem limits_extend {p : ℕ → Condition}
    (h : ∀ s, (p s).left <+: (p (s + 1)).left ∧ (p s).right <+: (p (s + 1)).right)
    (hlen : ∀ s, s ≤ (p s).left.length) (s m : ℕ) (hm : m < (p s).left.length) :
    leftLimit p m = (p s).left.getD m false ∧
      rightLimit p m = (p s).right.getD m false := by
  unfold leftLimit rightLimit
  by_cases hs : s ≤ m+1
  · have hp := word_prefix h hs
    exact ⟨getD_of_prefix hp.1 hm,
      getD_of_prefix hp.2 (by simpa [← (p s).sameLength] using hm)⟩
  · have hp := word_prefix h (Nat.le_of_not_ge hs)
    have hml : m < (p (m+1)).left.length := (Nat.lt_succ_self m).trans_le (hlen (m+1))
    exact ⟨(getD_of_prefix hp.1 hml).symm,
      (getD_of_prefix hp.2 (by simpa [← (p (m+1)).sameLength] using hml)).symm⟩

theorem eventual_column_agreement (A : ℕ → Oracle)
    (proposal : ℕ → Finset ℕ → Option ℕ) (p : ℕ → Condition)
    (hwords : ∀ s, (p s).left <+: (p (s + 1)).left ∧ (p s).right <+: (p (s + 1)).right)
    (hlen : ∀ s, s ≤ (p s).left.length)
    (hstep : ∀ s k, k ≤ s →
      (∀ t, action proposal s = some t → k ≤ t) →
      Extends A (atLevel (p s) k) (atLevel (p (s + 1)) k)) (k : ℕ) :
    ∃ S, ∀ m, (p S).left.length ≤ m → (Nat.unpair m).1 < k →
      A (Nat.unpair m).1 (Nat.unpair m).2 = true → leftLimit p m = rightLimit p m := by
  obtain ⟨S, hS⟩ := eventual_level_chain A proposal p hstep k
  refine ⟨S, ?_⟩
  intro m hm hk ha
  let u := max S (m+1)
  have hlen' : m < (p u).left.length :=
    (Nat.lt_succ_self m).trans_le ((le_max_right _ _).trans (hlen u))
  have hext := hS S le_rfl u (le_max_left _ _)
  have heq := hext.2.2.2 m ⟨hm, hk, ha⟩ hlen'
  have hlim := limits_extend hwords hlen u m hlen'
  exact hlim.1.trans (heq.trans hlim.2.symm)

end TuringRigidity.FiniteInjury

end OAI
