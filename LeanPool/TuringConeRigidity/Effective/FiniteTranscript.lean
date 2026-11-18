/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteTranscript.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracle

/-!
# Finite Transcript
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OracleCode

theorem eval_mono {g h : ℕ →. ℕ}
    (hgh : ∀ n a, a ∈ g n → a ∈ h n) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval g c n) : a ∈ eval h c n := by
  have happrox : ∀ k, Approximates (h k) (fun m => if m = 0 then g k else h k) := by
    intro k
    constructor
    · intro m b hb
      dsimp only at hb
      split at hb
      · exact hgh k b hb
      · exact hb
    · intro b hb
      exact ⟨1, fun m hm => by simpa [show m ≠ 0 by omega] using hb⟩
  exact (eval_approximates happrox c n).1 0 a (by simpa using ha)

theorem eval_finite_use (g : ℕ → ℕ) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval (fun k => Part.some (g k)) c n) :
    ∃ m, a ∈ eval (BranchMachine.lookup (UniformOracle.oraclePrefix g m)) c n := by
  obtain ⟨m,hm⟩ := (eval_approximates (UniformOracle.prefix_approximates g) c n).2 a ha
  exact ⟨m,hm m le_rfl⟩

theorem eval_prefix_stable (g : ℕ → ℕ) (h : ℕ →. ℕ) (m : ℕ)
    (he : ∀ k, k < m → g k ∈ h k) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval (BranchMachine.lookup (UniformOracle.oraclePrefix g m)) c n) :
    a ∈ eval h c n := by
  apply eval_mono (c := c) (n := n) (a := a) ?_ ha
  intro k b hb
  change b ∈ ((UniformOracle.oraclePrefix g m)[k]? : Part ℕ) at hb
  have hk : k < m := by
    by_contra hn
    have hnone : (UniformOracle.oraclePrefix g m)[k]? = none :=
      List.getElem?_eq_none (by
        simpa [UniformOracle.oraclePrefix, PrefixComputability.oraclePrefix]
          using Nat.le_of_not_gt hn)
    simp [hnone] at hb
  have hv : (UniformOracle.oraclePrefix g m)[k]? = some (g k) := by
    simp [UniformOracle.oraclePrefix, PrefixComputability.oraclePrefix, List.getElem?_range hk]
  have heq : b = g k := by simpa [hv] using hb
  subst b
  exact he k hk

theorem eval_total_stable (g : ℕ → ℕ) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval (fun k => Part.some (g k)) c n) :
    ∃ m, ∀ h : ℕ → ℕ, (∀ k, k < m → h k = g k) →
      a ∈ eval (fun k => Part.some (h k)) c n := by
  obtain ⟨m,hm⟩ := eval_finite_use g c n a ha
  exact ⟨m,fun h hh => eval_prefix_stable g _ m
    (fun k hk => Part.mem_some_iff.mpr (hh k hk).symm) c n a hm⟩

end TuringRigidity.OracleCode

end OAI
