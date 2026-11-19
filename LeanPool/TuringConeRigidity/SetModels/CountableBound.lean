/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountableBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracle
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Countable Bound
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountableBound
open UniformOracle

/-- Join a countable family of oracles as paired columns of a single oracle. -/
def sum (A : ℕ → Oracle) : Oracle := fun n => A (Nat.unpair n).1 (Nat.unpair n).2

theorem reduces_sum (A : ℕ → Oracle) (k : ℕ) : Reduces (A k) (sum A) := by
  apply RecursiveIn.iff_nat.mpr
  have hO : Nat.RecursiveIn {oracleFunction (sum A)} (oracleFunction (sum A)) :=
    .oracle _ (Set.mem_singleton _)
  have h := total_comp hO (total_pair (total_primrec (Primrec.const k)) (total_primrec Primrec.id))
  exact h.of_eq (fun n => by simp [oracleFunction, sum])

theorem countable_bounded (S : Set Degree) (hS : S.Countable) :
    ∃ b : Degree, ∀ x ∈ S, x ≤ b := by
  by_cases hne : S.Nonempty
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    choose A hA using (fun n => degree_surjective (f n))
    refine ⟨degree (sum A), ?_⟩
    intro x hx
    rw [hf] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [← hA n]
    exact reduces_sum A n
  · exact ⟨⊥, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

end TuringRigidity.CountableBound

end OAI
