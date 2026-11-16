/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# A measurable selection principle

Corresponds to Lemma \ref{lexstruct} in Section 2 of `proof_met.tex`, used throughout to
build measurable "first index satisfying a condition" maps out of countable dense families.
-/

@[expose] public section

namespace MultiplicativeErgodic

/-- Gluing countably many measurable maps along a measurable index. -/
theorem measurable_glue {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {N : Ω → ℕ}
    (hN : Measurable N) {W : ℕ → Ω → Y} (hW : ∀ i, Measurable (W i)) :
    Measurable fun ω => W (N ω) ω := by
  intro B hB
  have hset : (fun ω => W (N ω) ω) ⁻¹' B = ⋃ i, (N ⁻¹' {i}) ∩ (W i ⁻¹' B) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨N ω, rfl, h⟩, fun ⟨i, hi, h⟩ => by subst hi; exact h⟩
  rw [hset]
  exact MeasurableSet.iUnion fun i => (hN (measurableSet_singleton i)).inter (hW i hB)

/-- **Lemma \ref{lexstruct}.** If `{x_n}` is a sequence in a measurable space `Y` and
`{S_n}` is a measurable cover of `Ω`, then `N(ω) = inf{n : ω ∈ S_n}` is measurable, and so is
`ω ↦ x_{N(ω)}`. -/
theorem measurable_of_countable_cover {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (x : ℕ → Y) (S : ℕ → Set Ω) (hS : ∀ n, MeasurableSet (S n)) (hcover : (⋃ n, S n) = Set.univ) :
    ∃ N : Ω → ℕ, Measurable N ∧ Measurable (fun ω => x (N ω)) ∧
      ∀ ω, ω ∈ S (N ω) ∧ ∀ m, ω ∈ S m → N ω ≤ m := by
  classical
  -- Every `ω` lies in some `S n`, since the `S n` cover `Ω`.
  have hex : ∀ ω, ∃ n, ω ∈ S n := by
    intro ω
    have : ω ∈ (⋃ n, S n) := by rw [hcover]; exact Set.mem_univ ω
    simpa using this
  -- Define `N ω` as the least `n` with `ω ∈ S n`.
  set N : Ω → ℕ := fun ω => Nat.find (hex ω) with hNdef
  -- `N` is measurable: each fibre `{ω | N ω = m}` is a measurable set.
  have hN : Measurable N := by
    refine measurable_to_countable' fun m => ?_
    have heq : N ⁻¹' {m} = S m ∩ ⋂ k, ⋂ (_ : k < m), (S k)ᶜ := by
      ext ω
      simp only [hNdef, Set.mem_preimage, Set.mem_singleton_iff, Nat.find_eq_iff,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    rw [heq]
    exact (hS m).inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hS k).compl)
  refine ⟨N, hN, ?_, ?_⟩
  · -- `ω ↦ x (N ω)` is measurable: any map out of `ℕ` (with its `⊤` σ-algebra) is measurable.
    exact measurable_from_nat.comp hN
  · -- `N ω` realises the infimum: it is attained and is a lower bound.
    intro ω
    exact ⟨Nat.find_spec (hex ω), fun m hm => Nat.find_min' (hex ω) hm⟩

end MultiplicativeErgodic
