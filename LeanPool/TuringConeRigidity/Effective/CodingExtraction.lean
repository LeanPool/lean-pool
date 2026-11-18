/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingExtraction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingSplitSearch
public import LeanPool.TuringConeRigidity.Effective.RecursiveInfiniteSubset

/-!
# Coding Extraction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingExtraction
open CodingForcing CodingAgreement CodingLocations CodingSplitSearch PrefixComputability

theorem recursive_coding_locations {A : ℕ → Oracle} {Y : Oracle} {e₀ e₁ : OracleCode}
    {p : Condition} (hn : NoDisagreement A Y e₀ e₁ p)
    (hL : DenseLeft A Y e₀ p) (hR : DenseRight A Y e₁ p)
    (hU : ∀ q, Extends A p q → ¬ UniqueValues A Y e₀ q) :
    ∃ C : Oracle, Reduces C Y ∧ {m | C m = true}.Infinite ∧
      ∀ m, C m = true → CodingLocation A p m := by
  obtain ⟨E, hE, hEq⟩ := splittingLocations_enumerable Y e₀ p.left
  have hu : RecursiveInfiniteSubset.Unbounded E := by
    intro N
    obtain ⟨m, hm, hs⟩ := splittingLocation_unbounded hL hU N
    obtain ⟨z, hz⟩ := (hEq m).mp hs
    exact ⟨z, m, hm, hz⟩
  obtain ⟨C, hCY, hCinf, hC⟩ := RecursiveInfiniteSubset.infinite_recursive_subset Y E hu hE
  refine ⟨C, hCY, hCinf, ?_⟩
  intro m hm
  exact splittingLocation_sound hn hR ((hEq m).mpr (hC m hm))

theorem column_projection_reduces (C : Oracle) (k : ℕ) :
    Reduces (fun a => C (Nat.pair k a)) C := by
  apply RecursiveIn.iff_nat.mpr
  have hq : Nat.RecursiveIn {oracleFunction C} (oracleFunction C) := .oracle _ (Set.mem_singleton _)
  exact total_comp hq (total_primrec (Primrec₂.natPair.comp (Primrec.const k) Primrec.id))

theorem infinite_column {A : ℕ → Oracle} {Y C : Oracle} {p : Condition}
    (hCY : Reduces C Y) (hinf : {m | C m = true}.Infinite)
    (hC : ∀ m, C m = true → CodingLocation A p m) :
    ∃ k, k < p.active ∧ ∃ Z : Oracle, Reduces Z Y ∧ {a | Z a = true}.Infinite ∧
      ∀ a, Z a = true → A k a = true := by
  let F := fun k : Fin p.active => {m : ℕ | C m = true ∧ (Nat.unpair m).1 = k.val}
  have hex : ∃ k : Fin p.active, (F k).Infinite := by
    by_contra h
    have hf : ∀ k : Fin p.active, (F k).Finite := by
      intro k
      by_contra hi
      exact h ⟨k, hi⟩
    apply hinf
    apply (Set.finite_iUnion hf).subset
    intro m hm
    refine Set.mem_iUnion.mpr ⟨⟨(Nat.unpair m).1, (hC m hm).2.1⟩, ?_⟩
    exact ⟨hm, rfl⟩
  obtain ⟨k, hk⟩ := hex
  let Z : Oracle := fun a => C (Nat.pair k.val a)
  refine ⟨k.val, k.isLt, Z, reduces_trans (column_projection_reduces C k.val) hCY, ?_, ?_⟩
  · intro hZ
    apply hk
    apply (hZ.image (Nat.pair k.val)).subset
    intro m hm
    refine ⟨(Nat.unpair m).2, ?_, ?_⟩
    · change C (Nat.pair k.val (Nat.unpair m).2) = true
      rw [← hm.2, Nat.pair_unpair]
      exact hm.1
    · rw [← hm.2, Nat.pair_unpair]
  · intro a ha
    have hc := (hC (Nat.pair k.val a) ha).2.2
    simpa only [Nat.unpair_pair] using hc

theorem case2_computes_member {A : ℕ → Oracle} {Y : Oracle} {e₀ e₁ : OracleCode}
    {p : Condition}
    (hIntro : ∀ k Z, (∀ a, Z a = true → A k a = true) →
      {a | Z a = true}.Infinite → Reduces (A k) Z)
    (hn : NoDisagreement A Y e₀ e₁ p)
    (hL : DenseLeft A Y e₀ p) (hR : DenseRight A Y e₁ p)
    (hU : ∀ q, Extends A p q → ¬ UniqueValues A Y e₀ q) :
    ∃ k, k < p.active ∧ Reduces (A k) Y := by
  obtain ⟨C, hCY, hCinf, hC⟩ := recursive_coding_locations hn hL hR hU
  obtain ⟨k, hk, Z, hZY, hZinf, hZ⟩ := infinite_column hCY hCinf hC
  exact ⟨k, hk, reduces_trans (hIntro k Z hZ hZinf) hZY⟩

end TuringRigidity.CodingExtraction

end OAI
