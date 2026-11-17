/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePresentationCountability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePresentation

/-!
# Countability of arithmetic partial cone isomorphisms

A presentation real enumerates all source and target degrees (the target is a
subcollection of the source ideal). Thus the indexed graph determines the map,
even when the enumeration repeats degrees. Arithmetic graphs are countable.

Together with `arithmetic_presentation_of_jump_extension`, this counts the maps
that extend to the arithmetic jump ideal. The final persistence corollary
explicitly assumes that extension theorem; it does not assert it unconditionally.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePresentation

open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions

noncomputable section
attribute [local instance] Classical.propDecidable

theorem presentation_exists (I : CountableIdeal) : ∃ H, Presented I H := by
  obtain ⟨f, hf⟩ := I.countable.exists_eq_range I.nonempty
  choose A hA using fun n => degree_surjective (f n)
  refine ⟨CountableBound.sum A, fun x => ?_⟩
  have hc (k : ℕ) : columns (CountableBound.sum A) k = A k := by
    funext n
    simp only [columns, CountableBound.sum, Nat.unpair_pair]
  simp only [hc, hA, hf, Set.mem_range]

def graphOracle {I : CountableIdeal} {a : Degree} {H : Oracle}
    (hpres : Presented I H) (ρ : I ≃o ConePersistence.Cone I a) : Oracle :=
  fun n => decide (Graph ρ hpres n)

/-- Repetitions in the presentation cause no ambiguity: its indexed graph
still determines the entire partial cone isomorphism. -/
theorem graphOracle_injective {I : CountableIdeal} {a : Degree} {H : Oracle}
    (hpres : Presented I H) :
    Function.Injective (graphOracle (a := a) hpres) := by
  intro ρ σ he
  apply OrderIso.ext
  funext x
  obtain ⟨n, hn⟩ := (hpres x.val).mp x.property
  obtain ⟨j, hj⟩ := (hpres (ρ x).val).mp (ρ x).property.1
  have hx : presentationEntry hpres n = x := Subtype.ext hn
  have hp : Graph ρ hpres (Nat.pair n j) := by
    simp only [Graph, Nat.unpair_pair, hx, hj]
  have hq : Graph σ hpres (Nat.pair n j) := by
    by_contra hn
    have hh := congrFun he (Nat.pair n j)
    simp only [graphOracle, decide_eq_true hp, decide_eq_false hn] at hh
    cases hh
  apply Subtype.ext
  simpa only [Graph, Nat.unpair_pair, hx, hj] using hq.symm

theorem graphOracle_reduces {I : CountableIdeal} {a : Degree} {H Y : Oracle}
    (hpres : Presented I H) (ρ : I ≃o ConePersistence.Cone I a)
    (h : RecursivePred Y (Graph ρ hpres)) : Reduces (graphOracle hpres ρ) Y := by
  apply RecursiveIn.iff_nat.mpr
  exact h.of_eq (fun n => by simp [oracleFunction, graphOracle])

theorem recursive_maps_countable {I : CountableIdeal} {a : Degree} {H : Oracle}
    (hpres : Presented I H) (Y : Oracle) :
    {ρ : I ≃o ConePersistence.Cone I a | RecursivePred Y (Graph ρ hpres)}.Countable := by
  apply ((countable_reduces Y).preimage (graphOracle_injective hpres)).mono
  intro ρ hρ
  exact graphOracle_reduces hpres ρ hρ

/-- The finite jump bound is allowed to depend on the map. -/
theorem arithmetic_maps_countable {I : CountableIdeal} {a : Degree} {H : Oracle}
    (hpres : Presented I H) :
    {ρ : I ≃o ConePersistence.Cone I a |
      ∃ n, RecursivePred (iterate H n) (Graph ρ hpres)}.Countable := by
  have he : {ρ : I ≃o ConePersistence.Cone I a |
      ∃ n, RecursivePred (iterate H n) (Graph ρ hpres)} =
      ⋃ n : ℕ, {ρ : I ≃o ConePersistence.Cone I a |
        RecursivePred (iterate H n) (Graph ρ hpres)} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [he]
  exact Set.countable_iUnion (fun n => recursive_maps_countable hpres (iterate H n))

/-- The established arithmetic-presentation theorem has this countability
consequence, with the jump-ideal extension hypothesis still visible. -/
theorem jump_extendible_maps_countable {I : CountableIdeal} {a : Degree} {H : Oracle}
    (hpres : Presented I H) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    {ρ : I ≃o ConePersistence.Cone I a | HasJumpIdealExtension ρ hpres}.Countable := by
  apply (arithmetic_maps_countable hpres).mono
  intro ρ hρ
  obtain ⟨n, _, hr⟩ := arithmetic_presentation_of_jump_extension ρ hpres hz hρ
  exact ⟨n + 5, hr⟩

/-- Interface for the remaining locality step. Proving `hlocal` would make
countability of persistent partial cone isomorphisms unconditional. -/
theorem persistent_maps_countable_of_jump_extension
    {I : CountableIdeal} {a : Degree} {H : Oracle} (hpres : Presented I H)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hlocal : ∀ ρ : I ≃o ConePersistence.Cone I a,
      ConePersistence.Persistent I ρ → HasJumpIdealExtension ρ hpres) :
    {ρ : I ≃o ConePersistence.Cone I a | ConePersistence.Persistent I ρ}.Countable :=
  (jump_extendible_maps_countable hpres hz).mono (fun ρ hρ => hlocal ρ hρ)

end
end OAI.TuringRigidity.ConePresentation
