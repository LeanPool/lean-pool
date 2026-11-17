/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentCountability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentPresentation

/-!
# Persistent Countability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistentCountability
open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions PersistentPresentation
noncomputable section
attribute [local instance] Classical.propDecidable

theorem presentation_exists (I : CountableIdeal) : ∃ H, Presented I H := by
  obtain ⟨f,hf⟩ := I.countable.exists_eq_range I.nonempty
  choose A hA using (fun n => degree_surjective (f n))
  refine ⟨CountableBound.sum A,fun x => ?_⟩
  have hc (k : ℕ) : columns (CountableBound.sum A) k = A k := by
    funext n
    simp only [columns,CountableBound.sum,Nat.unpair_pair]
  simp only [hc,hA,hf,Set.mem_range]

/-- The Boolean oracle coding the graph of an automorphism in the chosen presentation. -/
def graphOracle {I : CountableIdeal} {H : Oracle} (hpres : Presented I H)
    (ρ : I ≃o I) : Oracle := fun n => decide (Graph ρ hpres n)

theorem graphOracle_injective {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) : Function.Injective (graphOracle hpres) := by
  intro ρ σ he
  apply OrderIso.ext
  funext x
  obtain ⟨n,hn⟩ := (hpres x.val).mp x.property
  obtain ⟨j,hj⟩ := (hpres (ρ x).val).mp (ρ x).property
  have hx : entry hpres n = x := Subtype.ext hn
  have hp : Graph ρ hpres (Nat.pair n j) := by
    simp only [PersistentPresentation.Graph,Nat.unpair_pair,hx,hj]
  have hq : Graph σ hpres (Nat.pair n j) := by
    by_contra hn
    have hh := congrFun he (Nat.pair n j)
    simp only [graphOracle,decide_eq_true hp,decide_eq_false hn] at hh
    cases hh
  apply Subtype.ext
  simpa only [PersistentPresentation.Graph,Nat.unpair_pair,hx,hj] using hq.symm

theorem graphOracle_reduces {I : CountableIdeal} {H Y : Oracle}
    (hpres : Presented I H) (ρ : I ≃o I) (h : RecursivePred Y (Graph ρ hpres)) :
    Reduces (graphOracle hpres ρ) Y := by
  apply RecursiveIn.iff_nat.mpr
  exact h.of_eq (fun n => by simp [oracleFunction,graphOracle])

theorem arithmetic_maps_countable {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) (Y : Oracle) :
    {ρ : I ≃o I | RecursivePred Y (Graph ρ hpres)}.Countable := by
  apply ((countable_reduces Y).preimage (graphOracle_injective hpres)).mono
  intro ρ hρ
  exact graphOracle_reduces hpres ρ hρ

theorem source_4_1_9 (I : CountableIdeal)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    {ρ : I ≃o I | Persistent I ρ}.Countable := by
  obtain ⟨H,hpres⟩ := presentation_exists I
  apply (arithmetic_maps_countable hpres (iterate H 11)).mono
  intro ρ hp
  exact (source_4_1_8 ρ hp hz hpres).2

end
end TuringRigidity.PersistentCountability

end OAI
