/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalRealRelation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalNaturalRelationReal
public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticComprehension

/-!
# Natural Real Relation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse EncodedForcing
universe u

noncomputable def realRelation (B : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ n k : ℕ, p = ZFSet.pair (natSet n) (natSet k) ∧ B (Nat.pair n k) = true)
    (ZFSet.prod ZFSet.omega ZFSet.omega)

theorem realRelation_on (B : Oracle) : On ZFSet.omega (realRelation.{u} B) :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem realRelation_pair (B : Oracle) (n k : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet k) ∈ realRelation B ↔ B (Nat.pair n k) = true := by
  rw [realRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,i,j,he,hb⟩
    obtain ⟨hi,hj⟩ := ZFSet.pair_inj.mp he
    obtain rfl := natSet_injective hi
    obtain rfl := natSet_injective hj
    exact hb
  · intro hb
    exact ⟨ZFSet.mem_prod.mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,
      natSet k,(mem_omega _).mpr ⟨k,rfl⟩,rfl⟩,n,k,rfl,hb⟩

namespace Formula
def realRelationMember (o Q B p : ℕ) : Formula :=
  .existsMem o (.existsMem (o+1) (.conj (.orderedPair (p+2) 1 0)
    (columnBit (o+2) (Q+2) 1 (B+2) 0)))

theorem realRelationMember_spec (o Q B p : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (A : Oracle) (hA : e B = realCode A) :
    (realRelationMember o Q B p).Eval e ↔ e p ∈ realRelation A := by
  simp only [realRelationMember,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  rw [ho]
  constructor
  · rintro ⟨x,hx,y,hy,he,hb⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    obtain ⟨k,rfl⟩ := (mem_omega y).mp hy
    rw [he,realRelation_pair]
    exact (columnBit_spec (o+2) (Q+2) 1 (B+2) 0
      (cons (natSet k) (cons (natSet n) e)) ho hQ A hA n k rfl rfl).mp hb
  · intro hp
    obtain ⟨_,n,k,he,hb⟩ := ZFSet.mem_sep.mp hp
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet k,(mem_omega _).mpr ⟨k,rfl⟩,he,
      (columnBit_spec (o+2) (Q+2) 1 (B+2) 0
        (cons (natSet k) (cons (natSet n) e)) ho hQ A hA n k rfl rfl).mpr hb⟩
end Formula

theorem sourceT_realRelation (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {B : Oracle} (hB : B ∈ modelReals M) : realRelation B ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  let e := cons ZFSet.omega (cons Q (fun _ => realCode B))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    exact hB
  have hs := sep_mem M hM hS (Formula.realRelationMember 1 2 3 0) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hω)
  have heq : ZFSet.sep (fun p => (Formula.realRelationMember 1 2 3 0).Eval (cons p e))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = realRelation B := by
    apply ZFSet.ext; intro p
    rw [ZFSet.mem_sep,Formula.realRelationMember_spec 1 2 3 0 (cons p e) rfl hQ B rfl]
    exact ⟨And.right,fun h => ⟨realRelation_on B h,h⟩⟩
  exact heq ▸ hs

theorem sourceT_realRelation_descent (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {B : Oracle} (hB : B ∈ modelReals M)
    (hbad : ∃ f : ℕ → ℕ, ∀ n, B (Nat.pair (f (n + 1)) (f n)) = true) :
    ∃ f : ℕ → ℕ, ∃ G ∈ modelReals M,
      (∀ n k, G (Nat.pair n k) = true ↔ k = f n) ∧
      ∀ n, B (Nat.pair (f (n+1)) (f n)) = true := by
  have hw : ¬ WellFounded (Rel ZFSet.omega (realRelation.{u} B)) := by
    intro hw
    obtain ⟨f,hf⟩ := hbad
    exact wellFounded_no_descent _ _ hw (fun n => natSet (f n))
      (fun n => (mem_omega _).mpr ⟨f n,rfl⟩)
      (fun n => (realRelation_pair B _ _).mpr (hf n))
  obtain ⟨f,G,hGM,hG,hf⟩ := sourceT_natural_descent_real M hM hT
    (sourceT_realRelation M hM hT hB) (realRelation_on B) hw
  exact ⟨f,G,hGM,hG,fun n => (realRelation_pair B _ _).mp (hf n)⟩

end TuringRigidity.BoundedSetTheory

end OAI
