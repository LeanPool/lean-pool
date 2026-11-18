/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/SparseCohenFilter.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseCounting

/-!
# Sparse Cohen Filter
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SparseCohenFilter
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCollapse
open InternalCohen (alphabet bitSet mem_alphabet bitSet_injective)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem finite_covered {c : ZFSet.{0}} (G : GenericFilter (Conditions c))
    (S : Set ZFSet.{0}) (hS : S.Finite)
    (hsub : ∀ z ∈ S, z ∈ unionGraph G) :
    ∃ p ∈ G.carrier, ∀ z ∈ S, z ∈ label c p := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨p,hp,fun _ h => False.elim h⟩
  | @insert z S hz hS ih =>
    obtain ⟨p,hp,hpS⟩ := ih (fun x hx => hsub x (Or.inr hx))
    obtain ⟨q,hq,hqz⟩ := (mem_unionGraph G z).mp (hsub z (Or.inl rfl))
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    refine ⟨r,hr,fun x hx => ?_⟩
    rcases hx with rfl|hx
    · exact hrq hqz
    · exact hrp (hpS x hx)

theorem mem_filter_iff_subset_union (A : ZFSet.{0})
    (G : GenericFilter (Conditions (conditions A)))
    (p : Conditions (conditions A)) :
    p ∈ G.carrier ↔ label _ p ⊆ unionGraph G := by
  constructor
  · intro hp z hz
    exact (mem_unionGraph G z).mpr ⟨p,hp,hz⟩
  · intro hsub
    have hfin := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions A _).mp (label_mem _ p)).1).2
    obtain ⟨q,hq,hqp⟩ := finite_covered G (label _ p) hfin (fun z hz => hsub hz)
    exact G.upper hqp hq

theorem union_real (G : GenericFilter (Conditions (conditions ZFSet.omega)))
    (hfun : FunctionGraph ZFSet.omega alphabet (unionGraph G)) :
    ∃ A : Oracle, ∀ n b,
      ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b := by
  classical
  have hex (n : ℕ) : ∃ b : Bool, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G := by
    obtain ⟨b,hb,hnb,_⟩ := hfun.2 _ ((mem_omega _).mpr ⟨n,rfl⟩)
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    exact ⟨b,hnb⟩
  let A : Oracle := fun n => (hex n).choose
  refine ⟨A,fun n b => ⟨fun hb => ?_,fun he => he ▸ (hex n).choose_spec⟩⟩
  obtain ⟨v,hv,hnv,huniq⟩ := hfun.2 _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact bitSet_injective ((huniq _ ((mem_alphabet _).mpr ⟨A n,rfl⟩)
    (hex n).choose_spec).trans (huniq _ ((mem_alphabet _).mpr ⟨b,rfl⟩) hb).symm)

theorem mem_filter_iff_agrees (G : GenericFilter (Conditions (conditions ZFSet.omega)))
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b)
    (p : Conditions (conditions ZFSet.omega)) :
    p ∈ G.carrier ↔ ∀ n b,
      ZFSet.pair (natSet n) (bitSet b) ∈ label _ p → A n = b := by
  rw [mem_filter_iff_subset_union]
  constructor
  · intro hp n b hb
    exact (hA n b).mp (hp hb)
  · intro hp z hz
    have hsub := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions ZFSet.omega _).mp (label_mem _ p)).1).1
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
    obtain ⟨n,rfl⟩ := (mem_omega _).mp hx
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    exact (hA n b).mpr (hp n b hz)

end TuringRigidity.SparseCohenFilter

end OAI
