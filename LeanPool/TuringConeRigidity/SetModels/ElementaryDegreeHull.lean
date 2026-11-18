/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryDegreeHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryDefinableSets
public import LeanPool.TuringConeRigidity.SetModels.ElementaryRealModel

/-!
# Elementary Degree Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm SetDegreeDecoding
universe u

theorem witness_in_hull (a : ℕ → ZFSet.{u}) (p : SentenceForm) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ hullSet a) (hex : ∃ x : ZFSet.{u}, p.Sat Set.univ (cons x e)) :
    ∃ x ∈ hullSet a, p.Sat Set.univ (cons x e) := by
  have hen : ∀ i, e i ∈ hull a := fun i => (mem_hullSet a _).mp (he i)
  obtain ⟨x,hx⟩ := hex
  have hs := (hull_elementary a (.ex p) e hen).mpr ⟨x,Set.mem_univ _,hx⟩
  obtain ⟨y,hy,hp⟩ := hs
  exact ⟨y,(mem_hullSet a _).mpr hy,(hull_elementary a p (cons y e)
    (by intro i; cases i <;> simp [cons,hen,hy])).mp hp⟩

theorem degree_representative_in_hull (a : ℕ → ZFSet.{u}) (b : Degree)
    (hb : degreeSet b ∈ hullSet a) : ∃ A : Oracle, realCode A ∈ hullSet a ∧ degree A = b := by
  obtain ⟨B,hB⟩ := degree_surjective b
  obtain ⟨x,hx,hxb⟩ := witness_in_hull a (.member 0 1) (fun _ => degreeSet b) (fun _ => hb)
    ⟨realCode B,(real_mem_degreeSet B b).mpr hB⟩
  obtain ⟨A,he,hA⟩ := (mem_degreeSet b x).mp hxb
  change x = realCode A at he
  exact ⟨A,he ▸ hx,hA⟩

theorem degreeSet_fixed (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a)
    (b : Degree) (hb : degreeSet b ∈ hullSet a) :
    structureMap (hullSet a) (degreeSet b) = degreeSet b := by
  obtain ⟨A,hA,hAb⟩ := degree_representative_in_hull a b hb
  have hAM := (collapsed_hull_reals a hn hω A).mpr hA
  apply collapse_fixed _ _ hb
  intro x hx
  obtain ⟨B,rfl,hBb⟩ := (mem_degreeSet b x).mp hx
  have hBM := sourceT_real_lower _ (collapsed_transitive _) (collapsed_hull_sourceT a) hAM
    (le_of_eq (hBb.trans hAb.symm))
  have hB := (collapsed_hull_reals a hn hω B).mp hBM
  exact ⟨hB,hull_real_fixed a hn hB⟩

theorem pair_components_mem_hull (a : ℕ → ZFSet.{u}) {x y : ZFSet.{u}}
    (hp : ZFSet.pair x y ∈ hullSet a) : x ∈ hullSet a ∧ y ∈ hullSet a := by
  constructor
  · apply unique_definable_mem a (.ex (fromBounded (.orderedPair 2 1 0)))
      (fun _ => ZFSet.pair x y) (fun _ => hp)
    · exact ⟨y,Set.mem_univ _,(bounded_univ _ _).mpr ((Formula.eval_orderedPair _ _ _ _).mpr rfl)⟩
    · intro z hz
      obtain ⟨w,_,hw⟩ := hz
      have he := (Formula.eval_orderedPair _ _ _ _).mp ((bounded_univ _ _).mp hw)
      exact (ZFSet.pair_inj.mp he).1.symm
  · apply unique_definable_mem a (.ex (fromBounded (.orderedPair 2 0 1)))
      (fun _ => ZFSet.pair x y) (fun _ => hp)
    · exact ⟨x,Set.mem_univ _,(bounded_univ _ _).mpr ((Formula.eval_orderedPair _ _ _ _).mpr rfl)⟩
    · intro z hz
      obtain ⟨w,_,hw⟩ := hz
      have he := (Formula.eval_orderedPair _ _ _ _).mp ((bounded_univ _ _).mp hw)
      exact (ZFSet.pair_inj.mp he).2.symm

/-- The set-coded graph of the global degree automorphism on set representations of degrees. -/
noncomputable def globalGraph (π : Degree ≃o Degree) : ZFSet.{u} :=
  ZFSet.range (fun b : Degree => ZFSet.pair (degreeSet b) (degreeSet (π b)))

theorem mem_globalGraph (π : Degree ≃o Degree) (z : ZFSet.{u}) :
    z ∈ globalGraph π ↔ ∃ b : Degree, z = ZFSet.pair (degreeSet b) (degreeSet (π b)) := by
  rw [globalGraph,ZFSet.mem_range]
  exact ⟨fun ⟨b,hb⟩ => ⟨b,hb.symm⟩,fun ⟨b,hb⟩ => ⟨b,hb.symm⟩⟩

theorem globalGraph_pair (π : Degree ≃o Degree) (b : Degree) (x : ZFSet.{u}) :
    ZFSet.pair (degreeSet b) x ∈ globalGraph π ↔ x = degreeSet (π b) := by
  rw [mem_globalGraph]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨hbc,hx⟩ := ZFSet.pair_inj.mp hc
    have hbc := degreeSet_injective hbc
    exact hbc.symm ▸ hx
  · intro hx; exact ⟨b,congrArg (ZFSet.pair (degreeSet b)) hx⟩

theorem globalGraph_inverse_pair (π : Degree ≃o Degree) (b : Degree) (x : ZFSet.{u}) :
    ZFSet.pair x (degreeSet b) ∈ globalGraph π ↔ x = degreeSet (π.symm b) := by
  rw [mem_globalGraph]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨hx,hbc⟩ := ZFSet.pair_inj.mp hc
    have hb := degreeSet_injective hbc
    have hc' : c = π.symm b := by rw [hb,π.symm_apply_apply]
    exact hx.trans (congrArg degreeSet hc')
  · intro hx
    refine ⟨π.symm b,?_⟩
    rw [hx,π.apply_symm_apply]

theorem image_degreeSet_mem_hull (a : ℕ → ZFSet.{u}) (π : Degree ≃o Degree)
    (hπ : globalGraph π ∈ hullSet a) (b : Degree) (hb : degreeSet b ∈ hullSet a) :
    degreeSet (π b) ∈ hullSet a ∧ degreeSet (π.symm b) ∈ hullSet a := by
  have he : ∀ i, cons (degreeSet b) (fun _ => globalGraph π) i ∈ hullSet a := by
    intro i; cases i <;> assumption
  constructor
  · apply unique_definable_mem a (fromBounded (.pairMem 1 0 2)) _ he
    · exact (bounded_univ _ _).mpr ((Formula.eval_pairMem _ _ _ _).mpr ((globalGraph_pair π b
      _).mpr rfl))
    · intro x hx
      exact (globalGraph_pair π b x).mp ((Formula.eval_pairMem _ _ _ _).mp ((bounded_univ _ _).mp
        hx))
  · apply unique_definable_mem a (fromBounded (.pairMem 0 1 2)) _ he
    · exact (bounded_univ _ _).mpr ((Formula.eval_pairMem _ _ _ _).mpr ((globalGraph_inverse_pair
      π b _).mpr rfl))
    · intro x hx
      exact (globalGraph_inverse_pair π b x).mp ((Formula.eval_pairMem _ _ _ _).mp ((bounded_univ
        _ _).mp hx))

end TuringRigidity.ElementaryModel

end OAI
