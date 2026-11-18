/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryDefinableSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.DegreeSetFormula
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction
public import LeanPool.TuringConeRigidity.SetModels.SetDegreeDecoding

/-!
# Elementary Definable Sets
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm SetDegreeDecoding
universe u

theorem unique_definable_mem (a : ℕ → ZFSet.{u}) (p : SentenceForm) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ hullSet a) (b : ZFSet.{u}) (hb : p.Sat Set.univ (cons b e))
    (hu : ∀ x, p.Sat Set.univ (cons x e) → x = b) : b ∈ hullSet a := by
  have hen : ∀ i, e i ∈ hull a := fun i => (mem_hullSet a _).mp (he i)
  have hs := (hull_elementary a (.ex p) e hen).mpr ⟨b,Set.mem_univ _,hb⟩
  obtain ⟨x,hx,hp⟩ := hs
  have ht := (hull_elementary a p (cons x e)
    (by intro i; cases i <;> simp [cons,hen,hx])).mp hp
  exact hu x ht ▸ (mem_hullSet a x).mpr hx

theorem unorderedPair_mem_hull (a : ℕ → ZFSet.{u}) {x y : ZFSet.{u}}
    (hx : x ∈ hullSet a) (hy : y ∈ hullSet a) : ({x,y} : ZFSet.{u}) ∈ hullSet a := by
  apply unique_definable_mem a (fromBounded (.unorderedPair 0 1 2)) (cons x (fun _ => y))
    (by intro i; cases i <;> assumption)
  · exact (bounded_univ _ _).mpr ((Formula.eval_unorderedPair _ _ _ _).mpr rfl)
  · intro z hz
    exact (Formula.eval_unorderedPair _ _ _ _).mp ((bounded_univ _ _).mp hz)

theorem orderedPair_mem_hull (a : ℕ → ZFSet.{u}) {x y : ZFSet.{u}}
    (hx : x ∈ hullSet a) (hy : y ∈ hullSet a) : ZFSet.pair x y ∈ hullSet a := by
  have hxx := unorderedPair_mem_hull a hx hx
  have hxy := unorderedPair_mem_hull a hx hy
  simpa [ZFSet.pair] using unorderedPair_mem_hull a hxx hxy

theorem collapse_unorderedPair (a : ℕ → ZFSet.{u}) {x y : ZFSet.{u}}
    (hx : x ∈ hullSet a) (hy : y ∈ hullSet a) :
    structureMap (hullSet a) ({x,y} : ZFSet.{u}) =
      ({structureMap (hullSet a) x,structureMap (hullSet a) y} : ZFSet.{u}) := by
  apply ZFSet.ext; intro z
  rw [structureMap,mem_value,ZFSet.mem_pair]
  constructor
  · rintro ⟨w,_,hw,hzw⟩
    have hwp := ((membershipRelation_pair _ _ _).mp hw).2.2
    rcases ZFSet.mem_pair.mp hwp with rfl|rfl
    · exact Or.inl hzw
    · exact Or.inr hzw
  · intro hz
    have hp := unorderedPair_mem_hull a hx hy
    rcases hz with hxz|hyz
    · exact ⟨x,hx,(membershipRelation_pair _ _ _).mpr ⟨hx,hp,ZFSet.mem_pair.mpr (Or.inl rfl)⟩,hxz⟩
    · exact ⟨y,hy,(membershipRelation_pair _ _ _).mpr ⟨hy,hp,ZFSet.mem_pair.mpr (Or.inr rfl)⟩,hyz⟩

theorem collapse_orderedPair (a : ℕ → ZFSet.{u}) {x y : ZFSet.{u}}
    (hx : x ∈ hullSet a) (hy : y ∈ hullSet a) :
    structureMap (hullSet a) (ZFSet.pair x y) =
      ZFSet.pair (structureMap (hullSet a) x) (structureMap (hullSet a) y) := by
  have hxx := unorderedPair_mem_hull a hx hx
  have hxy := unorderedPair_mem_hull a hx hy
  have hh := collapse_unorderedPair a hxx hxy
  rw [collapse_unorderedPair a hx hx,collapse_unorderedPair a hx hy] at hh
  simpa [ZFSet.pair] using hh

/-- The ambient set of all subsets of omega. -/
noncomputable def ambientRealSet : ZFSet.{u} := ZFSet.powerset ZFSet.omega
/-- The ambient set of all binary relations on omega. -/
noncomputable def ambientGraphBound : ZFSet.{u} := ZFSet.powerset (ZFSet.prod ZFSet.omega
  ZFSet.omega)

theorem ambient_real_decode (x : ZFSet.{u}) (hx : x ∈ ambientRealSet) :
    ∃ B : Oracle, realCode B = x :=
  ⟨decodeReal x,realCode_decodeReal (ZFSet.mem_powerset.mp hx)⟩

theorem ambient_graph_bound (f : ℕ → ℕ) (k : ℕ) : finiteNaturalGraph.{u} f k ∈ ambientGraphBound
  := by
  apply ZFSet.mem_powerset.mpr
  intro x hx
  obtain ⟨n,_,rfl⟩ := (mem_finiteNaturalGraph f k x).mp hx
  exact ZFSet.mem_prod.mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,
    natSet (f n),(mem_omega _).mpr ⟨f n,rfl⟩,rfl⟩

theorem ambient_degreeCode (A : Oracle) : degreeCode ambientRealSet.{u} A = degreeSet (degree A)
  := by
  apply ZFSet.ext; intro x
  rw [degreeCode,ZFSet.mem_sep,mem_degreeSet]
  exact ⟨And.right,fun ⟨B,hB,hBA⟩ =>
    ⟨hB.symm ▸ ZFSet.mem_powerset.mpr (realCode_subset B),B,hB,hBA⟩⟩

theorem degreeSet_mem_hull (a : ℕ → ZFSet.{u})
    (hω : ZFSet.omega ∈ hullSet a) (h0 : natSet 0 ∈ hullSet a)
    (hR : ambientRealSet ∈ hullSet a) (hQ : ambientGraphBound ∈ hullSet a)
    {A : Oracle} (hA : realCode A ∈ hullSet a) : degreeSet (degree A) ∈ hullSet a := by
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := cons ZFSet.omega (cons ambientGraphBound (cons (natSet 0) (cons ambientRealSet (fun _
    => realCode A))))
  have he : ∀ i, e i ∈ hullSet a := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQ
    rcases i with _ | i
    · exact h0
    rcases i with _ | i
    · exact hR
    exact hA
  let p := fromBounded (Formula.degreeSet φ 1 2 3 4 5 0)
  have hp (x : ZFSet.{u}) : p.Sat Set.univ (cons x e) ↔ x = degreeSet (degree A) := by
    rw [bounded_univ,Formula.degreeSet_spec hφ 1 2 3 4 5 0 _ rfl ambient_graph_bound rfl
      ambient_real_decode A rfl]
    simp only [cons_zero,cons_succ,e,ambient_degreeCode]
  exact unique_definable_mem a p e he _ ((hp _).mpr rfl) (fun x hx => (hp x).mp hx)

end TuringRigidity.ElementaryModel

end OAI
