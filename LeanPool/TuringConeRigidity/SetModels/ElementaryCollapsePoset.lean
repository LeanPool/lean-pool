/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryCollapsePoset.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryDefinableSets
public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeSyntax
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseConditions
public import LeanPool.TuringConeRigidity.SetModels.ElementaryRealModel

/-!
# Elementary Collapse Poset
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm
open FullSetForcing InternalCollapse
universe u

theorem definedSet_univ (s : ℕ) (p : Formula) (e : ℕ → ZFSet.{u}) :
    (definedSet s p).Sat Set.univ e ↔ ∀ x, x ∈ e s ↔ p.Eval (cons x e) := by
  simp only [definedSet,sat_all,sat_iff,Sat,bounded_univ,cons_zero,cons_succ,
    Set.mem_univ,forall_const]

theorem collapse_bounded_eval (a : ℕ → ZFSet.{u}) (p : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ hullSet a) :
    p.Eval (fun i => structureMap (hullSet a) (e i)) ↔ p.Eval e := by
  have h := collapsed_hull_elementary a (fromBounded p) e he
  rw [bounded_sat,Formula.absolute _ _ (collapsed_transitive _) _
    (fun i => (mem_collapsed _ _).mpr ⟨e i,he i,rfl⟩),bounded_univ] at h
  exact h

/-- The set-coded finite initial-segment functions into `A`. -/
noncomputable def ambientConditions (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (Prefix A) (ZFSet.powerset (ZFSet.prod ZFSet.omega A))

theorem mem_ambientConditions (A p : ZFSet.{u}) : p ∈ ambientConditions A ↔ Prefix A p := by
  rw [ambientConditions,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (prefix_subset h),h⟩⟩

theorem ambientConditions_def (A c : ZFSet.{u}) :
    (definedSet 0 (prefixFormula 3 2 0)).Sat Set.univ
      (cons c (cons A (fun _ => ZFSet.omega))) ↔ c = ambientConditions A := by
  rw [definedSet_univ]
  have hs (p : ZFSet.{u}) := eval_prefixFormula 3 2 0
    (cons p (cons c (cons A (fun _ => ZFSet.omega)))) rfl
  simp only [hs,cons_zero,cons_succ]
  exact ⟨fun h => ZFSet.ext (fun p => (h p).trans (mem_ambientConditions A p).symm),
    fun h p => h ▸ mem_ambientConditions A p⟩

theorem ambientConditions_mem_hull (a : ℕ → ZFSet.{u})
    (hω : ZFSet.omega ∈ hullSet a) {A : ZFSet.{u}} (hA : A ∈ hullSet a) :
    ambientConditions A ∈ hullSet a := by
  exact unique_definable_mem a (definedSet 0 (prefixFormula 3 2 0))
    (cons A (fun _ => ZFSet.omega)) (by intro i; cases i <;> assumption)
    _ ((ambientConditions_def A _).mpr rfl) (fun c hc => (ambientConditions_def A c).mp hc)

theorem collapse_ambientConditions (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a)
    {A : ZFSet.{u}} (hA : A ∈ hullSet a) :
    ∀ p, p ∈ structureMap (hullSet a) (ambientConditions A) ↔
      p ∈ collapsed (hullSet a) ∧ Prefix (structureMap (hullSet a) A) p := by
  let e := cons (ambientConditions A) (cons A (fun _ => ZFSet.omega))
  have hc := ambientConditions_mem_hull a hω hA
  have he : ∀ i, e i ∈ hullSet a := by
    intro i; rcases i with _|_|i
    · exact hc
    · exact hA
    · exact hω
  have ht := (collapsed_hull_elementary a (definedSet 0 (prefixFormula 3 2 0)) e he).mpr
    ((ambientConditions_def A _).mpr rfl)
  have hm := collapsed_transitive (hullSet a)
  have hei : ∀ i, structureMap (hullSet a) (e i) ∈ collapsed (hullSet a) :=
    fun i => (mem_collapsed _ _).mpr ⟨e i,he i,rfl⟩
  have h := (definedSet_spec _ hm 0 _ _ hei).mp ht
  have hω' := hull_omega_fixed a hn hω
  have hs (p : ZFSet.{u}) (hp : p ∈ collapsed (hullSet a)) :
      p ∈ structureMap (hullSet a) (ambientConditions A) ↔
      Prefix (structureMap (hullSet a) A) p :=
    (h p hp).trans (eval_prefixFormula 3 2 0
      (cons p (fun i => structureMap (hullSet a) (e i))) hω')
  intro p
  exact ⟨fun hp => ⟨hm _ (hei 0) _ hp,(hs p (hm _ (hei 0) _ hp)).mp hp⟩,
    fun hp => (hs p hp.1).mpr hp.2⟩

/-- Bounded formula describing a reverse-inclusion pair of coded conditions. -/
def orderMember (c z : ℕ) : Formula :=
  .existsMem c (.existsMem (c+1) (.conj (.orderedPair (z+2) 1 0) (.subset 0 1)))

theorem eval_orderMember (c z : ℕ) (e : ℕ → ZFSet.{u}) :
    (orderMember c z).Eval e ↔ e z ∈ orderSet (e c) := by
  simp only [orderMember,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
    cons_zero,cons_succ,orderSet,ZFSet.mem_sep]
  exact ⟨fun ⟨p,hp,q,hq,hz,hpq⟩ =>
    ⟨hz ▸ ZFSet.mem_prod.mpr ⟨p,hp,q,hq,rfl⟩,p,hp,q,hq,hz,hpq⟩,And.right⟩

theorem orderSet_mem_hull (a : ℕ → ZFSet.{u}) {c : ZFSet.{u}} (hc : c ∈ hullSet a) :
    orderSet c ∈ hullSet a := by
  have hs (x : ZFSet.{u}) : (definedSet 0 (orderMember 2 0)).Sat Set.univ
      (cons x (fun _ => c)) ↔ x = orderSet c := by
    rw [definedSet_univ]
    simp only [eval_orderMember,cons_zero,cons_succ]
    exact ZFSet.ext_iff.symm
  exact unique_definable_mem a (definedSet 0 (orderMember 2 0))
    (fun _ => c) (fun _ => hc) _ ((hs _).mpr rfl) (fun x hx => (hs x).mp hx)

theorem collapse_orderSet (a : ℕ → ZFSet.{u}) {c : ZFSet.{u}} (hc : c ∈ hullSet a) :
    structureMap (hullSet a) (orderSet c) = orderSet (structureMap (hullSet a) c) := by
  let e := cons (orderSet c) (fun _ => c)
  have he : ∀ i, e i ∈ hullSet a := by
    intro i; cases i
    · exact orderSet_mem_hull a hc
    exact hc
  have hi : ∀ i, structureMap (hullSet a) (e i) ∈ collapsed (hullSet a) :=
    fun i => (mem_collapsed _ _).mpr ⟨e i,he i,rfl⟩
  have hs : (definedSet 0 (orderMember 2 0)).Sat Set.univ e := by
    rw [definedSet_univ]
    intro x
    exact (eval_orderMember 2 0 (cons x e)).symm
  have ht := (collapsed_hull_elementary a _ e he).mpr hs
  exact (definedSet_unique _ (collapsed_transitive _) 0 _ _ hi
    (orderSet (structureMap (hullSet a) c))
    (orderSet_mem _ (collapsed_transitive _) (collapsed_hull_sourceT a) (hi 1))
    (fun x _ => eval_orderMember 2 0 _)).mp ht

theorem collapse_selected_condition (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a)
    {A p : ZFSet.{u}} (hA : A ∈ hullSet a) (hp : p ∈ hullSet a)
    (hpc : p ∈ ambientConditions A) :
    structureMap (hullSet a) p ∈ structureMap (hullSet a) (ambientConditions A) ∧
    Prefix (structureMap (hullSet a) A) (structureMap (hullSet a) p) := by
  have h := (collapse_membership _ (hullSet_extensional a) _ hp _
    (ambientConditions_mem_hull a hω hA)).mpr hpc
  exact ⟨h,((collapse_ambientConditions a hn hω hA _).mp h).2⟩

end TuringRigidity.ElementaryModel

end OAI
