/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCollapseConditions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelNaturalNumbers

/-!
# Internal Collapse Conditions
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

/-- A set-coded finite initial-segment function with values in `A`. -/
def Prefix (A p : ZFSet.{u}) : Prop :=
  ∃ n : ℕ, TransitiveNameModel.FunctionGraph (natSet n) A p

theorem prefix_subset {A p : ZFSet.{u}} (hp : Prefix A p) : p ⊆ ZFSet.prod ZFSet.omega A := by
  obtain ⟨n,hp⟩ := hp
  intro z hz
  obtain ⟨i,hi,x,hx,rfl⟩ := hp.1 z hz
  obtain ⟨k,_,rfl⟩ := (mem_natSet n i).mp hi
  exact ZFSet.mem_prod.mpr ⟨natSet k,(mem_omega _).mpr ⟨k,rfl⟩,x,hx,rfl⟩

theorem prefix_empty (A : ZFSet.{u}) : Prefix A ∅ :=
  ⟨0,fun _ h => False.elim (ZFSet.notMem_empty _ h),fun _ h => False.elim (ZFSet.notMem_empty _ h)⟩

/-- Append the pair consisting of index `n` and value `x` to the graph `p`. -/
noncomputable def append (p : ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) : ZFSet.{u} :=
  p ∪ ({ZFSet.pair (natSet n) x} : ZFSet.{u})

theorem mem_append (p : ZFSet.{u}) (n : ℕ) (x z : ZFSet.{u}) :
    z ∈ append p n x ↔ z ∈ p ∨ z = ZFSet.pair (natSet n) x := by
  simp only [append,ZFSet.mem_union,ZFSet.mem_singleton]

theorem append_function {A p x : ZFSet.{u}} {n : ℕ}
    (hp : TransitiveNameModel.FunctionGraph (natSet n) A p) (hx : x ∈ A) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) A (append p n x) := by
  have hold {i y : ZFSet.{u}} (h : ZFSet.pair i y ∈ p) : i ∈ natSet n := by
    obtain ⟨j,hj,z,_,he⟩ := hp.1 _ h
    obtain ⟨rfl,_⟩ := ZFSet.pair_inj.mp he
    exact hj
  constructor
  · intro z hz
    rcases (mem_append p n x z).mp hz with hz|rfl
    · obtain ⟨i,hi,y,hy,rfl⟩ := hp.1 z hz
      exact ⟨i,ZFSet.mem_insert_iff.mpr (Or.inr hi),y,hy,rfl⟩
    · exact ⟨natSet n,ZFSet.mem_insert_iff.mpr (Or.inl rfl),x,hx,rfl⟩
  · intro i hi
    change i ∈ insert (natSet n) (natSet n) at hi
    rcases ZFSet.mem_insert_iff.mp hi with rfl|hi
    · refine ⟨x,hx,(mem_append _ _ _ _).mpr (Or.inr rfl),?_⟩
      intro y _ hy
      rcases (mem_append _ _ _ _).mp hy with hy|hy
      · exact False.elim ((Nat.lt_irrefl n) ((natSet_mem_natSet n n).mp (hold hy)))
      · exact (ZFSet.pair_inj.mp hy).2
    · obtain ⟨y,hy,hiy,hunique⟩ := hp.2 i hi
      refine ⟨y,hy,(mem_append _ _ _ _).mpr (Or.inl hiy),?_⟩
      intro z hz hiz
      rcases (mem_append _ _ _ _).mp hiz with hiz|hiz
      · exact hunique z hz hiz
      · have he := (ZFSet.pair_inj.mp hiz).1
        rw [he] at hi
        exact False.elim ((Nat.lt_irrefl n) ((natSet_mem_natSet n n).mp hi))

theorem append_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {p x : ZFSet.{u}} (hp : p ∈ M) (hx : x ∈ M) (n : ℕ) : append p n x ∈ M :=
  binary_union_mem M hM hT.pairing hT.union hp
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing
      (hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)) hx))

/-- Bounded formula asserting that `p` is a finite initial-segment function into `A`. -/
def prefixFormula (o A p : ℕ) : Formula := .existsMem o (.functionGraph (p+1) 0 (A+1))

theorem eval_prefixFormula (o A p : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega) :
    (prefixFormula o A p).Eval e ↔ Prefix (e A) (e p) := by
  simp only [prefixFormula,Formula.Eval,Formula.eval_functionGraph,cons_zero,cons_succ]
  rw [ho]
  exact ⟨fun ⟨n,hn,h⟩ => by obtain ⟨k,rfl⟩ := (mem_omega n).mp hn; exact ⟨k,h⟩,
    fun ⟨n,h⟩ => ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,h⟩⟩

theorem conditions_exist (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ c ∈ M, ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hA)
  let e := cons ZFSet.omega (fun _ => A)
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> assumption
  let c := ZFSet.sep (fun p => (prefixFormula 1 2 0).Eval (cons p e)) Q
  refine ⟨c,sep_mem M hM hS _ e he hQM,fun p => ?_⟩
  rw [ZFSet.mem_sep,eval_prefixFormula 1 2 0 (cons p e) rfl,hQ]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,prefix_subset h.2⟩,h.2⟩⟩

/-- The reverse-inclusion partial order on the ground-model labels of conditions. -/
@[instance_reducible] noncomputable def order (c : ZFSet.{u}) : PartialOrder (Conditions c) where
  le p q := label c q ⊆ label c p
  lt left right := label c right ⊆ label c left ∧ ¬ label c left ⊆ label c right
  le_refl _ := fun _ h => h
  le_trans _ _ _ hpq hqr := fun _ h => hpq (hqr h)
  le_antisymm p q hpq hqp := label_injective c (ZFSet.ext (fun z => ⟨fun h => hqp h,fun h => hpq
    h⟩))

attribute [local instance] order

/-- The preorder induced by the reverse-inclusion partial order on condition labels. -/
@[instance_reducible] noncomputable def collapsePreorder
    (conditionSet : ZFSet.{u}) : Preorder (Conditions conditionSet) :=
  (order conditionSet).toPreorder

attribute [local instance] collapsePreorder

/-- The `OrderTop` instance on set-coded conditions when the empty condition belongs to the
poset. -/
@[instance_reducible] noncomputable def top (c : ZFSet.{u}) (h0 : (∅ : ZFSet.{u}) ∈ c) : OrderTop
  (Conditions c) where
  top := equivShrink c ⟨∅,h0⟩
  le_top p := by
    have he : label c (equivShrink c ⟨∅,h0⟩) = ∅ := by simp [label]
    change label c (equivShrink c ⟨∅,h0⟩) ⊆ label c p
    rw [he]
    exact fun z hz => False.elim (ZFSet.notMem_empty z hz)

/-- The set-coded reverse-inclusion order relation on `c`. -/
noncomputable def orderSet (c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ c, ∃ q ∈ c, z = ZFSet.pair p q ∧ q ⊆ p) (ZFSet.prod c c)

theorem orderSet_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (hc : c ∈ M) : orderSet c ∈ M := by
  let e : ℕ → ZFSet.{u} := fun _ => c
  simpa only
    [orderSet,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,cons_zero,cons_succ,e]
    using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.subset 0 1)))) e (fun _ => hc)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hc hc)

theorem orderSet_pair (c : ZFSet.{u}) (p q : Conditions c) :
    ZFSet.pair (label c p) (label c q) ∈ orderSet c ↔ p ≤ q := by
  rw [orderSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,_,y,_,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact h
  · intro h
    exact ⟨ZFSet.mem_prod.mpr ⟨_,label_mem c p,_,label_mem c q,rfl⟩,
      _,label_mem c p,_,label_mem c q,rfl,h⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
