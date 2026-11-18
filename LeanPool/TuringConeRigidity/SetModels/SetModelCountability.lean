/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelCountability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelInternalRelations

/-!
# Set Model Countability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open BoundedDefinability SetModelSyntax SetModelSequences
universe u
noncomputable section

/-- A set-coded total single-valued function from `a` to `b`. -/
def FunctionGraph (f a b : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y) ∧
  (∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ b, ZFSet.pair x z ∈ f → z = y)

/-- Bounded formula asserting that a function graph from `a` to `b` is onto. -/
def ontoFormula (f a b : ℕ) : Formula :=
  .conj (.functionGraph f a b) (.allMem b (.existsMem (a+1) (.pairMem 0 1 (f+2))))

@[simp] theorem eval_ontoFormula (f a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (ontoFormula f a b).Eval e ↔ FunctionGraph (e f) (e a) (e b) ∧
      ∀ y ∈ e b, ∃ x ∈ e a, ZFSet.pair x y ∈ e f := by
  simp only [ontoFormula,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,cons_zero,cons_succ,FunctionGraph]

/-- The model contains a graph it internally recognizes as a surjection from omega onto `a`. -/
def InternallyCountable (M a : ZFSet.{u}) : Prop :=
  ∃ f ∈ M, (ontoFormula 0 1 2).Realize M (cons f (cons ZFSet.omega (fun _ => a)))

/-- Bounded formula asserting a function from `a` to `b` whose chosen value belongs to each
input set. -/
def choiceFormula (f a b : ℕ) : Formula :=
  .conj (.functionGraph f a b) (.allMem a (.existsMem 0 (.pairMem 1 0 (f+2))))

@[simp] theorem eval_choiceFormula (f a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (choiceFormula f a b).Eval e ↔ FunctionGraph (e f) (e a) (e b) ∧
      ∀ x ∈ e a, ∃ y ∈ x, ZFSet.pair x y ∈ e f := by
  simp only [choiceFormula,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,cons_zero,cons_succ,FunctionGraph]

/-- The model internally supplies a choice function for every internally nonempty family
belonging to it. -/
def InternalChoice (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, (∀ x ∈ M, x ∈ a → ∃ y ∈ M, y ∈ x) →
    ∃ f ∈ M, (choiceFormula 0 1 2).Realize M
      (cons f (cons a (fun _ => ZFSet.sUnion a)))

variable {M : ZFSet.{u}}

theorem countable_graph (C : Context M) {a : ZFSet.{u}} (ha : a ∈ M)
    (hc : InternallyCountable M a) :
    ∃ f ∈ M, FunctionGraph f ZFSet.omega a ∧
      ∀ y ∈ a, ∃ n : ℕ, ZFSet.pair (natSet n) y ∈ f := by
  obtain ⟨f,hf,hfc⟩ := hc
  have he : ∀ i, cons f (cons ZFSet.omega (fun _ => a)) i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [hf,C.omega_mem,ha]
  have hh := ((ontoFormula 0 1 2).absolute M C.transitive _ he).mp hfc
  rw [eval_ontoFormula] at hh
  refine ⟨f,hf,hh.1,?_⟩
  intro y hy
  simpa only [cons_zero,cons_succ,omega_exists] using hh.2 y hy

theorem choice_graph (C : Context M) (hCh : InternalChoice M)
    {a : ZFSet.{u}} (ha : a ∈ M) (hne : ∀ x ∈ a, ∃ y, y ∈ x) :
    ∃ f ∈ M, FunctionGraph f a (ZFSet.sUnion a) ∧
      ∀ x ∈ a, ∃ y ∈ x, ZFSet.pair x y ∈ f := by
  obtain ⟨f,hf,hfc⟩ := hCh a ha (fun x hx hxa => by
    obtain ⟨y,hy⟩ := hne x hxa
    exact ⟨y,C.transitive x hx y hy,hy⟩)
  have hu := union_mem M C.transitive C.union ha
  have he : ∀ i, cons f (cons a (fun _ => ZFSet.sUnion a)) i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [hf,ha,hu]
  exact ⟨f,hf,(eval_choiceFormula 0 1 2 _).mp
    (((choiceFormula 0 1 2).absolute M C.transitive _ he).mp hfc)⟩

theorem FunctionGraph.unique {f a b x y z : ZFSet.{u}} (h : FunctionGraph f a b)
    (hx : x ∈ a) (hy : y ∈ b) (hz : z ∈ b)
    (hxy : ZFSet.pair x y ∈ f) (hxz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨v,hv,hxv,hu⟩ := h.2 x hx
  exact (hu y hy hxy).trans (hu z hz hxz).symm

theorem composition_mem (C : Context M) {a b c f g : ZFSet.{u}}
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    ∃ q ∈ M, ∀ z, z ∈ q ↔ ∃ x ∈ a, ∃ y ∈ b, ∃ t ∈ c,
      z = ZFSet.pair x t ∧ ZFSet.pair x y ∈ f ∧ ZFSet.pair y t ∈ g := by
  let P := fun e : ℕ → ZFSet.{u} => ∃ x ∈ a, ∃ y ∈ b, ∃ t ∈ c,
    e 0 = ZFSet.pair x t ∧ ZFSet.pair x y ∈ f ∧ ZFSet.pair y t ∈ g
  have hP : Definable M P :=
    ((((orderedPair_definable C 3 2 0).and
      ((pairMem_param hf 2 1).and (pairMem_param hg 1 0))).existsParam hc).existsParam
        hb).existsParam ha
  let q := ZFSet.sep (fun z => P (cons z (fun _ => ZFSet.omega))) (ZFSet.prod a c)
  refine ⟨q,hP.sep_mem C _ (fun _ => C.omega_mem) (C.prod_mem ha hc),?_⟩
  intro z
  simp only [q,ZFSet.mem_sep,P,cons_zero]
  constructor
  · exact And.right
  · rintro ⟨x,hx,y,hy,t,ht,rfl,hf,hg⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,ht⟩,x,hx,y,hy,t,ht,rfl,hf,hg⟩

end
end TuringRigidity.SetModelCountability

end OAI
