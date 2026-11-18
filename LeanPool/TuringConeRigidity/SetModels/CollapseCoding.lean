/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CollapseCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapseCollection

/-!
# Collapse Coding
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

/-- The set-coded graph `f` consists exactly of the pairs `(x, j x)` for `x` in `a`. -/
def Presents (a f : ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ z, z ∈ f ↔ ∃ x ∈ a, z = ZFSet.pair x (j x)

theorem Presents.pair_iff {a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents a f j) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ f ↔ x ∈ a ∧ y = j x := by
  rw [hf]
  constructor
  · rintro ⟨z,hz,he⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hz,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact ⟨x,hx,rfl⟩

/-- Transport membership on `a` to a relation on `d` through the graph `f`. -/
noncomputable def codedRelation (d a f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ u ∈ d, ∃ v ∈ d, z = ZFSet.pair u v ∧
    ∃ x ∈ a, ∃ y ∈ a, x ∈ y ∧ ZFSet.pair x u ∈ f ∧ ZFSet.pair y v ∈ f) (ZFSet.prod d d)

/-- Bounded formula describing the membership relation transported through a coded graph. -/
def codedFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
    (.existsMem 4 (.existsMem 5 (.conj (.member 1 0)
      (.conj (.pairMem 1 3 7) (.pairMem 0 2 7)))))))

theorem codedRelation_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d a f : ZFSet.{u}} (hd : d ∈ M) (ha : a ∈ M) (hf : f ∈ M) :
    codedRelation d a f ∈ M := by
  let e := cons d (cons a (cons f (fun _ => d)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hf
    exact hd
  simpa only [codedFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    e,cons_zero,cons_succ,codedRelation] using
    sep_mem M hM hS codedFormula e he (product_mem M hM hP hU hPow hS hd hd)

theorem codedRelation_on (d a f : ZFSet.{u}) : On d (codedRelation d a f) :=
  fun _ hz => (ZFSet.mem_sep.mp hz).1

theorem codedRelation_pair {d a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents a f j) (hj : ∀ x ∈ a, j x ∈ d) (u v : ZFSet.{u}) :
    ZFSet.pair u v ∈ codedRelation d a f ↔
      ∃ x ∈ a, ∃ y ∈ a, x ∈ y ∧ u = j x ∧ v = j y := by
  rw [codedRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,u',_,v',_,hp,x,hx,y,hy,hxy,hxu,hyv⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨x,hx,y,hy,hxy,((hf.pair_iff x u).mp hxu).2,((hf.pair_iff y v).mp hyv).2⟩
  · rintro ⟨x,hx,y,hy,hxy,rfl,rfl⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨_,hj x hx,_,hj y hy,rfl⟩,
      _,hj x hx,_,hj y hy,rfl,x,hx,y,hy,hxy,
      (hf.pair_iff x _).mpr ⟨hx,rfl⟩,(hf.pair_iff y _).mpr ⟨hy,rfl⟩⟩

theorem codedRelation_wellFounded {d a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents a f j) (hj : ∀ x ∈ a, j x ∈ d)
    (hi : ∀ x ∈ a, ∀ y ∈ a, j x = j y → x = y) :
    WellFounded (Rel d (codedRelation d a f)) := by
  classical
  let F : ZFSet.{u} → ZFSet.{u} := fun u =>
    if h : ∃ x ∈ a, j x = u then h.choose else ∅
  have hF (x : ZFSet.{u}) (hx : x ∈ a) : F (j x) = x := by
    have h : ∃ y ∈ a, j y = j x := ⟨x,hx,rfl⟩
    simp only [F,dite_eq_left h]
    exact hi _ h.choose_spec.1 x hx h.choose_spec.2
  apply (show WellFounded (fun y x => F y ∈ F x) from InvImage.wf F ZFSet.mem_wf).mono
  intro u v huv
  obtain ⟨x,hx,y,hy,hxy,rfl,rfl⟩ := (codedRelation_pair hf hj u v).mp huv.2
  simpa only [hF x hx,hF y hy] using hxy

theorem codedRelation_value {d a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (ha : Transitive a) (hf : Presents a f j) (hj : ∀ x ∈ a, j x ∈ d)
    (hi : ∀ x ∈ a, ∀ y ∈ a, j x = j y → x = y)
    (wf : WellFounded (Rel d (codedRelation d a f)))
    (x : ZFSet.{u}) (hx : x ∈ a) : value d (codedRelation d a f) wf (j x) = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [mem_value]
    constructor
    · rintro ⟨u,_,hux,hz⟩
      obtain ⟨y,hy,w,hw,hyw,rfl,hwx⟩ := (codedRelation_pair hf hj u (j x)).mp hux
      have hwx' : x = w := hi x hx w hw hwx
      subst w
      rw [ih y hyw hy] at hz
      exact hz ▸ hyw
    · intro hz
      have hza := ha x hx z hz
      refine ⟨j z,hj z hza,(codedRelation_pair hf hj _ _).mpr
        ⟨z,hza,x,hx,hz,rfl,rfl⟩,?_⟩
      exact (ih z hz hza).symm

theorem internal_small_transitive_bound (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hd : d ∈ M) :
    ∃ W ∈ M, ∀ a ∈ M, Transitive a → ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u},
      Presents a f j → (∀ x ∈ a, j x ∈ d) →
      (∀ x ∈ a, ∀ y ∈ a, j x = j y → x = y) → a ⊆ W := by
  obtain ⟨W,hW,hbound⟩ := internal_value_bound M d hM hP hU hPow hS hR hd
  refine ⟨W,hW,?_⟩
  intro a ha hat f hf j hfj hj hi x hx
  have hr := codedRelation_mem M hM hP hU hPow hS.bounded hd ha hf
  have wf := codedRelation_wellFounded hfj hj hi
  have hv := hbound _ hr (codedRelation_on d a f) wf (j x) (hj x hx)
  rw [codedRelation_value hat hfj hj hi wf x hx] at hv
  exact hv

end TuringRigidity.RelationCollapse

end OAI
