/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetPresentationDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelProducts
public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Set Presentation Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetPresentationDecoding
open BoundedSetTheory TransitiveNameModel
universe u

/-- The relation class of `x` inside `d`. -/
noncomputable def classSet (d E x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair x y ∈ E) d

@[simp] theorem mem_classSet (d E x y : ZFSet.{u}) :
    y ∈ classSet d E x ↔ y ∈ d ∧ ZFSet.pair x y ∈ E := ZFSet.mem_sep

/-- Bounded formula asserting that `c` is exactly the relation class of `x` inside `d`. -/
def classFormula (c x d E : ℕ) : Formula :=
  .conj (.subset c d) (.allMem d (.iff (.member 0 (c+1)) (.pairMem (x+1) 0 (E+1))))

@[simp] theorem eval_classFormula (c x d E : ℕ) (e : ℕ → ZFSet.{u}) :
    (classFormula c x d E).Eval e ↔ e c = classSet (e d) (e E) (e x) := by
  simp only [classFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext
    intro y
    rw [mem_classSet]
    exact ⟨fun hy => ⟨hsub hy,(h y (hsub hy)).mp hy⟩,
      fun hy => (h y hy.1).mpr hy.2⟩
  · intro h
    rw [h]
    exact ⟨fun _ hy => (mem_classSet _ _ _ _).mp hy |>.1,
      fun y hy => by simp [hy]⟩

theorem class_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {d E x : ZFSet.{u}} (hd : d ∈ M) (hE : E ∈ M) (hx : x ∈ M) :
    classSet d E x ∈ M := by
  let e := cons x (cons E (fun _ => d))
  have he : ∀ i, e i ∈ M := by intro i; cases i with
    | zero => exact hx
    | succ i => cases i <;> simp [e,hd,hE]
  simpa only [Formula.eval_pairMem,e,cons_zero,cons_succ,classSet] using
    sep_mem M hM hS (.pairMem 1 0 2) e he hd

/-- The family of relation classes represented by the elements of `a`. -/
noncomputable def quotientSet (d E a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun c => ∃ x ∈ a, c = classSet d E x) (ZFSet.powerset d)

@[simp] theorem mem_quotientSet (d E a c : ZFSet.{u}) :
    c ∈ quotientSet d E a ↔ ∃ x ∈ a, c = classSet d E x := by
  simp only [quotientSet,ZFSet.mem_sep,ZFSet.mem_powerset]
  constructor
  · exact And.right
  · rintro ⟨x,hx,rfl⟩
    exact ⟨fun y hy => (mem_classSet _ _ _ _).mp hy |>.1,⟨x,hx,rfl⟩⟩

theorem quotient_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M)
    {d E a : ZFSet.{u}} (hd : d ∈ M) (hE : E ∈ M) (ha : a ∈ M) :
    quotientSet d E a ∈ M := by
  obtain ⟨p,hp,hpdef⟩ := internal_power M hM hPow hd
  let e := cons a (cons d (fun _ => E))
  have he : ∀ i, e i ∈ M := by intro i; cases i with
    | zero => exact ha
    | succ i => cases i <;> simp [e,hd,hE]
  let φ : Formula := .existsMem 1 (classFormula 1 0 3 4)
  have h := sep_mem M hM hS φ e he hp
  have eq : ZFSet.sep (fun c => φ.Eval (cons c e)) p = quotientSet d E a := by
    apply ZFSet.ext
    intro c
    simp only [ZFSet.mem_sep,φ,Formula.Eval,eval_classFormula,cons_zero,cons_succ,e,
      mem_quotientSet]
    constructor
    · exact And.right
    · rintro ⟨x,hx,rfl⟩
      refine ⟨(hpdef _).mpr ⟨class_mem M hM hS hd hE (hM a ha x hx),?_⟩,⟨x,hx,rfl⟩⟩
      intro y hy
      exact (mem_classSet _ _ _ _).mp hy |>.1
  exact eq ▸ h

/-- The relation on classes induced by pairs in `R` whose two representatives belong to `a`. -/
noncomputable def actionGraph (d E a R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ a, ∃ y ∈ a,
    ZFSet.pair x y ∈ R ∧ z = ZFSet.pair (classSet d E x) (classSet d E y))
    (ZFSet.prod (quotientSet d E a) (quotientSet d E a))

@[simp] theorem mem_actionGraph (d E a R z : ZFSet.{u}) :
    z ∈ actionGraph d E a R ↔ ∃ x ∈ a, ∃ y ∈ a,
      ZFSet.pair x y ∈ R ∧ z = ZFSet.pair (classSet d E x) (classSet d E y) := by
  rw [actionGraph,ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨x,hx,y,hy,hxy,rfl⟩ := h
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_quotientSet _ _ _ _).mpr ⟨x,hx,rfl⟩,
      (mem_quotientSet _ _ _ _).mpr ⟨y,hy,rfl⟩⟩,⟨x,hx,y,hy,hxy,rfl⟩⟩

/-- Bounded formula describing the induced relation graph on represented classes. -/
def actionFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.pairMem 1 0 6)
    (.existsMem 7 (.existsMem 8 (.conj (classFormula 1 3 6 7)
      (.conj (classFormula 0 2 6 7) (.orderedPair 4 1 0)))))))

theorem eval_actionFormula (z a d E R q : ZFSet.{u}) :
    actionFormula.Eval (cons z (cons a (cons d (cons E (cons R (fun _ => q)))))) ↔
    ∃ x ∈ a, ∃ y ∈ a, ZFSet.pair x y ∈ R ∧
      ∃ c ∈ q, ∃ b ∈ q, c = classSet d E x ∧ b = classSet d E y ∧ z = ZFSet.pair c b := by
  simp only [actionFormula,Formula.Eval,Formula.eval_pairMem,eval_classFormula,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem action_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d E a R : ZFSet.{u}} (hd : d ∈ M) (hE : E ∈ M) (ha : a ∈ M) (hR : R ∈ M) :
    actionGraph d E a R ∈ M := by
  let q := quotientSet d E a
  have hq := quotient_mem M hM hPow hS hd hE ha
  have hprod := product_mem M hM hP hU hPow hS hq hq
  let e := cons a (cons d (cons E (cons R (fun _ => q))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp [e,ha,hd,hE,hR,q,hq]
  have h := sep_mem M hM hS actionFormula e he hprod
  have eq : ZFSet.sep (fun z => actionFormula.Eval (cons z e)) (ZFSet.prod q q) =
      actionGraph d E a R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_actionGraph,show actionFormula.Eval (cons z e) ↔ _ from
      eval_actionFormula z a d E R q]
    constructor
    · rintro ⟨_,x,hx,y,hy,hR,c,hc,b,hb,rfl,rfl,hz⟩
      exact ⟨x,hx,y,hy,hR,hz⟩
    · intro h
      obtain ⟨x,hx,y,hy,hxy,rfl⟩ := h
      have hxq : classSet d E x ∈ q := (mem_quotientSet _ _ _ _).mpr ⟨x,hx,rfl⟩
      have hyq : classSet d E y ∈ q := (mem_quotientSet _ _ _ _).mpr ⟨y,hy,rfl⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hxq,hyq⟩,
        ⟨x,hx,y,hy,hxy,_,hxq,_,hyq,rfl,rfl,rfl⟩⟩
  exact eq ▸ h

end TuringRigidity.SetPresentationDecoding

end OAI
