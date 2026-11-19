/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalUniformization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalChoice
public import LeanPool.TuringConeRigidity.SetModels.ModelProducts

/-!
# Internal Uniformization
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The relation fiber at `x`, restricted to the set `b`. -/
noncomputable def relationFiber (b r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair x y ∈ r) b

theorem relationFiber_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {b r x : ZFSet.{u}} (hb : b ∈ M) (hr : r ∈ M) (hx : x ∈ M) : relationFiber b r x ∈ M := by
  simpa only [relationFiber,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.pairMem 1 0 2) (cons x (fun _ => r))
      (by intro i; cases i <;> assumption) hb

/-- Bounded formula selecting from a relation fiber through the supplied selection graph. -/
def selectionFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.conj
      (.allMem 5 (.iff (.member 0 1) (.pairMem 3 0 9))) (.pairMem 0 1 7)))))

theorem eval_selectionFormula (z a b q f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    selectionFormula.Eval (cons z (cons a (cons b (cons q (cons f (cons r e)))))) ↔
      ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y ∧ ∃ s ∈ q,
        (∀ w ∈ b, w ∈ s ↔ ZFSet.pair x w ∈ r) ∧ ZFSet.pair s y ∈ f := by
  simp only [selectionFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ]

theorem internal_relation_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hAC : Choice M)
    {a b r : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) (hr : r ∈ M)
    (htotal : ∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ r) :
    ∃ g ∈ M, g ⊆ r ∧
      (∀ z ∈ g, ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y) ∧
      (∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ g ∧
        ∀ z ∈ b, ZFSet.pair x z ∈ g → z = y) := by
  obtain ⟨q,hq,f,hf,hfg,hqdef⟩ := internal_selector M hM hPow hS hAC hb
  let e := cons a (cons b (cons q (cons f (cons r (fun _ => a)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hb
    rcases i with _ | i
    · exact hq
    rcases i with _ | i
    · exact hf
    rcases i with _ | i
    · exact hr
    exact ha
  let g := ZFSet.sep (fun z => selectionFormula.Eval (cons z e)) (ZFSet.prod a b)
  have hg : g ∈ M := sep_mem M hM hS selectionFormula e he
    (product_mem M hM hP hU hPow hS ha hb)
  have hfiber (x : ZFSet.{u}) (hx : x ∈ a) : relationFiber b r x ∈ q := by
    apply (hqdef _).mpr
    obtain ⟨y,hy,hxy⟩ := htotal x hx
    exact ⟨relationFiber_mem M hM hS hb hr (hM a ha x hx),
      (fun _ hz => (ZFSet.mem_sep.mp hz).1),y,ZFSet.mem_sep.mpr ⟨hy,hxy⟩⟩
  have hfibereq (x s : ZFSet.{u}) (hs : s ∈ q)
      (hdef : ∀ w ∈ b, w ∈ s ↔ ZFSet.pair x w ∈ r) : s = relationFiber b r x := by
    apply ZFSet.ext
    intro w
    rw [relationFiber,ZFSet.mem_sep]
    constructor
    · intro hw
      have hwb := ((hqdef s).mp hs).2.1 hw
      exact ⟨hwb,(hdef w hwb).mp hw⟩
    · rintro ⟨hwb,hw⟩
      exact (hdef w hwb).mpr hw
  have hgpair (x y : ZFSet.{u}) : ZFSet.pair x y ∈ g ↔
      x ∈ a ∧ y ∈ b ∧ ZFSet.pair (relationFiber b r x) y ∈ f := by
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep]
    have eval := eval_selectionFormula (ZFSet.pair x y) a b q f r (fun _ => a)
    change selectionFormula.Eval (cons (ZFSet.pair x y) e) ↔ _ at eval
    rw [eval]
    constructor
    · rintro ⟨_,x',hx,y',hy,hp,s,hs,hdef,hsy⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      rw [hfibereq x s hs hdef] at hsy
      exact ⟨hx,hy,hsy⟩
    · rintro ⟨hx,hy,hsy⟩
      refine ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,
        relationFiber b r x,hfiber x hx,?_,hsy⟩
      intro w hw
      exact (ZFSet.mem_sep).trans (and_iff_right hw)
  have hgshape (z : ZFSet.{u}) (hz : z ∈ g) :
      ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y :=
    ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  refine ⟨g,hg,?_,hgshape,?_⟩
  · intro z hz
    obtain ⟨x,_,y,_,rfl⟩ := hgshape z hz
    have hsy := ((hgpair x y).mp hz).2.2
    obtain ⟨s,_,v,hv,heq⟩ := hfg.1 _ hsy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact (ZFSet.mem_sep.mp hv).2
  · intro x hx
    obtain ⟨y,hy,hsy,_⟩ := hfg.2 _ (hfiber x hx)
    have hyb := (ZFSet.mem_sep.mp hy).1
    refine ⟨y,hyb,(hgpair x y).mpr ⟨hx,hyb,hsy⟩,?_⟩
    intro z _ hxz
    exact hfg.functional ((hgpair x z).mp hxz).2.2 hsy

end TuringRigidity.BoundedSetTheory

end OAI
