/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SetRankCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations
public import Mathlib.SetTheory.ZFC.Rank

/-!
# Set Rank Certificate
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetRankCertificate
open BoundedSetTheory TransitiveNameModel
universe u
noncomputable section

def RankMap (d r b g : ZFSet.{u}) : Prop :=
  ((∀ z ∈ g, ∃ x ∈ d, ∃ y ∈ b, z = ZFSet.pair x y) ∧
    (∀ x ∈ d, ∃ y ∈ b, ZFSet.pair x y ∈ g ∧
      ∀ z ∈ b, ZFSet.pair x z ∈ g → z = y)) ∧
  (∀ x ∈ d, ∀ y ∈ d, ∀ a ∈ b, ∀ c ∈ b,
    ZFSet.pair x y ∈ r → ZFSet.pair x a ∈ g → ZFSet.pair y c ∈ g → a ∈ c)

def rankFormula (d r b g : ℕ) : Formula :=
  .conj (.functionGraph g d b)
    (.allMem d (.allMem (d+1) (.allMem (b+2) (.allMem (b+3)
      (.imp (.pairMem 3 2 (r+4))
        (.imp (.pairMem 3 1 (g+4)) (.imp (.pairMem 2 0 (g+4)) (.member 1 0))))))))

theorem eval_rankFormula (d r b g : ℕ) (e : ℕ → ZFSet.{u}) :
    (rankFormula d r b g).Eval e ↔ RankMap (e d) (e r) (e b) (e g) := by
  simp only [rankFormula,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ,RankMap]

theorem rankMap_sound {α : Type u} {rel : α → α → Prop} {d r b g : ZFSet.{u}}
    (e : α → ZFSet.{u}) (hd : ∀ x, e x ∈ d)
    (hr : ∀ x y, rel x y → ZFSet.pair (e x) (e y) ∈ r) (h : RankMap d r b g) :
    WellFounded rel := by
  let rank : α → ZFSet.{u} := fun x => (h.1.2 (e x) (hd x)).choose
  have hb (x) : rank x ∈ b := (h.1.2 (e x) (hd x)).choose_spec.1
  have hg (x) : ZFSet.pair (e x) (rank x) ∈ g := (h.1.2 (e x) (hd x)).choose_spec.2.1
  have hm (x y) (hxy : rel x y) : rank x ∈ rank y :=
    h.2 (e x) (hd x) (e y) (hd y) (rank x) (hb x) (rank y) (hb y)
      (hr x y hxy) (hg x) (hg y)
  exact Subrelation.wf (fun {x y} hxy => ZFSet.rank_lt_of_mem (hm x y hxy))
    (InvImage.wf (fun x => (rank x).rank) Ordinal.lt_wf)

def rankedFormula : SigmaFormula :=
  .existsSet (.existsSet (.bounded (rankFormula 2 3 1 0)))

theorem realize_rankedFormula (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    rankedFormula.Realize M e ↔ ∃ b ∈ M, ∃ g ∈ M, RankMap (e 0) (e 1) b g := by
  simp only [rankedFormula,SigmaFormula.Realize]
  apply exists_congr
  intro b
  apply and_congr_right
  intro hb
  apply exists_congr
  intro g
  apply and_congr_right
  intro hg
  have henv : ∀ i, cons g (cons b e) i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp only [cons_zero,cons_succ]
    · exact hg
    · exact hb
    · exact he i
  exact ((rankFormula 2 3 1 0).absolute M hM _ henv).trans (eval_rankFormula _ _ _ _ _)

theorem internal_rank_sound {α : Type u} {rel : α → α → Prop}
    (M : ZFSet.{u}) (hM : Transitive M) (env : ℕ → ZFSet.{u})
    (he : ∀ i, env i ∈ M) (e : α → ZFSet.{u}) (hd : ∀ x, e x ∈ env 0)
    (hr : ∀ x y, rel x y → ZFSet.pair (e x) (e y) ∈ env 1)
    (h : rankedFormula.Realize M env) : WellFounded rel := by
  obtain ⟨b,hb,g,hg,h⟩ := (realize_rankedFormula M hM env he).mp h
  exact rankMap_sound e hd hr h

end
end TuringRigidity.SetRankCertificate

end OAI
