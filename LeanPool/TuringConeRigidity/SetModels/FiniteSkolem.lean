/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FiniteSkolem.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TupleRelation
public import LeanPool.TuringConeRigidity.SetModels.InternalUniformization

/-!
# Finite Skolem
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

/-- The tuple codes in the designated space that occur as inputs of the relation `r`. -/
noncomputable def requests (d : ZFSet.{u}) (n : ℕ) (r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun t => ∃ y ∈ d, ZFSet.pair t y ∈ r) (space d n)

theorem requests_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (n : ℕ) :
    requests d n r ∈ M := by
  simpa only [requests,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.pairMem 1 0 3))
      (cons d (fun _ => r)) (by intro i; cases i <;> assumption)
      (space_mem M hM hP hU hPow hS hd n)

/-- A subrelation selecting exactly one witness for every satisfiable finite-tuple input. -/
def SkolemGraph (d : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (g : ZFSet.{u}) : Prop :=
  g ⊆ relation d n φ e ∧
  ∀ xs : List ZFSet.{u}, xs.length = n → (∀ x ∈ xs, x ∈ d) →
    (∃ y ∈ d, φ.Eval (cons y (prepend xs e))) →
      ∃ y ∈ d, ZFSet.pair (code xs) y ∈ g ∧
        ∀ z ∈ d, ZFSet.pair (code xs) z ∈ g → z = y

theorem internal_skolem_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    ∃ g ∈ M, SkolemGraph d n φ e g := by
  have hr := relation_mem M hM hP hU hPow hS hR hI hd n φ e he
  have ha := requests_mem M hM hP hU hPow hS hd hr n
  obtain ⟨g,hg,hgr,_,hsel⟩ := internal_relation_choice M hM hP hU hPow hS hAC ha hd hr
    (fun t ht => (ZFSet.mem_sep.mp ht).2)
  refine ⟨g,hg,hgr,?_⟩
  intro xs hlen hxs hw
  subst n
  have ht : code xs ∈ requests d xs.length (relation d xs.length φ e) := by
    obtain ⟨y,hy,hφ⟩ := hw
    exact ZFSet.mem_sep.mpr ⟨code_mem_space d xs hxs,y,hy,
      (relation_pair d y xs φ e).mpr ⟨hxs,hy,hφ⟩⟩
  exact hsel _ ht

theorem SkolemGraph.correct {d g : ZFSet.{u}} {n : ℕ} {φ : Formula}
    {e : ℕ → ZFSet.{u}} (hg : SkolemGraph d n φ e g)
    (xs : List ZFSet.{u}) (hlen : xs.length = n) {y : ZFSet.{u}}
    (hy : ZFSet.pair (code xs) y ∈ g) :
    (∀ x ∈ xs, x ∈ d) ∧ y ∈ d ∧ φ.Eval (cons y (prepend xs e)) := by
  subst n
  exact (relation_pair d y xs φ e).mp (hg.1 hy)

theorem SkolemGraph.functional {d g : ZFSet.{u}} {n : ℕ} {φ : Formula}
    {e : ℕ → ZFSet.{u}} (hg : SkolemGraph d n φ e g)
    (xs : List ZFSet.{u}) (hlen : xs.length = n) {y z : ZFSet.{u}}
    (hy : ZFSet.pair (code xs) y ∈ g) (hz : ZFSet.pair (code xs) z ∈ g) : y = z := by
  have hy' := hg.correct xs hlen hy
  have hz' := hg.correct xs hlen hz
  obtain ⟨w,_,_,hu⟩ := hg.2 xs hlen hy'.1 ⟨y,hy'.2⟩
  exact (hu y hy'.2.1 hy).trans (hu z hz'.2.1 hz).symm

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
