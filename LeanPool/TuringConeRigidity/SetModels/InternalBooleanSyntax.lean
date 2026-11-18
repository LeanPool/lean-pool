/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRegularAlgebra

/-!
# Internal Boolean Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanSyntax
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra

/-- Bounded formula describing the regular complement of a condition-set code. -/
def negFormula (c U V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (U+1) (.neg (.subset 1 0)))))

theorem negFormula_spec (c U V : ℕ) (e : ℕ → ZFSet.{0}) :
    (negFormula c U V).Eval e ↔ e V = neg (e c) (e U) := by
  simp only [negFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,cons_zero,cons_succ]
  constructor
  · rintro ⟨hVc,hV⟩
    apply ZFSet.ext
    intro p
    rw [neg,ZFSet.mem_sep]
    exact ⟨fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩,fun h => (hV p h.1).mpr h.2⟩
  · intro h
    rw [h]
    refine ⟨neg_subset _ _,fun p hp => ?_⟩
    exact (ZFSet.mem_sep).trans (and_iff_right hp)

/-- Bounded formula describing the regular supremum of a family of condition-set codes. -/
def supFormula (c F V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (c+1) (.imp (.subset 1 0)
      (.existsMem (F+2) (.existsMem 0 (.subset 2 0)))))))

theorem supFormula_spec (c F V : ℕ) (e : ℕ → ZFSet.{0}) :
    (supFormula c F V).Eval e ↔ e V = supCode (e c) (e F) := by
  simp only [supFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  have hu (q : ZFSet.{0}) : (∃ U ∈ e F, ∃ r ∈ U, q ⊆ r) ↔
      ∃ r ∈ ZFSet.sUnion (e F), q ⊆ r := by
    constructor
    · rintro ⟨U,hU,r,hr,hqr⟩; exact ⟨r,ZFSet.mem_sUnion.mpr ⟨U,hU,hr⟩,hqr⟩
    · rintro ⟨r,hr,hqr⟩; obtain ⟨U,hU,hr⟩ := ZFSet.mem_sUnion.mp hr
      exact ⟨U,hU,r,hr,hqr⟩
  simp only [hu]
  constructor
  · rintro ⟨hVc,hV⟩
    apply ZFSet.ext
    intro p
    rw [supCode,mem_regular]
    exact ⟨fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩,fun h => (hV p h.1).mpr h.2⟩
  · intro h
    rw [h]
    refine ⟨(join_isCode _ _).1,fun p hp => ?_⟩
    exact (mem_regular _ _ p).trans (and_iff_right hp)

/-- The subset `A` of `B` is closed under regular complements and the indexed suprema supplied
by `Q`. -/
def Closed (c B Q A : ZFSet.{0}) : Prop :=
  A ⊆ B ∧ (∀ U ∈ A, neg c U ∈ A) ∧
    ∀ F ∈ Q, F ⊆ A → supCode c F ∈ A

/-- Bounded formula expressing closure under regular complement and the prescribed family
suprema. -/
def closedFormula (c B Q A : ℕ) : Formula :=
  .conj (.subset A B) (.conj
    (.allMem A (.existsMem (A+1) (negFormula (c+2) 1 0)))
    (.allMem Q (.imp (.subset 0 (A+1))
      (.existsMem (A+1) (supFormula (c+2) 1 0)))))

theorem closedFormula_spec (c B Q A : ℕ) (e : ℕ → ZFSet.{0}) :
    (closedFormula c B Q A).Eval e ↔ Closed (e c) (e B) (e Q) (e A) := by
  simp only [closedFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_imp,negFormula_spec,supFormula_spec,cons_zero,cons_succ,Closed]
  simp only [exists_eq_right]

/-- The candidate subsets in `Q` that contain the seeds and satisfy the Boolean closure
conditions. -/
noncomputable def candidates (c B Q S : ZFSet.{0}) : ZFSet.{0} :=
  Q.sep (fun A => S ⊆ A ∧ Closed c B Q A)

theorem candidates_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) :
    candidates c B Q S ∈ M := by
  let e := cons c (cons B (cons Q (fun _ => S)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hc
    · exact hB
    · exact hQ
    · exact hS
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.conj (.subset 4 0) (closedFormula 1 2 3 0)) e he hQ
  simpa only [candidates,Formula.Eval,Formula.eval_subset,closedFormula_spec,
    cons_zero,cons_succ,e] using hs

end TuringRigidity.InternalBooleanSyntax

end OAI
