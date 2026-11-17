/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/CanonicalOmegaSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceInlining
public import LeanPool.TuringConeRigidity.SetModels.SetModelAddition

/-!
# Canonical Omega Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def inductiveSetFormula (w : ℕ) : Formula :=
  .conj (.existsMem w (.empty 0))
    (.allMem w (.existsMem (w+1) (.successor 0 1)))

theorem inductiveSetFormula_spec (w : ℕ) (e : ℕ → ZFSet.{u}) :
    (inductiveSetFormula w).Eval e ↔
      (∅ : ZFSet) ∈ e w ∧ ∀ x ∈ e w, insert x x ∈ e w := by
  simp only [inductiveSetFormula,Formula.Eval,Formula.eval_empty,
    Formula.eval_allMem,Formula.eval_successor,cons_zero,cons_succ]
  simp only [exists_eq_right]

theorem omega_subset_inductive {W : ZFSet.{u}}
    (h : (∅ : ZFSet) ∈ W ∧ ∀ x ∈ W, insert x x ∈ W) : ZFSet.omega ⊆ W := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  clear hx
  induction n with
  | zero => exact h.1
  | succ n ih => exact h.2 _ ih

noncomputable def canonicalOmega (w : ℕ) : SentenceForm :=
  .conj (fromBounded (inductiveSetFormula w))
    (SentenceForm.all (SentenceForm.imp (fromBounded (inductiveSetFormula 0))
      (fromBounded (.subset (w+1) 0))))

theorem canonicalOmega_spec (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (w : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (canonicalOmega w).Sat (M : Set ZFSet) e ↔ e w = ZFSet.omega := by
  have habs (p : Formula) (x : ZFSet.{u}) (hx : x ∈ M) :
      (fromBounded p).Sat (M : Set ZFSet) (cons x e) ↔ p.Eval (cons x e) := by
    rw [bounded_sat,Formula.absolute p M hM _
      (by
        intro i
        cases i
        · exact hx
        · exact he _)]
  have hw : (∅ : ZFSet.{u}) ∈ ZFSet.omega ∧
      ∀ x ∈ ZFSet.omega.{u}, insert x x ∈ ZFSet.omega :=
    ⟨(mem_omega _).mpr ⟨0,rfl⟩,SetModelArithmetic.setSucc_omega⟩
  change ((fromBounded (inductiveSetFormula w)).Sat (M : Set ZFSet) e ∧
    (SentenceForm.all (SentenceForm.imp (fromBounded (inductiveSetFormula 0))
      (fromBounded (.subset (w+1) 0)))).Sat (M : Set ZFSet) e) ↔ _
  simp only [SentenceForm.sat_all,SentenceForm.sat_imp]
  rw [bounded_sat,Formula.absolute _ M hM e he,inductiveSetFormula_spec]
  have hmin : (∀ x ∈ (M : Set ZFSet),
      (fromBounded (inductiveSetFormula 0)).Sat (M : Set ZFSet) (cons x e) →
      (fromBounded (.subset (w+1) 0)).Sat (M : Set ZFSet) (cons x e)) ↔
      ∀ x ∈ M, ((∅ : ZFSet) ∈ x ∧ ∀ y ∈ x, insert y y ∈ x) → e w ⊆ x := by
    apply forall_congr'; intro x
    apply forall_congr'; intro hx
    rw [habs _ x hx,habs _ x hx,inductiveSetFormula_spec,Formula.eval_subset]
    rfl
  rw [hmin]
  constructor
  · rintro ⟨hi,hminimal⟩
    exact ZFSet.ext fun x => ⟨fun hx => hminimal _ hω hw hx,fun hx => omega_subset_inductive hi hx⟩
  · intro h
    rw [h]
    exact ⟨hw,fun _ _ hi => omega_subset_inductive hi⟩

end TuringRigidity.RelativeConstructible

end OAI
