/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructionInputData.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructionInlining

/-!
# Construction Input Data
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

inductive ConstructionInput : Type (u + 1)
  | reals
  | stage (o : Ordinal.{u})
  | realPath (path : List ℕ)

def pathReal (P : Oracle) : List ℕ → Oracle
  | [] => P
  | i::is => pathReal (realPart P i) is

noncomputable def ConstructionInput.value (R : ZFSet.{u}) (P : Oracle) :
    ConstructionInput.{u} → ZFSet.{u}
  | .reals => R
  | .stage o => level R o
  | .realPath path => realCode (pathReal P path)

def ConstructionInput.prefix (i : ℕ) : ConstructionInput.{u} → ConstructionInput.{u}
  | .reals => .reals
  | .stage o => .stage o
  | .realPath path => .realPath (i::path)

theorem ConstructionInput.prefix_value (d : ConstructionInput.{u})
    (R : ZFSet.{u}) (P : Oracle) (i : ℕ) :
    (d.prefix i).value R P = d.value R (realPart P i) := by
  cases d <;> rfl

def ConstructionInput.Indexed (M : ZFSet.{u}) : ConstructionInput.{u} → Prop
  | .reals => True
  | .stage o => o.toZFSet ∈ M
  | .realPath _ => True

theorem ConstructionInput.prefix_indexed (d : ConstructionInput.{u})
    (M : ZFSet.{u}) (i : ℕ) : (d.prefix i).Indexed M ↔ d.Indexed M := by
  cases d <;> rfl

noncomputable def Construction.inputData : Construction.{u} → ℕ → ConstructionInput.{u}
  | .reals, _ => .reals
  | .parameter, _ => .realPath []
  | .define o _ _ _, 0 => .stage o
  | .define _ n _ c, k+1 =>
      if h : (Nat.unpair k).1 < n then
        ((c ⟨(Nat.unpair k).1,h⟩).inputData (Nat.unpair k).2).prefix (Nat.unpair k).1
      else .reals

theorem Construction.inputs_eq_data (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) (k : ℕ) : t.inputs R P k = (t.inputData k).value R P := by
  induction t generalizing P k with
  | reals => rfl
  | parameter => rfl
  | define o n p c ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Construction.inputs,Construction.inputData]
      split
      next h => rw [ConstructionInput.prefix_value]; exact ih _ _ _
      next => rfl

theorem Construction.inputData_indexed (t : Construction.{u}) (M : ZFSet.{u})
    (hi : t.Indexed M) : ∀ k, (t.inputData k).Indexed M := by
  induction t with
  | reals => exact fun _ => trivial
  | parameter => exact fun _ => trivial
  | define o n p c ih =>
    intro k
    cases k with
    | zero => exact hi.1
    | succ k =>
      simp only [Construction.inputData]
      split
      next h =>
        rw [ConstructionInput.prefix_indexed]
        exact ih _ (hi.2 _) _
      next => trivial

noncomputable def Construction.membershipFormula (t : Construction.{u}) : SentenceForm :=
  .ex (.conj (t.formula 0 (fun k => k+2)) (.member 1 0))

theorem Construction.membershipFormula_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M) (z : ZFSet.{u}) (hz : z ∈ M) :
    t.membershipFormula.Sat (M : Set ZFSet) (cons z (t.inputs R P)) ↔
      z ∈ t.value R P := by
  have hspec (x : ZFSet.{u}) (hx : x ∈ M) :
      (t.formula 0 (fun k => k+2)).Sat (M : Set ZFSet)
        (cons x (cons z (t.inputs R P))) ↔ x = t.value R P := by
    apply t.formula_spec M R hM hT hR P ht hi
    · intro i
      rcases i with _|_|i
      · exact hx
      · exact hz
      · exact t.inputs_mem M R hM hT hR P ht hi i
    · exact fun _ => rfl
  change (∃ x ∈ M, (t.formula 0 (fun k => k+2)).Sat (M : Set ZFSet)
    (cons x (cons z (t.inputs R P))) ∧ z ∈ x) ↔ _
  constructor
  · rintro ⟨x,hx,hf,hzx⟩
    exact (hspec x hx).mp hf ▸ hzx
  · intro hzt
    have hv := t.value_mem M R hM hT hR P ht hi
    exact ⟨_,hv,(hspec _ hv).mpr rfl,hzt⟩

theorem Construction.finite_membership_definition (t : Construction.{u}) :
    ∃ (n : ℕ) (p : SentenceForm) (d : Fin n → ConstructionInput.{u}),
      p.bound ≤ n+1 ∧
      ∀ (M R : ZFSet.{u}) (_hM : Transitive M) (_hT : SourceT M) (_hR : R ∈ M)
        (P : Oracle) (_ht : t.Certified R P) (_hi : t.Indexed M),
        (∀ i, (d i).Indexed M ∧ (d i).value R P ∈ M) ∧
        ∀ z ∈ M, p.Sat (M : Set ZFSet)
          (cons z (tupleEnv (fun i => (d i).value R P))) ↔ z ∈ t.value R P := by
  let p := t.membershipFormula
  refine ⟨p.bound,p,fun i => t.inputData i,by omega,?_⟩
  intro M R hM hT hR P ht hi
  refine ⟨fun i => ⟨t.inputData_indexed M hi i,?_⟩,?_⟩
  · rw [← t.inputs_eq_data]
    exact t.inputs_mem M R hM hT hR P ht hi i
  · intro z hz
    have hf : p.Sat (M : Set ZFSet)
        (cons z (tupleEnv (fun i : Fin p.bound => (t.inputData i).value R P))) ↔
        p.Sat (M : Set ZFSet) (cons z (t.inputs R P)) := by
      apply p.finite_support
      intro i hin
      cases i with
      | zero => rfl
      | succ i =>
        simp only [cons_succ]
        change tupleEnv (fun j : Fin p.bound => (t.inputData j).value R P) i = t.inputs R P i
        rw [tupleEnv, dite_eq_left (show i < p.bound by omega)]
        exact (t.inputs_eq_data R P i).symm
    exact hf.trans (t.membershipFormula_spec M R hM hT hR P ht hi z hz)

end TuringRigidity.RelativeConstructible

end OAI
