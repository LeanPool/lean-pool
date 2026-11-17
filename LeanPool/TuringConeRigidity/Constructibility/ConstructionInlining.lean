/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructionInlining.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceInlining
public import LeanPool.TuringConeRigidity.Constructibility.RelativeConstruction

/-!
# Construction Inlining
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- The concrete parameter environment needed to evaluate a relative construction. -/
noncomputable def Construction.inputs (R : ZFSet.{u}) (P : Oracle) :
    Construction.{u} → ℕ → ZFSet.{u}
  | .reals, _ => R
  | .parameter, _ => realCode P
  | .define o _ _ _, 0 => level R o
  | .define _ n _ c, k+1 =>
      if h : (Nat.unpair k).1 < n then
        (c ⟨(Nat.unpair k).1,h⟩).inputs R (realPart P (Nat.unpair k).1) (Nat.unpair k).2
      else R

theorem Construction.inputs_child (R : ZFSet.{u}) (P : Oracle)
    (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm) (c : Fin n → Construction.{u})
    (i : Fin n) (k : ℕ) :
    (Construction.define o n p c).inputs R P (Nat.pair i k+1) =
      (c i).inputs R (realPart P i) k := by
  simp [Construction.inputs,Nat.unpair_pair,i.isLt]

theorem Construction.inputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M) : ∀ k, t.inputs R P k ∈ M := by
  induction t generalizing P with
  | reals => exact fun _ => hR
  | parameter => exact fun _ => hM R hR _ ht
  | define o n p c ih =>
    intro k
    cases k with
    | zero => exact level_mem M R hM hT hR o hi.1
    | succ k =>
      simp only [Construction.inputs]
      split
      next h =>
        exact ih ⟨(Nat.unpair k).1,h⟩ _ (ht.2 ⟨(Nat.unpair k).1,h⟩).1
          (hi.2 ⟨(Nat.unpair k).1,h⟩) (Nat.unpair k).2
      next => exact hR

/-- The full formula defining a construction from its recursively supplied parameter slots. -/
noncomputable def Construction.formula : Construction.{u} → ℕ → (ℕ → ℕ) → SentenceForm
  | .reals, out, r => .equal out (r 0)
  | .parameter, out, r => .equal out (r 0)
  | .define _ n p c, out, r => bindComputed n
      (fun i => if h : i < n then
        (c ⟨i,h⟩).formula 0 (fun k => r (Nat.pair i k+1)+1)
        else .equal 0 0)
      (subsetBody n out (r 0) p)

theorem Construction.formula_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M)
    (out : ℕ) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hr : ∀ k, e (r k) = t.inputs R P k) :
    (t.formula out r).Sat (M : Set ZFSet) e ↔ e out = t.value R P := by
  induction t generalizing P out r e with
  | reals => exact Iff.of_eq (congrArg (e out = ·) (hr 0))
  | parameter => exact Iff.of_eq (congrArg (e out = ·) (hr 0))
  | define o n p c ih =>
    let w : ℕ → ZFSet.{u} := fun i => if h : i < n then
      (c ⟨i,h⟩).value R (realPart P i) else R
    have hw (i : ℕ) (hin : i < n) : w i ∈ M := by
      dsimp [w]; rw [dite_eq_left hin]
      exact hM _ (level_mem M R hM hT hR o hi.1) _ (ht.2 ⟨i,hin⟩).2
    have hf (i : ℕ) (hin : i < n) (x : ZFSet.{u}) (hx : x ∈ M) :
        (if h : i < n then (c ⟨i,h⟩).formula 0 (fun k => r (Nat.pair i k+1)+1)
          else .equal 0 0).Sat (M : Set ZFSet) (cons x e) ↔ x = w i := by
      rw [dite_eq_left hin,show w i = (c ⟨i,hin⟩).value R (realPart P i) from dite_eq_left hin]
      apply ih ⟨i,hin⟩ _ (ht.2 ⟨i,hin⟩).1 (hi.2 ⟨i,hin⟩) 0 _ _
        (by
          intro k
          cases k
          · exact hx
          · exact he _)
      intro k
      change e (r (Nat.pair i k+1)) = _
      rw [hr,Construction.inputs_child R P o n p c ⟨i,hin⟩ k]
    rw [Construction.formula,bindComputed_spec M n _ _ e w hw hf,
      subsetBody_spec M hM n out (r 0) p ht.1 e w he hw]
    have ha : e (r 0) = level R o := hr 0
    rw [ha]
    have hv : (fun i : Fin n => w i) = (fun i : Fin n => (c i).value R (realPart P i)) := by
      funext i; exact dite_eq_left i.isLt
    rw [hv]
    rfl

theorem Construction.inlined_definition (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M) :
    ∃ p : SentenceForm, ∀ x ∈ M,
      p.Sat (M : Set ZFSet) (cons x (t.inputs R P)) ↔ x = t.value R P := by
  refine ⟨t.formula 0 Nat.succ,?_⟩
  intro x hx
  exact t.formula_spec M R hM hT hR P ht hi 0 Nat.succ _
    (by
      intro i
      cases i
      · exact hx
      · exact t.inputs_mem M R hM hT hR P ht hi _) (fun _ => rfl)

end TuringRigidity.RelativeConstructible

end OAI
