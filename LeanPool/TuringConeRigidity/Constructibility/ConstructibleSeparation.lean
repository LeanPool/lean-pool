/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructibleSeparation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleClosure
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Constructible Separation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel SentenceForm BoundedSetTheory TransitiveNameModel
universe u

/-- Shift the non-distinguished parameter slots to reserve one additional variable. -/
def parameterShift : ℕ → ℕ | 0 => 0 | i+1 => i+2

theorem shifted_parameters (p : SentenceForm) (D : Set ZFSet.{u})
    (x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename parameterShift).Sat D (cons x (cons a e)) ↔ p.Sat D (cons x e) := by
  rw [sat_rename]
  have he : (fun i => cons x (cons a e) (parameterShift i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [he]

theorem bounded_separation_mem_definablePower (A a : ZFSet.{u}) (hA : Transitive A)
    (ha : a ∈ A) (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    a.sep (fun x => φ.Eval (cons x e)) ∈ definablePower A := by
  let ψ := SentenceForm.conj (.member 0 1) ((fromBounded φ).rename parameterShift)
  have hψ := separation_mem_definablePower A ψ (cons a e) (by
    intro i _
    cases i
    · exact ha
    · exact he _)
  have heq : A.sep (fun x => ψ.Sat (A : Set ZFSet) (cons x (cons a e))) =
      a.sep (fun x => φ.Eval (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,ψ,Sat,cons_zero,cons_succ,shifted_parameters,bounded_sat]
    constructor
    · rintro ⟨hx,hxa,hφ⟩
      exact ⟨hxa,(φ.absolute A hA _ (by
        intro i
        cases i
        · exact hx
        · exact he _)).mp hφ⟩
    · rintro ⟨hxa,hφ⟩
      have hx := hA a ha x hxa
      exact ⟨hx,hxa,(φ.absolute A hA _ (by
        intro i
        cases i
        · exact hx
        · exact he _)).mpr hφ⟩
  rwa [heq] at hψ

theorem bounded_separation_in_relativeL (R a : ZFSet.{u}) (ha : InRelativeL R a)
    (φ : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, i < (fromBounded φ).bound → InRelativeL R (e i)) :
    InRelativeL R (a.sep (fun x => φ.Eval (cons x e))) := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := finite_parameters_in_level R e (fromBounded φ).bound he
  let A := level R (max i j)
  have haA : a ∈ A := level_mono R (le_max_left i j) hi
  let e' : ℕ → ZFSet.{u} := fun n => if n < (fromBounded φ).bound then e n else a
  have heA : ∀ n, e' n ∈ A := by
    intro n
    dsimp [e']; split
    next hn => exact level_mono R (le_max_right i j) (hj n hn)
    next => exact haA
  have heval (x : ZFSet.{u}) : φ.Eval (cons x e') ↔ φ.Eval (cons x e) := by
    rw [← bounded_univ,← bounded_univ]
    apply (fromBounded φ).finite_support
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      change e' k = e k
      simp [e',show k < (fromBounded φ).bound by omega]
  have heq : a.sep (fun x => φ.Eval (cons x e')) = a.sep (fun x => φ.Eval (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,heval]
  refine ⟨max i j + 1,?_⟩
  rw [level_succ,← heq]
  exact bounded_separation_mem_definablePower A a (level_transitive R _) haA φ e' heA

theorem bounded_class_absolute (R : ZFSet.{u}) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, InRelativeL R (e i)) :
    (fromBounded φ).Sat {x | InRelativeL R x} e ↔ φ.Eval e := by
  induction φ generalizing e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ e he) (ihψ e he)
  | neg φ ih => exact not_congr (ih e he)
  | existsMem i φ ih =>
    simp only [fromBounded,Sat,Formula.Eval,cons_zero,cons_succ,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x,hx,hxi,hφ⟩
      exact ⟨x,hxi,(ih (cons x e) (by
        intro k
        cases k
        · exact hx
        · exact he _)).mp hφ⟩
    · rintro ⟨x,hxi,hφ⟩
      have hx := relativeL_transitive R (he i) hxi
      exact ⟨x,hx,hxi,(ih (cons x e) (by
        intro k
        cases k
        · exact hx
        · exact he _)).mpr hφ⟩

theorem relativeL_bounded_separation (R : ZFSet.{u}) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, InRelativeL R (e i))
    (a : ZFSet.{u}) (ha : InRelativeL R a) :
    ∃ b, InRelativeL R b ∧ ∀ x, InRelativeL R x →
      (x ∈ b ↔ x ∈ a ∧ (fromBounded φ).Sat {y | InRelativeL R y} (cons x e)) := by
  refine ⟨a.sep (fun x => φ.Eval (cons x e)),
    bounded_separation_in_relativeL R a ha φ e (fun i _ => he i),?_⟩
  intro x hx
  rw [ZFSet.mem_sep,bounded_class_absolute R φ _ (by
    intro i
    cases i
    · exact hx
    · exact he _)]

end TuringRigidity.RelativeConstructible

end OAI
