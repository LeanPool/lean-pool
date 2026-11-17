/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SetSatisfactionBounded.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.DefinablePower

/-!
# Set Satisfaction Bounded
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- Relativize every full-formula set quantifier to a designated domain and rename its free
variables. -/
def setBounded : SentenceForm → ℕ → (ℕ → ℕ) → Formula
  | .equal i j, _, v => .equal (v i) (v j)
  | .member i j, _, v => .member (v i) (v j)
  | .conj p q, a, v => .conj (setBounded p a v) (setBounded q a v)
  | .neg p, a, v => .neg (setBounded p a v)
  | .ex p, a, v => .existsMem a
      (setBounded p (a+1) (fun i => match i with | 0 => 0 | j+1 => v j+1))

theorem setBounded_eval (p : SentenceForm) (a : ℕ) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) :
    (setBounded p a v).Eval e ↔ p.Sat (e a : Set ZFSet) (fun i => e (v i)) := by
  induction p generalizing a v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp a v e) (ihq a v e)
  | neg p ih => exact not_congr (ih a v e)
  | ex p ih =>
    simp only [setBounded,Formula.Eval,SentenceForm.Sat]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih (a+1) _ (cons x e)).trans (he ▸ Iff.rfl)

theorem setBounded_absolute (p : SentenceForm) (M : ZFSet.{u}) (hM : Transitive M)
    (a : ℕ) (v : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (setBounded p a v).Realize M e ↔ p.Sat (e a : Set ZFSet) (fun i => e (v i)) :=
  ((setBounded p a v).absolute M hM e he).trans (setBounded_eval p a v e)

theorem definedSubset_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n + 1) :
    definedSubset A p v ∈ M := by
  let f : ℕ → ZFSet.{u} := fun i => if h : i < n then v ⟨i,h⟩ else A
  let e := cons A f
  let shift : ℕ → ℕ := fun i => match i with | 0 => 0 | j+1 => j+2
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hA
    | succ i =>
      dsimp [e,cons,f]
      split
      next h => exact hM A hA _ (hv ⟨i,h⟩)
      next => exact hA
  have hs := sep_mem M hM hS (setBounded p 1 shift) e he hA
  have heq : A.sep (fun x => (setBounded p 1 shift).Eval (cons x e)) =
      definedSubset A p v := by
    apply ZFSet.ext; intro x
    rw [ZFSet.mem_sep,mem_definedSubset,setBounded_eval]
    apply and_congr_right; intro _
    apply p.finite_support
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      change f i = tupleEnv v i
      have hin : i < n := by omega
      simp [f,tupleEnv,hin]
  exact heq ▸ hs

theorem definablePower_subset_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) : definablePower A ⊆ M := by
  intro S hS'
  obtain ⟨n,p,v,hb,hv,rfl⟩ := (mem_definablePower A S).mp hS'
  exact definedSubset_mem M A hM hS hA p v hv hb

theorem definablePower_internal_bound (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hP : PowerSet M) (hA : A ∈ M) :
    ∃ Q ∈ M, (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ A) ∧ definablePower A ⊆ Q := by
  obtain ⟨Q,hQ,hdef⟩ := internal_power M hM hP hA
  exact ⟨Q,hQ,hdef,fun S hS' => (hdef S).mpr
    ⟨definablePower_subset_model M A hM hS hA hS',subset_of_mem_definablePower hS'⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
