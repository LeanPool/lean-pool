/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/FiniteFragment.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TupleFormula

/-!
# Finite Fragment
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def scope : Formula → ℕ
  | .equal i j | .member i j => max (i+1) (j+1)
  | .conj φ ψ => max φ.scope ψ.scope
  | .neg φ => φ.scope
  | .existsMem i φ => max (i+1) (φ.scope-1)

theorem realize_congr (φ : Formula) (d : ZFSet.{u}) (e f : ℕ → ZFSet.{u})
    (h : ∀ i, i < φ.scope → e i = f i) : φ.Realize d e ↔ φ.Realize d f := by
  induction φ generalizing e f with
  | equal i j => simp only [Realize,h i (by simp [scope]),h j (by simp [scope])]
  | member i j => simp only [Realize,h i (by simp [scope]),h j (by simp [scope])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e f (fun i hi => h i (by simp only [scope]; omega)))
      (ihψ e f (fun i hi => h i (by simp only [scope]; omega)))
  | neg φ ih => exact not_congr (ih e f h)
  | existsMem i φ ih =>
    simp only [Realize,h i (by simp only [scope]; omega)]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    apply ih; intro j hj
    cases j with
    | zero => rfl
    | succ j => exact h j (by simp only [scope]; omega)

def width : Formula → ℕ
  | .equal i j | .member i j => max (i+1) (j+1)
  | .conj φ ψ => max φ.width ψ.width
  | .neg φ => φ.width
  | .existsMem i φ => max (i+1) φ.width

theorem scope_le_width (φ : Formula) : φ.scope ≤ φ.width := by
  induction φ <;> simp only [scope,width] at * <;> omega
end Formula
namespace FiniteTuple

def takeEnv : ℕ → (ℕ → ZFSet.{u}) → List ZFSet.{u}
  | 0,_ => []
  | n+1,e => e 0 :: takeEnv n (fun i => e (i+1))

@[simp] theorem length_takeEnv (n : ℕ) (e : ℕ → ZFSet.{u}) : (takeEnv n e).length = n := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => simp only [takeEnv,List.length_cons,ih]

theorem takeEnv_mem (n : ℕ) (e : ℕ → ZFSet.{u}) (h : ZFSet.{u}) (he : ∀ i, e i ∈ h) :
    ∀ x ∈ takeEnv n e, x ∈ h := by
  induction n generalizing e with
  | zero => simp [takeEnv]
  | succ n ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact he 0
    · exact ih (fun i => e (i+1)) (fun i => he (i+1)) x hx

theorem takeEnv_agree (n : ℕ) (e f : ℕ → ZFSet.{u}) (i : ℕ) (hi : i < n) :
    prepend (takeEnv n e) f i = e i := by
  induction n generalizing e i with
  | zero => omega
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih (fun j => e (j+1)) i (Nat.lt_of_succ_lt_succ hi)

def witnessBody (n i : ℕ) (φ : Formula) : Formula :=
  .conj (.member 0 (i+1)) (relativizeBounded (n+1) φ)

theorem eval_witnessBody (n i : ℕ) (φ : Formula) (hn : i < n) (hφ : φ.scope ≤ n + 1)
    (d x : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (witnessBody n i φ).Eval (cons x (prepend (takeEnv n e) (fun _ => d))) ↔
      x ∈ e i ∧ φ.Realize d (cons x e) := by
  simp only [witnessBody,Formula.Eval,cons_zero,cons_succ,eval_relativizeBounded]
  rw [takeEnv_agree n e _ i hn]
  have hd : prepend (takeEnv n e) (fun _ => d) n = d := by
    simpa only [length_takeEnv,Nat.add_zero] using prepend_tail (takeEnv n e) (fun _ => d) 0
  rw [hd]
  apply and_congr_right; intro _
  apply φ.realize_congr; intro j hj
  cases j with
  | zero => rfl
  | succ j => exact takeEnv_agree n e _ j (by omega)

def occurrences : Formula → List (ℕ × Formula)
  | .equal _ _ | .member _ _ => []
  | .conj φ ψ => occurrences φ ++ occurrences ψ
  | .neg φ => occurrences φ
  | .existsMem i φ => (i,φ) :: occurrences φ

def fragment (n : ℕ) (φ : Formula) : List Formula :=
  (occurrences φ).map (fun p => witnessBody n p.1 p.2)

theorem occurrence_width (φ : Formula) (i : ℕ) (ψ : Formula)
    (hm : (i, ψ) ∈ occurrences φ) : i < φ.width ∧ ψ.scope ≤ φ.width + 1 := by
  induction φ with
  | equal => simp [occurrences] at hm
  | member => simp [occurrences] at hm
  | conj φ θ ihφ ihθ =>
    rcases List.mem_append.mp hm with hm|hm
    · have hh := ihφ hm; simp only [Formula.width]; omega
    · have hh := ihθ hm; simp only [Formula.width]; omega
  | neg φ ih => exact ih hm
  | existsMem j φ ih =>
    rcases List.mem_cons.mp hm with hp|hm
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
      have hh := Formula.scope_le_width ψ
      simp only [Formula.width]; omega
    · have hh := ih hm; simp only [Formula.width]; omega

def Witnesses (d h : ZFSet.{u}) (φ : Formula) : Prop :=
  ∀ i ψ, (i, ψ) ∈ occurrences φ →
    ∀ e : ℕ → ZFSet.{u}, (∀ j, e j ∈ h) →
      (∃ x ∈ d, x ∈ e i ∧ ψ.Realize d (cons x e)) →
        ∃ x ∈ h, x ∈ e i ∧ ψ.Realize d (cons x e)

theorem realize_of_witnesses (d h : ZFSet.{u}) (hhd : h ⊆ d) (φ : Formula)
    (hw : Witnesses d h φ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ h) :
    φ.Realize h e ↔ φ.Realize d e := by
  induction φ generalizing e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ =>
    have hwφ : Witnesses d h φ := fun i θ hi => hw i θ (List.mem_append_left _ hi)
    have hwψ : Witnesses d h ψ := fun i θ hi => hw i θ (List.mem_append_right _ hi)
    exact and_congr (ihφ hwφ e he) (ihψ hwψ e he)
  | neg φ ih => exact not_congr (ih hw e he)
  | existsMem i φ ih =>
    have hwφ : Witnesses d h φ := fun j θ hj => hw j θ (List.mem_cons_of_mem _ hj)
    have env (x : ZFSet.{u}) (hx : x ∈ h) : ∀ j, cons x e j ∈ h := by
      intro j; cases j with
      | zero => exact hx
      | succ j => exact he j
    constructor
    · rintro ⟨x,hx,hxi,hφ⟩
      exact ⟨x,hhd hx,hxi,(ih hwφ (cons x e) (env x hx)).mp hφ⟩
    · intro hφ
      obtain ⟨x,hx,hxi,hψ⟩ := hw i φ (List.mem_cons_self) e he hφ
      exact ⟨x,hx,hxi,(ih hwφ (cons x e) (env x hx)).mpr hψ⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
