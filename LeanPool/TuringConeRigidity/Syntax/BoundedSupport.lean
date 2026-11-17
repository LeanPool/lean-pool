/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedSupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.BoundedForcingCode
public import LeanPool.TuringConeRigidity.SetModels.InternalContainer

/-!
# Bounded Support
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

def bound : BoundedSetTheory.Formula → ℕ
  | .equal i j => max (i+1) (j+1)
  | .member i j => max (i+1) (j+1)
  | .conj φ ψ => max (bound φ) (bound ψ)
  | .neg φ => bound φ
  | .existsMem i φ => max (i+1) (bound φ - 1)

theorem forces_congr {P : Type u} [Preorder P] (φ : BoundedSetTheory.Formula)
    (e e' : ℕ → Name P) (h : ∀ i, i < bound φ → e i = e' i) (p : P) :
    Forces e φ p ↔ Forces e' φ p := by
  induction φ generalizing e e' p with
  | equal i j => simp only [Forces,h i (by simp [bound]),h j (by simp [bound])]
  | member i j => simp only [Forces,h i (by simp [bound]),h j (by simp [bound])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e e' (fun i hi => h i (by simp only [bound]; omega)) p)
      (ihψ e e' (fun i hi => h i (by simp only [bound]; omega)) p)
  | neg φ ih =>
    exact forall_congr' (fun q => imp_congr_right (fun _ => not_congr (ih e e' h q)))
  | existsMem i φ ih =>
    have hei := h i (by simp only [bound]; omega)
    change (fun a : Name P => ∃ j : a.arity, p ≤ a.tag j ∧ Forces (push (a.child j) e) φ p) (e i)
      ↔ _
    rw [hei]
    apply exists_congr
    intro j
    apply and_congr_right
    intro _
    apply ih
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      simp only [push_succ]
      exact h n (by simp only [bound]; omega)

theorem eval_congr (φ : BoundedSetTheory.Formula) (e e' : ℕ → ZFSet.{u})
    (h : ∀ i, i < bound φ → e i = e' i) : φ.Eval e ↔ φ.Eval e' := by
  induction φ generalizing e e' with
  | equal i j => simp only [Formula.Eval,h i (by simp [bound]),h j (by simp [bound])]
  | member i j => simp only [Formula.Eval,h i (by simp [bound]),h j (by simp [bound])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e e' (fun i hi => h i (by simp only [bound]; omega)))
      (ihψ e e' (fun i hi => h i (by simp only [bound]; omega)))
  | neg φ ih => exact not_congr (ih e e' h)
  | existsMem i φ ih =>
    have hei := h i (by simp only [bound]; omega)
    simp only [Formula.Eval,hei]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    apply ih
    intro n hn
    cases n with
    | zero => rfl
    | succ n => exact h n (by simp only [bound]; omega)

def truncate {α : Sort*} (n : ℕ) (e : ℕ → α) (i : ℕ) : α := if i < n then e i else e 0

theorem truncate_forces {P : Type u} [Preorder P] (φ : BoundedSetTheory.Formula)
    (e : ℕ → Name P) (p : P) : Forces (truncate (bound φ) e) φ p ↔ Forces e φ p :=
  forces_congr φ _ e (fun _ hi => ite_eq_left hi) p

theorem finite_container (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (n : ℕ) :
    ∃ d ∈ M, Transitive d ∧ e 0 ∈ d ∧ ∀ i, i < n → e i ∈ d := by
  induction n with
  | zero =>
    obtain ⟨d,hd,hdT,he0⟩ := internal_transitive_container M hM hP hU hS hR hI (he 0)
    exact ⟨d,hd,hdT,he0,fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
  | succ n ih =>
    obtain ⟨d,hd,hdT,he0,hen⟩ := ih
    obtain ⟨v,hv,hvT,hvpair⟩ := internal_transitive_container M hM hP hU hS hR hI
      (pair_mem M hM hP hd (he n))
    have hdv : d ∈ v := hvT _ hvpair _ (ZFSet.mem_pair.mpr (Or.inl rfl))
    have hnv : e n ∈ v := hvT _ hvpair _ (ZFSet.mem_pair.mpr (Or.inr rfl))
    refine ⟨v,hv,hvT,hvT d hdv _ he0,fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hvT d hdv _ (hen i hi)
    · exact hnv

end TuringRigidity.BoundedForcing

end OAI
