/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaBoundedUniversal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaDomainCollection

/-!
# Sigma Bounded Universal
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def envBound : ℕ → Formula
  | 0 => .equal 0 0
  | n+1 => .conj (envBound n) (.member (n+1) 0)

theorem eval_envBound (n : ℕ) (e : ℕ → ZFSet.{u}) :
    (envBound n).Eval e ↔ ∀ i, i < n → e (i+1) ∈ e 0 := by
  induction n with
  | zero => simp [envBound,Eval]
  | succ n ih =>
    simp only [envBound,Eval,ih]
    constructor
    · rintro ⟨h,hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi),h n (Nat.lt_succ_self n)⟩
end Formula
namespace SigmaFormula

def skipDomain : ℕ → ℕ
  | 0 => 0
  | i+1 => i+2

def allDomainMatrix (a : ℕ) (φ : SigmaFormula) : Formula :=
  .conj (.transitive 0) (.conj (.existsMem 0 (.empty 0))
    (.conj (.envBound φ.scope) (.conj (.member (a+1) 0)
      (.allMem (a+1) (FiniteTuple.relativizeSigma 1 (φ.rename skipDomain))))))

def allMem (a : ℕ) (φ : SigmaFormula) : SigmaFormula := .existsSet (.bounded (allDomainMatrix a φ))

theorem eval_allDomainMatrix (a : ℕ) (φ : SigmaFormula) (d : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (allDomainMatrix a φ).Eval (cons d e) ↔ Transitive d ∧ (∅ : ZFSet.{u}) ∈ d ∧
      (∀ i, i < φ.scope → e i ∈ d) ∧ e a ∈ d ∧ ∀ x ∈ e a, φ.Realize d (cons x e) := by
  simp only [allDomainMatrix,Formula.Eval,Formula.eval_transitive,Formula.eval_empty,
    Formula.eval_envBound,Formula.eval_allMem,FiniteTuple.eval_relativizeSigma,
    realize_rename,cons_zero,cons_succ]
  have eq (x : ZFSet.{u}) : (fun i => cons x (cons d e) (skipDomain i)) = cons x e := by
    funext i; cases i <;> rfl
  simp only [eq,exists_eq_right]

theorem realize_allMem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hC : SigmaCollection M)
    (a : ℕ) (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (allMem a φ).Realize M e ↔ ∀ x ∈ e a, φ.Realize M (cons x e) := by
  classical
  let e' := fun i => if i < φ.scope then e i else (∅ : ZFSet.{u})
  have congr (d x : ZFSet.{u}) : φ.Realize d (cons x e) ↔ φ.Realize d (cons x e') := by
    apply φ.realize_congr; intro i hi
    cases i with
    | zero => rfl
    | succ i => exact (ite_eq_left (show i < φ.scope by omega)).symm
  have matrix (d : ZFSet.{u}) (hd : d ∈ M) :
      (allDomainMatrix a φ).Realize M (cons d e) ↔ Transitive d ∧ (∅ : ZFSet.{u}) ∈ d ∧
        (∀ i, i < φ.scope → e i ∈ d) ∧ e a ∈ d ∧ ∀ x ∈ e a, φ.Realize d (cons x e) := by
    rw [Formula.absolute _ M hM _ (by intro i; cases i <;> simp [cons,he,hd])]
    exact eval_allDomainMatrix a φ d e
  change (∃ d ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,h⟩
    obtain ⟨hdt,h0,heD,haD,hφ⟩ := (matrix d hd).mp h
    have he' : ∀ i, e' i ∈ d := by
      intro i; dsimp [e']; split_ifs with hi
      · exact heD i hi
      · exact h0
    intro x hx
    apply (congr M x).mpr
    exact φ.transitive_upward hdt hM (fun y hy => hM d hd y hy) (cons x e')
      (by intro i; cases i with
          | zero => exact hdt _ haD x hx
          | succ i => exact he' i) ((congr d x).mp (hφ x hx))
  · intro hφ
    have hω := omega_mem M hM hS hI
    let ee := cons (e a) (cons ZFSet.omega e)
    have hee : ∀ i, ee i ∈ M := by
      intro i
      rcases i with _ | i
      · exact he a
      rcases i with _ | i
      · exact hω
      exact he i
    obtain ⟨t,ht,htt,hat,hentries⟩ := BoundedForcing.finite_container M hM hP hU hS hR hI
      ee hee (φ.scope+2)
    have hωt : ZFSet.omega.{u} ∈ t := hentries 1 (by omega)
    have h0t : (∅ : ZFSet.{u}) ∈ t := htt _ hωt _ ZFSet.omega_zero
    have he' : ∀ i, e' i ∈ t := by
      intro i; dsimp [e']; split_ifs with hi
      · exact hentries (i+2) (by omega)
      · exact h0t
    obtain ⟨D,hD,hDT,htD,hφD⟩ := internal_bounded_domain M hM hP hU hS hR hI hC
      (he a) ht htt hat e' he' φ (fun x hx => (congr M x).mp (hφ x hx))
    refine ⟨D,hD,(matrix D hD).mpr ⟨hDT,htD h0t,?_,htD hat,?_⟩⟩
    · intro i hi
      exact htD (hentries (i+2) (by omega))
    · intro x hx
      exact (congr D x).mpr (hφD x hx)
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
