/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TupleFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteTuple

/-!
# Tuple Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

/-- Unpack a nested-pair tuple code into bound variables before evaluating the renamed body. -/
def unpack : ℕ → ℕ → ℕ → ℕ → Formula → Formula
  | 0,t,_c,z,φ => .conj (.equal t z) φ
  | n+1,t,c,z,φ => .existsMem c (.existsMem (c+1)
      (.conj (.orderedPair (t+2) 1 0)
        (unpack n 0 (c+2) (z+2) (φ.rename (rotate n)))))

theorem pair_components {c x y : ZFSet.{u}} (hc : Transitive c)
    (hp : ZFSet.pair x y ∈ c) : x ∈ c ∧ y ∈ c := by
  have hxy : ({x,y} : ZFSet.{u}) ∈ c :=
    hc _ hp _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  exact ⟨hc _ hxy _ (ZFSet.mem_pair.mpr (Or.inl rfl)),
    hc _ hxy _ (ZFSet.mem_pair.mpr (Or.inr rfl))⟩

theorem eval_unpack (xs : List ZFSet.{u}) (t c z : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (ht : e t = code xs) (hc : Transitive (e c))
    (hcode : code xs ∈ e c) (hz : e z = ∅) :
    (unpack xs.length t c z φ).Eval e ↔ φ.Eval (prepend xs e) := by
  induction xs generalizing t c z φ e with
  | nil =>
    simp only [List.length_nil,unpack,Formula.Eval,ht,hz,code,prepend_nil,true_and]
  | cons x xs ih =>
    have hparts := pair_components hc hcode
    simp only [List.length_cons,unpack,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,ht]
    constructor
    · rintro ⟨y,hy,s,hs,hpair,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
      have h := (ih 0 (c+2) (z+2) (φ.rename (rotate xs.length))
        (cons (code xs) (cons x e)) rfl hc hparts.2 hz).mp hφ
      rw [Formula.eval_rename,prepend_rotate] at h
      exact h
    · intro h
      refine ⟨x,hparts.1,code xs,hparts.2,rfl,?_⟩
      apply (ih 0 (c+2) (z+2) (φ.rename (rotate xs.length))
        (cons (code xs) (cons x e)) rfl hc hparts.2 hz).mpr
      rw [Formula.eval_rename,prepend_rotate]
      exact h

/-- Relativize every bounded existential quantifier to the specified domain slot. -/
def relativizeBounded (d : ℕ) : Formula → Formula
  | .equal i j => .equal i j
  | .member i j => .member i j
  | .conj φ ψ => .conj (relativizeBounded d φ) (relativizeBounded d ψ)
  | .neg φ => .neg (relativizeBounded d φ)
  | .existsMem i φ => .existsMem d (.conj (.member 0 (i+1)) (relativizeBounded (d+1) φ))

theorem eval_relativizeBounded (φ : Formula) (d : ℕ) (e : ℕ → ZFSet.{u}) :
    (relativizeBounded d φ).Eval e ↔ φ.Realize (e d) e := by
  induction φ generalizing d e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ d e) (ihψ d e)
  | neg φ ih => exact not_congr (ih d e)
  | existsMem i φ ih =>
    simp only [relativizeBounded,Formula.Eval,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    exact and_congr_right (fun _ => ih (d+1) (cons x e))

/-- Turn sigma existential set quantifiers into bounded quantifiers over the specified domain. -/
def relativizeSigma (d : ℕ) : SigmaFormula → Formula
  | .bounded φ => relativizeBounded d φ
  | .existsSet φ => .existsMem d (relativizeSigma (d+1) φ)

theorem eval_relativizeSigma (φ : SigmaFormula) (d : ℕ) (e : ℕ → ZFSet.{u}) :
    (relativizeSigma d φ).Eval e ↔ φ.Realize (e d) e := by
  induction φ generalizing d e with
  | bounded φ => exact eval_relativizeBounded φ d e
  | existsSet φ ih =>
    simp only [relativizeSigma,Formula.Eval,SigmaFormula.Realize]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (d+1) (cons x e))

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
