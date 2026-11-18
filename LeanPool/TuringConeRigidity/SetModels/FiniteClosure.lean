/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FiniteClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TupleFormula

/-!
# Finite Closure
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

/-- The set `h` is closed under the outputs of the `n`-ary graph `g`. -/
def Closed (n : ℕ) (g h : ZFSet.{u}) : Prop :=
  ∀ xs : List ZFSet.{u}, xs.length = n → (∀ x ∈ xs, x ∈ h) →
    ∀ y, ZFSet.pair (code xs) y ∈ g → y ∈ h

/-- Bounded formula asserting that the first `n` variable values belong to the set in slot
`h`. -/
def memberPrefix : ℕ → ℕ → Formula
  | 0,_ => .equal 0 0
  | n+1,h => .conj (memberPrefix n h) (.member n h)

theorem eval_memberPrefix (n h : ℕ) (e : ℕ → ZFSet.{u}) :
    (memberPrefix n h).Eval e ↔ ∀ i, i < n → e i ∈ e h := by
  induction n with
  | zero => simp [memberPrefix,Formula.Eval]
  | succ n ih =>
    simp only [memberPrefix,Formula.Eval,ih]
    constructor
    · rintro ⟨ha,hb⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
      · exact ha i hi
      · exact hb
    · intro ha; exact ⟨fun i hi => ha i (Nat.lt_succ_of_lt hi),ha n (Nat.lt_succ_self n)⟩

theorem prepend_members (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) (h : ZFSet.{u}) :
    (∀ i, i < xs.length → prepend xs e i ∈ h) ↔ ∀ x ∈ xs, x ∈ h := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    constructor
    · intro ha y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ha 0 (Nat.zero_lt_succ _)
      · exact ih.mp (fun i hi => ha (i+1) (Nat.succ_lt_succ hi)) y hy
    · intro ha i hi
      cases i with
      | zero => exact ha x (by simp)
      | succ i => exact ih.mpr (fun y hy => ha y (by simp [hy])) i (Nat.lt_of_succ_lt_succ hi)

/-- Bounded formula asserting closure under the coded finite-tuple function graph. -/
def closedFormula (n a d c z g h : ℕ) : Formula :=
  .allMem a (.allMem (d+1) (.imp (.pairMem 1 0 (g+2))
    (.imp (unpack n 1 (c+2) (z+2) (memberPrefix n (n+h+2))) (.member 0 (h+2)))))

theorem eval_closedFormula (n a d c z g h : ℕ) (e : ℕ → ZFSet.{u})
    (ha : e a = space (e d) n) (hc : Transitive (e c))
    (hac : space (e d) n ⊆ e c) (hz : e z = ∅)
    (hg : e g ⊆ ZFSet.prod (space (e d) n) (e d)) (hh : e h ⊆ e d) :
    (closedFormula n a d c z g h).Eval e ↔ Closed n (e g) (e h) := by
  simp only [closedFormula,Formula.eval_allMem,Formula.eval_imp,Formula.eval_pairMem,
    Formula.Eval,cons_zero,cons_succ,ha]
  have decode (xs : List ZFSet.{u}) (hlen : xs.length = n) (hxs : ∀ x ∈ xs, x ∈ e d)
      (y : ZFSet.{u}) :
      (unpack n 1 (c+2) (z+2) (memberPrefix n (n+h+2))).Eval (cons y (cons (code xs) e)) ↔
        ∀ x ∈ xs, x ∈ e h := by
    subst n
    rw [eval_unpack xs 1 (c+2) (z+2) _ _ rfl hc (hac (code_mem_space _ xs hxs)) hz,
      eval_memberPrefix]
    have hp : prepend xs (cons y (cons (code xs) e)) (xs.length+h+2) = e h := by
      rw [show xs.length+h+2 = xs.length+(h+2) by omega,prepend_tail]
      rfl
    rw [hp]
    exact prepend_members xs _ _
  constructor
  · intro hf xs hlen hxs y hy
    have hxd : ∀ x ∈ xs, x ∈ e d := fun x hx => hh (hxs x hx)
    have hyD : y ∈ e d := by
      obtain ⟨t,_,v,hv,hp⟩ := ZFSet.mem_prod.mp (hg hy)
      obtain ⟨_,rfl⟩ := ZFSet.pair_inj.mp hp
      exact hv
    have ht : code xs ∈ space (e d) n := hlen ▸ code_mem_space _ xs hxd
    exact hf _ ht y hyD hy ((decode xs hlen hxd y).mpr hxs)
  · intro hf t ht y _ hty hhx
    obtain ⟨xs,hlen,hxs,rfl⟩ := (mem_space (e d) t n).mp ht
    exact hf xs hlen ((decode xs hlen hxs y).mp hhx) y hty

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
