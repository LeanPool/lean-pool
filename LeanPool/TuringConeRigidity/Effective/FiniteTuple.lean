/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteTuple.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaSyntax
public import LeanPool.TuringConeRigidity.SetModels.ModelProducts

/-!
# Finite Tuple
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace Formula
theorem eval_rename (φ : Formula) (v : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (φ.rename v).Eval e ↔ φ.Eval (fun i => e (v i)) := by
  induction φ generalizing v e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v e) (ihψ v e)
  | neg φ ih => exact not_congr (ih v e)
  | existsMem i φ ih =>
    simp only [rename,Eval]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    have he : (fun i => cons x e (liftMap v i)) = cons x (fun i => e (v i)) := by
      funext i; cases i <;> rfl
    exact (ih (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)
end Formula

namespace FiniteTuple
/-- Encode a list of sets as nested ordered pairs ending in the empty set. -/
noncomputable def code : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x (code xs)

/-- The set of nested-pair codes for tuples of the specified length with entries in `d`. -/
noncomputable def space (d : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => {∅}
  | n+1 => ZFSet.prod d (space d n)

/-- Prepend a finite list of values to a variable environment. -/
def prepend (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u} :=
  xs.foldr cons e

@[simp] theorem prepend_nil (e : ℕ → ZFSet.{u}) : prepend [] e = e := rfl
@[simp] theorem prepend_cons (x : ZFSet.{u}) (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    prepend (x :: xs) e = cons x (prepend xs e) := rfl

theorem space_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) : space d n ∈ M := by
  have h0 : (∅ : ZFSet.{u}) ∈ M := by
    have hs := sep_mem M hM hS (.neg (.equal 0 0)) (fun _ => d) (fun _ => hd) hd
    have heq : ZFSet.sep (fun x => (Formula.neg (.equal 0 0)).Eval (cons x (fun _ => d))) d = ∅ :=
      by
      apply ZFSet.ext; intro x; simp [ZFSet.mem_sep,Formula.Eval]
    exact heq ▸ hs
  induction n with
  | zero => exact singleton_mem M hM hP h0
  | succ n ih => exact product_mem M hM hP hU hPow hS hd ih

theorem mem_space (d t : ZFSet.{u}) (n : ℕ) :
    t ∈ space d n ↔ ∃ xs : List ZFSet.{u}, xs.length = n ∧
      (∀ x ∈ xs, x ∈ d) ∧ t = code xs := by
  induction n generalizing t with
  | zero =>
    simp only [space,ZFSet.mem_singleton,List.length_eq_zero_iff]
    constructor
    · intro h; exact ⟨[],rfl,by simp,h⟩
    · rintro ⟨xs,rfl,_,h⟩; exact h
  | succ n ih =>
    rw [space,ZFSet.mem_prod]
    constructor
    · rintro ⟨x,hx,t,ht,rfl⟩
      obtain ⟨xs,hlen,hxs,rfl⟩ := (ih t).mp ht
      refine ⟨x :: xs, by simp [hlen], ?_, rfl⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hxs y hy
    · rintro ⟨xs,hlen,hxs,rfl⟩
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
        refine ⟨x,hxs x (by simp),code xs,(ih _).mpr ?_,rfl⟩
        exact ⟨xs,Nat.succ.inj hlen,fun y hy => hxs y (by simp [hy]),rfl⟩

theorem code_mem_space (d : ZFSet.{u}) (xs : List ZFSet.{u})
    (hx : ∀ x ∈ xs, x ∈ d) : code xs ∈ space d xs.length :=
  (mem_space d _ _).mpr ⟨xs,rfl,hx,rfl⟩

theorem code_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (h0 : (∅ : ZFSet.{u}) ∈ M) (xs : List ZFSet.{u})
    (hx : ∀ x ∈ xs, x ∈ M) : code xs ∈ M := by
  induction xs with
  | nil => exact h0
  | cons x xs ih =>
    exact orderedPair_mem M hM hP (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))

theorem code_injective_length (xs ys : List ZFSet.{u}) (hlen : xs.length = ys.length)
    (h : code xs = code ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨rfl,ht⟩ := ZFSet.pair_inj.mp h
      rw [ih ys (Nat.succ.inj hlen) ht]

theorem prepend_tail (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) (i : ℕ) :
    prepend xs e (xs.length+i) = e i := by
  induction xs with
  | nil => simp only [prepend_nil,List.length_nil,Nat.zero_add]
  | cons x xs ih => simpa only [List.length_cons,Nat.succ_add,prepend_cons,cons_succ] using ih

theorem prepend_congr (xs : List ZFSet.{u}) (e f : ℕ → ZFSet.{u})
    (i : ℕ) (hi : i < xs.length) : prepend xs e i = prepend xs f i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- Map slot zero to `n + 1`, shift slots one through `n` down by one, and shift later slots
up by one. -/
def rotate (n : ℕ) : ℕ → ℕ
  | 0 => n+1
  | i+1 => if i < n then i else i+2

theorem prepend_rotate (xs : List ZFSet.{u}) (x t : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fun i => prepend xs (cons t (cons x e)) (rotate xs.length i)) =
      cons x (prepend xs e) := by
  funext i
  cases i with
  | zero => exact prepend_tail xs (cons t (cons x e)) 1
  | succ i =>
    change prepend xs (cons t (cons x e)) (if i < xs.length then i else i+2) = prepend xs e i
    by_cases hi : i < xs.length
    · rw [ite_eq_left hi]; exact prepend_congr xs _ _ i hi
    · rw [ite_eq_right hi]
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      rw [Nat.add_assoc,prepend_tail,prepend_tail]
      rfl

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
