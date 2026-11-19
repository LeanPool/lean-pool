/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalInfinity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Internal Infinity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The von Neumann natural number corresponding to `n`. -/
def natSet : ℕ → ZFSet.{u}
  | 0 => ∅
  | n+1 => insert (natSet n) (natSet n)

theorem natSet_eq_mk (n : ℕ) : natSet.{u} n = ZFSet.mk (PSet.ofNat n) := by
  induction n with
  | zero => rfl
  | succ n ih => change insert (natSet n) (natSet n) = _; rw [ih]; rfl

theorem mem_natSet (n : ℕ) (x : ZFSet.{u}) :
    x ∈ natSet n ↔ ∃ i < n, x = natSet i := by
  induction n with
  | zero => simp [natSet]
  | succ n ih =>
    rw [natSet,ZFSet.mem_insert_iff,ih]
    constructor
    · rintro (rfl|⟨i,hi,hx⟩)
      · exact ⟨n,Nat.lt_succ_self n,rfl⟩
      · exact ⟨i,Nat.lt_succ_of_lt hi,hx⟩
    · rintro ⟨i,hi,hx⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
      · exact Or.inr ⟨i,hi,hx⟩
      · exact Or.inl hx

theorem natSet_injective : Function.Injective natSet.{u} := by
  intro n m h
  rcases Nat.lt_trichotomy n m with hn|he|hm
  · exact False.elim (ZFSet.mem_irrefl (natSet m)
      (h ▸ (mem_natSet m _).mpr ⟨n,hn,rfl⟩))
  · exact he
  · exact False.elim (ZFSet.mem_irrefl (natSet n)
      (h.symm ▸ (mem_natSet n _).mpr ⟨m,hm,rfl⟩))

theorem natSet_mem_natSet (n m : ℕ) : natSet.{u} n ∈ natSet m ↔ n < m := by
  rw [mem_natSet]
  exact ⟨fun ⟨i,hi,he⟩ => natSet_injective he ▸ hi,fun h => ⟨n,h,rfl⟩⟩

theorem natSet_transitive (n : ℕ) : Transitive (natSet.{u} n) := by
  intro x hx y hy
  obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
  obtain ⟨j,hj,rfl⟩ := (mem_natSet i y).mp hy
  exact (natSet_mem_natSet j n).mpr (Nat.lt_trans hj hi)

theorem mem_omega (x : ZFSet.{u}) : x ∈ ZFSet.omega ↔ ∃ n, x = natSet n := by
  induction x using Quotient.inductionOn with
  | h x =>
    change (∃ n : ULift ℕ, PSet.Equiv x (PSet.ofNat n.down)) ↔ _
    constructor
    · rintro ⟨⟨n⟩,hn⟩
      exact ⟨n,(Quotient.sound hn).trans (natSet_eq_mk n).symm⟩
    · rintro ⟨n,hn⟩
      exact ⟨⟨n⟩,Quotient.exact (hn.trans (natSet_eq_mk n))⟩

theorem omega_transitive : Transitive ZFSet.omega.{u} := by
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
  exact (mem_omega _).mpr ⟨i,rfl⟩

namespace Formula
/-- Bounded formula asserting that the set in slot `x` has no members. -/
def empty (x : ℕ) : Formula := allMem x (.neg (.equal 0 0))
/-- Bounded formula asserting that `s` is the von Neumann successor of `n`. -/
def successor (s n : ℕ) : Formula :=
  .conj (.member n s) (.conj (subset n s)
    (allMem s (disj (.equal 0 (n+1)) (.member 0 (n+1)))))

@[simp] theorem eval_empty (x : ℕ) (e : ℕ → ZFSet.{u}) :
    (empty x).Eval e ↔ e x = ∅ := by
  simp only [empty,eval_allMem,Eval,cons_zero,not_true_eq_false]
  constructor
  · intro h; apply ZFSet.ext; intro z; simp only [ZFSet.notMem_empty,iff_false]; exact h z
  · intro h; simp [h]

@[simp] theorem eval_successor (s n : ℕ) (e : ℕ → ZFSet.{u}) :
    (successor s n).Eval e ↔ e s = insert (e n) (e n) := by
  simp only [successor,Eval,eval_subset,eval_allMem,eval_disj,cons_zero,cons_succ]
  constructor
  · rintro ⟨hn,hsub,hall⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨hall z,fun h => h.elim (fun h => h ▸ hn) (fun h => hsub h)⟩
  · intro h; rw [h]
    exact ⟨ZFSet.mem_insert _ _,fun _ hz => ZFSet.mem_insert_of_mem _ hz,
      fun _ hz => ZFSet.mem_insert_iff.mp hz⟩

/-- Bounded formula asserting that the set is empty or is a successor of one of its members. -/
def zeroOrSuccessor (x : ℕ) : Formula :=
  disj (empty x) (.existsMem x (successor (x+1) 0))

/-- Bounded formula characterizing a finite ordinal by transitivity and zero-or-successor
clauses. -/
def finiteOrdinal (x : ℕ) : Formula := .conj (transitive x)
  (.conj (allMem x (transitive 0))
    (.conj (zeroOrSuccessor x) (allMem x (zeroOrSuccessor 0))))

theorem eval_zeroOrSuccessor (x : ℕ) (e : ℕ → ZFSet.{u}) :
    (zeroOrSuccessor x).Eval e ↔ e x = ∅ ∨ ∃ y ∈ e x, e x = insert y y := by
  simp only [zeroOrSuccessor,eval_disj,eval_empty,Eval,eval_successor,cons_zero,cons_succ]
end Formula

/-- Transitivity and zero-or-successor clauses characterizing the von Neumann finite ordinals. -/
def FiniteOrdinal (x : ZFSet.{u}) : Prop := Transitive x ∧ (∀ y ∈ x, Transitive y) ∧
  (x = ∅ ∨ ∃ y ∈ x, x = insert y y) ∧
  ∀ y ∈ x, y = ∅ ∨ ∃ z ∈ y, y = insert z z

theorem eval_finiteOrdinal (x : ℕ) (e : ℕ → ZFSet.{u}) :
    (Formula.finiteOrdinal x).Eval e ↔ FiniteOrdinal (e x) := by
  simp only [Formula.finiteOrdinal,Formula.Eval,Formula.eval_transitive,
    Formula.eval_allMem,Formula.eval_zeroOrSuccessor,cons_zero,FiniteOrdinal]

theorem finiteOrdinal_natSet (n : ℕ) : FiniteOrdinal (natSet.{u} n) := by
  have hshape (n : ℕ) : natSet.{u} n = ∅ ∨ ∃ y ∈ natSet n, natSet n = insert y y := by
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨_,ZFSet.mem_insert _ _,rfl⟩
  refine ⟨natSet_transitive n,?_,hshape n,?_⟩
  · intro y hy
    obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
    exact natSet_transitive i
  · intro y hy
    obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
    exact hshape i

theorem finiteOrdinal_iff (x : ZFSet.{u}) : FiniteOrdinal x ↔ ∃ n, x = natSet n := by
  constructor
  · induction x using ZFSet.inductionOn with
    | h x ih =>
      intro h
      rcases h.2.2.1 with he|⟨y,hy,he⟩
      · exact ⟨0,he⟩
      · have hyf : FiniteOrdinal y := ⟨h.2.1 y hy,
          fun z hz => h.2.1 z (h.1 y hy z hz),h.2.2.2 y hy,
          fun z hz => h.2.2.2 z (h.1 y hy z hz)⟩
        obtain ⟨n,rfl⟩ := ih y hy hyf
        exact ⟨n+1,he⟩
  · rintro ⟨n,rfl⟩; exact finiteOrdinal_natSet n

/-- The model contains an internally inductive set with an internally empty element. -/
def Infinity (M : ZFSet.{u}) : Prop :=
  ∃ a ∈ M, (∃ e ∈ M, e ∈ a ∧ ∀ z ∈ M, z ∉ e) ∧
    ∀ x ∈ M, x ∈ a → ∃ s ∈ M, s ∈ a ∧
      ∀ z ∈ M, z ∈ s ↔ z = x ∨ z ∈ x

theorem omega_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hI : Infinity M) : ZFSet.omega.{u} ∈ M := by
  obtain ⟨a,ha,⟨e,he,hea,hee⟩,hs⟩ := hI
  have he0 : e = ∅ := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.notMem_empty,iff_false]
    exact fun hz => hee z (hM e he z hz) hz
  have hn (n : ℕ) : natSet.{u} n ∈ a := by
    induction n with
    | zero => simpa only [natSet,he0] using hea
    | succ n ih =>
      obtain ⟨s,hsM,hsa,hsdef⟩ := hs _ (hM a ha _ ih) ih
      have heq : s = insert (natSet n) (natSet n) := by
        apply ZFSet.ext; intro z; rw [ZFSet.mem_insert_iff]
        constructor
        · intro hz; exact (hsdef z (hM s hsM z hz)).mp hz
        · intro hz
          have hzM : z ∈ M := hz.elim (fun h => h ▸ hM a ha _ ih)
            (fun h => hM _ (hM a ha _ ih) z h)
          exact (hsdef z hzM).mpr hz
      simpa only [natSet,←heq] using hsa
  have hsep := sep_mem M hM hS (.finiteOrdinal 0) (fun _ => a) (fun _ => ha) ha
  have heq : ZFSet.sep (fun x => (Formula.finiteOrdinal 0).Eval (cons x (fun _ => a))) a =
      ZFSet.omega := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,eval_finiteOrdinal,cons_zero,finiteOrdinal_iff,mem_omega]
    exact ⟨And.right,fun h => ⟨by obtain ⟨n,rfl⟩ := h; exact hn n,h⟩⟩
  exact heq ▸ hsep

end TuringRigidity.BoundedSetTheory

end OAI
