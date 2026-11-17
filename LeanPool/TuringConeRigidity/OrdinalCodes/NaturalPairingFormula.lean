/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalPairingFormula.lean.
Also incorporates the common natural-pair witness argument from upstream
SetModels/CountableSetReal.lean, SetModels/InternalNaturalRelationReal.lean and
SetModels/InternalCountableFiniteUnion.lean under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalTermFormula

/-!
# Natural Pairing Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

/-- Variable renaming supplying the two inputs of the numerical pairing terms. -/
def pairVars (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | _+1 => b

/-- The arithmetic term used by the increasing-coordinate branch of natural-number pairing. -/
def pairLeftTerm : NaturalTerm := .binary false (.binary true (.var 1) (.var 1)) (.var 0)
/-- The arithmetic term used by the other branch of natural-number pairing. -/
def pairRightTerm : NaturalTerm := .binary false
  (.binary false (.binary true (.var 0) (.var 0)) (.var 0)) (.var 1)

/-- Bounded formula computing natural-number pairing by its two arithmetic branches. -/
def naturalPair (o Q x n y : ℕ) : Formula := .disj
  (.conj (.member x n) (pairLeftTerm.graph o Q y (pairVars x n)))
  (.conj (.neg (.member x n)) (pairRightTerm.graph o Q y (pairVars x n)))

theorem naturalPair_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (naturalPair o Q x n y).Eval e ↔ e y = natSet (Nat.pair a b) := by
  have hv : ∀ i, e (pairVars x n i) = natSet (pairVars a b i) := by
    intro i; cases i <;> assumption
  have hl := NaturalTerm.graph_spec pairLeftTerm o Q y (pairVars x n) e ho hQ (pairVars a b) hv
  have hr := NaturalTerm.graph_spec pairRightTerm o Q y (pairVars x n) e ho hQ (pairVars a b) hv
  change (pairLeftTerm.graph o Q y (pairVars x n)).Eval e ↔ e y = natSet (b*b+a) at hl
  change (pairRightTerm.graph o Q y (pairVars x n)).Eval e ↔ e y = natSet (a*a+a+b) at hr
  simp only [naturalPair,eval_disj,Formula.Eval,hl,hr,ha,hb,natSet_mem_natSet,Nat.pair]
  by_cases h : a < b <;> simp [h]

/-- Eliminate two natural witnesses whose paired code is fixed, preserving any payload. -/
theorem naturalPair_exists_payload (o Q v : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N K : ℕ) (hv : e v = natSet (Nat.pair N K)) (P : ZFSet.{u} → ZFSet.{u} → Prop) :
    (∃ n ∈ ZFSet.omega, ∃ k ∈ ZFSet.omega,
      (naturalPair (o+2) (Q+2) 1 0 (v+2)).Eval (cons k (cons n e)) ∧ P n k) ↔
      P (natSet N) (natSet K) := by
  constructor
  · rintro ⟨n,hn,k,hk,hpair,hrest⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
    have hpair' := (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
      (cons (natSet k) (cons (natSet n) e)) ho hQ n k rfl rfl).mp hpair
    have he := congrArg Nat.unpair (natSet_injective (hv.symm.trans hpair'))
    simp only [Nat.unpair_pair, Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact hrest
  · intro h
    exact ⟨natSet N,(mem_omega _).mpr ⟨N,rfl⟩,natSet K,(mem_omega _).mpr ⟨K,rfl⟩,
      (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
        (cons (natSet K) (cons (natSet N) e)) ho hQ N K rfl rfl).mpr hv,h⟩

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
