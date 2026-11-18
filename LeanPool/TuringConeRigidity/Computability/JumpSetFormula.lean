/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/JumpSetFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticOracles
public import LeanPool.TuringConeRigidity.Computability.ArithmeticSetSyntax

/-!
# Jump Set Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic OracleJump
universe u

namespace Formula
/-- Variable renaming that supplies one oracle parameter to every oracle query slot. -/
def singleOracleVars (o Q A n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => o
  | 2 => Q
  | _+3 => A

/-- Specialize an arithmetic formula to a single oracle parameter. -/
def singleOracle (φ : Formula) (o Q A n : ℕ) : Formula := φ.rename (singleOracleVars o Q A n)

theorem singleOracle_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q A n : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (B : Oracle) (hA : e A = realCode B) (N : ℕ) (hn : e n = natSet N) :
    (singleOracle φ o Q A n).Eval e ↔ P (fun _ => B) N := by
  rw [singleOracle,eval_rename]
  have he : (fun i => e (singleOracleVars o Q A n i)) = arithmeticEnv (e Q) (fun _ => B) N := by
    funext i
    rcases i with _ | i
    · exact hn
    rcases i with _ | i
    · exact ho
    rcases i with _ | i
    · rfl
    exact hA
  rw [he]
  exact hφ _ hQ _ _

/-- On the domain in slot `o`, match membership in slot `B` with the arithmetic formula for
the oracle in slot `A`. -/
def oracleGraph (φ : Formula) (o Q A B : ℕ) : Formula :=
  allMem o (iff (.member 0 (B+1)) (singleOracle φ (o+1) (Q+1) (A+1) 0))

theorem oracleGraph_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (A B : Oracle) (hx : e x = realCode A) (hy : e y = realCode B) :
    (oracleGraph φ o Q x y).Eval e ↔ ∀ n, B n = true ↔ P (fun _ => A) n := by
  simp only [oracleGraph,eval_allMem,eval_iff,Formula.Eval,cons_zero,cons_succ]
  rw [ho]
  constructor
  · intro h n
    have hn := h (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
    rw [hy,natSet_mem_realCode] at hn
    exact hn.trans (singleOracle_spec hφ (o+1) (Q+1) (x+1) 0 (cons (natSet n) e) ho hQ A hx n rfl)
  · intro h z hz
    obtain ⟨n,rfl⟩ := (mem_omega z).mp hz
    rw [hy,natSet_mem_realCode]
    exact (h n).trans (singleOracle_spec hφ (o+1) (Q+1) (x+1) 0 (cons (natSet n) e) ho hQ A hx n
      rfl).symm
end Formula

theorem jump_bounded_relation : ∃ φ : Formula, ∀ o Q x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.oracleGraph φ o Q x y).Eval e ↔ B = jump A) := by
  have h := Arith.comp (fun n => Nat.pair 0 n) (jump_arith (parameter_arith 0))
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)
  have hp : Arith (fun O n => jump (O 0) n = true) := h.congr (fun _ _ => by
    simp only [right, Nat.unpair_pair])
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hp
  refine ⟨φ,?_⟩
  intro o Q x y e ho hQ A B hx hy
  rw [Formula.oracleGraph_spec hφ o Q x y e ho hQ A B hx hy]
  constructor
  · intro hb
    funext n
    have hn := hb n
    cases ha : B n <;> cases hj : jump A n <;> simp_all
  · intro hb; subst B; exact fun _ => Iff.rfl

end TuringRigidity.BoundedSetTheory

end OAI
