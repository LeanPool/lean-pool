/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelRealOperations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticComprehension
public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations

/-!
# Model Real Operations
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic Encodable TableIndices OracleJump IndexMatrix
universe u

theorem sourceT_arithmetic_oracle (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {B : OracleFamily} (hB : ArithmeticOracle B) (O : Oracles)
    (hO : ∀ i, O i ∈ modelReals M) (v : ℕ) : B O v ∈ modelReals M := by
  have hp := Arith.comp (fun n => Nat.pair v n) hB (Primrec₂.natPair.comp (Primrec.const v)
    Primrec.id)
  exact sourceT_arithmetic_real M hM hT hp O hO (B O v)
    (fun n => by simp only [left,right,Nat.unpair_pair])

theorem sourceT_real_lower (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A B : Oracle} (hB : B ∈ modelReals M) (hAB : Reduces A B) : A ∈ modelReals M := by
  obtain ⟨d,hd⟩ := reduces_represents hAB
  have hd' : Represents B (machine (encode d)) A := by simpa using hd
  have h := sourceT_arithmetic_oracle M hM hT
    (tableOracle_arith (parameter_arith 0) (Primrec.const (encode d))) (fun _ => B) (fun _ => hB) 0
  change tableOracle B (encode d) ∈ modelReals M at h
  rw [tableOracle_eq hd'] at h
  exact h

theorem sourceT_real_join (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A B : Oracle} (hA : A ∈ modelReals M) (hB : B ∈ modelReals M) :
    TuringRigidity.join A B ∈ modelReals M := by
  let O : Oracles := fun i => if i = 0 then A else B
  have hO : ∀ i, O i ∈ modelReals M := by
    intro i; dsimp [O]; split <;> assumption
  have h := sourceT_arithmetic_oracle M hM hT
    (join_arith (parameter_arith 0) (parameter_arith 1)) O hO 0
  simpa [O] using h

theorem sourceT_real_jump (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) : jump A ∈ modelReals M :=
  sourceT_arithmetic_oracle M hM hT (jump_arith (parameter_arith 0))
    (fun _ => A) (fun _ => hA) 0

theorem sourceT_real_iterate (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) (n : ℕ) : iterate A n ∈ modelReals M := by
  induction n with
  | zero => exact hA
  | succ n ih => exact sourceT_real_jump M hM hT ih

end TuringRigidity.BoundedSetTheory

end OAI
