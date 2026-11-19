/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedLimits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedComputability

public import LeanPool.TuringConeRigidity.Effective.StageEngineLimits

/-!
# Guarded Limits
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open GuardedStage
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The left limit oracle of the guarded condition construction. -/
def G₀ (A : Oracle) : Oracle :=
  StageEngineLimits.G₀ stateInterface (procedures A)

/-- The right limit oracle of the guarded condition construction. -/
def G₁ (A : Oracle) : Oracle :=
  StageEngineLimits.G₁ stateInterface (procedures A)

theorem generic_prefix_next (A : Oracle) (s : ℕ) :
    (generic A (construction A s)).left <+: (conditions A (s+1)).left ∧
    (generic A (construction A s)).right <+: (conditions A (s+1)).right :=
  StageEngineLimits.generic_prefix_next stateInterface (procedures A) (candidate_extends A) s

theorem limits_extend_generic (A : Oracle) (s : ℕ) :
    CommonIdeal.Extends (G₀ A) (generic A (construction A s)).left ∧
    CommonIdeal.Extends (G₁ A) (generic A (construction A s)).right :=
  StageEngineLimits.limits_extend_generic stateInterface (procedures A) (candidate_extends A)
    (open_extends A) s

/-- The selected open procedure decides each requirement above its output condition. -/
theorem open_decision (A : Oracle) (e : ℕ) (p : Condition) :
    OracleJump.Halts A e (openProcedure A (Nat.pair e (code p))) ∨
      ∀ r, Extends (columns A) (condition (openProcedure A (Nat.pair e (code p))))
        (condition r) → ¬ OracleJump.Halts A e r :=
  ((Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).2
    e (code p)).2

theorem meets_dense (A : Oracle) {P : ℕ → Prop} (hP : Sigma A 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends (columns A) p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ A) (condition q).left ∧
      CommonIdeal.Extends (G₁ A) (condition q).right :=
  StageEngineLimits.meets_dense stateInterface (procedures A) (candidate_extends A) (open_extends A)
    (open_decision A) hP hdense

theorem disagreement_recursive (A X : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hX : Reduces X A) : RecursivePred A (fun v =>
      loc (Nat.unpair v).2 < (left (Nat.unpair v).1).length ∧
      (left (Nat.unpair v).1).getD (loc (Nat.unpair v).2) false ≠ X (Nat.unpair v).2) :=
  StageEngineLimits.disagreement_recursive A X loc hloc hX

theorem reads_not_reduces (A : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ A (loc n)) A :=
  StageEngineLimits.reads_not_reduces stateInterface (procedures A) (candidate_extends A)
    (open_extends A)
    (open_decision A) loc hloc hunbounded

/-- Each individual coding column reduces to the construction's background oracle. -/
theorem column_reduces (A : Oracle) (k : ℕ) : Reduces ((columns A) k) A :=
  CodingExtraction.column_projection_reduces A k

theorem common_noncomputable_columns (A : Oracle)
    (hA : ∀ k, {a | columns A k a = true}.Infinite) :
    ∀ k, ∃ C : Oracle, Reduces C (join (G₀ A) (columns A k)) ∧
      Reduces C (join (G₁ A) (columns A k)) ∧ ¬ Reduces C (columns A k) :=
  StageEngineLimits.common_noncomputable_columns stateInterface (procedures A)
    (candidate_extends A) (open_extends A) (open_decision A) (column_reduces A) hA

theorem effective_first_clause (A : Oracle)
    (hA : ∀ k, {a | columns A k a = true}.Infinite) :
    Reduces (join (G₀ A) (G₁ A)) (OracleJump.jump A) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join (G₀ A) (columns A k)) ∧
        Reduces C (join (G₁ A) (columns A k)) ∧ ¬ Reduces C (columns A k) :=
  ⟨GuardedComputability.limits_recursive A,common_noncomputable_columns A hA⟩

end
end TuringRigidity.GuardedLimits

end OAI
