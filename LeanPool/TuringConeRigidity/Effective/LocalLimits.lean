/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalLimits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalComputability

public import LeanPool.TuringConeRigidity.Effective.StageEngineLimits

/-!
# Local Limits
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open LocalStage
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The left limit oracle of the local condition construction. -/
def G₀ (D : LocalInputs.Data) : Oracle :=
  StageEngineLimits.G₀ stateInterface (procedures D)

/-- The right limit oracle of the local condition construction. -/
def G₁ (D : LocalInputs.Data) : Oracle :=
  StageEngineLimits.G₁ stateInterface (procedures D)

theorem generic_prefix_next (D : LocalInputs.Data) (s : ℕ) :
    (generic D (construction D s)).left <+: (conditions D (s+1)).left ∧
    (generic D (construction D s)).right <+: (conditions D (s+1)).right :=
  StageEngineLimits.generic_prefix_next stateInterface (procedures D) (candidate_extends D) s

theorem limits_extend_generic (D : LocalInputs.Data) (s : ℕ) :
    CommonIdeal.Extends (G₀ D) (generic D (construction D s)).left ∧
    CommonIdeal.Extends (G₁ D) (generic D (construction D s)).right :=
  StageEngineLimits.limits_extend_generic stateInterface (procedures D) (candidate_extends D)
    (open_extends D) s

/-- The selected open procedure decides each requirement above its output condition. -/
theorem open_decision (D : LocalInputs.Data) (e : ℕ) (p : Condition) :
    OracleJump.Halts D.B e (openProcedure D (Nat.pair e (code p))) ∨
      ∀ r, Extends D.F (condition (openProcedure D (Nat.pair e (code p))))
        (condition r) → ¬ OracleJump.Halts D.B e r := by
  rcases (D.open_spec e (code p)).2 with h | ⟨he, hn⟩
  · exact Or.inl h
  · exact Or.inr (by simpa only [openProcedure, he] using hn)

theorem meets_dense (D : LocalInputs.Data) {P : ℕ → Prop} (hP : Sigma D.B 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends D.F p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ D) (condition q).left ∧
      CommonIdeal.Extends (G₁ D) (condition q).right :=
  StageEngineLimits.meets_dense stateInterface (procedures D) (candidate_extends D) (open_extends D)
    (open_decision D) hP hdense

theorem disagreement_recursive (A X : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hX : Reduces X A) : RecursivePred A (fun v =>
      loc (Nat.unpair v).2 < (left (Nat.unpair v).1).length ∧
      (left (Nat.unpair v).1).getD (loc (Nat.unpair v).2) false ≠ X (Nat.unpair v).2) :=
  StageEngineLimits.disagreement_recursive A X loc hloc hX

theorem reads_not_reduces (D : LocalInputs.Data) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction D.B} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ D (loc n)) D.B :=
  StageEngineLimits.reads_not_reduces stateInterface (procedures D) (candidate_extends D)
    (open_extends D)
    (open_decision D) loc hloc hunbounded

/-- Each individual coding column reduces to the construction's background oracle. -/
theorem column_reduces (D : LocalInputs.Data) (k : ℕ) : Reduces (D.F k) D.B :=
  TableIndices.represents_reduces (D.codes_valid (k+1) k (Nat.lt_succ_self k))

theorem common_noncomputable_columns (D : LocalInputs.Data)
    (hA : ∀ k, {a | D.F k a = true}.Infinite) :
    ∀ k, ∃ C : Oracle, Reduces C (join (G₀ D) (D.F k)) ∧
      Reduces C (join (G₁ D) (D.F k)) ∧ ¬ Reduces C (D.F k) :=
  StageEngineLimits.common_noncomputable_columns stateInterface (procedures D)
    (candidate_extends D) (open_extends D) (open_decision D) (column_reduces D) hA

theorem effective_first_clause (D : LocalInputs.Data)
    (hA : ∀ k, {a | D.F k a = true}.Infinite) :
    Reduces (join (G₀ D) (G₁ D)) (D.bound) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join (G₀ D) (D.F k)) ∧
        Reduces C (join (G₁ D) (D.F k)) ∧ ¬ Reduces C (D.F k) :=
  ⟨LocalComputability.limits_recursive D,common_noncomputable_columns D hA⟩

end
end TuringRigidity.LocalLimits

end OAI
