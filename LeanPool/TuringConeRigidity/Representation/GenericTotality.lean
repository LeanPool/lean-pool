/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericTotality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.ProgramContinuity
public import LeanPool.TuringConeRigidity.Representation.GenericTruth

/-!
# Generic Totality
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set FiniteShuffle ShuffleRequirements GenericTruth

/-- The computation halts on the specified input with one of the two Boolean values. -/
def BinaryHalts (p : OracleCode) (P A : Oracle) (n : ℕ) : Prop :=
  0 ∈ OracleCode.eval (oracleFunction (join A P)) p n ∨
  1 ∈ OracleCode.eval (oracleFunction (join A P)) p n

theorem total_iff_binaryHalts (p : OracleCode) (P A : Oracle) :
    Total p P A ↔ ∀ n, BinaryHalts p P A n := by
  constructor
  · rintro ⟨B,hB⟩ n
    unfold BinaryHalts
    rw [hB]
    cases B n <;> simp [oracleFunction]
  · intro h
    apply (total_iff p P A).mpr
    apply (OracleCode.eval_eq_oracle_iff p _ _).mpr
    intro n
    rcases h n with h0 | h1
    · have hv : value p P A n = false := by
        have hn : ¬ 1 ∈ OracleCode.eval (oracleFunction (join A P)) p n := by
          intro h1
          have he := Part.mem_unique h0 h1
          omega
        simp [value,programOutput,hn]
      simpa [hv] using h0
    · have hv : value p P A n = true := by
        simp [value,programOutput,h1]
      simpa [hv] using h1

theorem binaryHalts_isOpen (p : OracleCode) (P : Oracle) (n : ℕ) :
    IsOpen {A | BinaryHalts p P A n} := by
  have hO : Continuous (fun A : Oracle => join A P) := by
    apply continuous_pi
    intro i
    dsimp only [join]
    split
    · exact continuous_const
    · exact continuous_apply _
  exact ((OracleCode.halting_set_open p n 0).union
    (OracleCode.halting_set_open p n 1)).preimage hO

theorem generic_totality_of_dense (p : OracleCode) (P : Oracle)
    (hd : Dense {A | Total p P A}) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
      (∀ A, GenericFor D A → Total p P A) ∧
      ContinuousOn (value p P) {A | GenericFor D A} := by
  let D := fun n => CylinderIn {A | BinaryHalts p P A n}
  have hD : ∀ n, DenseOpen (D n) := by
    intro n
    apply cylinderIn_denseOpen _ (binaryHalts_isOpen p P n)
    exact hd.mono (fun A hA => (total_iff_binaryHalts p P A).mp hA n)
  have ht : ∀ A, GenericFor D A → Total p P A := by
    intro A hA
    apply (total_iff_binaryHalts p P A).mpr
    intro n
    obtain ⟨s,hs,hAs⟩ := hA n
    exact hs A hAs
  exact ⟨D,hD,ht,value_continuousOn p P _ ht⟩

end TuringRigidity.GenericIdentity

end OAI
