/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/JumpProperties.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.OracleJump
public import LeanPool.TuringConeRigidity.Computability.ArithmeticAtoms

/-!
# Jump Properties
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OracleJump
open Encodable UniformOracle CommonIdeal TableIndices IndexMatrix ArithmeticHierarchy

theorem recursive_transfer {Y Z : Oracle} {P : ℕ → Prop}
    (h : RecursivePred Y P) (hYZ : Reduces Y Z) : RecursivePred Z P :=
  RecursiveIn.iff_nat.mp (TuringReducible.trans (RecursiveIn.iff_nat.mpr h) hYZ)

theorem recursive_lift {Y : Oracle} {P : ℕ → Prop} (h : RecursivePred Y P) :
    RecursivePred (jump Y) P := by
  have hh := exists_recursive_jump (recursive_comp h (Primrec.fst.comp Primrec.unpair))
  exact Form.congr (n := 0) (s := true) hh (fun x => by simp)

theorem reduces_jump (Y : Oracle) : Reduces Y (jump Y) := by
  have h : RecursivePred Y (fun x => Y x = true) := by
    classical
    have hq : Nat.RecursiveIn {oracleFunction Y} (oracleFunction Y) :=
      .oracle _ (Set.mem_singleton _)
    exact hq.of_eq (fun x => by cases hy : Y x <;> simp [oracleFunction,hy])
  apply RecursiveIn.iff_nat.mpr
  exact (recursive_lift h).of_eq (fun x => by cases hy : Y x <;> simp [oracleFunction,hy])

theorem halts_sigma (Y : Oracle) :
    Sigma Y 1 (fun v => Halts Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have ht := total_comp (run_uniform_recursive Y) (total_primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (s.comp f) s)))
  have hcheck : Primrec (fun v : ℕ => bit ((decode (α := Option ℕ) v).getD none).isSome) :=
    bit_primrec.comp (Primrec.option_isSome.comp
      (Primrec.option_getD.comp Primrec.decode (Primrec.const none)))
  have h : RecursivePred Y (fun v =>
      (TableIndices.run Y (machine (Nat.unpair (Nat.unpair v).1).1)
        (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2).isSome = true) := by
    exact (total_comp (total_primrec hcheck) ht).of_eq (fun v => by
      simp only [Nat.unpair_pair, encodek, Option.getD_some, bit]
      congr 1
      split <;> rfl)
  apply (exists_form (n := 0) h).congr
  intro v
  simp only [Nat.unpair_pair, Halts]
  apply exists_congr
  intro z
  cases TableIndices.run Y (machine (Nat.unpair v).1) (Nat.unpair v).2 z <;> simp

theorem jump_mono {Y Z : Oracle} (hYZ : Reduces Y Z) : Reduces (jump Y) (jump Z) := by
  obtain ⟨Q,hQ,he⟩ := halts_sigma Y
  have h := exists_recursive_jump (recursive_transfer hQ hYZ)
  have h' : RecursivePred (jump Z) (fun v => Halts Y (Nat.unpair v).1 (Nat.unpair v).2) :=
    Form.congr (n := 0) (s := true) h (fun v => (he v).symm)
  apply RecursiveIn.iff_nat.mpr
  exact h'.of_eq (fun v => by
    classical
    by_cases h : Halts Y (Nat.unpair v).1 (Nat.unpair v).2 <;> simp [oracleFunction, jump, h])

theorem iterate_mono {Y Z : Oracle} (hYZ : Reduces Y Z) (n : ℕ) :
    Reduces (iterate Y n) (iterate Z n) := by
  induction n with
  | zero => exact hYZ
  | succ n ih => exact jump_mono ih

/-- The Turing jump operation on degrees, independent of the chosen oracle representative. -/
noncomputable def degreeJump (x : Degree) : Degree :=
  Quotient.liftOn x (fun Y => degree (jump Y)) (fun Y Z h =>
    (degree_eq_iff (jump Y) (jump Z)).mpr ⟨jump_mono h.1, jump_mono h.2⟩)

@[simp] theorem degreeJump_degree (Y : Oracle) : degreeJump (degree Y) = degree (jump Y) := rfl

theorem degree_le_jump (x : Degree) : x ≤ degreeJump x := by
  obtain ⟨Y,rfl⟩ := degree_surjective x
  exact reduces_jump Y

theorem degreeJump_mono : Monotone degreeJump := by
  intro x y h
  obtain ⟨Y,rfl⟩ := degree_surjective x
  obtain ⟨Z,rfl⟩ := degree_surjective y
  exact jump_mono h

end TuringRigidity.OracleJump

end OAI
