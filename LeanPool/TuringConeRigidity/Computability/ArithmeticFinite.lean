/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticFinite.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticHierarchy

/-!
# Arithmetic Finite
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

theorem form_true (Y : Oracle) (n : ℕ) (s : Bool) : Form Y n s (fun _ => True) := by
  induction n with
  | zero =>
    classical
    simpa only [Form, RecursivePred, ↓reduceIte] using
      (total_primrec (O := {oracleFunction Y}) (Primrec.const 1))
  | succ n ih => exact ih.raise

theorem Form.finite_all {Y n s k} {P : Fin k → ℕ → Prop}
    (h : ∀ i, Form Y n s (P i)) : Form Y n s (fun x => ∀ i, P i x) := by
  induction k with
  | zero => exact (form_true Y n s).congr (fun x => by simp)
  | succ k ih =>
    exact ((h 0).and (ih (fun i => h i.succ))).congr (fun x => by
      simp only [Fin.forall_fin_succ])

end TuringRigidity.ArithmeticHierarchy

end OAI
