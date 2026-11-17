/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalInputs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalPair
public import LeanPool.TuringConeRigidity.Effective.LocalOpen
public import LeanPool.TuringConeRigidity.Effective.LocalColumnIndices

/-!
# Local Inputs
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalInputs
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing CodingForcing
noncomputable section

structure Data where
  B : Oracle
  X : Oracle
  F : ℕ → Oracle
  codes : ℕ → ℕ
  codes_recursive : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (codes n))
  codes_valid : ∀ n, LocalColumnCertificates.Presents B F (codes n) n

def Data.bound (D : Data) : Oracle := join D.X (jump D.B)

theorem total_transfer {Y Z : Oracle} {f : ℕ → ℕ}
    (h : Nat.RecursiveIn {oracleFunction Y} (fun n => Part.some (f n))) (hYZ : Reduces Y Z) :
    Nat.RecursiveIn {oracleFunction Z} (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp (TuringReducible.trans (RecursiveIn.iff_nat.mpr h) hYZ)

def Data.request (D : Data) (v : ℕ) : ℕ :=
  encode [D.codes (active (Nat.unpair v).2),(Nat.unpair v).1,(Nat.unpair v).2]

theorem Data.request_recursive (D : Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun n => Part.some (D.request n)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hc := total_comp (total_transfer D.codes_recursive (reduces_join_left D.X (jump D.B)))
    (total_primrec (active_primrec.comp r))
  have hm := Primrec.encode.comp (Primrec.list_cons.comp f
    (Primrec.list_cons.comp (f.comp r) (Primrec.list_cons.comp (r.comp r) (Primrec.const []))))
  exact (total_comp (total_primrec hm) (total_pair hc (total_primrec Primrec.id))).of_eq
    (fun n => by simp only [Nat.unpair_pair]; rfl)

def Data.pairProcedure (D : Data) (v : ℕ) : ℕ :=
  Classical.choose (LocalPair.pair_exists D.B) (D.request v)

theorem Data.pair_recursive (D : Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun n => Part.some (D.pairProcedure n)) :=
  total_comp (f := Classical.choose (LocalPair.pair_exists D.B)) (g := D.request)
    (total_transfer (Classical.choose_spec (LocalPair.pair_exists D.B)).1
    (reduces_join_right D.X (jump D.B))) D.request_recursive

theorem Data.pair_spec (D : Data) (x p : ℕ) :
    Extends D.F (condition p) (condition (D.pairProcedure (Nat.pair x p))) ∧
      (UniformAgreement.Disagreement D.B x (condition (D.pairProcedure (Nat.pair x p))) ∨
        ((condition (D.pairProcedure (Nat.pair x p))).active = active p ∧
          LocalAgreement.NoDisagreement D.B D.F x (condition p) ∧
          (LocalPair.Decisive D.B D.F x (condition (D.pairProcedure (Nat.pair x p))) ∨
            (condition (D.pairProcedure (Nat.pair x p)) = condition p ∧
              LocalPair.NoBad D.B D.F x p ∧ LocalPair.Outcome D.B D.F x p)))) := by
  simpa only [Data.pairProcedure,Data.request,Nat.unpair_pair] using
    (Classical.choose_spec (LocalPair.pair_exists D.B)).2 D.F (D.codes (active p)) x p
      (D.codes_valid _)

def Data.openProcedure (D : Data) (v : ℕ) : ℕ :=
  Classical.choose (LocalOpen.uniform_open_decision D.B) (D.request v)

theorem Data.open_recursive (D : Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun n => Part.some (D.openProcedure n)) :=
  total_comp (f := Classical.choose (LocalOpen.uniform_open_decision D.B)) (g := D.request)
    (total_transfer (Classical.choose_spec (LocalOpen.uniform_open_decision D.B)).1
    (reduces_join_right D.X (jump D.B))) D.request_recursive

theorem Data.open_spec (D : Data) (e p : ℕ) :
    Extends D.F (condition p) (condition (D.openProcedure (Nat.pair e p))) ∧
      (Halts D.B e (D.openProcedure (Nat.pair e p)) ∨
        (D.openProcedure (Nat.pair e p) = p ∧
          ∀ q, Extends D.F (condition p) (condition q) → ¬ Halts D.B e q)) := by
  simpa only [Data.openProcedure,Data.request,Nat.unpair_pair] using
    (Classical.choose_spec (LocalOpen.uniform_open_decision D.B)).2 D.F (D.codes (active p)) e p
      (D.codes_valid _)

end
end TuringRigidity.LocalInputs

end OAI
