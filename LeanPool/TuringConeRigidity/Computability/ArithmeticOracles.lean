/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticOracles.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTables
public import LeanPool.TuringConeRigidity.Computability.OracleJump
public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing

/-!
# Arithmetic Oracles
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
noncomputable section

theorem ArithmeticOracle.comp {B : OracleFamily} (hB : ArithmeticOracle B)
    {f : ℕ → ℕ} (hf : Primrec f) : ArithmeticOracle (fun O v => B O (f v)) := by
  exact query_at hB (hf.comp left_primrec) right_primrec

theorem parameter_arith (i : ℕ) : ArithmeticOracle (fun O _ => O i) :=
  (Arith.query i).comp _ right_primrec

theorem column_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {k : ℕ → ℕ} (hk : Primrec k) :
    ArithmeticOracle (fun O v => columns (B O v) (k v)) :=
  query_at hB left_primrec (Primrec₂.natPair.comp (hk.comp left_primrec) right_primrec)

/-- The indexed oracle machine halts with Boolean output one on the given input. -/
def tableGraph (B : Oracle) (e n : ℕ) : Prop :=
  ∃ z, run B (machine e) n z = some 1

/-- The Boolean oracle whose true inputs are accepted by the indexed oracle machine. -/
def tableOracle (B : Oracle) (e : ℕ) : Oracle := by
  classical
  exact fun n => decide (tableGraph B e n)

theorem tableGraph_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n) :
    Arith (fun O v => tableGraph (B O (c v)) (e v) (n v)) :=
  ((run_arith hB (hc.comp left_primrec) (he.comp left_primrec)
    (hn.comp left_primrec) right_primrec (Primrec.const 1)).ex).congr
      (fun _ _ => by simp only [tableGraph,left,right,Nat.unpair_pair])

theorem tableOracle_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {e : ℕ → ℕ} (he : Primrec e) :
    ArithmeticOracle (fun O v => tableOracle (B O v) (e v)) := by
  exact (tableGraph_arith hB left_primrec (he.comp left_primrec) right_primrec).congr
    (fun _ _ => by simp [tableOracle])

theorem halts_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n) :
    Arith (fun O v => Halts (B O (c v)) (e v) (n v)) := by
  have h := (run_arith hB (hc.comp (left_primrec.comp left_primrec))
    (he.comp (left_primrec.comp left_primrec))
    (hn.comp (left_primrec.comp left_primrec)) (right_primrec.comp left_primrec)
    right_primrec).ex.ex
  exact h.congr (fun _ _ => by simp only [Halts,left,right,Nat.unpair_pair,Option.mem_def])

theorem jump_arith {B : OracleFamily} (hB : ArithmeticOracle B) :
    ArithmeticOracle (fun O v => jump (B O v)) :=
  (halts_arith hB left_primrec (left_primrec.comp right_primrec)
    (right_primrec.comp right_primrec)).congr (fun _ _ => by simp [jump])

theorem iterate_arith {B : OracleFamily} (hB : ArithmeticOracle B) (k : ℕ) :
    ArithmeticOracle (fun O v => iterate (B O v) k) := by
  induction k with
  | zero => exact hB
  | succ k ih => exact jump_arith ih

theorem tableOracle_eq {B A : Oracle} {e : ℕ}
    (h : Represents B (machine e) A) : tableOracle B e = A := by
  funext n
  have hg : tableGraph B e n ↔ A n = true := by
    constructor
    · rintro ⟨z,hz⟩
      have hh := h.1 n z 1 (Option.mem_def.mpr hz)
      cases ha : A n <;> simp [bit,ha] at hh ⊢
    · intro ha
      obtain ⟨z,a,hz⟩ := h.2 n
      refine ⟨z,?_⟩
      have hh := h.1 n z a hz
      simpa [hh,bit,ha] using Option.mem_def.mp hz
  simp [tableOracle,hg]

end
end TuringRigidity.UniformArithmetic

end OAI
