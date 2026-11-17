/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BranchFrequency.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BranchRecovery

/-!
# Branch Frequency
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

namespace UniformOracle

def runningSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => runningSum f n + f n

theorem runningSum_recursive {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n))) :
    Nat.RecursiveIn O (fun n => Part.some (runningSum f n)) := by
  have hy := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp (total_primrec (Primrec.nat_add.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hf hy))
  have hp := Nat.RecursiveIn.prec (total_primrec (Primrec.const 0)) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    change (Part.some (runningSum f n)).bind _ = _
    rw [Part.bind_some]
    rfl
end UniformOracle

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

def count (d : RecoveryData F t u v) : ℕ → ℕ :=
  UniformOracle.runningSum (fun n => if d.branchOracle n then 1 else 0)

theorem count_eq_sum (d : RecoveryData F t u v) (n : ℕ) :
    (d.count n : ℝ) = ∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k := by
  induction n with
  | zero => simp [count,UniformOracle.runningSum]
  | succ n ih =>
    simp only [count,UniformOracle.runningSum,Finset.sum_range_succ,Nat.cast_add]
    rw [show (UniformOracle.runningSum (fun n => if d.branchOracle n then 1 else 0) n : ℝ) =
      ∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k from ih]
    congr 1
    cases hb : d.branchOracle n <;> simp [branch,choiceBit,branchOracle] at hb ⊢ <;> simp [hb]

theorem count_recursive (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    Nat.RecursiveIn {oracleFunction (fourTuple F t u v d.delta)}
      (fun n => Part.some (d.count n)) := by
  exact UniformOracle.runningSum_recursive (RecursiveIn.iff_nat.mp (d.branch_reduces ht0 ht1))

theorem count_frequency_bound (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (n : ℕ) (hn : 0 < n) :
    |t - (d.count n : ℝ)/(n : ℝ)| < 1/((n : ℝ)*(d.delta : ℝ)) := by
  rw [count_eq_sum]
  exact d.frequency_bound ht0 ht1 n hn

end RecoveryData
end TuringRigidity

end OAI
