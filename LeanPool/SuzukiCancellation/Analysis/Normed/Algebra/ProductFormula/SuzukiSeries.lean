/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: verified intermediate tables and updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialListCoefficients
public import LeanPool.SuzukiCancellation.Algebra.Word.CentralBinaryTable
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.Palindromic
public import LeanPool.SuzukiCancellation.Algebra.Lie.BCH.SuzukiTerms
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiParameter

/-!
# Quintic Suzuki coefficient matching

Finite ordered exponential coefficients and their logarithm are represented by
integer word tables with explicit denominators. A central letter records the real parameter;
the other two letters retain their order. Integer quotient certificates identify
the linear and quintic coefficients modulo the Suzuki cubic relation.

The ordinary letters are evaluated at `a/120` and `b/120`. Integer exponential
weights `60^i/i!` and logarithm weights `60 * logCoeff i` clear all denominators
through degree five. The quotient tables use the same letter scale.

## Main results

* `sum_expListLogCoeff_fiveStageStrang_eq`: the finite logarithm through degree five.
-/

@[expose] public noncomputable section

open Finset Finset.Nat

namespace FQFP.BCH

private abbrev ParamTable := CoeffWordTable.Table ℤ (Option (Fin 2))

private def argumentTables : List ParamTable :=
  [[([none, some 0], 1)], [([none, some 1], 2)],
    [([none, some 0], 2)], [([none, some 1], 2)],
    [([some 0], 1), ([none, some 0], -3)],
    [([some 1], 2), ([none, some 1], -8)],
    [([some 0], 1), ([none, some 0], -3)],
    [([none, some 1], 2)], [([none, some 0], 2)],
    [([none, some 1], 2)], [([none, some 0], 1)]]

private def tablePow (t : ParamTable) : ℕ → ParamTable
  | 0 => CoeffWordTable.unit
  | n + 1 => CentralBinaryWordTable.collect (CoeffWordTable.mul t (tablePow t n))

private def tableExpFrom : List ParamTable → (ℕ → ParamTable) → ℕ → ParamTable
  | [], tail, n => tail n
  | t :: ts, tail, n => CentralBinaryWordTable.collect ((List.range (n + 1)).flatMap fun i ↦
      CoeffWordTable.smul (60 ^ i / Nat.factorial i : ℕ)
        (CoeffWordTable.mul (tablePow t i) (tableExpFrom ts tail (n - i))))

private def tableExp (ts : List ParamTable) (n : ℕ) : ParamTable :=
  tableExpFrom ts (fun i ↦ if i = 0 then CoeffWordTable.unit else []) n

private lemma tableExp_append (front back : List ParamTable) (n : ℕ) :
    tableExp (front ++ back) n = tableExpFrom front (tableExp back) n := by
  induction front generalizing n with
  | nil => rfl
  | cons t ts ih =>
    change tableExp (t :: (ts ++ back)) n = _
    simp only [tableExp, tableExpFrom]
    have h (i : ℕ) :
        tableExpFrom (ts ++ back) (fun j ↦ if j = 0 then CoeffWordTable.unit else []) i =
          tableExpFrom ts (tableExp back) i := ih i
    simp only [h]

/-- Grouping the last five factors before multiplying the first six factors
bounds the certificate's kernel reduction cost. -/
private def argumentTailTable : ℕ → ParamTable
  | 0 => [([], 1)]
  | 1 => [([none, some 1], 240), ([some 0], 60)]
  | 2 => [([none, none, some 0, some 1], -28800),
    ([none, none, some 1, some 0], 28800),
    ([none, none, some 1, some 1], 28800),
    ([none, some 0, some 1], 14400),
    ([some 0, some 0], 1800)]
  | 3 => [([none, none, none, some 0, some 0, some 1], 2160000),
    ([none, none, none, some 0, some 1, some 0], -4320000),
    ([none, none, none, some 0, some 1, some 1], -4320000),
    ([none, none, none, some 1, some 0, some 0], 2160000),
    ([none, none, none, some 1, some 0, some 1], 1728000),
    ([none, none, none, some 1, some 1, some 0], 2592000),
    ([none, none, none, some 1, some 1, some 1], 2304000),
    ([none, none, some 0, some 0, some 1], -1728000),
    ([none, none, some 0, some 1, some 0], 1728000),
    ([none, none, some 0, some 1, some 1], 1728000),
    ([none, some 0, some 0, some 1], 432000),
    ([some 0, some 0, some 0], 36000)]
  | 4 => [([none, none, none, none, some 0, some 0, some 0, some 1], -120960000),
    ([none, none, none, none, some 0, some 0, some 1, some 0], 362880000),
    ([none, none, none, none, some 0, some 0, some 1, some 1], 362880000),
    ([none, none, none, none, some 0, some 1, some 0, some 0], -362880000),
    ([none, none, none, none, some 0, some 1, some 0, some 1], -311040000),
    ([none, none, none, none, some 0, some 1, some 1, some 0], -414720000),
    ([none, none, none, none, some 0, some 1, some 1, some 1], -380160000),
    ([none, none, none, none, some 1, some 0, some 0, some 0], 120960000),
    ([none, none, none, none, some 1, some 0, some 0, some 1], 103680000),
    ([none, none, none, none, some 1, some 0, some 1, some 0], 103680000),
    ([none, none, none, none, some 1, some 0, some 1, some 1], 103680000),
    ([none, none, none, none, some 1, some 1, some 0, some 0], 155520000),
    ([none, none, none, none, some 1, some 1, some 0, some 1], 103680000),
    ([none, none, none, none, some 1, some 1, some 1, some 0], 172800000),
    ([none, none, none, none, some 1, some 1, some 1, some 1], 138240000),
    ([none, none, none, some 0, some 0, some 0, some 1], 129600000),
    ([none, none, none, some 0, some 0, some 1, some 0], -259200000),
    ([none, none, none, some 0, some 0, some 1, some 1], -259200000),
    ([none, none, none, some 0, some 1, some 0, some 0], 129600000),
    ([none, none, none, some 0, some 1, some 0, some 1], 103680000),
    ([none, none, none, some 0, some 1, some 1, some 0], 155520000),
    ([none, none, none, some 0, some 1, some 1, some 1], 138240000),
    ([none, none, some 0, some 0, some 0, some 1], -51840000),
    ([none, none, some 0, some 0, some 1, some 0], 51840000),
    ([none, none, some 0, some 0, some 1, some 1], 51840000),
    ([none, some 0, some 0, some 0, some 1], 8640000),
    ([some 0, some 0, some 0, some 0], 540000)]
  | 5 => [([none, none, none, none, none, some 0, some 0, some 0, some 0, some 1], 5313600000),
    ([none, none, none, none, none, some 0, some 0, some 0, some 1, some 0], -21254400000),
    ([none, none, none, none, none, some 0, some 0, some 0, some 1, some 1], -21254400000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 0, some 0], 31881600000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 0, some 1], 27993600000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 1, some 0], 35769600000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 1, some 1], 33177600000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 0, some 0], -21254400000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 0, some 1], -18662400000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 1, some 0], -18662400000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 1, some 1], -18662400000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 0, some 0], -26438400000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 0, some 1], -18662400000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 1, some 0], -29030400000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 1, some 1], -23846400000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 0, some 0], 5313600000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 0, some 1], 4147200000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 1, some 0], 6220800000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 1, some 1], 6220800000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 0, some 0], 3110400000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 1, some 0], 6220800000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 1, some 1], 4147200000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 0, some 0], 7776000000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 0, some 1], 6220800000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 1, some 0], 6220800000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 1, some 1], 6220800000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 0, some 0], 8294400000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 0, some 1], 4147200000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 1, some 0], 9331200000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 1, some 1], 6635520000),
    ([none, none, none, none, some 0, some 0, some 0, some 0, some 1], -7257600000),
    ([none, none, none, none, some 0, some 0, some 0, some 1, some 0], 21772800000),
    ([none, none, none, none, some 0, some 0, some 0, some 1, some 1], 21772800000),
    ([none, none, none, none, some 0, some 0, some 1, some 0, some 0], -21772800000),
    ([none, none, none, none, some 0, some 0, some 1, some 0, some 1], -18662400000),
    ([none, none, none, none, some 0, some 0, some 1, some 1, some 0], -24883200000),
    ([none, none, none, none, some 0, some 0, some 1, some 1, some 1], -22809600000),
    ([none, none, none, none, some 0, some 1, some 0, some 0, some 0], 7257600000),
    ([none, none, none, none, some 0, some 1, some 0, some 0, some 1], 6220800000),
    ([none, none, none, none, some 0, some 1, some 0, some 1, some 0], 6220800000),
    ([none, none, none, none, some 0, some 1, some 0, some 1, some 1], 6220800000),
    ([none, none, none, none, some 0, some 1, some 1, some 0, some 0], 9331200000),
    ([none, none, none, none, some 0, some 1, some 1, some 0, some 1], 6220800000),
    ([none, none, none, none, some 0, some 1, some 1, some 1, some 0], 10368000000),
    ([none, none, none, none, some 0, some 1, some 1, some 1, some 1], 8294400000),
    ([none, none, none, some 0, some 0, some 0, some 0, some 1], 3888000000),
    ([none, none, none, some 0, some 0, some 0, some 1, some 0], -7776000000),
    ([none, none, none, some 0, some 0, some 0, some 1, some 1], -7776000000),
    ([none, none, none, some 0, some 0, some 1, some 0, some 0], 3888000000),
    ([none, none, none, some 0, some 0, some 1, some 0, some 1], 3110400000),
    ([none, none, none, some 0, some 0, some 1, some 1, some 0], 4665600000),
    ([none, none, none, some 0, some 0, some 1, some 1, some 1], 4147200000),
    ([none, none, some 0, some 0, some 0, some 0, some 1], -1036800000),
    ([none, none, some 0, some 0, some 0, some 1, some 0], 1036800000),
    ([none, none, some 0, some 0, some 0, some 1, some 1], 1036800000),
    ([none, some 0, some 0, some 0, some 0, some 1], 129600000),
    ([some 0, some 0, some 0, some 0, some 0], 6480000)]
  | _ => []

private def argumentTail (n : ℕ) : ParamTable :=
  if n ≤ 5 then argumentTailTable n else tableExp (argumentTables.drop 6) n

private lemma argumentTail_eq : argumentTail = tableExp (argumentTables.drop 6) := by
  funext n
  by_cases h : n ≤ 5
  · rw [argumentTail, ite_eq_left h]
    interval_cases n <;> decide +kernel
  · simp [argumentTail, h]

/-- Grouped coefficients of the scaled eleven-factor series through degree five.
The kernel checks each row table against the ordered exponential recurrence. -/
private def argumentExpTable : ℕ → ParamTable
  | 0 => [([], 1)]
  | 1 => [([some 0], 120), ([some 1], 120)]
  | 2 => [([some 0, some 0], 7200), ([some 0, some 1], 7200),
    ([some 1, some 0], 7200), ([some 1, some 1], 7200)]
  | 3 => [([none, none, none, some 0, some 0, some 1], 4320000),
    ([none, none, none, some 0, some 1, some 0], -8640000),
    ([none, none, none, some 0, some 1, some 1], -8640000),
    ([none, none, none, some 1, some 0, some 0], 4320000),
    ([none, none, none, some 1, some 0, some 1], 17280000),
    ([none, none, none, some 1, some 1, some 0], -8640000),
    ([none, none, some 0, some 0, some 1], -3456000),
    ([none, none, some 0, some 1, some 0], 6912000),
    ([none, none, some 0, some 1, some 1], 6912000),
    ([none, none, some 1, some 0, some 0], -3456000),
    ([none, none, some 1, some 0, some 1], -13824000),
    ([none, none, some 1, some 1, some 0], 6912000),
    ([none, some 0, some 0, some 1], 864000),
    ([none, some 0, some 1, some 0], -1728000),
    ([none, some 0, some 1, some 1], -1728000),
    ([none, some 1, some 0, some 0], 864000),
    ([none, some 1, some 0, some 1], 3456000),
    ([none, some 1, some 1, some 0], -1728000),
    ([some 0, some 0, some 0], 288000),
    ([some 0, some 0, some 1], 216000),
    ([some 0, some 1, some 0], 432000),
    ([some 0, some 1, some 1], 432000),
    ([some 1, some 0, some 0], 216000),
    ([some 1, some 1, some 0], 432000),
    ([some 1, some 1, some 1], 288000)]
  | 4 => [([none, none, none, some 0, some 0, some 0, some 1], 259200000),
    ([none, none, none, some 0, some 0, some 1, some 0], -259200000),
    ([none, none, none, some 0, some 0, some 1, some 1], -259200000),
    ([none, none, none, some 0, some 1, some 0, some 0], -259200000),
    ([none, none, none, some 0, some 1, some 0, some 1], 518400000),
    ([none, none, none, some 0, some 1, some 1, some 0], -1036800000),
    ([none, none, none, some 0, some 1, some 1, some 1], -518400000),
    ([none, none, none, some 1, some 0, some 0, some 0], 259200000),
    ([none, none, none, some 1, some 0, some 0, some 1], 518400000),
    ([none, none, none, some 1, some 0, some 1, some 0], 518400000),
    ([none, none, none, some 1, some 0, some 1, some 1], 518400000),
    ([none, none, none, some 1, some 1, some 0, some 0], -259200000),
    ([none, none, none, some 1, some 1, some 0, some 1], 518400000),
    ([none, none, none, some 1, some 1, some 1, some 0], -518400000),
    ([none, none, some 0, some 0, some 0, some 1], -207360000),
    ([none, none, some 0, some 0, some 1, some 0], 207360000),
    ([none, none, some 0, some 0, some 1, some 1], 207360000),
    ([none, none, some 0, some 1, some 0, some 0], 207360000),
    ([none, none, some 0, some 1, some 0, some 1], -414720000),
    ([none, none, some 0, some 1, some 1, some 0], 829440000),
    ([none, none, some 0, some 1, some 1, some 1], 414720000),
    ([none, none, some 1, some 0, some 0, some 0], -207360000),
    ([none, none, some 1, some 0, some 0, some 1], -414720000),
    ([none, none, some 1, some 0, some 1, some 0], -414720000),
    ([none, none, some 1, some 0, some 1, some 1], -414720000),
    ([none, none, some 1, some 1, some 0, some 0], 207360000),
    ([none, none, some 1, some 1, some 0, some 1], -414720000),
    ([none, none, some 1, some 1, some 1, some 0], 414720000),
    ([none, some 0, some 0, some 0, some 1], 51840000),
    ([none, some 0, some 0, some 1, some 0], -51840000),
    ([none, some 0, some 0, some 1, some 1], -51840000),
    ([none, some 0, some 1, some 0, some 0], -51840000),
    ([none, some 0, some 1, some 0, some 1], 103680000),
    ([none, some 0, some 1, some 1, some 0], -207360000),
    ([none, some 0, some 1, some 1, some 1], -103680000),
    ([none, some 1, some 0, some 0, some 0], 51840000),
    ([none, some 1, some 0, some 0, some 1], 103680000),
    ([none, some 1, some 0, some 1, some 0], 103680000),
    ([none, some 1, some 0, some 1, some 1], 103680000),
    ([none, some 1, some 1, some 0, some 0], -51840000),
    ([none, some 1, some 1, some 0, some 1], 103680000),
    ([none, some 1, some 1, some 1, some 0], -103680000),
    ([some 0, some 0, some 0, some 0], 8640000),
    ([some 0, some 0, some 0, some 1], 4320000),
    ([some 0, some 0, some 1, some 0], 12960000),
    ([some 0, some 0, some 1, some 1], 12960000),
    ([some 0, some 1, some 0, some 0], 12960000),
    ([some 0, some 1, some 1, some 0], 25920000),
    ([some 0, some 1, some 1, some 1], 17280000),
    ([some 1, some 0, some 0, some 0], 4320000),
    ([some 1, some 1, some 0, some 0], 12960000),
    ([some 1, some 1, some 1, some 0], 17280000),
    ([some 1, some 1, some 1, some 1], 8640000)]
  | 5 => [([none, none, none, none, none, some 0, some 0, some 0, some 0, some 1], 10627200000),
    ([none, none, none, none, none, some 0, some 0, some 0, some 1, some 0], -42508800000),
    ([none, none, none, none, none, some 0, some 0, some 0, some 1, some 1], -42508800000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 0, some 0], 63763200000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 0, some 1], 55987200000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 1, some 0], 71539200000),
    ([none, none, none, none, none, some 0, some 0, some 1, some 1, some 1], 66355200000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 0, some 0], -42508800000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 0, some 1], 87091200000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 1, some 0], -286156800000),
    ([none, none, none, none, none, some 0, some 1, some 0, some 1, some 1], -286156800000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 0, some 0], 71539200000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 0, some 1], 460339200000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 1, some 0], -306892800000),
    ([none, none, none, none, none, some 0, some 1, some 1, some 1, some 1], -47692800000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 0, some 0], 10627200000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 0, some 1], -58060800000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 1, some 0], 87091200000),
    ([none, none, none, none, none, some 1, some 0, some 0, some 1, some 1], 87091200000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 0, some 0], 55987200000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 0, some 1], -348364800000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 1, some 0], 460339200000),
    ([none, none, none, none, none, some 1, some 0, some 1, some 1, some 1], 190771200000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 0, some 0], -42508800000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 0, some 1], 87091200000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 1, some 0], -286156800000),
    ([none, none, none, none, none, some 1, some 1, some 0, some 1, some 1], -286156800000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 0, some 0], 66355200000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 0, some 1], 190771200000),
    ([none, none, none, none, none, some 1, some 1, some 1, some 1, some 0], -47692800000),
    ([none, none, none, none, some 0, some 0, some 0, some 0, some 1], -14515200000),
    ([none, none, none, none, some 0, some 0, some 0, some 1, some 0], 58060800000),
    ([none, none, none, none, some 0, some 0, some 0, some 1, some 1], 58060800000),
    ([none, none, none, none, some 0, some 0, some 1, some 0, some 0], -87091200000),
    ([none, none, none, none, some 0, some 0, some 1, some 0, some 1], -80870400000),
    ([none, none, none, none, some 0, some 0, some 1, some 1, some 0], -93312000000),
    ([none, none, none, none, some 0, some 0, some 1, some 1, some 1], -89164800000),
    ([none, none, none, none, some 0, some 1, some 0, some 0, some 0], 58060800000),
    ([none, none, none, none, some 0, some 1, some 0, some 0, some 1], -105753600000),
    ([none, none, none, none, some 0, some 1, some 0, some 1, some 0], 373248000000),
    ([none, none, none, none, some 0, some 1, some 0, some 1, some 1], 373248000000),
    ([none, none, none, none, some 0, some 1, some 1, some 0, some 0], -93312000000),
    ([none, none, none, none, some 0, some 1, some 1, some 0, some 1], -584755200000),
    ([none, none, none, none, some 0, some 1, some 1, some 1, some 0], 389836800000),
    ([none, none, none, none, some 0, some 1, some 1, some 1, some 1], 62208000000),
    ([none, none, none, none, some 1, some 0, some 0, some 0, some 0], -14515200000),
    ([none, none, none, none, some 1, some 0, some 0, some 0, some 1], 70502400000),
    ([none, none, none, none, some 1, some 0, some 0, some 1, some 0], -105753600000),
    ([none, none, none, none, some 1, some 0, some 0, some 1, some 1], -105753600000),
    ([none, none, none, none, some 1, some 0, some 1, some 0, some 0], -80870400000),
    ([none, none, none, none, some 1, some 0, some 1, some 0, some 1], 423014400000),
    ([none, none, none, none, some 1, some 0, some 1, some 1, some 0], -584755200000),
    ([none, none, none, none, some 1, some 0, some 1, some 1, some 1], -248832000000),
    ([none, none, none, none, some 1, some 1, some 0, some 0, some 0], 58060800000),
    ([none, none, none, none, some 1, some 1, some 0, some 0, some 1], -105753600000),
    ([none, none, none, none, some 1, some 1, some 0, some 1, some 0], 373248000000),
    ([none, none, none, none, some 1, some 1, some 0, some 1, some 1], 373248000000),
    ([none, none, none, none, some 1, some 1, some 1, some 0, some 0], -89164800000),
    ([none, none, none, none, some 1, some 1, some 1, some 0, some 1], -248832000000),
    ([none, none, none, none, some 1, some 1, some 1, some 1, some 0], 62208000000),
    ([none, none, none, some 0, some 0, some 0, some 0, some 1], 15552000000),
    ([none, none, none, some 0, some 0, some 0, some 1, some 0], -31104000000),
    ([none, none, none, some 0, some 0, some 0, some 1, some 1], -31104000000),
    ([none, none, none, some 0, some 0, some 1, some 0, some 0], 31104000000),
    ([none, none, none, some 0, some 0, some 1, some 0, some 1], 52876800000),
    ([none, none, none, some 0, some 0, some 1, some 1, some 0], 9331200000),
    ([none, none, none, some 0, some 0, some 1, some 1, some 1], 23846400000),
    ([none, none, none, some 0, some 1, some 0, some 0, some 0], -31104000000),
    ([none, none, none, some 0, some 1, some 0, some 0, some 1], 59097600000),
    ([none, none, none, some 0, some 1, some 0, some 1, some 0], -161740800000),
    ([none, none, none, some 0, some 1, some 0, some 1, some 1], -161740800000),
    ([none, none, none, some 0, some 1, some 1, some 0, some 0], 9331200000),
    ([none, none, none, some 0, some 1, some 1, some 0, some 1], 279936000000),
    ([none, none, none, some 0, some 1, some 1, some 1, some 0], -228096000000),
    ([none, none, none, some 0, some 1, some 1, some 1, some 1], -47692800000),
    ([none, none, none, some 1, some 0, some 0, some 0, some 0], 15552000000),
    ([none, none, none, some 1, some 0, some 0, some 0, some 1], -18662400000),
    ([none, none, none, some 1, some 0, some 0, some 1, some 0], 59097600000),
    ([none, none, none, some 1, some 0, some 0, some 1, some 1], 59097600000),
    ([none, none, none, some 1, some 0, some 1, some 0, some 0], 52876800000),
    ([none, none, none, some 1, some 0, some 1, some 0, some 1], -174182400000),
    ([none, none, none, some 1, some 0, some 1, some 1, some 0], 279936000000),
    ([none, none, none, some 1, some 0, some 1, some 1, some 1], 128563200000),
    ([none, none, none, some 1, some 1, some 0, some 0, some 0], -31104000000),
    ([none, none, none, some 1, some 1, some 0, some 0, some 1], 59097600000),
    ([none, none, none, some 1, some 1, some 0, some 1, some 0], -161740800000),
    ([none, none, none, some 1, some 1, some 0, some 1, some 1], -161740800000),
    ([none, none, none, some 1, some 1, some 1, some 0, some 0], 23846400000),
    ([none, none, none, some 1, some 1, some 1, some 0, some 1], 128563200000),
    ([none, none, none, some 1, some 1, some 1, some 1, some 0], -47692800000),
    ([none, none, some 0, some 0, some 0, some 0, some 1], -8294400000),
    ([none, none, some 0, some 0, some 0, some 1, some 0], 8294400000),
    ([none, none, some 0, some 0, some 0, some 1, some 1], 8294400000),
    ([none, none, some 0, some 0, some 1, some 0, some 1], -18662400000),
    ([none, none, some 0, some 0, some 1, some 1, some 0], 18662400000),
    ([none, none, some 0, some 0, some 1, some 1, some 1], 6220800000),
    ([none, none, some 0, some 1, some 0, some 0, some 0], 8294400000),
    ([none, none, some 0, some 1, some 0, some 0, some 1], -18662400000),
    ([none, none, some 0, some 1, some 0, some 1, some 0], 24883200000),
    ([none, none, some 0, some 1, some 0, some 1, some 1], 24883200000),
    ([none, none, some 0, some 1, some 1, some 0, some 0], 18662400000),
    ([none, none, some 0, some 1, some 1, some 0, some 1], -62208000000),
    ([none, none, some 0, some 1, some 1, some 1, some 0], 74649600000),
    ([none, none, some 0, some 1, some 1, some 1, some 1], 20736000000),
    ([none, none, some 1, some 0, some 0, some 0, some 0], -8294400000),
    ([none, none, some 1, some 0, some 0, some 0, some 1], -4147200000),
    ([none, none, some 1, some 0, some 0, some 1, some 0], -18662400000),
    ([none, none, some 1, some 0, some 0, some 1, some 1], -18662400000),
    ([none, none, some 1, some 0, some 1, some 0, some 0], -18662400000),
    ([none, none, some 1, some 0, some 1, some 0, some 1], 24883200000),
    ([none, none, some 1, some 0, some 1, some 1, some 0], -62208000000),
    ([none, none, some 1, some 0, some 1, some 1, some 1], -33177600000),
    ([none, none, some 1, some 1, some 0, some 0, some 0], 8294400000),
    ([none, none, some 1, some 1, some 0, some 0, some 1], -18662400000),
    ([none, none, some 1, some 1, some 0, some 1, some 0], 24883200000),
    ([none, none, some 1, some 1, some 0, some 1, some 1], 24883200000),
    ([none, none, some 1, some 1, some 1, some 0, some 0], 6220800000),
    ([none, none, some 1, some 1, some 1, some 0, some 1], -33177600000),
    ([none, none, some 1, some 1, some 1, some 1, some 0], 20736000000),
    ([none, some 0, some 0, some 0, some 0, some 1], 1814400000),
    ([none, some 0, some 0, some 0, some 1, some 0], -1036800000),
    ([none, some 0, some 0, some 0, some 1, some 1], -1036800000),
    ([none, some 0, some 0, some 1, some 0, some 0], -1555200000),
    ([none, some 0, some 0, some 1, some 0, some 1], 3110400000),
    ([none, some 0, some 0, some 1, some 1, some 0], -6220800000),
    ([none, some 0, some 0, some 1, some 1, some 1], -3110400000),
    ([none, some 0, some 1, some 0, some 0, some 0], -1036800000),
    ([none, some 0, some 1, some 0, some 0, some 1], 3110400000),
    ([none, some 0, some 1, some 1, some 0, some 0], -6220800000),
    ([none, some 0, some 1, some 1, some 0, some 1], 6220800000),
    ([none, some 0, some 1, some 1, some 1, some 0], -12441600000),
    ([none, some 0, some 1, some 1, some 1, some 1], -4147200000),
    ([none, some 1, some 0, some 0, some 0, some 0], 1814400000),
    ([none, some 1, some 0, some 0, some 0, some 1], 2073600000),
    ([none, some 1, some 0, some 0, some 1, some 0], 3110400000),
    ([none, some 1, some 0, some 0, some 1, some 1], 3110400000),
    ([none, some 1, some 0, some 1, some 0, some 0], 3110400000),
    ([none, some 1, some 0, some 1, some 1, some 0], 6220800000),
    ([none, some 1, some 0, some 1, some 1, some 1], 4147200000),
    ([none, some 1, some 1, some 0, some 0, some 0], -1036800000),
    ([none, some 1, some 1, some 0, some 0, some 1], 3110400000),
    ([none, some 1, some 1, some 1, some 0, some 0], -3110400000),
    ([none, some 1, some 1, some 1, some 0, some 1], 4147200000),
    ([none, some 1, some 1, some 1, some 1, some 0], -4147200000),
    ([some 0, some 0, some 0, some 0, some 0], 207360000),
    ([some 0, some 0, some 0, some 0, some 1], 64800000),
    ([some 0, some 0, some 0, some 1, some 0], 259200000),
    ([some 0, some 0, some 0, some 1, some 1], 259200000),
    ([some 0, some 0, some 1, some 0, some 0], 388800000),
    ([some 0, some 0, some 1, some 1, some 0], 777600000),
    ([some 0, some 0, some 1, some 1, some 1], 518400000),
    ([some 0, some 1, some 0, some 0, some 0], 259200000),
    ([some 0, some 1, some 1, some 0, some 0], 777600000),
    ([some 0, some 1, some 1, some 1, some 0], 1036800000),
    ([some 0, some 1, some 1, some 1, some 1], 518400000),
    ([some 1, some 0, some 0, some 0, some 0], 64800000),
    ([some 1, some 1, some 0, some 0, some 0], 259200000),
    ([some 1, some 1, some 1, some 0, some 0], 518400000),
    ([some 1, some 1, some 1, some 1, some 0], 518400000),
    ([some 1, some 1, some 1, some 1, some 1], 207360000)]
  | _ => []

private lemma argumentExpTable_eq (n : ℕ) (hn : n ≤ 5) :
    argumentExpTable n = tableExp argumentTables n := by
  calc
    argumentExpTable n = tableExpFrom (argumentTables.take 6) argumentTail n := by
      interval_cases n <;> decide +kernel
    _ = tableExp argumentTables n := by
      rw [argumentTail_eq, ← tableExp_append, List.take_append_drop]

private def tablePower : ℕ → ℕ → ParamTable
  | 0, n => if n = 0 then CoeffWordTable.unit else []
  | k + 1, n => CentralBinaryWordTable.collect ((List.range (n - k)).flatMap fun i ↦
      CoeffWordTable.mul (argumentExpTable (i + 1)) (tablePower k (n - (i + 1))))

private def logWeights : ℕ → ℤ
  | 1 => 60
  | 2 => -30
  | 3 => 20
  | 4 => -15
  | 5 => 12
  | _ => 0

private def tableLog (n : ℕ) : ParamTable :=
  CentralBinaryWordTable.collect ((List.range (n + 1)).flatMap fun k ↦
    CoeffWordTable.smul (logWeights k) (tablePower k n))

private def tableBracket (s t : ParamTable) : ParamTable :=
  CentralBinaryWordTable.collect (CoeffWordTable.mul s t ++
    CoeffWordTable.smul (-1) (CoeffWordTable.mul t s))

private def childsTables : Fin 8 → ParamTable := fun i ↦
  let a : ParamTable := [([some 0], 1)]
  let b : ParamTable := [([some 1], 1)]
  let x := if i.val < 4 then a else b
  let y := if i.val % 4 < 2 then a else b
  let z := if i.val % 2 = 0 then a else b
  tableBracket x (tableBracket y (tableBracket z (tableBracket b a)))

private def betaTables : Fin 8 → ParamTable :=
  ![[
    ([], -1036800),
    ([none], 8985600),
    ([none, none], 21945600)],
    [
    ([], -6220800),
    ([none], 53913600),
    ([none, none], 2073600)],
    [],
    [
    ([], -12441600),
    ([none], 107827200),
    ([none, none], -168652800)],
    [
    ([], 2073600),
    ([none], -17971200),
    ([none, none], 85708800)],
    [
    ([], 6220800),
    ([none], -53913600),
    ([none, none], 257126400)],
    [],
    [
    ([], -4147200),
    ([none], 35942400),
    ([none, none], 1382400)]]

private def targetTable : ℕ → ParamTable
  | 1 => [([some 0], 120), ([some 1], 120)]
  | 5 => CentralBinaryWordTable.collect ((List.finRange 8).flatMap fun i ↦
      CoeffWordTable.mul (betaTables i) (childsTables i))
  | _ => []

private def relationTable : ParamTable :=
  [([], 1), ([none], -12), ([none, none], 48), ([none, none, none], -60)]

/-- Integral quotient witnesses for the Suzuki relation at letter scale `120`. -/
private def suzukiQuotientTable : ℕ → ParamTable
  | 3 => [
    ([some 0, some 0, some 1], -72000),
    ([some 0, some 1, some 0], 144000),
    ([some 0, some 1, some 1], 144000),
    ([some 1, some 0, some 0], -72000),
    ([some 1, some 0, some 1], -288000),
    ([some 1, some 1, some 0], 144000)]
  | 5 => [
    ([some 0, some 0, some 0, some 0, some 1], 29203200),
    ([some 0, some 0, some 0, some 1, some 0], -116812800),
    ([some 0, some 0, some 0, some 1, some 1], -116812800),
    ([some 0, some 0, some 1, some 0, some 0], 175219200),
    ([some 0, some 0, some 1, some 0, some 1], 304819200),
    ([some 0, some 0, some 1, some 1, some 0], 45619200),
    ([some 0, some 0, some 1, some 1, some 1], 132019200),
    ([some 0, some 1, some 0, some 0, some 0], -116812800),
    ([some 0, some 1, some 0, some 0, some 1], -213580800),
    ([some 0, some 1, some 0, some 1, some 0], -182476800),
    ([some 0, some 1, some 0, some 1, some 1], -182476800),
    ([some 0, some 1, some 1, some 0, some 0], 45619200),
    ([some 0, some 1, some 1, some 0, some 1], -244684800),
    ([some 0, some 1, some 1, some 1, some 0], 163123200),
    ([some 0, some 1, some 1, some 1, some 1], -30412800),
    ([some 1, some 0, some 0, some 0, some 0], 29203200),
    ([some 1, some 0, some 0, some 0, some 1], 142387200),
    ([some 1, some 0, some 0, some 1, some 0], -213580800),
    ([some 1, some 0, some 0, some 1, some 1], -213580800),
    ([some 1, some 0, some 1, some 0, some 0], 304819200),
    ([some 1, some 0, some 1, some 0, some 1], 854323200),
    ([some 1, some 0, some 1, some 1, some 0], -244684800),
    ([some 1, some 0, some 1, some 1, some 1], 121651200),
    ([some 1, some 1, some 0, some 0, some 0], -116812800),
    ([some 1, some 1, some 0, some 0, some 1], -213580800),
    ([some 1, some 1, some 0, some 1, some 0], -182476800),
    ([some 1, some 1, some 0, some 1, some 1], -182476800),
    ([some 1, some 1, some 1, some 0, some 0], 132019200),
    ([some 1, some 1, some 1, some 0, some 1], 121651200),
    ([some 1, some 1, some 1, some 1, some 0], -30412800),
    ([none, some 0, some 0, some 0, some 0, some 1], 100224000),
    ([none, some 0, some 0, some 0, some 1, some 0], -400896000),
    ([none, some 0, some 0, some 0, some 1, some 1], -400896000),
    ([none, some 0, some 0, some 1, some 0, some 0], 601344000),
    ([none, some 0, some 0, some 1, some 0, some 1], 601344000),
    ([none, some 0, some 0, some 1, some 1, some 0], 601344000),
    ([none, some 0, some 0, some 1, some 1, some 1], 601344000),
    ([none, some 0, some 1, some 0, some 0, some 0], -400896000),
    ([none, some 0, some 1, some 0, some 0, some 1], 601344000),
    ([none, some 0, some 1, some 0, some 1, some 0], -2405376000),
    ([none, some 0, some 1, some 0, some 1, some 1], -2405376000),
    ([none, some 0, some 1, some 1, some 0, some 0], 601344000),
    ([none, some 0, some 1, some 1, some 0, some 1], 3608064000),
    ([none, some 0, some 1, some 1, some 1, some 0], -2405376000),
    ([none, some 0, some 1, some 1, some 1, some 1], -400896000),
    ([none, some 1, some 0, some 0, some 0, some 0], 100224000),
    ([none, some 1, some 0, some 0, some 0, some 1], -400896000),
    ([none, some 1, some 0, some 0, some 1, some 0], 601344000),
    ([none, some 1, some 0, some 0, some 1, some 1], 601344000),
    ([none, some 1, some 0, some 1, some 0, some 0], 601344000),
    ([none, some 1, some 0, some 1, some 0, some 1], -2405376000),
    ([none, some 1, some 0, some 1, some 1, some 0], 3608064000),
    ([none, some 1, some 0, some 1, some 1, some 1], 1603584000),
    ([none, some 1, some 1, some 0, some 0, some 0], -400896000),
    ([none, some 1, some 1, some 0, some 0, some 1], 601344000),
    ([none, some 1, some 1, some 0, some 1, some 0], -2405376000),
    ([none, some 1, some 1, some 0, some 1, some 1], -2405376000),
    ([none, some 1, some 1, some 1, some 0, some 0], 601344000),
    ([none, some 1, some 1, some 1, some 0, some 1], 1603584000),
    ([none, some 1, some 1, some 1, some 1, some 0], -400896000),
    ([none, none, some 0, some 0, some 0, some 0, some 1], -177120000),
    ([none, none, some 0, some 0, some 0, some 1, some 0], 708480000),
    ([none, none, some 0, some 0, some 0, some 1, some 1], 708480000),
    ([none, none, some 0, some 0, some 1, some 0, some 0], -1062720000),
    ([none, none, some 0, some 0, some 1, some 0, some 1], -933120000),
    ([none, none, some 0, some 0, some 1, some 1, some 0], -1192320000),
    ([none, none, some 0, some 0, some 1, some 1, some 1], -1105920000),
    ([none, none, some 0, some 1, some 0, some 0, some 0], 708480000),
    ([none, none, some 0, some 1, some 0, some 0, some 1], -1451520000),
    ([none, none, some 0, some 1, some 0, some 1, some 0], 4769280000),
    ([none, none, some 0, some 1, some 0, some 1, some 1], 4769280000),
    ([none, none, some 0, some 1, some 1, some 0, some 0], -1192320000),
    ([none, none, some 0, some 1, some 1, some 0, some 1], -7672320000),
    ([none, none, some 0, some 1, some 1, some 1, some 0], 5114880000),
    ([none, none, some 0, some 1, some 1, some 1, some 1], 794880000),
    ([none, none, some 1, some 0, some 0, some 0, some 0], -177120000),
    ([none, none, some 1, some 0, some 0, some 0, some 1], 967680000),
    ([none, none, some 1, some 0, some 0, some 1, some 0], -1451520000),
    ([none, none, some 1, some 0, some 0, some 1, some 1], -1451520000),
    ([none, none, some 1, some 0, some 1, some 0, some 0], -933120000),
    ([none, none, some 1, some 0, some 1, some 0, some 1], 5806080000),
    ([none, none, some 1, some 0, some 1, some 1, some 0], -7672320000),
    ([none, none, some 1, some 0, some 1, some 1, some 1], -3179520000),
    ([none, none, some 1, some 1, some 0, some 0, some 0], 708480000),
    ([none, none, some 1, some 1, some 0, some 0, some 1], -1451520000),
    ([none, none, some 1, some 1, some 0, some 1, some 0], 4769280000),
    ([none, none, some 1, some 1, some 0, some 1, some 1], 4769280000),
    ([none, none, some 1, some 1, some 1, some 0, some 0], -1105920000),
    ([none, none, some 1, some 1, some 1, some 0, some 1], -3179520000),
    ([none, none, some 1, some 1, some 1, some 1, some 0], 794880000)]
  | _ => []

private def residualTable (n : ℕ) : ParamTable :=
  CentralBinaryWordTable.collect (tableLog n ++ CoeffWordTable.smul (-60) (targetTable n) ++
    CoeffWordTable.smul (-60) (CoeffWordTable.mul relationTable (suzukiQuotientTable n)))

private lemma coefficients_match (n : Fin 6) :
    (residualTable n).all (fun row ↦ row.2 == 0) = true := by
  fin_cases n <;> decide +kernel

section Semantics

variable {A : Type*} [Ring A] [Algebra ℝ A]

private def parameterLetters (a b : A) (p : ℝ) : Option (Fin 2) → A :=
  fun x ↦ match x with
      | none => p • 1
      | some i => (120 : ℝ)⁻¹ • (![a, b] : Fin 2 → A) i

variable (a b : A) (p : ℝ)

local notation "E" => CoeffWordTable.eval (Int.castRingHom ℝ) (parameterLetters a b p)

private lemma eval_collect (t : ParamTable) :
    E (CentralBinaryWordTable.collect t) = E t := by
  convert CentralBinaryWordTable.eval_collect (Int.castRingHom ℝ) p
    (fun i ↦ (120 : ℝ)⁻¹ • (![a, b] : Fin 2 → A) i) t using 2 <;>
    funext x <;> cases x <;> rfl

private lemma eval_tablePow (t : ParamTable) (n : ℕ) :
    E (tablePow t n) = E t ^ n := by
  induction n with
  | zero => simp [tablePow, CoeffWordTable.eval_unit]
  | succ n ih =>
      rw [tablePow, eval_collect, CoeffWordTable.eval_mul, ih, pow_succ']

private lemma eval_argumentTables :
    (argumentTables.map fun t ↦ (60 : ℝ) • E t) =
      fiveStageStrangArguments a b p 1 := by
  norm_num [argumentTables, parameterLetters, CoeffWordTable.eval, fiveStageStrangArguments,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  repeat' constructor
  all_goals module

private lemma eval_tableBracket (s t : ParamTable) :
    E (tableBracket s t) =
      E s * E t - E t * E s := by
  rw [tableBracket, eval_collect, CoeffWordTable.eval_append,
    CoeffWordTable.eval_mul, CoeffWordTable.eval_smul,
    CoeffWordTable.eval_mul]
  rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]

private lemma eval_childsTables (i : Fin 8) :
    E (childsTables i) =
      binaryQuinticCommutator ((120 : ℝ)⁻¹ • a) ((120 : ℝ)⁻¹ • b) i := by
  fin_cases i <;> dsimp [childsTables]
  all_goals
    simp only [eval_tableBracket, CoeffWordTable.eval_singleton, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, map_one, one_smul, parameterLetters,
      Matrix.cons_val_zero, Matrix.cons_val_one, Ring.lie_def]

private lemma eval_betaTables (i : Fin 8) :
    E (betaTables i) =
      ((120 : ℝ) ^ 5 * suzukiQuinticCoeff p i) • (1 : A) := by
  fin_cases i <;>
    norm_num [betaTables, suzukiQuinticCoeff, parameterLetters, CoeffWordTable.eval,
      smul_mul_assoc, smul_smul]
  all_goals module

private lemma binaryQuinticCommutator_smul (a b : A) (c : ℝ) (i : Fin 8) :
    binaryQuinticCommutator (c • a) (c • b) i = c ^ 5 • binaryQuinticCommutator a b i := by
  have hbracket (x y : A) (r s : ℝ) :
      (r • x) * (s • y) - (s • y) * (r • x) = (r * s) • (x * y - y * x) := by
    simp only [smul_mul_smul_comm, smul_sub]
    rw [mul_comm s r]
  unfold binaryQuinticCommutator
  split <;> simp only [Ring.lie_def, hbracket] <;> congr 1 <;> ring

private lemma eval_targetTable_five :
    E (targetTable 5) = suzukiQuinticTerm a b p := by
  rw [targetTable, eval_collect, CoeffWordTable.eval_flatMap]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  unfold suzukiQuinticTerm
  apply sum_congr rfl
  intro i hi
  rw [CoeffWordTable.eval_mul, eval_betaTables, eval_childsTables, binaryQuinticCommutator_smul,
    smul_mul_smul_comm, one_mul]
  congr 1
  norm_num
  ring

private lemma eval_relationTable :
    E relationTable = suzukiCubicCoeff p • (1 : A) := by
  norm_num [relationTable, parameterLetters, CoeffWordTable.eval, suzukiCubicCoeff,
    smul_mul_assoc, smul_smul]
  module

variable [Algebra ℚ A] [IsScalarTower ℚ ℝ A]

private lemma eval_tableExp (ts : List ParamTable) (n : ℕ) :
    n ≤ 5 → E (tableExp ts n) =
      expListTerm (ts.map fun t ↦ (60 : ℝ) • E t) n := by
  induction ts generalizing n with
  | nil =>
      intro hn
      by_cases h : n = 0 <;>
        simp [tableExp, tableExpFrom, expListTerm, h, CoeffWordTable.eval_unit,
          CoeffWordTable.eval_nil]
  | cons t ts ih =>
      intro hn
      rw [tableExp, tableExpFrom, eval_collect, CoeffWordTable.eval_flatMap_range,
        List.map_cons, expListTerm, sum_antidiagonal_eq_sum_range_succ_mk]
      apply sum_congr rfl
      intro i hi
      rw [← tableExp, CoeffWordTable.eval_smul, CoeffWordTable.eval_mul, eval_tablePow,
        ih _ (by lia)]
      simp only [← Rat.cast_smul_eq_qsmul ℝ,
        smul_pow, smul_mul_assoc, smul_smul]
      have hi5 : i ≤ 5 := by
        have := mem_range.mp hi
        lia
      interval_cases i <;> norm_num [Nat.factorial]

private lemma eval_tablePower (k n : ℕ) (hn : n ≤ 5) :
    E (tablePower k n) =
      positivePowerCoeff (expListTerm (fiveStageStrangArguments a b p 1)) k n := by
  induction k generalizing n with
  | zero => by_cases h : n = 0 <;>
      simp [tablePower, positivePowerCoeff, h, CoeffWordTable.eval_unit,
        CoeffWordTable.eval_nil]
  | succ k ih =>
      rw [tablePower, eval_collect, CoeffWordTable.eval_flatMap_range, positivePowerCoeff]
      apply sum_congr rfl
      intro i hi
      have hi5 : i + 1 ≤ 5 := by
        have := mem_range.mp hi
        lia
      rw [CoeffWordTable.eval_mul, argumentExpTable_eq _ hi5,
        eval_tableExp a b p argumentTables _ hi5, eval_argumentTables, ih _ (by lia)]

private lemma eval_tableLog (n : ℕ) (hn : n ≤ 5) :
    E (tableLog n) =
      (60 : ℝ) • expListLogCoeff (fiveStageStrangArguments a b p 1) n := by
  rw [tableLog, eval_collect, expListLogCoeff, smul_sum, CoeffWordTable.eval_flatMap_range]
  apply sum_congr rfl
  intro k hk
  rw [CoeffWordTable.eval_smul, eval_tablePower a b p k n hn]
  have hk5 : k ≤ 5 := by
    have := mem_range.mp hk
    lia
  simp only [← Rat.cast_smul_eq_qsmul ℝ, smul_smul]
  interval_cases k <;> norm_num [logWeights, logCoeff]

private lemma log_coefficient_eq_target (hp : IsSuzukiCubic p) (n : Fin 6) :
    expListLogCoeff (fiveStageStrangArguments a b p 1) n = E (targetTable n) := by
  have hz := CoeffWordTable.eval_eq_zero_of_all (Int.castRingHom ℝ)
    (parameterLetters a b p) (residualTable n) (coefficients_match n)
  rw [residualTable, eval_collect, CoeffWordTable.eval_append, CoeffWordTable.eval_append,
    CoeffWordTable.eval_smul, CoeffWordTable.eval_smul, CoeffWordTable.eval_mul,
    eval_tableLog a b p n (by
      have := n.isLt
      lia), eval_relationTable] at hz
  change suzukiCubicCoeff p = 0 at hp
  rw [hp, zero_smul, zero_mul, smul_zero, add_zero] at hz
  norm_num only [map_neg, map_ofNat, neg_smul] at hz
  have heq : (60 : ℝ) • expListLogCoeff (fiveStageStrangArguments a b p 1) n =
      (60 : ℝ) • E (targetTable n) := by
    simpa only [add_neg_eq_zero] using hz
  exact (smul_right_injective A (by norm_num : (60 : ℝ) ≠ 0)) heq

end Semantics

/-- The individual formal logarithm coefficients through degree five. This
statement includes the zero slots, rather than only their finite sum. -/
theorem expListLogCoeff_fiveStageStrang_through_five
    {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A] (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 6) :
    expListLogCoeff (fiveStageStrangArguments a b p 1) n =
      if n = 1 then a + b else if n = 5 then suzukiQuinticTerm a b p else 0 := by
  rw [log_coefficient_eq_target a b p hp n]
  fin_cases n
  · simp [targetTable, CoeffWordTable.eval]
  · norm_num [targetTable, parameterLetters, CoeffWordTable.eval, smul_smul]
  · simp [targetTable, CoeffWordTable.eval]
  · simp [targetTable, CoeffWordTable.eval]
  · simp [targetTable, CoeffWordTable.eval]
  · simpa using eval_targetTable_five a b p

/-- **Quintic Suzuki matching**: cubic cancellation leaves the linear term and the
source binary quintic polynomial through degree five. -/
theorem sum_expListLogCoeff_fiveStageStrang_eq {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]
    (a b : A) (p t : ℝ) (hp : IsSuzukiCubic p) :
    (∑ d ∈ range 6, expListLogCoeff (fiveStageStrangArguments a b p t) d) =
      t • (a + b) + t ^ 5 • suzukiQuinticTerm a b p := by
  rw [fiveStageStrangArguments_smul]
  simp only [expListLogCoeff_smul]
  calc
    _ = ∑ d ∈ range 6, t ^ d •
        CoeffWordTable.eval (Int.castRingHom ℝ) (parameterLetters a b p) (targetTable d) := by
      apply sum_congr rfl
      intro d hd
      rw [log_coefficient_eq_target a b p hp ⟨d, mem_range.mp hd⟩]
    _ = _ := by
      simp only [sum_range_succ, sum_range_zero]
      rw [eval_targetTable_five]
      norm_num [targetTable, parameterLetters, CoeffWordTable.eval, smul_smul]

end FQFP.BCH
