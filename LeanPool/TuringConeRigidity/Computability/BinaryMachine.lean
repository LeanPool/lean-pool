/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BinaryMachine.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BinarySeries
public import LeanPool.TuringConeRigidity.Computability.RationalCut

/-!
# Binary Machine
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable

theorem eventually_constant_reduces (B A : Oracle) (b : Bool) (N : ℕ)
    (h : ∀ n, N ≤ n → B n = b) : Reduces B A := by
  let L := (List.range N).map (bit B)
  let d : ℕ := if b then 1 else 0
  have hp : Primrec (fun n => L.getD n d) := (Primrec.list_getD d).comp (Primrec.const L) Primrec.id
  have he (n : ℕ) : L.getD n d = bit B n := by
    by_cases hn : n < N
    · simp [L, List.getD, List.getElem?_map, List.getElem?_range hn]
    · have hb := h n (by omega)
      have hz : (List.range N)[n]? = none := List.getElem?_eq_none (by simp; omega)
      simp [L, List.getD, hz, bit, hb, d]
  apply RecursiveIn.iff_nat.mpr
  exact total_primrec (hp.of_eq he)

theorem mixed_of_noncomputable (B : Oracle) (h : ¬ Reduces B (fun _ => false)) : Mixed B := by
  intro N
  constructor
  · by_contra hn
    push Not at hn
    apply h
    exact eventually_constant_reduces B _ false N (fun n hN => Bool.eq_false_iff.mpr (hn n hN))
  · by_contra hn
    push Not at hn
    apply h
    exact eventually_constant_reduces B _ true N (fun n hN => Bool.eq_true_of_not_eq_false (hn n
      hN))

/-- Interpret a finite list of binary values as a binary numeral. -/
def foldNumeral (L : List ℕ) : ℕ := L.foldl (fun a b => 2*a+b) 0

theorem foldNumeral_primrec : Primrec foldNumeral :=
  Primrec.list_foldl Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) Primrec.snd).comp
      Primrec.snd).to₂

theorem foldNumeral_prefix (B : Oracle) (n : ℕ) :
    foldNumeral (oraclePrefix (bit B) n) = numeral B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [foldNumeral, oraclePrefix, List.range_succ, List.foldl_append, numeral] using
      congrArg (fun a => 2*a+bit B n) ih

theorem numeral_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction B} (fun n => Part.some (numeral B n)) := by
  have hf := total_comp (total_primrec (foldNumeral_primrec.comp
      (Primrec.option_getD_default.comp Primrec.decode))) (prefix_recursive (bit B))
  exact hf.of_eq (fun n => by simp only [encodek, Option.getD_some, foldNumeral_prefix])

theorem powTwo_primrec : Primrec (fun n : ℕ => 2^n) := by
  have hp : Primrec (fun n : ℕ => (List.range n).foldl (fun a _ => 2*a) 1) :=
    Primrec.list_foldl Primrec.list_range (Primrec.const 1)
      ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst).comp Primrec.snd).to₂
  apply hp.of_eq
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, pow_succ, Nat.mul_comm]

/-- The left natural-number cross-product in the rational comparison for binary cut
computation. -/
def fracLeft (z : ℕ × ℕ × ℕ) : ℕ := positiveNumerator z.1 * z.2.2
/-- The right natural-number cross-product in the rational comparison for binary cut
computation. -/
def fracRight (z : ℕ × ℕ × ℕ) : ℕ := z.2.1 * denominator z.1 + negativeNumerator z.1 * z.2.2

theorem fracLeft_primrec : Primrec fracLeft := Primrec.nat_mul.comp
  (positiveNumerator_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
theorem fracRight_primrec : Primrec fracRight := Primrec.nat_add.comp
  (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (denominator_primrec.comp Primrec.fst))
  (Primrec.nat_mul.comp (negativeNumerator_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem frac_lt_iff (q k D : ℕ) (hD : 0 < D) :
    fracLeft (q,k,D) < fracRight (q,k,D) ↔ (rationalEnumeration q : ℝ) < (k : ℝ)/D := by
  have hden : (0 : ℝ) < denominator q := by exact_mod_cast denominator_pos q
  rw [signed_query_value, div_lt_div_iff₀ hden (by exact_mod_cast hD)]
  unfold fracLeft fracRight
  constructor <;> intro h
  · have hh : (positiveNumerator q : ℝ)*D < k*denominator q + negativeNumerator q*D := by
      exact_mod_cast h
    nlinarith
  · have hh : (positiveNumerator q : ℝ)*D < k*denominator q + negativeNumerator q*D := by nlinarith
    exact_mod_cast hh

theorem lt_frac_iff (q k D : ℕ) (hD : 0 < D) :
    fracRight (q,k,D) < fracLeft (q,k,D) ↔ (k : ℝ)/D < (rationalEnumeration q : ℝ) := by
  have hden : (0 : ℝ) < denominator q := by exact_mod_cast denominator_pos q
  rw [signed_query_value, div_lt_div_iff₀ (by exact_mod_cast hD) hden]
  unfold fracLeft fracRight
  constructor <;> intro h
  · have hh : k* (denominator q : ℝ) + negativeNumerator q*D < positiveNumerator q*D := by
      exact_mod_cast h
    nlinarith
  · have hh : k* (denominator q : ℝ) + negativeNumerator q*D < positiveNumerator q*D := by nlinarith
    exact_mod_cast hh

theorem frac_eq_iff (q k D : ℕ) (hD : 0 < D) :
    fracLeft (q,k,D) = fracRight (q,k,D) ↔ (rationalEnumeration q : ℝ) = (k : ℝ)/D := by
  constructor
  · intro he
    apply le_antisymm
    · exact le_of_not_gt (fun h => by have := (lt_frac_iff q k D hD).mpr h; omega)
    · exact le_of_not_gt (fun h => by have := (frac_lt_iff q k D hD).mpr h; omega)
  · intro he
    apply Nat.le_antisymm
    · exact Nat.le_of_not_gt (fun h => by have := (lt_frac_iff q k D hD).mp h; linarith)
    · exact Nat.le_of_not_gt (fun h => by have := (frac_lt_iff q k D hD).mp h; linarith)

end TuringRigidity.BinarySeries

end OAI
