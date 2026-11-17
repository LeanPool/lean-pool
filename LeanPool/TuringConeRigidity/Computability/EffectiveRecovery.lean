/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/EffectiveRecovery.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.RationalCoding
public import LeanPool.TuringConeRigidity.Computability.BranchFrequency

/-!
# Effective Recovery
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

namespace EffectiveRecovery
open RationalCoding

def window (A B : ℕ) (z : Bool × (ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if z.1 then some 1 else
  if z.2.1.1*z.2.2.1*A + z.2.1.2*B < z.2.1.2*z.2.2.2*A then some 1 else
  if z.2.1.2*(z.2.2.2*A+B) < z.2.1.1*z.2.2.1*A then some 0 else none

theorem window_primrec (A B : ℕ) : Primrec (window A B) := by
  let Q := Primrec.fst.comp (Primrec.fst.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  let D := Primrec.snd.comp (Primrec.fst.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  let N := Primrec.fst.comp (Primrec.snd.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  let S := Primrec.snd.comp (Primrec.snd.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) (Primrec.const (some 1))
    (Primrec.ite (Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp Q N) (Primrec.const A))
        (Primrec.nat_mul.comp D (Primrec.const B)))
      (Primrec.nat_mul.comp (Primrec.nat_mul.comp D S) (Primrec.const A)))
      (Primrec.const (some 1))
      (Primrec.ite (Primrec.nat_lt.comp
        (Primrec.nat_mul.comp D (Primrec.nat_add.comp
          (Primrec.nat_mul.comp S (Primrec.const A)) (Primrec.const B)))
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp Q N) (Primrec.const A)))
        (Primrec.const (some 0)) (Primrec.const none)))

theorem lower_iff (Q D N S A B : ℕ) (hD : 0 < D) (hN : 0 < N) (hA : 0 < A) :
    (Q : ℝ)/D < (S : ℝ)/N - (B : ℝ)/(N*A) ↔ Q*N*A+D*B < D*S*A := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hden : (0 : ℝ) < D*N*A := mul_pos (mul_pos hd hn) ha
  have he : ((S : ℝ)/N - (B : ℝ)/(N*A) - (Q : ℝ)/D) * (D*N*A) =
      (D : ℝ)*S*A - ((Q : ℝ)*N*A+D*B) := by
    field_simp
    ring
  constructor
  · intro h
    have hp := mul_pos (sub_pos.mpr h) hden
    rw [he] at hp
    exact_mod_cast sub_pos.mp hp
  · intro h
    have hr : (Q : ℝ)*N*A+D*B < (D : ℝ)*S*A := by exact_mod_cast h
    have hp : 0 < ((S : ℝ)/N - (B : ℝ)/(N*A) - (Q : ℝ)/D) * (D*N*A) := by
      rw [he]; linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hp)

theorem upper_iff (Q D N S A B : ℕ) (hD : 0 < D) (hN : 0 < N) (hA : 0 < A) :
    (S : ℝ)/N + (B : ℝ)/(N*A) < (Q : ℝ)/D ↔ D*(S*A+B) < Q*N*A := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hden : (0 : ℝ) < D*N*A := mul_pos (mul_pos hd hn) ha
  have he : ((Q : ℝ)/D - ((S : ℝ)/N + (B : ℝ)/(N*A))) * (D*N*A) =
      (Q : ℝ)*N*A - (D : ℝ)*(S*A+B) := by
    field_simp
  constructor
  · intro h
    have hp := mul_pos (sub_pos.mpr h) hden
    rw [he] at hp
    exact_mod_cast sub_pos.mp hp
  · intro h
    have hr : (D : ℝ)*(S*A+B) < (Q : ℝ)*N*A := by exact_mod_cast h
    have hp : 0 < ((Q : ℝ)/D - ((S : ℝ)/N + (B : ℝ)/(N*A))) * (D*N*A) := by
      rw [he]; linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hp)
end EffectiveRecovery

namespace RecoveryData
open RationalCoding EffectiveRecovery
variable {F : ℝ → Oracle} {t u v : ℝ}

theorem delta_numerator_pos (d : RecoveryData F t u v) : 0 < d.delta.num.natAbs := by
  have hn : 0 < d.delta.num := Rat.num_pos.mpr d.delta_pos
  have he : (d.delta.num.natAbs : ℤ) = d.delta.num := by
    rw [Int.natCast_natAbs,abs_of_pos hn]
  rw [←he] at hn
  exact_mod_cast hn

theorem delta_fraction (d : RecoveryData F t u v) :
    (d.delta : ℝ) = (d.delta.num.natAbs : ℝ)/(d.delta.den : ℝ) := by
  have hn : 0 < d.delta.num := Rat.num_pos.mpr d.delta_pos
  have he : (d.delta.num.natAbs : ℤ) = d.delta.num := by
    rw [Int.natCast_natAbs,abs_of_pos hn]
  have he' : (d.delta.num.natAbs : ℝ) = (d.delta.num : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) he
  rw [Rat.cast_def,he']

theorem radius_fraction (d : RecoveryData F t u v) (N : ℕ) (hN : 0 < N) :
    1/((N : ℝ)*(d.delta : ℝ)) = (d.delta.den : ℝ)/((N : ℝ)*d.delta.num.natAbs) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < d.delta.num.natAbs := by exact_mod_cast d.delta_numerator_pos
  have hb : (0 : ℝ) < d.delta.den := by exact_mod_cast d.delta.den_pos
  rw [d.delta_fraction]
  field_simp

def cutTrial (d : RecoveryData F t u v) (i m : ℕ) : Option ℕ :=
  window d.delta.num.natAbs d.delta.den
    (negative i,(numeratorMagnitude i,denominator i),(m+1,d.count (m+1)))

theorem cutTrial_recursive (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    Nat.RecursiveIn {oracleFunction (fourTuple F t u v d.delta)}
      (fun z => Part.some (Encodable.encode (d.cutTrial (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (fourTuple F t u v d.delta)}
  have hq := UniformOracle.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hN := UniformOracle.total_primrec (O := O) (Primrec.succ.comp (Primrec.snd.comp
    Primrec.unpair))
  have hS := UniformOracle.total_comp (d.count_recursive ht0 ht1) hN
  have hwindow : Primrec (fun z : ℕ => Encodable.encode
      (window d.delta.num.natAbs d.delta.den
        (negative (Nat.unpair z).1,
          (numeratorMagnitude (Nat.unpair z).1,denominator (Nat.unpair z).1),
          ((Nat.unpair (Nat.unpair z).2).1,(Nat.unpair (Nat.unpair z).2).2)))) :=
    Primrec.encode.comp ((window_primrec _ _).comp
      ((negative_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
        (((numeratorMagnitude_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
          (denominator_primrec.comp (Primrec.fst.comp Primrec.unpair))).pair
            (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
  exact (UniformOracle.total_comp (UniformOracle.total_primrec hwindow)
    (UniformOracle.total_pair hq (UniformOracle.total_pair hN hS))).of_eq
      (fun z => by simp [cutTrial])

theorem cutTrial_sound (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (i m r : ℕ) (hr : r ∈ d.cutTrial i m) : r = if cut t i then 1 else 0 := by
  have hn : 0 < m+1 := Nat.succ_pos m
  have he := d.count_frequency_bound ht0 ht1 (m+1) hn
  rw [d.radius_fraction (m+1) hn] at he
  unfold cutTrial window at hr
  split at hr
  · rename_i hneg
    have hr' : r=1 := by symm; simpa using hr
    subst r
    have hq : (rationalEnumeration i : ℝ) ≤ 0 := by
      rw [query_value,ite_eq_left hneg]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hc : cut t i = true := (cut_eq_true t i).mpr (hq.trans_lt ht0)
    simp [hc]
  · rename_i hneg
    have hq : (rationalEnumeration i : ℝ) = (numeratorMagnitude i : ℝ)/(denominator i : ℝ) := by
      rw [query_value,ite_eq_right hneg]
    split at hr
    · rename_i hl
      have hr' : r=1 := by symm; simpa using hr
      subst r
      have hl' := (lower_iff (numeratorMagnitude i) (denominator i) (m+1) (d.count (m+1))
        d.delta.num.natAbs d.delta.den (denominator_pos i) hn d.delta_numerator_pos).mpr hl
      rw [←hq] at hl'
      have hh := (abs_lt.mp he).1
      have hc : cut t i = true := (cut_eq_true t i).mpr (by linarith)
      simp [hc]
    · split at hr
      · rename_i hu
        have hr' : r=0 := by symm; simpa using hr
        subst r
        have hu' := (upper_iff (numeratorMagnitude i) (denominator i) (m+1) (d.count (m+1))
          d.delta.num.natAbs d.delta.den (denominator_pos i) hn d.delta_numerator_pos).mpr hu
        rw [←hq] at hu'
        have hh := (abs_lt.mp he).2
        have htq : t < (rationalEnumeration i : ℝ) := by linarith
        have hc : cut t i = false := Bool.eq_false_iff.mpr
          (fun h => (not_lt_of_gt htq) ((cut_eq_true t i).mp h))
        simp [hc]
      · simp at hr

theorem cutTrial_complete (d : RecoveryData F t u v) (ht : Irrational t)
    (ht0 : 0 < t) (ht1 : t < 1) (i : ℕ) : ∃ m r, r ∈ d.cutTrial i m := by
  by_cases hneg : negative i = true
  · exact ⟨0,1,by simp [cutTrial,window,hneg]⟩
  · have hq : (rationalEnumeration i : ℝ) = (numeratorMagnitude i : ℝ)/(denominator i : ℝ) := by
      rw [query_value,ite_eq_right hneg]
    have hne : (rationalEnumeration i : ℝ) ≠ t := fun h => ht ⟨rationalEnumeration i,h⟩
    obtain ⟨⟨N,hN,hs⟩,_⟩ := comparison_search t (d.delta : ℝ)
      (fun n => (d.count n : ℝ)/(n : ℝ)) (by exact_mod_cast d.delta_pos)
      (fun n hn => d.count_frequency_bound ht0 ht1 n hn) (rationalEnumeration i) hne
    rw [d.radius_fraction N hN,hq] at hs
    have hm : N-1+1=N := by omega
    rcases hs with hl | hu
    · have hl' := (lower_iff (numeratorMagnitude i) (denominator i) N (d.count N)
        d.delta.num.natAbs d.delta.den (denominator_pos i) hN d.delta_numerator_pos).mp hl
      exact ⟨N-1,1,by simp [cutTrial,hm,window,hneg,hl']⟩
    · have hu' := (upper_iff (numeratorMagnitude i) (denominator i) N (d.count N)
        d.delta.num.natAbs d.delta.den (denominator_pos i) hN d.delta_numerator_pos).mp hu
      by_cases hl' : numeratorMagnitude i*N*d.delta.num.natAbs+denominator i*d.delta.den <
          denominator i*d.count N*d.delta.num.natAbs
      · exact ⟨N-1,1,by simp [cutTrial,hm,window,hneg,hl']⟩
      · exact ⟨N-1,0,by simp [cutTrial,hm,window,hneg,hl',hu']⟩

theorem cut_reduces (d : RecoveryData F t u v) (ht : Irrational t)
    (ht0 : 0 < t) (ht1 : t < 1) : Reduces (cut t) (fourTuple F t u v d.delta) := by
  apply RecursiveIn.iff_nat.mpr
  exact UniformOracle.total_search (d.cutTrial_recursive ht0 ht1)
    (fun i => if cut t i then 1 else 0) (d.cutTrial_sound ht0 ht1)
      (d.cutTrial_complete ht ht0 ht1)

theorem cut_single_program (d : RecoveryData F t u v) (ht : Irrational t)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ c : OracleCode, OracleCode.eval (oracleFunction (fourTuple F t u v d.delta)) c =
      oracleFunction (cut t) :=
  (OracleCode.turingReducible_iff_exists_code _ _).mp (d.cut_reduces ht ht0 ht1)

end RecoveryData

theorem four_value_recovery : FourValueRecovery := by
  intro F hF hfiber hadd t ht ht0 ht1
  obtain ⟨G,hG,hdata⟩ := recovery_data_exists F hF hfiber hadd t
  refine ⟨G,hG,?_⟩
  intro p hp
  obtain ⟨d⟩ := hdata p hp
  refine ⟨d.delta,d.delta_pos,?_,d.cut_reduces ht ht0 ht1⟩
  exact_mod_cast d.delta_lt.trans d.radius_lt_one

theorem main_of_remaining_obligations (hrep : BorelRepresentation) (harith : CutArithmetic)
    (hcover : IrrationalDegreeCoverage) (havoid : CategoryAvoidance) : MainTheorem :=
  main_of_obligations hrep harith hcover four_value_recovery havoid

end TuringRigidity

end OAI
