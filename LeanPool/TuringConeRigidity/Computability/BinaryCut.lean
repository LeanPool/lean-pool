/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BinaryCut.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BinaryMachine

/-!
# Binary Cut
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable Filter

def approxDecision (z : ℕ × ℕ × ℕ) : Option ℕ :=
  if fracLeft (z.1,z.2.2,2^z.2.1) < fracRight (z.1,z.2.2,2^z.2.1) then some 1
  else if fracRight (z.1,z.2.2+1,2^z.2.1) < fracLeft (z.1,z.2.2+1,2^z.2.1) then some 0
  else none

theorem approxDecision_primrec : Primrec approxDecision := by
  have hD : Primrec (fun z : ℕ × ℕ × ℕ => 2^z.2.1) := powTwo_primrec.comp (Primrec.fst.comp
    Primrec.snd)
  have hlo := Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair hD)
  have hhi := Primrec.fst.pair ((Primrec.succ.comp (Primrec.snd.comp Primrec.snd)).pair hD)
  exact Primrec.ite (Primrec.nat_lt.comp (fracLeft_primrec.comp hlo) (fracRight_primrec.comp hlo))
    (Primrec.const (some 1))
    (Primrec.ite (Primrec.nat_lt.comp (fracRight_primrec.comp hhi) (fracLeft_primrec.comp hhi))
      (Primrec.const (some 0)) (Primrec.const none))

def approxTrial (B : Oracle) (q n : ℕ) : Option ℕ := approxDecision (q,n,numeral B n)

theorem approxTrial_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction B}
      (fun z => Part.some (encode (approxTrial B (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have hq := total_primrec (O := {oracleFunction B}) (Primrec.fst.comp Primrec.unpair)
  have hn := total_primrec (O := {oracleFunction B}) (Primrec.snd.comp Primrec.unpair)
  have hk := total_comp (numeral_recursive B) hn
  have hdec := Primrec.encode.comp (approxDecision_primrec.comp
    ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp
      Primrec.unpair))))
  exact (total_comp (total_primrec hdec) (total_pair hq (total_pair hn hk))).of_eq
    (fun z => by simp [approxTrial])

theorem approxTrial_sound (B : Oracle) (q n a : ℕ) (ha : a ∈ approxTrial B q n) :
    a = if cut (value B) q then 1 else 0 := by
  have hb := bracket B n
  unfold approxTrial approxDecision at ha
  split at ha
  · rename_i h
    have hq := (frac_lt_iff q (numeral B n) (2^n) (by positivity)).mp h
    have hc : cut (value B) q = true := (cut_eq_true _ _).mpr (lt_of_lt_of_le (by simpa using hq)
      hb.1)
    simpa [hc] using (Option.mem_def.mp ha).symm
  · split at ha
    · rename_i h
      have hq := (lt_frac_iff q (numeral B n+1) (2^n) (by positivity)).mp h
      have hc : cut (value B) q = false := Bool.eq_false_iff.mpr (fun hc => by
        have hh := (cut_eq_true _ _).mp hc
        push_cast at hq
        linarith)
      simpa [hc] using (Option.mem_def.mp ha).symm
    · simp at ha

theorem small_width (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, (2^n : ℝ)⁻¹ < ε := by
  have ht : Tendsto (fun n : ℕ => (2^n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2:ℝ)⁻¹| < 1))
  exact (ht.eventually (eventually_lt_nhds hε)).exists

theorem approxTrial_complete (B : Oracle) (hi : Irrational (value B)) (q : ℕ) :
    ∃ n a, a ∈ approxTrial B q n := by
  have hne : (rationalEnumeration q : ℝ) ≠ value B := fun h => hi ⟨_,h⟩
  rcases lt_or_gt_of_ne hne with hq | hq
  · obtain ⟨n,hn⟩ := small_width (value B - rationalEnumeration q) (by linarith)
    have hb := bracket B n
    have hl : (rationalEnumeration q : ℝ) < (numeral B n : ℝ)/(2^n : ℕ) := by
      push_cast
      rw [add_div] at hb
      simp only [one_div] at hb
      linarith
    have hd := (frac_lt_iff q (numeral B n) (2^n) (by positivity)).mpr hl
    exact ⟨n,1,by simp [approxTrial,approxDecision,hd]⟩
  · obtain ⟨n,hn⟩ := small_width (rationalEnumeration q - value B) (by linarith)
    have hb := bracket B n
    have hu : ((numeral B n+1 : ℕ) : ℝ)/(2^n : ℕ) < rationalEnumeration q := by
      push_cast
      rw [add_div]
      simp only [one_div]
      linarith
    have hd := (lt_frac_iff q (numeral B n+1) (2^n) (by positivity)).mpr hu
    have hl : ¬ fracLeft (q,numeral B n,2^n) < fracRight (q,numeral B n,2^n) := by
      intro hh
      have hh' := (frac_lt_iff q (numeral B n) (2^n) (by positivity)).mp hh
      push_cast at hh'
      linarith [hb.1]
    exact ⟨n,0,by simp [approxTrial,approxDecision,hl,hd]⟩

theorem cut_reduces (B : Oracle) (hi : Irrational (value B)) : Reduces (cut (value B)) B := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (approxTrial_recursive B) _ (approxTrial_sound B) (approxTrial_complete B hi)

theorem cut_single_program (B : Oracle) (hi : Irrational (value B)) :
    ∃ p : OracleCode, ∀ q, OracleCode.eval (oracleFunction B) p q = oracleFunction (cut (value B))
      q := by
  obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp (cut_reduces B hi)
  exact ⟨p,fun q => congrFun hp q⟩

end TuringRigidity.BinarySeries

end OAI
