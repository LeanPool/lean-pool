/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BinaryRecovery.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BinaryMachine
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Binary Recovery
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable

/-- Rational endpoints match the two prescribed adjacent dyadic boundaries. -/
def recoverGuard (z : ℕ × ℕ × ℕ × ℕ) : Prop :=
  fracLeft (z.2.2.1,z.2.1,2^(z.1+1)) = fracRight (z.2.2.1,z.2.1,2^(z.1+1)) ∧
  fracLeft (z.2.2.2,z.2.1+1,2^(z.1+1)) = fracRight (z.2.2.2,z.2.1+1,2^(z.1+1))
instance (z : ℕ × ℕ × ℕ × ℕ) : Decidable (recoverGuard z) := inferInstanceAs (Decidable (_ ∧ _))

theorem recoverGuard_primrec : PrimrecPred recoverGuard := by
  have hn : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => 2^(z.1+1)) :=
    powTwo_primrec.comp (Primrec.succ.comp Primrec.fst)
  have hk : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => z.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp
    Primrec.snd)
  have hj : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd)
  exact (Primrec.eq.comp (fracLeft_primrec.comp (hi.pair (hk.pair hn)))
    (fracRight_primrec.comp (hi.pair (hk.pair hn)))).and
    (Primrec.eq.comp (fracLeft_primrec.comp (hj.pair ((Primrec.succ.comp hk).pair hn)))
      (fracRight_primrec.comp (hj.pair ((Primrec.succ.comp hk).pair hn))))

/-- Recover a binary digit when both boundary tests certify the required dyadic interval. -/
def recoverDecision (z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if recoverGuard z.1 ∧ z.2.1=1 ∧ z.2.2=0 then some (z.1.2.1%2) else none

theorem recoverDecision_primrec : Primrec recoverDecision :=
  Primrec.ite ((recoverGuard_primrec.comp Primrec.fst).and
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))))
    (Primrec.option_some.comp (Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 2))) (Primrec.const none)

/-- Try to recover a binary digit from two queried cut bits and a coded dyadic interval. -/
noncomputable def recoverTrial (B : Oracle) (n m : ℕ) : Option ℕ :=
  let k := (Nat.unpair m).1
  let i := (Nat.unpair (Nat.unpair m).2).1
  let j := (Nat.unpair (Nat.unpair m).2).2
  recoverDecision ((n,k,i,j),(bit (cut (value B)) i,bit (cut (value B)) j))

theorem recoverTrial_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction (cut (value B))}
      (fun z => Part.some (encode (recoverTrial B (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (cut (value B))}
  have hn := total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hm := total_primrec (O := O) (Primrec.snd.comp Primrec.unpair)
  have hk := total_comp (total_primrec (Primrec.fst.comp Primrec.unpair)) hm
  have hi := total_comp (total_primrec (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    Primrec.unpair)))) hm
  have hj := total_comp (total_primrec (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    Primrec.unpair)))) hm
  have hg : Nat.RecursiveIn O (oracleFunction (cut (value B))) := .oracle _ (Set.mem_singleton _)
  have hmeta := total_pair hn (total_pair hk (total_pair hi hj))
  have hbits := total_pair (total_comp hg hi) (total_comp hg hj)
  have hdecode : Primrec (fun z : ℕ =>
      (((Nat.unpair (Nat.unpair z).1).1,
        (Nat.unpair (Nat.unpair (Nat.unpair z).1).2).1,
        Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair z).1).2).2),Nat.unpair (Nat.unpair z).2))
          := by
    exact (((Primrec.fst.comp Primrec.unpair).pair
      (((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp
        Primrec.unpair))).comp
        (Primrec.snd.comp Primrec.unpair))).comp (Primrec.fst.comp Primrec.unpair)).pair
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact (total_comp (total_primrec (Primrec.encode.comp (recoverDecision_primrec.comp hdecode)))
    (total_pair hmeta hbits)).of_eq (fun z => by simp [recoverTrial,bit])

theorem recoverTrial_sound (B : Oracle) (hB : Mixed B) (n m a : ℕ)
    (ha : a ∈ recoverTrial B n m) : a = bit B n := by
  let k := (Nat.unpair m).1
  let i := (Nat.unpair (Nat.unpair m).2).1
  let j := (Nat.unpair (Nat.unpair m).2).2
  change a ∈ recoverDecision ((n,k,i,j),(bit (cut (value B)) i,bit (cut (value B)) j)) at ha
  unfold recoverDecision at ha
  split at ha
  · rename_i h
    have hai : a=k%2 := by simpa using (Option.mem_def.mp ha).symm
    have hi := (frac_eq_iff i k (2^(n+1)) (by positivity)).mp h.1.1
    have hj := (frac_eq_iff j (k+1) (2^(n+1)) (by positivity)).mp h.1.2
    have hci : cut (value B) i=true := by cases hh : cut (value B) i <;> simp_all [bit]
    have hcj : cut (value B) j=false := by cases hh : cut (value B) j <;> simp_all [bit]
    have hlo := (cut_eq_true _ _).mp hci
    have hup : value B ≤ (rationalEnumeration j : ℝ) := le_of_not_gt (fun hh => by
      have := (cut_eq_true _ _).mpr hh; simp_all)
    rw [hi] at hlo
    rw [hj] at hup
    have hb := strict_bracket B hB (n+1)
    have hD : (0 : ℝ) < (2^(n+1) : ℝ) := by positivity
    have hk1 : (k : ℝ) < numeral B (n+1)+1 := by
      have hh := lt_trans hlo hb.2
      push_cast at hh
      exact (div_lt_div_iff_of_pos_right hD).mp hh
    have hk2 : (numeral B (n+1) : ℝ) < k+1 := by
      have hh := lt_of_lt_of_le hb.1 hup
      push_cast at hh
      exact (div_lt_div_iff_of_pos_right hD).mp hh
    have hk : k = numeral B (n+1) := by
      have h1 : k < numeral B (n+1)+1 := by exact_mod_cast hk1
      have h2 : numeral B (n+1) < k+1 := by exact_mod_cast hk2
      omega
    rw [hai,hk,numeral]
    unfold bit
    split <;> omega
  · simp at ha

theorem recoverTrial_complete (B : Oracle) (hB : Mixed B) (n : ℕ) :
    ∃ m a, a ∈ recoverTrial B n m := by
  let k := numeral B (n+1)
  let i := encode ((k : ℚ)/2^(n+1))
  let j := encode (((k+1 : ℕ) : ℚ)/2^(n+1))
  have hi : (rationalEnumeration i : ℝ) = (k : ℝ)/(2^(n+1) : ℕ) := by simp [i,rationalEnumeration]
  have hj : (rationalEnumeration j : ℝ) = ((k+1 : ℕ) : ℝ)/(2^(n+1) : ℕ) := by
    simp [j,rationalEnumeration]
  have hg : recoverGuard (n,k,i,j) := ⟨(frac_eq_iff _ _ _ (by positivity)).mpr hi,
    (frac_eq_iff _ _ _ (by positivity)).mpr hj⟩
  have hb := strict_bracket B hB (n+1)
  have hci : cut (value B) i=true := (cut_eq_true _ _).mpr (by simpa [hi,k] using hb.1)
  have hcj : cut (value B) j=false := Bool.eq_false_iff.mpr (fun hh => by
    have hh' := (cut_eq_true _ _).mp hh
    rw [hj] at hh'
    push_cast at hh'
    dsimp only [k] at hh'
    linarith [hb.2])
  exact ⟨Nat.pair k (Nat.pair i j),k%2,by simp [recoverTrial,recoverDecision,bit,hci,hcj,hg]⟩

theorem set_reduces_cut (B : Oracle) (hB : Mixed B) : Reduces B (cut (value B)) := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (recoverTrial_recursive B) _ (recoverTrial_sound B hB) (recoverTrial_complete
    B hB)

theorem set_single_program (B : Oracle) (hB : Mixed B) :
    ∃ p : OracleCode, ∀ n, OracleCode.eval (oracleFunction (cut (value B))) p n = oracleFunction B
      n := by
  obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp (set_reduces_cut B hB)
  exact ⟨p,fun n => congrFun hp n⟩

end TuringRigidity.BinarySeries

end OAI
