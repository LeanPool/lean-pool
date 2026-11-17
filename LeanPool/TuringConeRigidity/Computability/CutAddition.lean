/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/CutAddition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.SumComparison
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Cut Addition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
namespace CutAddition
open RationalCoding UniformOracle

def decision (z : ℕ × (ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if z.2.2.1=1 ∧ z.2.2.2=1 ∧ sumLeft (z.1,z.2.1.1,z.2.1.2)<sumRight (z.1,z.2.1.1,z.2.1.2)
    then some 1 else
  if z.2.2.1=0 ∧ z.2.2.2=0 ∧ sumRight (z.1,z.2.1.1,z.2.1.2)<sumLeft (z.1,z.2.1.1,z.2.1.2)
    then some 0 else none

theorem decision_primrec : Primrec decision := by
  let hargs := Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
    (α := ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  let hfirst := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    (α := ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  let hsecond := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    (α := ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  exact Primrec.ite ((Primrec.eq.comp hfirst (Primrec.const 1)).and
    ((Primrec.eq.comp hsecond (Primrec.const 1)).and
      (Primrec.nat_lt.comp (sumLeft_primrec.comp hargs) (sumRight_primrec.comp hargs))))
    (Primrec.const (some 1))
    (Primrec.ite ((Primrec.eq.comp hfirst (Primrec.const 0)).and
      ((Primrec.eq.comp hsecond (Primrec.const 0)).and
        (Primrec.nat_lt.comp (sumRight_primrec.comp hargs) (sumLeft_primrec.comp hargs))))
      (Primrec.const (some 0)) (Primrec.const none))

noncomputable def trial (x y : ℝ) (n m : ℕ) : Option ℕ :=
  decision (n,Nat.unpair m,
    (if cut x (Nat.unpair m).1 then 1 else 0,if cut y (Nat.unpair m).2 then 1 else 0))

theorem trial_recursive (x y : ℝ) :
    Nat.RecursiveIn {oracleFunction (join (cut x) (cut y))}
      (fun z => Part.some (Encodable.encode (trial x y (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (join (cut x) (cut y))}
  have hq := total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hi := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    Primrec.unpair)))
  have hj := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    Primrec.unpair)))
  have hg : Nat.RecursiveIn O (oracleFunction (join (cut x) (cut y))) := .oracle _
    (Set.mem_singleton _)
  have hbi := total_comp hg (total_comp
    (total_primrec (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)) hi)
  have hbj := total_comp hg (total_comp
    (total_primrec (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1))) hj)
  have hdec : Primrec (fun z : ℕ => Encodable.encode (decision
      ((Nat.unpair z).1,Nat.unpair (Nat.unpair (Nat.unpair z).2).1,
        Nat.unpair (Nat.unpair (Nat.unpair z).2).2))) :=
    Primrec.encode.comp (decision_primrec.comp
      ((Primrec.fst.comp Primrec.unpair).pair
        ((Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
          Primrec.unpair)))).pair
          (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
            Primrec.unpair)))))))
  exact (total_comp (total_primrec hdec)
    (total_pair hq (total_pair (total_pair hi hj) (total_pair hbi hbj)))).of_eq
      (fun z => by simp [trial])

private theorem bit_one (b : Bool) (h : (if b then (1 : ℕ) else 0) = 1) : b=true := by
  cases b <;> simp_all
private theorem bit_zero (b : Bool) (h : (if b then (1 : ℕ) else 0) = 0) : b=false := by
  cases b <;> simp_all

theorem trial_sound (x y : ℝ) (n m r : ℕ) (hr : r ∈ trial x y n m) :
    r = if cut (x+y) n then 1 else 0 := by
  let i := (Nat.unpair m).1
  let j := (Nat.unpair m).2
  change r ∈ decision (n,(i,j),(if cut x i then 1 else 0,if cut y j then 1 else 0)) at hr
  generalize hbi : (if cut x i then (1 : ℕ) else 0) = bi at hr
  generalize hbj : (if cut y j then (1 : ℕ) else 0) = bj at hr
  unfold decision at hr
  split at hr
  · rename_i h
    have hr' : r=1 := by symm; simpa using hr
    subst r
    have hx := (cut_eq_true x i).mp (bit_one _ (hbi.trans h.1))
    have hy := (cut_eq_true y j).mp (bit_one _ (hbj.trans h.2.1))
    have hq := (lt_sum_iff n i j).mp h.2.2
    have hc : cut (x+y) n=true := (cut_eq_true _ _).mpr (by linarith)
    simp [hc]
  · split at hr
    · rename_i h
      have hr' : r=0 := by symm; simpa using hr
      subst r
      have hx : x ≤ (rationalEnumeration i : ℝ) := le_of_not_gt
        (fun hx => Bool.noConfusion ((bit_zero _ (hbi.trans h.1)).symm.trans ((cut_eq_true x
          i).mpr hx)))
      have hy : y ≤ (rationalEnumeration j : ℝ) := le_of_not_gt
        (fun hy => Bool.noConfusion ((bit_zero _ (hbj.trans h.2.1)).symm.trans ((cut_eq_true y
          j).mpr hy)))
      have hq := (sum_lt_iff n i j).mp h.2.2
      have hnot : ¬(rationalEnumeration n : ℝ)<x+y := by linarith
      have hc : cut (x+y) n=false := Bool.eq_false_iff.mpr
        (fun hc => hnot ((cut_eq_true _ _).mp hc))
      simp [hc]
    · simp at hr

theorem trial_complete (x y : ℝ) (hxy : Irrational (x + y)) (n : ℕ) :
    ∃ m r, r ∈ trial x y n m := by
  have hne : (rationalEnumeration n : ℝ) ≠ x+y := fun h => hxy ⟨rationalEnumeration n,h⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨a,ha,hax⟩ := exists_rat_btwn (show (rationalEnumeration n : ℝ)-y<x by linarith)
    obtain ⟨b,hb,hby⟩ := exists_rat_btwn (show (rationalEnumeration n : ℝ)-(a : ℝ)<y by linarith)
    obtain ⟨i,hi⟩ := rationalEnumeration_surjective a
    obtain ⟨j,hj⟩ := rationalEnumeration_surjective b
    have hci : cut x i=true := (cut_eq_true x i).mpr (by simpa only [hi] using hax)
    have hcj : cut y j=true := (cut_eq_true y j).mpr (by simpa only [hj] using hby)
    have hl : sumLeft (n,i,j)<sumRight (n,i,j) := (lt_sum_iff n i j).mpr (by rw [hi,hj]; linarith)
    exact ⟨Nat.pair i j,1,by simp [trial,decision,hci,hcj,hl]⟩
  · obtain ⟨a,hxa,ha⟩ := exists_rat_btwn (show x<(rationalEnumeration n : ℝ)-y by linarith)
    obtain ⟨b,hyb,hb⟩ := exists_rat_btwn (show y<(rationalEnumeration n : ℝ)-(a : ℝ) by linarith)
    obtain ⟨i,hi⟩ := rationalEnumeration_surjective a
    obtain ⟨j,hj⟩ := rationalEnumeration_surjective b
    have hci : cut x i=false := Bool.eq_false_iff.mpr (fun hc => by
      have hh := (cut_eq_true x i).mp hc
      rw [hi] at hh
      linarith)
    have hcj : cut y j=false := Bool.eq_false_iff.mpr (fun hc => by
      have hh := (cut_eq_true y j).mp hc
      rw [hj] at hh
      linarith)
    have hu : sumRight (n,i,j)<sumLeft (n,i,j) := (sum_lt_iff n i j).mpr (by rw [hi,hj]; linarith)
    exact ⟨Nat.pair i j,0,by simp [trial,decision,hci,hcj,hu]⟩

theorem irrational_add_reduces (x y : ℝ) (hxy : Irrational (x + y)) :
    Reduces (cut (x+y)) (join (cut x) (cut y)) := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (trial_recursive x y) (fun n => if cut (x+y) n then 1 else 0)
    (trial_sound x y) (trial_complete x y hxy)
end CutAddition

theorem cut_add_reduces (x y : ℝ) : Reduces (cut (x+y)) (join (cut x) (cut y)) := by
  by_cases hxy : Irrational (x+y)
  · exact CutAddition.irrational_add_reduces x y hxy
  · obtain ⟨q,hq⟩ := not_not.mp hxy
    rw [←hq]
    exact rational_cut_reduces q _

end TuringRigidity

end OAI
