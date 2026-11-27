/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Betting
public import Mathlib.Computability.RE
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring

/-!
# Computable rational arithmetic

This file supplies explicit computability proofs for the canonical numerator and
denominator representation used by `ComputableRealCapital`.
-/

@[expose] public section

namespace Klr.RationalComputability

theorem primrec_int_split : Primrec Equiv.intEquivNatSumNat := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq (fun z => by cases z <;> rfl)

theorem primrec_int_merge : Primrec Equiv.intEquivNatSumNat.symm := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq (fun z => by cases z <;> rfl)

theorem primrec_int_ofNat : Primrec Int.ofNat :=
  primrec_int_merge.comp Primrec.sumInl

theorem primrec_int_negSucc : Primrec Int.negSucc :=
  primrec_int_merge.comp Primrec.sumInr

/-- The nonnegative part of an integer as a natural number. -/
def positivePart : ℤ → ℕ
  | .ofNat n => n
  | .negSucc _ => 0

/-- The magnitude of the negative part of an integer. -/
def negativePart : ℤ → ℕ
  | .ofNat _ => 0
  | .negSucc n => n + 1

theorem primrec_positivePart : Primrec positivePart :=
  (Primrec.sumCasesOn primrec_int_split Primrec.snd.to₂ (Primrec.const 0).to₂).of_eq
    (fun z => by cases z <;> rfl)

theorem primrec_negativePart : Primrec negativePart :=
  (Primrec.sumCasesOn primrec_int_split (Primrec.const 0).to₂
    (Primrec.succ.comp Primrec.snd).to₂).of_eq (fun z => by cases z <;> rfl)

theorem int_eq_parts (z : ℤ) : z = (positivePart z : ℤ) - negativePart z := by
  cases z <;> simp [positivePart, negativePart, Int.negSucc_eq]

theorem primrec_int_natAbs : Primrec Int.natAbs :=
  (Primrec.nat_add.comp primrec_positivePart primrec_negativePart).of_eq
    (fun z => by cases z <;> simp [positivePart, negativePart])

/-- Integer difference of two natural numbers without truncation. -/
def signedDifference (a b : ℕ) : ℤ :=
  if b ≤ a then .ofNat (a - b) else .negSucc (b - a - 1)

theorem signedDifference_eq (a b : ℕ) : signedDifference a b = (a : ℤ) - b := by
  unfold signedDifference
  split_ifs with h
  · change ((a - b : ℕ) : ℤ) = _
    exact Int.ofNat_sub h
  · rw [Int.negSucc_eq]
    omega

theorem primrec_signedDifference : Primrec₂ signedDifference :=
  (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (primrec_int_ofNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (primrec_int_negSucc.comp (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))).to₂

theorem primrec_int_neg : Primrec (fun z : ℤ => -z) :=
  (primrec_signedDifference.comp primrec_negativePart primrec_positivePart).of_eq
    (fun z => by rw [signedDifference_eq]; have h := int_eq_parts z; omega)

theorem primrec_int_add : Primrec₂ (fun a b : ℤ => a + b) := by
  apply (primrec_signedDifference.comp
    (Primrec.nat_add.comp (primrec_positivePart.comp Primrec.fst)
      (primrec_positivePart.comp Primrec.snd))
    (Primrec.nat_add.comp (primrec_negativePart.comp Primrec.fst)
      (primrec_negativePart.comp Primrec.snd))).to₂.of_eq
  intro a b
  rw [signedDifference_eq]
  conv_rhs => rw [int_eq_parts a, int_eq_parts b]
  push_cast
  ring

theorem primrec_int_mul : Primrec₂ (fun a b : ℤ => a * b) := by
  apply (primrec_signedDifference.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (primrec_positivePart.comp Primrec.fst)
        (primrec_positivePart.comp Primrec.snd))
      (Primrec.nat_mul.comp (primrec_negativePart.comp Primrec.fst)
        (primrec_negativePart.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (primrec_positivePart.comp Primrec.fst)
        (primrec_negativePart.comp Primrec.snd))
      (Primrec.nat_mul.comp (primrec_negativePart.comp Primrec.fst)
        (primrec_positivePart.comp Primrec.snd)))).to₂.of_eq
  intro a b
  rw [signedDifference_eq]
  conv_rhs => rw [int_eq_parts a, int_eq_parts b]
  push_cast
  ring

theorem primrec_int_le : PrimrecRel (fun a b : ℤ => a ≤ b) := by
  apply (Primrec.nat_le.comp
    (Primrec.nat_add.comp (primrec_positivePart.comp Primrec.fst)
      (primrec_negativePart.comp Primrec.snd))
    (Primrec.nat_add.comp (primrec_positivePart.comp Primrec.snd)
      (primrec_negativePart.comp Primrec.fst))).of_eq
  intro p
  have ha := int_eq_parts p.1
  have hb := int_eq_parts p.2
  omega

theorem gcd_eq_findGreatest (a b : ℕ) :
    Nat.findGreatest (fun d => a % d = 0 ∧ b % d = 0) (a + b) = a.gcd b := by
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
    Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)⟩, ?_⟩
  · by_cases ha : a = 0
    · simp [ha]
    · exact (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha)).trans (Nat.le_add_right a b)
  · intro n hn hbound hdiv
    have hd : n ∣ a.gcd b :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hdiv.1) (Nat.dvd_of_mod_eq_zero hdiv.2)
    by_cases hg : a.gcd b = 0
    · obtain ⟨ha, hb⟩ := Nat.gcd_eq_zero_iff.mp hg
      omega
    · exact (not_le_of_gt hn) (Nat.le_of_dvd (Nat.pos_of_ne_zero hg) hd)

theorem primrec_nat_gcd : Primrec₂ Nat.gcd := by
  apply (Primrec.nat_findGreatest
    (p := fun (ab : ℕ × ℕ) d => ab.1 % d = 0 ∧ ab.2 % d = 0) Primrec.nat_add
    ((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.const 0)).and
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const 0)))).to₂.of_eq
  exact gcd_eq_findGreatest

/-- A numerator and positive denominator in lowest terms. -/
def IsCanonical (p : ℤ × ℕ) : Prop := p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2

instance : DecidablePred IsCanonical := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem primrec_isCanonical : PrimrecPred IsCanonical :=
  (Primrec.eq.comp Primrec.snd (Primrec.const 0)).not.and
    (Primrec.eq.comp
      (primrec_nat_gcd.comp (primrec_int_natAbs.comp Primrec.fst) Primrec.snd)
      (Primrec.const 1))

/-- Canonical signed numerator and positive denominator codes. -/
abbrev RationalCode := {p : ℤ × ℕ // IsCanonical p}

instance : Primcodable RationalCode := Primcodable.subtype primrec_isCanonical

/-- The bijection between rationals and reduced numerator-denominator pairs. -/
def ratCodeEquiv : ℚ ≃ RationalCode where
  toFun q := ⟨(q.num, q.den), q.den_nz, q.reduced⟩
  invFun p := ⟨p.val.1, p.val.2, p.property.1, p.property.2⟩
  left_inv q := by cases q; rfl
  right_inv p := by rcases p with ⟨⟨n, d⟩, h⟩; rfl

/-- A primitive-recursive presentation of the rationals by their canonical fields. -/
instance instPrimcodableRational : Primcodable ℚ := Primcodable.ofEquiv RationalCode ratCodeEquiv

theorem primrec_rat_numDen : Primrec (fun q : ℚ => (q.num, q.den)) :=
  (Primrec.subtype_val (hp := primrec_isCanonical)).comp (Primrec.of_equiv
    (e := ratCodeEquiv))

theorem primrec_rat_num : Primrec Rat.num := Primrec.fst.comp primrec_rat_numDen

theorem primrec_rat_den : Primrec Rat.den := Primrec.snd.comp primrec_rat_numDen

theorem primrec_rat_of_numDen {α : Type*} [Primcodable α] {f : α → ℚ}
    (hf : Primrec (fun a => ((f a).num, (f a).den))) : Primrec f := by
  have hcode : Primrec (fun a => ratCodeEquiv (f a)) :=
    Primrec.subtype_mk (hp := primrec_isCanonical) hf
  exact (Primrec.of_equiv_iff ratCodeEquiv).mp hcode

theorem computable_rat_of_numDen {α : Type*} [Primcodable α] {f : α → ℚ}
    (hf : Computable (fun a => ((f a).num, (f a).den))) : Computable f := by
  have hcode : Computable (fun a => ratCodeEquiv (f a)) :=
    Computable.subtype_mk primrec_isCanonical hf
  have hc : Computable (fun a => ratCodeEquiv.symm (ratCodeEquiv (f a))) :=
    (Primrec.of_equiv_symm (e := ratCodeEquiv)).to_comp.comp hcode
  exact hc.of_eq (fun a => ratCodeEquiv.symm_apply_apply (f a))

/-- Divide an integer magnitude by a natural number and retain its sign. -/
def signedQuotient (n : ℤ) (d : ℕ) : ℤ :=
  signedDifference (positivePart n / d) (negativePart n / d)

theorem primrec_signedQuotient : Primrec₂ signedQuotient :=
  (primrec_signedDifference.comp
    (Primrec.nat_div.comp (primrec_positivePart.comp Primrec.fst) Primrec.snd)
    (Primrec.nat_div.comp (primrec_negativePart.comp Primrec.fst) Primrec.snd)).to₂

theorem signedQuotient_eq_of_dvd (n : ℤ) (d : ℕ) (hd : (d : ℤ) ∣ n) :
    signedQuotient n d = n / d := by
  cases n with
  | ofNat n =>
    simp [signedQuotient, positivePart, negativePart, signedDifference_eq,
      Int.natCast_ediv]
  | negSucc n =>
    have hd' : (d : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
      simpa [Int.negSucc_eq] using (dvd_neg.mp hd)
    simp only [signedQuotient, positivePart, negativePart, signedDifference_eq,
      Nat.zero_div, Nat.cast_zero, zero_sub]
    rw [Int.negSucc_eq, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp,
      Int.neg_ediv_of_dvd hd', Int.natCast_ediv]

/-- Reduce a numerator-denominator pair, sending a zero denominator to the code for zero. -/
def normalizeCode (p : ℤ × ℕ) : ℤ × ℕ :=
  if p.2 = 0 then (0, 1)
  else (signedQuotient p.1 (p.2.gcd p.1.natAbs), p.2 / p.2.gcd p.1.natAbs)

theorem primrec_normalizeCode : Primrec normalizeCode :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const (0, 1))
    ((primrec_signedQuotient.comp Primrec.fst
      (primrec_nat_gcd.comp Primrec.snd (primrec_int_natAbs.comp Primrec.fst))).pair
    (Primrec.nat_div.comp Primrec.snd
      (primrec_nat_gcd.comp Primrec.snd (primrec_int_natAbs.comp Primrec.fst))))

theorem normalizeCode_eq (p : ℤ × ℕ) :
    normalizeCode p = ((mkRat p.1 p.2).num, (mkRat p.1 p.2).den) := by
  by_cases hd : p.2 = 0
  · simp [normalizeCode, hd]
  · simp only [normalizeCode, hd, ite_false, Rat.num_mkRat, Rat.den_mkRat]
    congr 1
    exact signedQuotient_eq_of_dvd _ _
      (Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right p.2 p.1.natAbs))

theorem primrec_mkRat : Primrec₂ mkRat := by
  apply primrec_rat_of_numDen
  exact primrec_normalizeCode.of_eq normalizeCode_eq

theorem primrec_rat_intCast : Primrec (fun n : ℤ => (n : ℚ)) :=
  (primrec_mkRat.comp Primrec.id (Primrec.const 1)).of_eq (fun n => by
    simp [Rat.mkRat_eq_divInt])

theorem primrec_rat_natCast : Primrec (fun n : ℕ => (n : ℚ)) :=
  primrec_rat_intCast.comp primrec_int_ofNat

theorem primrec_rat_neg : Primrec (fun q : ℚ => -q) := by
  apply primrec_rat_of_numDen
  exact ((primrec_int_neg.comp primrec_rat_num).pair primrec_rat_den).of_eq
    (fun q => by simp)

theorem primrec_rat_add : Primrec₂ (fun a b : ℚ => a + b) := by
  apply (primrec_mkRat.comp
    (primrec_int_add.comp
      (primrec_int_mul.comp (primrec_rat_num.comp Primrec.fst)
        (primrec_int_ofNat.comp (primrec_rat_den.comp Primrec.snd)))
      (primrec_int_mul.comp (primrec_rat_num.comp Primrec.snd)
        (primrec_int_ofNat.comp (primrec_rat_den.comp Primrec.fst))))
    (Primrec.nat_mul.comp (primrec_rat_den.comp Primrec.fst)
      (primrec_rat_den.comp Primrec.snd))).to₂.of_eq
  intro a b
  rw [Rat.add_def, Rat.normalize_eq_mkRat]
  rfl

theorem primrec_rat_mul : Primrec₂ (fun a b : ℚ => a * b) := by
  apply (primrec_mkRat.comp
    (primrec_int_mul.comp (primrec_rat_num.comp Primrec.fst)
      (primrec_rat_num.comp Primrec.snd))
    (Primrec.nat_mul.comp (primrec_rat_den.comp Primrec.fst)
      (primrec_rat_den.comp Primrec.snd))).to₂.of_eq
  intro a b
  rw [Rat.mul_def, Rat.normalize_eq_mkRat]

theorem primrec_rat_divInt : Primrec₂ Rat.divInt := by
  apply (Primrec.sumCasesOn (primrec_int_split.comp Primrec.snd)
    (primrec_mkRat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    (primrec_mkRat.comp (primrec_int_neg.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.succ.comp Primrec.snd)).to₂).to₂.of_eq
  intro n d
  cases d <;> rfl

theorem primrec_rat_inv : Primrec (fun q : ℚ => q⁻¹) :=
  (primrec_rat_divInt.comp (primrec_int_ofNat.comp primrec_rat_den) primrec_rat_num).of_eq
    (fun q => (Rat.inv_def q).symm)

theorem primrec_rat_div : Primrec₂ (fun a b : ℚ => a / b) :=
  (primrec_rat_mul.comp Primrec.fst (primrec_rat_inv.comp Primrec.snd)).to₂.of_eq
    (fun a b => (div_eq_mul_inv a b).symm)

theorem primrec_rat_sub : Primrec₂ (fun a b : ℚ => a - b) :=
  (primrec_rat_add.comp Primrec.fst (primrec_rat_neg.comp Primrec.snd)).to₂.of_eq
    (fun a b => (sub_eq_add_neg a b).symm)

theorem primrec_rat_le : PrimrecRel (fun a b : ℚ => a ≤ b) := by
  apply (primrec_int_le.comp
    (primrec_int_mul.comp (primrec_rat_num.comp Primrec.fst)
      (primrec_int_ofNat.comp (primrec_rat_den.comp Primrec.snd)))
    (primrec_int_mul.comp (primrec_rat_num.comp Primrec.snd)
      (primrec_int_ofNat.comp (primrec_rat_den.comp Primrec.fst)))).of_eq
  intro p
  exact (Rat.le_iff p.1 p.2).symm

theorem primrec_rat_min : Primrec₂ (min : ℚ → ℚ → ℚ) :=
  (Primrec.ite primrec_rat_le Primrec.fst Primrec.snd).to₂.of_eq
    (fun a b => (min_def a b).symm)

theorem primrec_rat_max : Primrec₂ (max : ℚ → ℚ → ℚ) :=
  (Primrec.ite primrec_rat_le Primrec.snd Primrec.fst).to₂.of_eq
    (fun a b => (max_def a b).symm)

end Klr.RationalComputability

namespace Klr

/-- Rational computability expressed in the canonical fields used by real-capital witnesses. -/
def ComputableRat {α : Type*} [Primcodable α] (f : α → ℚ) : Prop :=
  Computable (fun a => ((f a).num, (f a).den))

theorem computableRat_iff {α : Type*} [Primcodable α] {f : α → ℚ} :
    ComputableRat f ↔ Computable f :=
  ⟨RationalComputability.computable_rat_of_numDen,
    fun h => RationalComputability.primrec_rat_numDen.to_comp.comp h⟩

namespace ComputableRat

variable {α β : Type*} [Primcodable α] [Primcodable β] {f g : α → ℚ}

theorem const (q : ℚ) : ComputableRat (fun _ : α => q) := Computable.const _

theorem comp (hf : ComputableRat f) {g : β → α} (hg : Computable g) :
    ComputableRat (fun b => f (g b)) := Computable.comp hf hg

theorem add (hf : ComputableRat f) (hg : ComputableRat g) :
    ComputableRat (fun a => f a + g a) :=
  computableRat_iff.mpr (RationalComputability.primrec_rat_add.to_comp.comp
    (computableRat_iff.mp hf) (computableRat_iff.mp hg))

theorem mul (hf : ComputableRat f) (hg : ComputableRat g) :
    ComputableRat (fun a => f a * g a) :=
  computableRat_iff.mpr (RationalComputability.primrec_rat_mul.to_comp.comp
    (computableRat_iff.mp hf) (computableRat_iff.mp hg))

theorem neg (hf : ComputableRat f) : ComputableRat (fun a => -f a) :=
  computableRat_iff.mpr (RationalComputability.primrec_rat_neg.to_comp.comp
    (computableRat_iff.mp hf))

theorem div (hf : ComputableRat f) (hg : ComputableRat g) :
    ComputableRat (fun a => f a / g a) :=
  computableRat_iff.mpr (RationalComputability.primrec_rat_div.to_comp.comp
    (computableRat_iff.mp hf) (computableRat_iff.mp hg))

theorem min (hf : ComputableRat f) (hg : ComputableRat g) :
    ComputableRat (fun a => min (f a) (g a)) :=
  computableRat_iff.mpr (RationalComputability.primrec_rat_min.to_comp.comp
    (computableRat_iff.mp hf) (computableRat_iff.mp hg))

theorem max (hf : ComputableRat f) (hg : ComputableRat g) :
    ComputableRat (fun a => max (f a) (g a)) :=
  computableRat_iff.mpr (RationalComputability.primrec_rat_max.to_comp.comp
    (computableRat_iff.mp hf) (computableRat_iff.mp hg))

end ComputableRat

/-- Computable rational capital is a special case of the existing computable-real interface. -/
theorem computableRealCapital_of_rat {d : List Bool → ℚ} (hd : Computable d) :
    ComputableRealCapital (fun v => (d v : ℝ)) := by
  refine ⟨fun v _ => d v, ?_, ?_⟩
  · exact RationalComputability.primrec_rat_numDen.to_comp.comp (hd.comp Computable.fst)
  · intro v n
    simp

theorem computableRealCapital_of_computableRat {d : List Bool → ℚ}
    (hd : ComputableRat d) : ComputableRealCapital (fun v => (d v : ℝ)) :=
  computableRealCapital_of_rat (computableRat_iff.mp hd)

end Klr
