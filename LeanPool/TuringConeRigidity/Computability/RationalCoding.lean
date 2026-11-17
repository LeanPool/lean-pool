/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/RationalCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.Cuts

/-!
# Rational Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
open Encodable

namespace RationalCoding

/-- Decode the absolute value of an integer numerator code. -/
def magnitude (n : ℕ) : ℕ := n/2+n%2

theorem magnitude_primrec : Primrec magnitude :=
  Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))

theorem encode_int_nonneg (n : ℕ) : encode (Int.ofNat n) = 2*n := by
  change Nat.bit false n = 2*n
  simp [Nat.bit]

theorem encode_int_neg (n : ℕ) : encode (Int.negSucc n) = 2*n+1 := by
  change Nat.bit true n = 2*n+1
  simp [Nat.bit]

theorem magnitude_encode_int (z : ℤ) : magnitude (encode z) = z.natAbs := by
  cases z with
  | ofNat n =>
    change magnitude (encode (Int.ofNat n)) = n
    rw [encode_int_nonneg]
    simp [magnitude]
  | negSucc n => simp [encode_int_neg,magnitude]; omega

theorem encode_rat (q : ℚ) : encode q = Nat.pair (encode q.num) q.den := rfl

/-- A rational code has positive denominator and coprime numerator magnitude and denominator. -/
def valid (n : ℕ) : Prop :=
  0 < (Nat.unpair n).2 ∧ (magnitude (Nat.unpair n).1).Coprime (Nat.unpair n).2

instance (n : ℕ) : Decidable (valid n) := inferInstanceAs (Decidable (_ ∧ _))

theorem valid_iff (n : ℕ) : valid n ↔ ∃ q : ℚ, encode q = n := by
  constructor
  · rintro ⟨hd,hcop⟩
    let z := Equiv.intEquivNat.symm (Nat.unpair n).1
    have hz : encode z = (Nat.unpair n).1 := Equiv.intEquivNat.apply_symm_apply _
    have hm : z.natAbs = magnitude (Nat.unpair n).1 := by rw [←hz,magnitude_encode_int]
    let q : ℚ := ⟨z,(Nat.unpair n).2,Nat.ne_of_gt hd,hm.symm ▸ hcop⟩
    refine ⟨q,?_⟩
    rw [encode_rat]
    change Nat.pair (encode z) (Nat.unpair n).2 = n
    rw [hz,Nat.pair_unpair]
  · rintro ⟨q,rfl⟩
    simp only [valid,encode_rat,Nat.unpair_pair,magnitude_encode_int]
    exact ⟨q.den_pos,q.reduced⟩

theorem coprime_bounded (a b : ℕ) :
    (0 < b ∧ a.Coprime b) ↔
      (0 < b ∧ ∀ k ∈ List.range (b+1), a%k ≠ 0 ∨ b%k ≠ 0 ∨ k=1) := by
  constructor
  · rintro ⟨hb,hc⟩
    refine ⟨hb,fun k _hk => ?_⟩
    by_cases ha : a%k = 0
    · by_cases hb' : b%k = 0
      · exact Or.inr (Or.inr (Nat.dvd_one.mp (by
          rw [←hc]
          exact Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb'))))
      · exact Or.inr (Or.inl hb')
    · exact Or.inl ha
  · rintro ⟨hb,h⟩
    refine ⟨hb,?_⟩
    have hg : a.gcd b ∈ List.range (b+1) := by
      simp only [List.mem_range,Nat.lt_succ_iff]
      exact Nat.gcd_le_right a hb
    have hh := h (a.gcd b) hg
    simpa [Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
      Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)] using hh

theorem coprime_positive_primrec : PrimrecPred (fun p : ℕ × ℕ => 0 < p.2 ∧ p.1.Coprime p.2) := by
  have hr : PrimrecRel (fun k (p : ℕ × ℕ) => p.1%k ≠ 0 ∨ p.2%k ≠ 0 ∨ k=1) :=
    ((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.const 0)).not).or
    (((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.const 0)).not).or (Primrec.eq.comp Primrec.fst (Primrec.const 1)))
  have hh := (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (hr.forall_mem_list.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) Primrec.id)
  exact hh.of_eq (fun p => (coprime_bounded p.1 p.2).symm)

theorem valid_primrec : PrimrecPred valid :=
  coprime_positive_primrec.comp ((magnitude_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))

/-- Keep a valid rational code, replacing an invalid code by the canonical code of zero. -/
def canonicalCode (n : ℕ) : ℕ := if valid n then n else encode (0 : ℚ)

theorem canonicalCode_primrec : Primrec canonicalCode :=
  Primrec.ite valid_primrec Primrec.id (Primrec.const (encode (0 : ℚ)))

theorem decode_invalid (n : ℕ) (hv : ¬valid n) : decode (α := ℚ) n = none := by
  let z := Equiv.intEquivNat.symm (Nat.unpair n).1
  have hz : decode (α := ℤ) (Nat.unpair n).1 = some z := rfl
  have henc : encode z = (Nat.unpair n).1 := Equiv.intEquivNat.apply_symm_apply _
  have hbad : ¬(0 < (Nat.unpair n).2 ∧ z.natAbs.Coprime (Nat.unpair n).2) := by
    simpa only [valid, ←henc, magnitude_encode_int] using hv
  have hsub : decode (α := { b : ℕ // 0 < b ∧ z.natAbs.Coprime b }) (Nat.unpair n).2 = none := by
    change Encodable.decodeSubtype (P := fun b => 0 < b ∧ z.natAbs.Coprime b) _ = none
    simp [Encodable.decodeSubtype,hbad]
  have hsigma : decode (α := Σ z : ℤ, { b : ℕ // 0 < b ∧ z.natAbs.Coprime b }) n = none := by
    change Encodable.decodeSigma (γ := fun z : ℤ => { b : ℕ // 0 < b ∧ z.natAbs.Coprime b }) n =
      none
    simp only [Encodable.decodeSigma]
    rw [hz]
    simp only [Option.bind_some]
    rw [hsub]
    rfl
  simp only [Encodable.decode_ofEquiv,hsigma,Option.map_none]

theorem canonicalCode_eq (n : ℕ) : canonicalCode n = encode (rationalEnumeration n) := by
  by_cases hv : valid n
  · obtain ⟨q,rfl⟩ := (valid_iff n).mp hv
    simp only [canonicalCode,ite_eq_left hv,rationalEnumeration,encodek,Option.getD_some]
  · have hn := decode_invalid n hv
    simp only [canonicalCode,ite_eq_right hv,rationalEnumeration,hn,Option.getD_none]

/-- The integer numerator code of the canonicalized rational code. -/
def numeratorCode (n : ℕ) : ℕ := (Nat.unpair (canonicalCode n)).1
/-- The absolute numerator of the canonicalized rational code. -/
def numeratorMagnitude (n : ℕ) : ℕ := magnitude (numeratorCode n)
/-- The denominator of the canonicalized rational code. -/
def denominator (n : ℕ) : ℕ := (Nat.unpair (canonicalCode n)).2
/-- The sign bit of the numerator of the canonicalized rational code. -/
def negative (n : ℕ) : Bool := (numeratorCode n).bodd

theorem numeratorCode_primrec : Primrec numeratorCode :=
  (Primrec.fst.comp Primrec.unpair).comp canonicalCode_primrec
theorem numeratorMagnitude_primrec : Primrec numeratorMagnitude :=
  magnitude_primrec.comp numeratorCode_primrec
theorem denominator_primrec : Primrec denominator :=
  (Primrec.snd.comp Primrec.unpair).comp canonicalCode_primrec
theorem negative_primrec : Primrec negative := Primrec.nat_bodd.comp numeratorCode_primrec

theorem numeratorCode_eq (n : ℕ) : numeratorCode n = encode (rationalEnumeration n).num := by
  rw [numeratorCode,canonicalCode_eq,encode_rat,Nat.unpair_pair]
theorem numeratorMagnitude_eq (n : ℕ) : numeratorMagnitude n = (rationalEnumeration n).num.natAbs
  := by
  rw [numeratorMagnitude,numeratorCode_eq,magnitude_encode_int]
theorem denominator_eq (n : ℕ) : denominator n = (rationalEnumeration n).den := by
  rw [denominator,canonicalCode_eq,encode_rat,Nat.unpair_pair]
theorem denominator_pos (n : ℕ) : 0 < denominator n := by
  rw [denominator_eq]
  exact (rationalEnumeration n).den_pos

theorem query_value (n : ℕ) : (rationalEnumeration n : ℝ) =
    if negative n then -(numeratorMagnitude n : ℝ)/(denominator n : ℝ)
    else (numeratorMagnitude n : ℝ)/(denominator n : ℝ) := by
  rw [negative,numeratorCode_eq,numeratorMagnitude_eq,denominator_eq,Rat.cast_def]
  cases hz : (rationalEnumeration n).num with
  | ofNat k =>
    rw [encode_int_nonneg]
    simp [Nat.bodd_mul]
  | negSucc k => simp [encode_int_neg,Nat.bodd_mul]

end RationalCoding
end TuringRigidity

end OAI
