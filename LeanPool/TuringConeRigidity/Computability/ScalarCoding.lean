/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ScalarCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.RationalCut

/-!
# Scalar Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
namespace RationalCoding

/-- The left natural-number cross-product for comparing a rational with a rational scalar
multiple. -/
def scalarLeft (r : ℕ) (z : ℕ × ℕ) : ℕ :=
  (positiveNumerator r*positiveNumerator z.2 + negativeNumerator r*negativeNumerator
    z.2)*denominator z.1 +
    negativeNumerator z.1*denominator r*denominator z.2

/-- The right natural-number cross-product for comparing a rational with a rational scalar
multiple. -/
def scalarRight (r : ℕ) (z : ℕ × ℕ) : ℕ :=
  (positiveNumerator r*negativeNumerator z.2 + negativeNumerator r*positiveNumerator
    z.2)*denominator z.1 +
    positiveNumerator z.1*denominator r*denominator z.2

private theorem scalarPolynomial_primrec (a b D : ℕ) {p q c : ℕ → ℕ}
    (hp : Primrec p) (hq : Primrec q) (hc : Primrec c) :
    Primrec (fun z : ℕ × ℕ => (a*p z.2+b*q z.2)*denominator z.1+c z.1*D*denominator z.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const a) (hp.comp Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.const b) (hq.comp Primrec.snd)))
      (denominator_primrec.comp Primrec.fst))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (hc.comp Primrec.fst) (Primrec.const D))
      (denominator_primrec.comp Primrec.snd))

theorem scalarLeft_primrec (r : ℕ) : Primrec (scalarLeft r) :=
  scalarPolynomial_primrec _ _ _ positiveNumerator_primrec negativeNumerator_primrec
    negativeNumerator_primrec

theorem scalarRight_primrec (r : ℕ) : Primrec (scalarRight r) :=
  scalarPolynomial_primrec _ _ _ negativeNumerator_primrec positiveNumerator_primrec
    positiveNumerator_primrec

theorem scalar_eq_iff (r i j : ℕ) : scalarLeft r (i,j)=scalarRight r (i,j) ↔
    (rationalEnumeration r : ℝ)*(rationalEnumeration j : ℝ)=(rationalEnumeration i : ℝ) := by
  have hr : (denominator r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos r))
  have hi : (denominator i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos i))
  have hj : (denominator j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos j))
  rw [signed_query_value,signed_query_value,signed_query_value]
  have he : ((positiveNumerator r : ℝ)-negativeNumerator r)/denominator r *
      (((positiveNumerator j : ℝ)-negativeNumerator j)/denominator j) =
      ((positiveNumerator i : ℝ)-negativeNumerator i)/denominator i ↔
      (scalarLeft r (i,j) : ℝ)=(scalarRight r (i,j) : ℝ) := by
    simp only [scalarLeft,scalarRight,Nat.cast_add,Nat.cast_mul]
    field_simp
    constructor <;> intro h <;> nlinarith
  rw [he]
  exact Nat.cast_inj.symm

/-- The rational-enumeration index obtained by dividing the indexed rational by `r`. -/
def divideIndex (r : ℚ) (i : ℕ) : ℕ := Encodable.encode (rationalEnumeration i/r)

theorem divideIndex_value (r : ℚ) (i : ℕ) :
    rationalEnumeration (divideIndex r i) = rationalEnumeration i/r := by
  simp only [divideIndex,rationalEnumeration,Encodable.encodek,Option.getD_some]

theorem divideIndex_recursive {O : Set (ℕ →. ℕ)} (r : ℚ) (hr : r ≠ 0) :
    Nat.RecursiveIn O (fun i => Part.some (divideIndex r i)) := by
  let ridx := Encodable.encode r
  let E : ℕ → ℕ → Option ℕ := fun i j =>
    if valid j ∧ scalarLeft ridx (i,j)=scalarRight ridx (i,j) then some j else none
  have hE : Primrec (fun z : ℕ => Encodable.encode (E (Nat.unpair z).1 (Nat.unpair z).2)) :=
    Primrec.encode.comp ((Primrec.ite ((valid_primrec.comp Primrec.snd).and
      (Primrec.eq.comp (scalarLeft_primrec ridx) (scalarRight_primrec ridx)))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).comp Primrec.unpair)
  have hridx : rationalEnumeration ridx = r := by simp [ridx,rationalEnumeration]
  apply UniformOracle.total_search (UniformOracle.total_primrec hE) (divideIndex r)
  · intro i j a ha
    dsimp only [E] at ha
    split at ha
    · rename_i h
      have haj : a=j := by symm; simpa using ha
      subst a
      have he := (scalar_eq_iff ridx i j).mp h.2
      rw [hridx] at he
      have heq : r*rationalEnumeration j=rationalEnumeration i := by exact_mod_cast he
      have hval : rationalEnumeration j=rationalEnumeration i/r :=
        (eq_div_iff hr).mpr (by simpa [mul_comm] using heq)
      have hj : canonicalCode j=j := ite_eq_left h.1
      rw [canonicalCode_eq,hval] at hj
      exact hj.symm
    · simp at ha
  · intro i
    let j := divideIndex r i
    have hv : valid j := (valid_iff j).mpr ⟨rationalEnumeration i/r,rfl⟩
    have he : scalarLeft ridx (i,j)=scalarRight ridx (i,j) := by
      apply (scalar_eq_iff ridx i j).mpr
      rw [hridx,show rationalEnumeration j=rationalEnumeration i/r from divideIndex_value r i]
      push_cast
      field_simp
    exact ⟨j,j,by simp [E,hv,he]⟩

end RationalCoding
end TuringRigidity

end OAI
