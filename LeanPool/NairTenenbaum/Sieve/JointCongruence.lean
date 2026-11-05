/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.BadPrimeMass
public import Mathlib.Data.ZMod.QuotientRing

/-! # Simultaneous polynomial congruences

The Chinese remainder theorem gives the exact density for different polynomial
conditions at pairwise coprime moduli. The bad-prime modulus may be a least common
multiple; its coordinates need not be mutually coprime.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Interval discrepancy for any collection of residue classes. -/
theorem residueSet_count_error {q : ℕ} (hq : 0 < q) [NeZero q]
    (S : Finset (ZMod q)) (a b : ℤ) (hab : a ≤ b) :
    |(((Finset.Ioc a b).filter fun n : ℤ => (n : ZMod q) ∈ S).card : ℝ) -
      ((b : ℝ) - a) * S.card / q| ≤ S.card := by
  classical
  let c : ZMod q → ℝ := fun r =>
    (((Finset.Ioc a b).filter fun n => Int.ModEq (q : ℤ) n r.val).card : ℝ)
  have hc : (((Finset.Ioc a b).filter fun n : ℤ => (n : ZMod q) ∈ S).card : ℝ) = ∑ r ∈ S, c r := by
    have H := Finset.sum_card_fiberwise_eq_card_filter (Finset.Ioc a b) S
      (fun n : ℤ => (n : ZMod q))
    rw [← H, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    apply Finset.filter_congr
    intro n _
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (ZMod.intCast_eq_intCast_iff n (r.val : ℤ) q)
  have H : |∑ r ∈ S, (c r - ((b : ℝ) - a) / q)| ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ r ∈ S, |c r - ((b : ℝ) - a) / q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum fun r _ => residue_count_error a b r.val hab hq
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at H
  rw [hc]
  convert H using 2
  ring

/-- The joint residue set, obtained from the product of the individual root sets. -/
noncomputable def jointResidueSet {ι : Type*} [Fintype ι] (Q : ι → ℤ[X])
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hcop : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    Finset (ZMod (∏ i, q i)) := by
  classical
  exact (Fintype.piFinset fun i => residueRootSet (Q i) (q i)).image
    (ZMod.prodEquivPi q hcop).symm

theorem jointResidueSet_card {ι : Type*} [Fintype ι] (Q : ι → ℤ[X])
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hcop : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    (jointResidueSet Q q hcop).card = ∏ i, rootCount (Q i) (q i) := by
  classical
  rw [jointResidueSet, Finset.card_image_of_injective _ (ZMod.prodEquivPi q hcop).symm.injective,
    Fintype.card_piFinset]
  simp only [residueRootSet_card]

theorem cast_mem_jointResidueSet {ι : Type*} [Fintype ι] (Q : ι → ℤ[X])
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hcop : Pairwise fun i j => Nat.Coprime (q i) (q j))
    (n : ℤ) : (n : ZMod (∏ i, q i)) ∈ jointResidueSet Q q hcop ↔ ∀ i, (q i : ℤ) ∣ (Q i).eval n := by
  classical
  have he : (ZMod.prodEquivPi q hcop) (n : ZMod (∏ i, q i)) = fun i => (n : ZMod (q i)) := by
    rw [map_intCast]
    rfl
  simp only [jointResidueSet, Finset.mem_image, RingEquiv.symm_apply_eq, exists_eq_right,
    he, Fintype.mem_piFinset, cast_mem_residueRootSet]

/-- The number of integers in an interval satisfying all polynomial congruences. -/
noncomputable def jointCongruenceCount {ι : Type*} [Fintype ι]
    (Q : ι → ℤ[X]) (q : ι → ℕ) (a b : ℤ) : ℕ :=
  ((Finset.Ioc a b).filter fun n => ∀ i, (q i : ℤ) ∣ (Q i).eval n).card

/-- Exact CRT main term with one root-count error per joint residue class. -/
theorem jointCongruenceCount_error {ι : Type*} [Fintype ι]
    (Q : ι → ℤ[X]) (q : ι → ℕ) (hq : ∀ i, 0 < q i)
    (hcop : Pairwise fun i j => Nat.Coprime (q i) (q j)) (a b : ℤ) (hab : a ≤ b) :
    |(jointCongruenceCount Q q a b : ℝ) -
      ((b : ℝ) - a) * (∏ i, rootCount (Q i) (q i)) / (∏ i, q i)| ≤
      ∏ i, rootCount (Q i) (q i) := by
  let : ∀ i, NeZero (q i) := fun i => ⟨(hq i).ne'⟩
  have hp : 0 < ∏ i, q i := Finset.prod_pos (fun i _ => hq i)
  let : NeZero (∏ i, q i) := ⟨hp.ne'⟩
  have H := residueSet_count_error hp (jointResidueSet Q q hcop) a b hab
  simpa only [cast_mem_jointResidueSet, jointResidueSet_card, Nat.cast_prod, jointCongruenceCount]
      using H

/-- The residue-class error is absorbed whenever the modulus fits in the interval. -/
theorem jointCongruenceCount_le {ι : Type*} [Fintype ι]
    (Q : ι → ℤ[X]) (q : ι → ℕ) (hq : ∀ i, 0 < q i)
    (hcop : Pairwise fun i j => Nat.Coprime (q i) (q j)) (a b : ℤ) (hab : a ≤ b)
    (hsize : (∏ i, q i : ℝ) ≤ (b : ℝ) - a) :
    (jointCongruenceCount Q q a b : ℝ) ≤
      2 * ((b : ℝ) - a) * ∏ i, ((rootCount (Q i) (q i) : ℝ) / q i) := by
  have hp : (0 : ℝ) < ∏ i, (q i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hq i)
  have hρ : (0 : ℝ) ≤ ∏ i, (rootCount (Q i) (q i) : ℝ) := Finset.prod_nonneg (fun i _ =>
      Nat.cast_nonneg _)
  have H := (abs_le.mp (jointCongruenceCount_error Q q hq hcop a b hab)).2
  have H' : (∏ i, (rootCount (Q i) (q i) : ℝ)) ≤
      ((b : ℝ) - a) * (∏ i, (rootCount (Q i) (q i) : ℝ)) / (∏ i, (q i : ℝ)) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsize hρ]
  simp only [Nat.cast_prod] at H
  rw [Finset.prod_div_distrib]
  calc
    _ ≤ 2 * (((b : ℝ) - a) * (∏ i, (rootCount (Q i) (q i) : ℝ)) / (∏ i, (q i : ℝ))) := by linarith
    _ = _ := by ring

/-- A bad-prime modulus and the remaining coprime polynomial conditions. -/
noncomputable def mixedCongruenceCount {r : ℕ} (Q : ℤ[X]) (R : Fin r → ℤ[X])
    (d : ℕ) (m : Tuple r) (a b : ℤ) : ℕ :=
  jointCongruenceCount (Fin.cons Q R) (Fin.cons d (fun i => (m i : ℕ))) a b

theorem mixedCongruenceCount_le {r : ℕ} (Q : ℤ[X]) (R : Fin r → ℤ[X])
    {d : ℕ} (hd : 0 < d) (m : Tuple r)
    (hpair : Pairwise fun i j => Nat.Coprime (m i) (m j))
    (hcross : ∀ i, Nat.Coprime d (m i)) (a b : ℤ) (hab : a ≤ b)
    (hsize : (d : ℝ) * mass m ≤ (b : ℝ) - a) :
    (mixedCongruenceCount Q R d m a b : ℝ) ≤
      2 * ((b : ℝ) - a) * ((rootCount Q d : ℝ) / d) *
        ∏ i, ((rootCount (R i) (m i) : ℝ) / m i) := by
  have hpos : ∀ i : Fin (r + 1), 0 < (Fin.cons d (fun i => (m i : ℕ)) : Fin (r + 1) → ℕ) i := by
    intro i
    refine Fin.cases hd (fun i => (m i).pos) i
  have hcop : Pairwise fun i j =>
      Nat.Coprime ((Fin.cons d (fun i => (m i : ℕ)) : Fin (r + 1) → ℕ) i) ((Fin.cons d (fun i =>
          (m i : ℕ)) : Fin (r + 1) → ℕ) j) := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact fun h => (h rfl).elim
    · exact fun _ => hcross j
    · exact fun _ => (hcross i).symm
    · exact fun h => hpair (fun e => h (congrArg Fin.succ e))
  have H := jointCongruenceCount_le (Fin.cons Q R) (Fin.cons d (fun i => (m i : ℕ)))
    hpos hcop a b hab (by simpa [Fin.prod_univ_succ, mass, Nat.cast_prod] using hsize)
  simpa only [mixedCongruenceCount, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      using H

/-- Simultaneous factor divisibility implies radical divisibility at the LCM. -/
theorem PolynomialSystem.tupleLCM_dvd_radical_eval {k r : ℕ} (P : PolynomialSystem k r)
    (m : Tuple r) (a : ℤ) (hm : ∀ i, (m i : ℤ) ∣ (P.R i).eval a) :
    (tupleLCM m : ℤ) ∣ P.radical.eval a := by
  apply Int.natCast_dvd.mpr
  apply Finset.lcm_dvd
  intro i _
  exact Int.natCast_dvd.mp ((hm i).trans (Polynomial.eval_dvd (P.factor_dvd_radical i)))

/-- The full bad-prime part is kept as an LCM congruence while each good
coordinate keeps its own irreducible-factor congruence. -/
theorem PolynomialSystem.jointCongruenceCount_le_mixed {k r : ℕ} (P : PolynomialSystem k r)
    (u v : Tuple r) (a b : ℤ) :
    jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b ≤
      mixedCongruenceCount P.radical P.R (tupleLCM u) v a b := by
  classical
  unfold mixedCongruenceCount jointCongruenceCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  obtain ⟨hn, hdiv⟩ := hn
  refine ⟨hn, ?_⟩
  have hu : ∀ i, (u i : ℤ) ∣ (P.R i).eval n := by
    intro i
    exact (dvd_mul_right (u i : ℤ) (v i : ℤ)).trans (by simpa using hdiv i)
  have hv : ∀ i, (v i : ℤ) ∣ (P.R i).eval n := by
    intro i
    exact (dvd_mul_left (v i : ℤ) (u i : ℤ)).trans (by simpa using hdiv i)
  intro i
  exact Fin.cases (P.tupleLCM_dvd_radical_eval u n hu) hv i

end NairTenenbaum
