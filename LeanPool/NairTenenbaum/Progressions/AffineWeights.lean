/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Progressions.AffineBadDiscriminant
public import LeanPool.NairTenenbaum.Smooth.SmoothWeightSum

/-! # Exact progression identity for the original weights -/

@[expose] public section

namespace NairTenenbaum

/-- Coprimality of the weighted mass is equivalent to coprimality in every
irreducible coordinate. Positive exponents are essential in the reverse direction. -/
theorem coprime_weightedMass_iff {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (q : ℕ) (n : Tuple r) :
    Nat.Coprime q (weightedMass γ n) ↔ ∀ i, Nat.Coprime q (n i) := by
  simp only [weightedMass, Nat.coprime_prod_right_iff, Finset.mem_univ, true_implies]
  exact forall_congr' (fun i => Nat.coprime_pow_right_iff (hγ i) q (n i))

/-- On tuples coprime to the progression modulus, the dagger restrictions for
the original and transformed discriminants coincide. -/
theorem PolynomialSystem.dagger_affine_iff {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs)
    (n : Tuple r) (hqn : ∀ i, Nat.Coprime q (n i)) :
    Dagger (P.affine q a hq hqa).discriminant n ↔ Dagger P.discriminant n := by
  rw [P.affine_discriminant]
  simp only [Dagger, Nat.coprime_mul_iff_right]
  exact and_congr_right (fun _ => forall_congr' (fun i =>
    and_iff_right ((hqn i).symm.pow_right _)))

/-- On every mass coprime to `q`, both the fiber restriction and every root
factor in the weight are unchanged by affine substitution. -/
theorem PolynomialSystem.affine_weight_of_coprime {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs)
    (F : ArithmeticMap k) (N : ℕ+) (hN : Nat.Coprime q N) :
    (P.affine q a hq hqa).weight F N = P.weight F N := by
  classical
  have hcoord (n : Tuple r) (hn : weightedMass P.exponent n = N) : ∀ i, Nat.Coprime q (n i) :=
    (coprime_weightedMass_iff P.exponent P.exponent_pos q n).mp (hn.symm ▸ hN)
  have hfiber : weightFiber (P.affine q a hq hqa).exponent (P.affine q a hq hqa).discriminant N =
      weightFiber P.exponent P.discriminant N := by
    ext n
    rw [mem_weightFiber _ (P.affine q a hq hqa).exponent_pos, mem_weightFiber _ P.exponent_pos]
    change (weightedMass P.exponent n = N ∧ Dagger (P.affine q a hq hqa).discriminant n) ↔ _
    exact and_congr_right (fun hn => P.dagger_affine_iff q a hq hqa n (hcoord n hn))
  unfold PolynomialSystem.weight NairTenenbaum.weight
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro n hn
  have hmass := ((mem_weightFiber P.exponent P.exponent_pos P.discriminant N n).mp hn).1
  change pullback P.exponent F n * _ = _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  unfold PolynomialSystem.rootVector
  rw [P.affine_factor_rootCount, ite_eq_left (hcoord n hmass i)]

/-- If the mass shares a prime with `q`, one root factor vanishes in every
summand, regardless of the dagger restriction. -/
theorem PolynomialSystem.affine_weight_eq_zero {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs)
    (F : ArithmeticMap k) (N : ℕ+) (hN : ¬Nat.Coprime q N) :
    (P.affine q a hq hqa).weight F N = 0 := by
  classical
  unfold PolynomialSystem.weight NairTenenbaum.weight
  apply Finset.sum_eq_zero
  intro n hn
  have hmass := ((mem_weightFiber _ (P.affine q a hq hqa).exponent_pos _ N n).mp hn).1
  change weightedMass P.exponent n = N at hmass
  have hnot : ¬∀ i, Nat.Coprime q (n i) := fun h => hN
    (hmass ▸ (coprime_weightedMass_iff P.exponent P.exponent_pos q n).mpr h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have hzero : ∏ j, (P.affine q a hq hqa).rootVector j (n j) / (n j : ℝ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold PolynomialSystem.rootVector
    rw [P.affine_factor_rootCount, ite_eq_right hi, Nat.cast_zero, zero_div]
  rw [hzero, mul_zero]

/-- The exact identity used after equation (38): the transformed weight equals
the original weight with the extra coprimality condition `(N,q)=1`. -/
theorem PolynomialSystem.affine_weight {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs)
    (F : ArithmeticMap k) (N : ℕ+) :
    (P.affine q a hq hqa).weight F N = if Nat.Coprime q N then P.weight F N else 0 := by
  by_cases hN : Nat.Coprime q N
  · rw [ite_eq_left hN, P.affine_weight_of_coprime q a hq hqa F N hN]
  · rw [ite_eq_right hN, P.affine_weight_eq_zero q a hq hqa F N hN]

theorem PolynomialSystem.sum_affine_weight {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs)
    (F : ArithmeticMap k) (x : ℝ) :
    (∑ N ∈ positiveUpTo x, (P.affine q a hq hqa).weight F N) =
      ∑ N ∈ (positiveUpTo x).filter (fun N : ℕ+ => Nat.Coprime q N), P.weight F N := by
  classical
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun N _ => P.affine_weight q a hq hqa F N)

end NairTenenbaum
