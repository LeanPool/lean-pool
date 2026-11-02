/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ProductArithmetic
public import LeanPool.NairTenenbaum.Polynomials.SubstitutionDensity

/-! # The factored weight bound for pairwise coprime polynomials

Tuples are first grouped by their original substituted arguments. The
combined density of each fiber is bounded by the corresponding product of
original-polynomial root densities. Only then is the mass cutoff enlarged
to a box and the independent one-variable sums multiplied.
-/

@[expose] public section

namespace NairTenenbaum

/-- The one-variable root-weighted sum appearing in Corollary 3. -/
noncomputable def rootWeightedSum (Q : Polynomial ℤ) (F : ArithmeticMap 1) (x : ℝ) : ℝ :=
  ∑ n ∈ positiveUpTo x, F (fun _ => n) * ((rootCount Q n : ℝ) / (n : ℝ))

/-- Factored upper bound for the full dagger weight sum at an integral cutoff. -/
theorem PolynomialSystem.sum_weight_product_le {k r : ℕ} (P : PolynomialSystem k r)
    (hcop : ∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map
        (Int.castRingHom ℚ)))
    (F : Fin k → ArithmeticMap 1) (hF : ∀ j n, 0 ≤ F j n) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N, P.weight (productArithmeticMap F) n) ≤
      ∏ j, ∑ m ∈ Finset.Icc 1 N, F j (fun _ => m) * ((rootCount (P.Q j) m : ℝ) / (m : ℝ)) := by
  classical
  unfold PolynomialSystem.weight
  rw [sum_weight_eq_sum_weightUpTo _ P.exponent_pos]
  let T := weightUpTo P.exponent P.discriminant N
  have hmap : ∀ n ∈ T, substitute P.exponent n ∈ tupleBox k N := by
    intro n hn
    apply mem_tupleBox.mpr
    intro j
    change (substitute P.exponent n j : ℕ) ≤ (N : ℕ)
    have H := coordinate_le_weightedMass (identityExponents k) (by intro i; simp)
      (substitute P.exponent n) j
    simp only [weightedMass_identity, mass_substitute] at H
    exact H.trans ((mem_weightUpTo P.exponent P.exponent_pos _ _ n).mp hn).1
  change (∑ n ∈ T, pullback P.exponent (productArithmeticMap F) n *
    ∏ i, (P.rootVector i (n i)) / (n i : ℝ)) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap, ← Finset.sum_prod_piFinset]
  apply Finset.sum_le_sum
  intro m hm
  have hnonneg : 0 ≤ productArithmeticMap F m := Finset.prod_nonneg (fun j _ => hF j _)
  have Hdensity : (∑ n ∈ T.filter (fun n => substitute P.exponent n = m),
      ∏ i, P.rootVector i (n i) / (n i : ℝ)) ≤
      ∏ j, (rootCount (P.Q j) (m j) : ℝ) / (m j : ℝ) := by
    by_cases hS : (T.filter (fun n => substitute P.exponent n = m)).Nonempty
    · obtain ⟨n, hn⟩ := hS
      have hn' := Finset.mem_filter.mp hn
      have hdagger := ((mem_weightUpTo P.exponent P.exponent_pos _ _ n).mp hn'.1).2
      have hpair := P.substitute_pairwise_coprime hcop n hdagger.1
      rw [hn'.2] at hpair
      exact P.sum_substitutionFiber_rootDensity_le _ (fun n hn =>
        ((mem_weightUpTo P.exponent P.exponent_pos _ _ n).mp (Finset.mem_filter.mp hn).1).2)
        m hpair (fun n hn => (Finset.mem_filter.mp hn).2)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
      exact Finset.prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (by positivity))
  calc
    _ = productArithmeticMap F m * ∑ n ∈ T.filter (fun n => substitute P.exponent n = m),
        ∏ i, P.rootVector i (n i) / (n i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [pullback, (Finset.mem_filter.mp hn).2]
    _ ≤ productArithmeticMap F m * ∏ j, (rootCount (P.Q j) (m j) : ℝ) / (m j : ℝ) :=
      mul_le_mul_of_nonneg_left Hdensity hnonneg
    _ = _ := by rw [productArithmeticMap, ← Finset.prod_mul_distrib]

/-- The same bound at every real cutoff, including the empty range below one. -/
theorem PolynomialSystem.sum_weight_product_real_le {k r : ℕ} (P : PolynomialSystem k r)
    (hcop : ∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map
        (Int.castRingHom ℚ)))
    (F : Fin k → ArithmeticMap 1) (hF : ∀ j n, 0 ≤ F j n) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, P.weight (productArithmeticMap F) n) ≤
      ∏ j, rootWeightedSum (P.Q j) (F j) x := by
  by_cases hx : 1 ≤ x
  · simpa only [rootWeightedSum, positiveUpTo_eq_Icc hx] using
      P.sum_weight_product_le hcop F hF (Nat.toPNat' ⌊x⌋₊)
  · rw [positiveUpTo_eq_empty (lt_of_not_ge hx), Finset.sum_empty]
    exact Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun n _ =>
      mul_nonneg (hF j _) (div_nonneg (Nat.cast_nonneg _) (by positivity))))

/-- Right side of Corollary 3, without the implicit constant. -/
noncomputable def factoredMainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : Fin k → ArithmeticMap 1) (x y : ℝ) : ℝ :=
  y * sieveProduct P.total x * ∏ j, rootWeightedSum (P.Q j) (F j) x

theorem PolynomialSystem.product_mainTerm_le {k r : ℕ} (P : PolynomialSystem k r)
    (hcop : ∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map
        (Int.castRingHom ℚ)))
    (F : Fin k → ArithmeticMap 1) (hF : ∀ j n, 0 ≤ F j n) (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    mainTerm P (productArithmeticMap F) x y ≤ factoredMainTerm P F x y :=
  mul_le_mul_of_nonneg_left (P.sum_weight_product_real_le hcop F hF x)
    (mul_nonneg hy (sieveProduct_pos P.noFixedPrime x).le)

end NairTenenbaum
