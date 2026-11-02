/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Products of one-variable admissible arithmetic functions -/

@[expose] public section

namespace NairTenenbaum

/-- The total prime-factor count is additive over a finite nonzero product. -/
theorem bigOmega_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) (hn : ∀ i ∈ s, n i ≠ 0) :
    bigOmega (∏ i ∈ s, n i) = ∑ i ∈ s, bigOmega (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, bigOmega_mul (hn i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hn j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hn j (Finset.mem_insert_of_mem hj)), Finset.sum_insert hi]

/-- The coordinate product of one-variable arithmetic functions. -/
noncomputable def productArithmeticMap {k : ℕ} (F : Fin k → ArithmeticMap 1) : ArithmeticMap k :=
  fun n => ∏ j, F j (fun _ => n j)

/-- The product belongs to `M_k(A,B^k,σ)`, with no change in the growth exponent. -/
theorem admissible_productArithmeticMap {k : ℕ} {A B σ : ℝ} {F : Fin k → ArithmeticMap 1}
    (hF : ∀ j, Admissible A B σ (F j)) : Admissible A (B ^ k) σ (productArithmeticMap F) := by
  have hnonneg (n : Tuple k) : 0 ≤ productArithmeticMap F n :=
    Finset.prod_nonneg (fun j _ => (hF j).nonneg _)
  refine ⟨hnonneg, ?_⟩
  intro m n hmn
  have H (j : Fin k) := (hF j).growth (fun _ => m j) (fun _ => n j) (fun _ => hmn j)
  have HA (j : Fin k) : F j (fun _ => m j * n j) ≤ A ^ bigOmega (m j) * F j (fun _ => n j) := by
    apply (H j).trans
    exact mul_le_mul_of_nonneg_right (by
      simp only [growthBound, mass, Fin.prod_univ_one]
      exact min_le_left _ _) ((hF j).nonneg _)
  have HB (j : Fin k) : F j (fun _ => m j * n j) ≤ B * (m j : ℝ) ^ σ * F j (fun _ => n j) := by
    apply (H j).trans
    exact mul_le_mul_of_nonneg_right (by
      simp only [growthBound, mass, Fin.prod_univ_one]
      exact min_le_right _ _) ((hF j).nonneg _)
  have HAp := Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => (hF j).nonneg (fun _ => m j * n
      j)) (fun j _ => HA j)
  have HBp := Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => (hF j).nonneg (fun _ => m j * n
      j)) (fun j _ => HB j)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← bigOmega_prod Finset.univ (fun j => (m j : ℕ)) (fun j _ => (m j).ne_zero)] at HAp
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Real.finsetProd_rpow _ _ (fun _ _ => by positivity)] at HBp
  have hcast : (∏ j, (m j : ℝ)) = (mass m : ℝ) := by simp only [mass, Nat.cast_prod]
  rw [hcast] at HBp
  unfold growthBound
  rw [min_mul_of_nonneg _ _ (hnonneg n)]
  exact le_min HAp HBp

/-- Zero extension commutes with the coordinate product, including tuples
with vanishing polynomial values. -/
theorem extend_productArithmeticMap {k : ℕ} (F : Fin k → ArithmeticMap 1) (n : Fin k → ℕ) :
    extendArithmeticMap (productArithmeticMap F) n =
      ∏ j, extendArithmeticMap (F j) (fun _ => n j) := by
  classical
  unfold extendArithmeticMap
  split_ifs with hn
  · unfold productArithmeticMap
    apply Finset.prod_congr rfl
    intro j _
    rw [dite_eq_left (fun _ => hn j)]
  · symm
    push Not at hn
    obtain ⟨j, hj⟩ := hn
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply dite_eq_right
    intro h
    exact (not_lt_of_ge hj) (h 0)

end NairTenenbaum
