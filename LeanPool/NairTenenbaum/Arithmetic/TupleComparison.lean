/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ComparisonKernel

/-! # Multivariable whole prime-power comparison

The prime subsets may be chosen independently in each coordinate. The dagger
condition will supply the cross-coordinate coprimality needed by exponent
substitution. The finite comparison retains any domain closed under removing
whole prime-power factors, including the weighted-mass truncation.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The possible whole-prime-power selections in each tuple coordinate. -/
noncomputable def unitaryChoices {r : ℕ} (n : Tuple r) : Finset (Fin r → Finset ℕ) :=
  Fintype.piFinset (fun i => (n i : ℕ).primeFactors.powerset)

@[simp] theorem mem_unitaryChoices {r : ℕ} (n : Tuple r) (t : Fin r → Finset ℕ) :
    t ∈ unitaryChoices n ↔ ∀ i, t i ⊆ (n i : ℕ).primeFactors := by
  simp [unitaryChoices]

/-- The coordinatewise unitary part selected by the chosen prime sets. -/
def tupleUnitaryPart {r : ℕ} (n : Tuple r) (t : Fin r → Finset ℕ) : Tuple r :=
  fun i => unitaryPart (n i) (t i)

/-- The coordinatewise remainder after removing the selected unitary parts. -/
def tupleUnitaryRest {r : ℕ} (n : Tuple r) (t : Fin r → Finset ℕ) : Tuple r :=
  fun i => unitaryRest (n i) (t i)

theorem tupleUnitaryPart_mul_rest {r : ℕ} (n : Tuple r) (t : Fin r → Finset ℕ) :
    tupleUnitaryPart n t * tupleUnitaryRest n t = n := by
  funext i
  exact unitaryPart_mul_rest (n i) (t i)

theorem tupleUnitarySplit_injective {r : ℕ} {n m : Tuple r} {s t : Fin r → Finset ℕ}
    (hs : s ∈ unitaryChoices n) (ht : t ∈ unitaryChoices m)
    (h : (tupleUnitaryPart n s, tupleUnitaryRest n s) =
      (tupleUnitaryPart m t, tupleUnitaryRest m t)) : n = m ∧ s = t := by
  have hi (i : Fin r) : n i = m i ∧ s i = t i :=
    unitarySplit_injective ((mem_unitaryChoices n s).mp hs i) ((mem_unitaryChoices _ t).mp ht i)
      (congrArg (fun x : Tuple r × Tuple r => (x.1 i, x.2 i)) h)
  exact ⟨funext (fun i => (hi i).1), funext (fun i => (hi i).2)⟩

/-- Coordinatewise prime-product expansion as a sum over all choices. -/
theorem prod_radicalProduct_one_add {r : ℕ} (l : Fin r → ℕ → ℝ) (n : Tuple r) :
    (∏ i, radicalProduct (fun p => 1 + l i p) (n i)) =
      ∑ t ∈ unitaryChoices n, ∏ i, radicalProduct (l i) (tupleUnitaryPart n t i) := by
  classical
  simp only [radicalProduct, Finset.prod_one_add]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro i _
  rw [tupleUnitaryPart, unitaryPart_support ((mem_unitaryChoices _ t).mp ht i)]

/-- Pointwise comparison for a prescribed tuple and its coprime splittings. -/
theorem tuple_comparison_pointwise {r : ℕ} {w : Tuple r → ℝ} {U : Fin r → ℕ+ → ℝ}
    {l : Fin r → ℕ → ℝ} (hl : ∀ i p, 0 ≤ l i p) (n : Tuple r)
    (hw : ∀ t ∈ unitaryChoices n, w n ≤
      (∏ i, U i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) :
    w n * (∏ i, radicalProduct (fun p => 1 + l i p) (n i)) ≤
      ∑ t ∈ unitaryChoices n,
        (∏ i, U i (tupleUnitaryPart n t i) * radicalProduct (l i) (tupleUnitaryPart n t i)) *
          w (tupleUnitaryRest n t) := by
  classical
  rw [prod_radicalProduct_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ ≤ ((∏ i, U i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) *
        (∏ i, radicalProduct (l i) (tupleUnitaryPart n t i)) :=
      mul_le_mul_of_nonneg_right (hw t ht)
        (Finset.prod_nonneg (fun i _ => radicalProduct_nonneg (hl i) _))
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

/-- The tuple version of the finite convolution comparison. The original
truncated domain is preserved in the second factor. -/
theorem tuple_comparison_sum {r : ℕ} {w : Tuple r → ℝ} {U : Fin r → ℕ+ → ℝ}
    {l : Fin r → ℕ → ℝ} (hw₀ : ∀ n, 0 ≤ w n) (hU : ∀ i n, 0 ≤ U i n)
    (hl : ∀ i p, 0 ≤ l i p) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hrest : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, tupleUnitaryRest n t ∈ S)
    (hw : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, w n ≤
      (∏ i, U i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) :
    (∑ n ∈ S, w n * ∏ i, radicalProduct (fun p => 1 + l i p) (n i)) ≤
      (∏ i, ∑ a ∈ Finset.Icc 1 N, U i a * radicalProduct (l i) a) * ∑ b ∈ S, w b := by
  classical
  let R := S.sigma (fun n => unitaryChoices n)
  let T := (tupleBox r N) ×ˢ S
  let f : (Σ _n : Tuple r, Fin r → Finset ℕ) → Tuple r × Tuple r :=
    fun x => (tupleUnitaryPart x.1 x.2, tupleUnitaryRest x.1 x.2)
  have hfmem : ∀ x ∈ R, f x ∈ T := by
    intro x hx
    obtain ⟨hn, ht⟩ := Finset.mem_sigma.mp hx
    exact Finset.mem_product.mpr ⟨mem_tupleBox.mpr (fun i =>
      (unitaryPart_le (x.1 i) (x.2 i)).trans (hbox x.1 hn i)), hrest x.1 hn x.2 ht⟩
  have hfinj : Set.InjOn f R := by
    intro x hx y hy hxy
    have h := tupleUnitarySplit_injective (Finset.mem_sigma.mp hx).2 (Finset.mem_sigma.mp hy).2 hxy
    obtain ⟨n, s⟩ := x
    obtain ⟨m, t⟩ := y
    obtain ⟨rfl, rfl⟩ := h
    rfl
  calc
    _ ≤ ∑ n ∈ S, ∑ t ∈ unitaryChoices n,
        (∏ i, U i (tupleUnitaryPart n t i) * radicalProduct (l i) (tupleUnitaryPart n t i)) *
          w (tupleUnitaryRest n t) :=
      Finset.sum_le_sum (fun n hn => tuple_comparison_pointwise hl n (hw n hn))
    _ = ∑ x ∈ R, (∏ i, U i ((f x).1 i) * radicalProduct (l i) ((f x).1 i)) * w (f x).2 := by
      rw [Finset.sum_sigma]
    _ ≤ ∑ x ∈ T, (∏ i, U i (x.1 i) * radicalProduct (l i) (x.1 i)) * w x.2 :=
      Finset.sum_le_sum_of_injOn f hfinj (Finset.image_subset_iff.mpr hfmem) (fun _ _ => le_rfl)
        (fun x _ _ => mul_nonneg (Finset.prod_nonneg (fun i _ =>
          mul_nonneg (hU i _) (radicalProduct_nonneg (hl i) _))) (hw₀ _))
    _ = _ := by
      rw [Finset.sum_product]
      dsimp only
      rw [← Finset.sum_mul_sum]
      congr 1
      exact (Finset.prod_univ_sum (fun _ : Fin r => Finset.Icc 1 N)
        (fun i a => U i a * radicalProduct (l i) a)).symm

/-- Summable coordinate kernels supply a uniform multivariable comparison. -/
theorem tuple_comparison_uniform {r : ℕ} {w : Tuple r → ℝ} {U l : Fin r → ℕ → ℝ}
    (hw₀ : ∀ n, 0 ≤ w n) (hU₀ : ∀ i, U i 0 = 0) (hU₁ : ∀ i, U i 1 = 1)
    (hU : ∀ i n, 0 ≤ U i n) (hl : ∀ i p, 0 ≤ l i p)
    (hmul : ∀ i m n, Nat.Coprime m n → U i (m * n) = U i m * U i n)
    (hs : ∀ i p, p.Prime → Summable (fun ν : ℕ => U i (p ^ ν)))
    (hE : ∀ i, Summable (fun p : Nat.Primes => kernelLocalError (U i) (l i) p))
    (S : Finset (Tuple r)) (N : ℕ+) (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hrest : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, tupleUnitaryRest n t ∈ S)
    (hw : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, w n ≤
      (∏ i, U i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) :
    (∑ n ∈ S, w n * ∏ i, radicalProduct (fun p => 1 + l i p) (n i)) ≤
      (∏ i, Real.exp (∑' p : Nat.Primes, kernelLocalError (U i) (l i) p)) * ∑ b ∈ S, w b := by
  refine (tuple_comparison_sum hw₀ (fun i n => hU i n) hl S N hbox hrest hw).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => hw₀ n))
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.sum_nonneg (fun n _ => mul_nonneg (hU i n) (radicalProduct_nonneg (hl i) n))
  · intro i _
    exact (comparisonKernel_sum_le_product (hU₀ i) (hU₁ i) (hU i) (hl i) (hmul i) (hs i) N).trans
      (kernelLocalError_product_le (hU i) (hl i) (hE i) _)

end NairTenenbaum
