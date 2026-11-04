/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.TupleComparison
public import LeanPool.NairTenenbaum.Smooth.TiltedAuxiliary

/-! # Comparison with prime-power dependent increments

The exponential moment requires an increment depending on the valuation, not
just the prime. Selecting whole prime powers preserves that valuation and
therefore gives an exact expansion over the existing unitary splittings.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The product of the local prime-power weights over the prime factors. -/
noncomputable def primePowerProduct (l : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, l p (n.factorization p)

@[simp] theorem primePowerProduct_one (l : ℕ → ℕ → ℝ) : primePowerProduct l 1 = 1 := by
  simp [primePowerProduct]

theorem primePowerProduct_nonneg {l : ℕ → ℕ → ℝ}
    (hl : ∀ p, p.Prime → ∀ ν, 0 ≤ l p ν) (n : ℕ) : 0 ≤ primePowerProduct l n :=
  Finset.prod_nonneg (fun p hp => hl p (Nat.prime_of_mem_primeFactors hp) _)

theorem primePowerProduct_mul (l : ℕ → ℕ → ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    primePowerProduct l (m * n) = primePowerProduct l m * primePowerProduct l n := by
  simp only [primePowerProduct]
  rw [hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_of_coprime_left hmn
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_of_coprime_right hmn
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]

theorem primePowerProduct_prime_pow_succ (l : ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    primePowerProduct l (p ^ (ν + 1)) = l p (ν + 1) := by
  rw [primePowerProduct, Nat.primeFactors_prime_pow (by omega) hp,
    Finset.prod_singleton, Nat.factorization_pow_self hp]

theorem primePowerProduct_unitaryPart (l : ℕ → ℕ → ℝ) (n : ℕ+)
    {s : Finset ℕ} (hs : s ⊆ (n : ℕ).primeFactors) :
    primePowerProduct l (unitaryPart n s) = ∏ p ∈ s, l p ((n : ℕ).factorization p) := by
  rw [primePowerProduct, unitaryPart_support hs]
  apply Finset.prod_congr rfl
  intro p hp
  rw [unitaryPart, factorization_primeSelect, ite_eq_left hp]

theorem primePowerProduct_one_add (l : ℕ → ℕ → ℝ) (n : ℕ+) :
    primePowerProduct (fun p ν => 1 + l p ν) n =
      ∑ s ∈ (n : ℕ).primeFactors.powerset, primePowerProduct l (unitaryPart n s) := by
  rw [primePowerProduct, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro s hs
  exact (primePowerProduct_unitaryPart l n (Finset.mem_powerset.mp hs)).symm

/-- Reconstruct a real power from its complete prime-power factors. -/
theorem primePowerProduct_rpow (β : ℝ) {n : ℕ} (hn : n ≠ 0) :
    primePowerProduct (fun p ν => ((p : ℝ) ^ ν) ^ β) n = (n : ℝ) ^ β := by
  unfold primePowerProduct
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  simpa only [Nat.cast_prod, Nat.cast_pow] using congrArg (fun x : ℝ => x ^ β) h.symm

theorem prod_primePowerProduct_one_add {r : ℕ} (l : Fin r → ℕ → ℕ → ℝ) (n : Tuple r) :
    (∏ i, primePowerProduct (fun p ν => 1 + l i p ν) (n i)) =
      ∑ t ∈ unitaryChoices n, ∏ i, primePowerProduct (l i) (tupleUnitaryPart n t i) := by
  classical
  simp_rw [primePowerProduct_one_add]
  exact Finset.prod_univ_sum _ _

/-- Pointwise coprime comparison with increments at arbitrary prime powers. -/
theorem tuple_primePower_comparison_pointwise {r : ℕ} {w : Tuple r → ℝ}
    {U : Fin r → ℕ+ → ℝ} {l : Fin r → ℕ → ℕ → ℝ}
    (hl : ∀ i p, p.Prime → ∀ ν, 0 ≤ l i p ν) (n : Tuple r)
    (hw : ∀ t ∈ unitaryChoices n, w n ≤
      (∏ i, U i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) :
    w n * (∏ i, primePowerProduct (fun p ν => 1 + l i p ν) (n i)) ≤
      ∑ t ∈ unitaryChoices n,
        (∏ i, U i (tupleUnitaryPart n t i) * primePowerProduct (l i) (tupleUnitaryPart n t i)) *
          w (tupleUnitaryRest n t) := by
  classical
  rw [prod_primePowerProduct_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ ≤ ((∏ i, U i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) *
        (∏ i, primePowerProduct (l i) (tupleUnitaryPart n t i)) :=
      mul_le_mul_of_nonneg_right (hw t ht)
        (Finset.prod_nonneg (fun i _ => primePowerProduct_nonneg (hl i) _))
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

/-- The finite convolution estimate with separate coordinate domains. In
particular those domains may retain a prescribed finite prime support. -/
theorem tuple_unitary_convolution_sum {r : ℕ} {w v : Tuple r → ℝ}
    {K : Fin r → ℕ+ → ℝ} (hw : ∀ n, 0 ≤ w n) (hK : ∀ i n, 0 ≤ K i n)
    (S : Finset (Tuple r)) (T : Fin r → Finset ℕ+)
    (hpart : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, ∀ i, tupleUnitaryPart n t i ∈ T i)
    (hrest : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, tupleUnitaryRest n t ∈ S)
    (hv : ∀ n ∈ S, v n ≤ ∑ t ∈ unitaryChoices n,
      (∏ i, K i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t)) :
    (∑ n ∈ S, v n) ≤ (∏ i, ∑ a ∈ T i, K i a) * ∑ b ∈ S, w b := by
  classical
  let R := S.sigma (fun n => unitaryChoices n)
  let V := Fintype.piFinset T ×ˢ S
  let f : (Σ _n : Tuple r, Fin r → Finset ℕ) → Tuple r × Tuple r :=
    fun x => (tupleUnitaryPart x.1 x.2, tupleUnitaryRest x.1 x.2)
  have hfmem : ∀ x ∈ R, f x ∈ V := by
    intro x hx
    obtain ⟨hn, ht⟩ := Finset.mem_sigma.mp hx
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (hpart x.1 hn x.2 ht),
      hrest x.1 hn x.2 ht⟩
  have hfinj : Set.InjOn f R := by
    intro x hx y hy hxy
    have h := tupleUnitarySplit_injective (Finset.mem_sigma.mp hx).2 (Finset.mem_sigma.mp hy).2 hxy
    obtain ⟨n, s⟩ := x
    obtain ⟨m, t⟩ := y
    obtain ⟨rfl, rfl⟩ := h
    rfl
  calc
    _ ≤ ∑ n ∈ S, ∑ t ∈ unitaryChoices n,
        (∏ i, K i (tupleUnitaryPart n t i)) * w (tupleUnitaryRest n t) :=
      Finset.sum_le_sum hv
    _ = ∑ x ∈ R, (∏ i, K i ((f x).1 i)) * w (f x).2 := by rw [Finset.sum_sigma]
    _ ≤ ∑ x ∈ V, (∏ i, K i (x.1 i)) * w x.2 :=
      Finset.sum_le_sum_of_injOn f hfinj (Finset.image_subset_iff.mpr hfmem) (fun _ _ => le_rfl)
        (fun x _ _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hK i _)) (hw _))
    _ = _ := by
      rw [Finset.sum_product]
      dsimp only
      rw [← Finset.sum_mul_sum]
      congr 1
      exact (Finset.prod_univ_sum T K).symm

end NairTenenbaum
