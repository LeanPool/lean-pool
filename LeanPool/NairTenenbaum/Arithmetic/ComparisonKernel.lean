/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ComparisonLocal
public import LeanPool.NairTenenbaum.Arithmetic.UnitaryComparison

/-! # Summable kernels for the corrected comparison

Multiplying the coprime majorant by the product of prime increments produces
a convolution kernel. Its positive local terms are exactly the weighted tails
proved convergent in `ComparisonLocal`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The convolution kernel used in the arithmetic-weight comparison. -/
noncomputable def comparisonKernel (U l : ℕ → ℝ) (n : ℕ) : ℝ := U n * radicalProduct l n

/-- The higher-prime-power error of the comparison kernel. -/
noncomputable def kernelLocalError (U l : ℕ → ℝ) (p : ℕ) : ℝ :=
  l p * ∑' ν : ℕ, U (p ^ (ν + 1))

theorem comparisonKernel_nonneg {U l : ℕ → ℝ} (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (n : ℕ) : 0 ≤ comparisonKernel U l n := mul_nonneg (hU n) (radicalProduct_nonneg hl n)

theorem kernelLocalError_nonneg {U l : ℕ → ℝ} (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (p : ℕ) : 0 ≤ kernelLocalError U l p := mul_nonneg (hl p) (tsum_nonneg (fun _ => hU _))

theorem comparisonKernel_one {U l : ℕ → ℝ} (hU₁ : U 1 = 1) : comparisonKernel U l 1 = 1 := by
  simp [comparisonKernel, hU₁]

theorem comparisonKernel_mul {U l : ℕ → ℝ} (hU₀ : U 0 = 0)
    (hU : ∀ m n, Nat.Coprime m n → U (m * n) = U m * U n)
    {m n : ℕ} (hmn : m.Coprime n) :
    comparisonKernel U l (m * n) = comparisonKernel U l m * comparisonKernel U l n := by
  by_cases hm : m = 0
  · simp [hm, comparisonKernel, hU₀]
  by_cases hn : n = 0
  · simp [hn, comparisonKernel, hU₀]
  rw [comparisonKernel, hU m n hmn, radicalProduct_mul l hm hn hmn]
  simp only [comparisonKernel]
  ring

theorem comparisonKernel_prime_pow_succ (U l : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    comparisonKernel U l (p ^ (ν + 1)) = l p * U (p ^ (ν + 1)) := by
  rw [comparisonKernel, radicalProduct, Nat.primeFactors_prime_pow (by omega) hp]
  simp [mul_comm]

theorem comparisonKernel_prime_pow_summable {U l : ℕ → ℝ} {p : ℕ} (hp : p.Prime)
    (hs : Summable (fun ν : ℕ => U (p ^ ν))) :
    Summable (fun ν : ℕ => comparisonKernel U l (p ^ ν)) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [comparisonKernel_prime_pow_succ U l hp]
  exact ((summable_nat_add_iff 1).mpr hs).mul_left _

theorem comparisonKernel_local_tsum {U l : ℕ → ℝ} (hU₁ : U 1 = 1)
    {p : ℕ} (hp : p.Prime) (hs : Summable (fun ν : ℕ => U (p ^ ν))) :
    (∑' ν : ℕ, comparisonKernel U l (p ^ ν)) = 1 + kernelLocalError U l p := by
  rw [(comparisonKernel_prime_pow_summable hp hs).tsum_eq_zero_add]
  simp only [pow_zero, comparisonKernel_one hU₁]
  simp_rw [comparisonKernel_prime_pow_succ U l hp]
  rw [tsum_mul_left]
  rfl

/-- Exact finite Euler product for the auxiliary convolution kernel. -/
theorem comparisonKernel_smooth_hasSum {U l : ℕ → ℝ} (hU₀ : U 0 = 0) (hU₁ : U 1 = 1)
    (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (hmul : ∀ m n, Nat.Coprime m n → U (m * n) = U m * U n)
    (hs : ∀ p, p.Prime → Summable (fun ν : ℕ => U (p ^ ν))) (s : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers s => comparisonKernel U l n)
      (∏ p ∈ s.filter Nat.Prime, (1 + kernelLocalError U l p)) := by
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (comparisonKernel_one (l := l) hU₁) (fun hmn => comparisonKernel_mul (l := l) hU₀ hmul hmn)
    (fun {p} hp => by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (comparisonKernel_nonneg hU hl _)]
      exact comparisonKernel_prime_pow_summable hp (hs p hp)) s).2
  convert h using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (comparisonKernel_local_tsum hU₁ (Finset.mem_filter.mp hp).2 (hs p (Finset.mem_filter.mp
      hp).2)).symm

/-- A kernel partial sum is bounded by its finite Euler product. -/
theorem comparisonKernel_sum_le_product {U l : ℕ → ℝ} (hU₀ : U 0 = 0) (hU₁ : U 1 = 1)
    (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (hmul : ∀ m n, Nat.Coprime m n → U (m * n) = U m * U n)
    (hs : ∀ p, p.Prime → Summable (fun ν : ℕ => U (p ^ ν))) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N, comparisonKernel U l n) ≤
      ∏ p ∈ (Finset.range ((N : ℕ) + 1)).filter Nat.Prime, (1 + kernelLocalError U l p) := by
  classical
  let s := Finset.range ((N : ℕ) + 1)
  have hmem (n : ℕ+) (hn : n ∈ Finset.Icc 1 N) : (n : ℕ) ∈ Nat.factoredNumbers s := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset n.ne_zero
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_dvd n.pos
      (Nat.dvd_of_mem_primeFactors hp)).trans (Finset.mem_Icc.mp hn).2))
  let e : {n : ℕ+ // n ∈ Finset.Icc 1 N} → Nat.factoredNumbers s := fun n => ⟨n.1, hmem n.1 n.2⟩
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact PNat.coe_injective (show (n.1 : ℕ) = (m.1 : ℕ) from congrArg (fun x :
        Nat.factoredNumbers s => (x : ℕ)) h)
  have H := comparisonKernel_smooth_hasSum hU₀ hU₁ hU hl hmul hs s
  have hb := H.summable.sum_le_tsum ((Finset.Icc 1 N).attach.image e)
    (fun n _ => comparisonKernel_nonneg hU hl n)
  rw [H.tsum_eq, Finset.sum_image (fun n _ m _ h => he h)] at hb
  change (∑ n ∈ (Finset.Icc 1 N).attach, comparisonKernel U l (n.1 : ℕ)) ≤ _ at hb
  rw [Finset.sum_attach (Finset.Icc 1 N) (fun n : ℕ+ => comparisonKernel U l (n : ℕ))] at hb
  exact hb

/-- The finite Euler products have a uniform bound if their local errors are
summable. The bound is independent of the cutoff. -/
theorem kernelLocalError_product_le {U l : ℕ → ℝ} (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (hs : Summable (fun p : Nat.Primes => kernelLocalError U l p)) (s : Finset ℕ) :
    (∏ p ∈ s.filter Nat.Prime, (1 + kernelLocalError U l p)) ≤
      Real.exp (∑' p : Nat.Primes, kernelLocalError U l p) := by
  classical
  rw [← Finset.prod_subtype_eq_prod_filter (fun p => 1 + kernelLocalError U l p)]
  calc
    _ ≤ ∏ p ∈ s.subtype Nat.Prime, Real.exp (kernelLocalError U l p) := by
      apply Finset.prod_le_prod₀
      · intro p _
        exact add_nonneg zero_le_one (kernelLocalError_nonneg hU hl p)
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (kernelLocalError U l p)
    _ = Real.exp (∑ p ∈ s.subtype Nat.Prime, kernelLocalError U l p) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs' : Summable (fun p : {p : ℕ // p.Prime} => kernelLocalError U l p) := by
        simpa only [Nat.Primes] using hs
      have hb := hs'.sum_le_tsum (s.subtype Nat.Prime)
        (fun p _ => kernelLocalError_nonneg hU hl p)
      exact hb

/-- A corrected global comparison for scalar weights, with explicit sufficient
hypotheses on their coprime majorant and prime increments. -/
theorem unitary_comparison_uniform {w : ℕ+ → ℝ} {U l : ℕ → ℝ}
    (hw₀ : ∀ n, 0 ≤ w n) (hU₀ : U 0 = 0) (hU₁ : U 1 = 1)
    (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (hmul : ∀ m n, Nat.Coprime m n → U (m * n) = U m * U n)
    (hw : ∀ a b : ℕ+, Nat.Coprime a b → w (a * b) ≤ U a * w b)
    (hs : ∀ p, p.Prime → Summable (fun ν : ℕ => U (p ^ ν)))
    (hE : Summable (fun p : Nat.Primes => kernelLocalError U l p)) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N, w n * radicalProduct (fun p => 1 + l p) n) ≤
      Real.exp (∑' p : Nat.Primes, kernelLocalError U l p) * (∑ n ∈ Finset.Icc 1 N, w n) := by
  refine (unitary_comparison_sum hw₀ (fun n => hU n) hl hw N).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => hw₀ n))
  exact (comparisonKernel_sum_le_product hU₀ hU₁ hU hl hmul hs N).trans
    (kernelLocalError_product_le hU hl hE _)

end NairTenenbaum
