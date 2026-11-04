/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerComparison
public import LeanPool.NairTenenbaum.Smooth.MomentPrimeBounds

/-! # The convolution kernel for exponential moments

The prime-power increments give exactly the local errors bounded in
`MomentPrimeBounds`. Their multiplicative extension has a convergent Euler
product on every finite prime support.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The increment introduced by tilting a prime power by the moment exponent. -/
noncomputable def momentIncrement (b : ℝ) (p ν : ℕ) : ℝ := ((p : ℝ) ^ ν) ^ b - 1

theorem momentIncrement_nonneg {b : ℝ} (hb : 0 ≤ b) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    0 ≤ momentIncrement b p ν :=
  sub_nonneg.mpr (Real.one_le_rpow (one_le_pow₀ (by exact_mod_cast hp.one_le)) hb)

theorem primePowerProduct_one_add_momentIncrement (b : ℝ) (n : ℕ+) :
    primePowerProduct (fun p ν => 1 + momentIncrement b p ν) n = (n : ℝ) ^ b := by
  simpa only [momentIncrement, add_sub_cancel] using primePowerProduct_rpow b n.ne_zero

/-- Convolution kernel for the exponential moment comparison. -/
noncomputable def momentKernel (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) (n : ℕ) : ℝ :=
  rootAuxiliary A B ε γ Q n * primePowerProduct (momentIncrement ((γ : ℝ) * β)) n

@[simp] theorem momentKernel_one (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) :
    momentKernel A B ε β γ Q 1 = 1 := by simp [momentKernel]

theorem momentKernel_nonneg {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (γ : ℕ) (Q : ℤ[X]) (n : ℕ) : 0 ≤ momentKernel A B ε β γ Q n :=
  mul_nonneg (rootAuxiliary_nonneg hA hB γ Q n)
    (primePowerProduct_nonneg
      (fun _ hp ν => momentIncrement_nonneg (mul_nonneg (Nat.cast_nonneg γ) hβ) hp ν) n)

theorem momentKernel_mul (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X]) {m n : ℕ}
    (hmn : m.Coprime n) : momentKernel A B ε β γ Q (m * n) =
      momentKernel A B ε β γ Q m * momentKernel A B ε β γ Q n := by
  rw [momentKernel, rootAuxiliary_mul A B ε γ Q hmn, primePowerProduct_mul _ hmn]
  simp only [momentKernel]
  ring

theorem momentKernel_prime_pow_succ (A B ε β : ℝ) (γ : ℕ) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    momentKernel A B ε β γ Q (p ^ (ν + 1)) = localMomentTerm A B ε β γ Q p ν := by
  rw [momentKernel, primePowerProduct_prime_pow_succ _ hp]
  rfl

theorem momentKernel_prime_pow_summable {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    Summable (fun ν : ℕ => momentKernel A B ε β γ Q (p ^ ν)) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [momentKernel_prime_pow_succ A B ε β γ Q hp]
  exact localMomentTerm_summable hA hB hε hβ γ hγ Q hp C hρ

theorem momentKernel_local_tsum {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, momentKernel A B ε β γ Q (p ^ ν)) =
      1 + localMomentError A B ε β γ Q p := by
  rw [(momentKernel_prime_pow_summable hA hB hε hβ γ hγ Q hp C hρ).tsum_eq_zero_add]
  simp only [pow_zero, momentKernel_one]
  simp_rw [momentKernel_prime_pow_succ A B ε β γ Q hp]
  rfl

/-- Exact Euler product for the moment convolution kernel. -/
theorem momentKernel_smooth_hasSum {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) (s : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers s => momentKernel A B ε β γ Q n)
      (∏ p ∈ s.filter Nat.Prime, (1 + localMomentError A B ε β γ Q p)) := by
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (momentKernel_one A B ε β γ Q) (fun hmn => momentKernel_mul A B ε β γ Q hmn)
    (fun {p} hp => by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg
        (momentKernel_nonneg hA (zero_le_one.trans hB) hβ γ Q _)]
      exact momentKernel_prime_pow_summable hA hB hε hβ γ hγ Q hp C (hρ p hp)) s).2
  convert H using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (momentKernel_local_tsum hA hB hε hβ γ hγ Q
    (Finset.mem_filter.mp hp).2 C (hρ p (Finset.mem_filter.mp hp).2)).symm

/-- Every finite smooth partial sum is bounded by the kernel's Euler product. -/
theorem momentKernel_sum_le_product {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C)
    (s : Finset ℕ) (T : Finset ℕ+) (hT : ∀ n ∈ T, (n : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ T, momentKernel A B ε β γ Q n) ≤
      ∏ p ∈ s.filter Nat.Prime, (1 + localMomentError A B ε β γ Q p) := by
  classical
  let e : {n : ℕ+ // n ∈ T} → Nat.factoredNumbers s := fun n => ⟨n.1, hT n.1 n.2⟩
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact PNat.coe_injective
      (show (n.1 : ℕ) = (m.1 : ℕ) from congrArg (fun x : Nat.factoredNumbers s => (x : ℕ)) h)
  have H := momentKernel_smooth_hasSum hA hB hε hβ γ hγ Q C hρ s
  have hb := H.summable.sum_le_tsum (T.attach.image e)
    (fun n _ => momentKernel_nonneg hA (zero_le_one.trans hB) hβ γ Q n)
  rw [H.tsum_eq, Finset.sum_image (fun n _ m _ h => he h)] at hb
  change (∑ n ∈ T.attach, momentKernel A B ε β γ Q (n.1 : ℕ)) ≤ _ at hb
  rw [Finset.sum_attach T (fun n : ℕ+ => momentKernel A B ε β γ Q (n : ℕ))] at hb
  exact hb

end NairTenenbaum
