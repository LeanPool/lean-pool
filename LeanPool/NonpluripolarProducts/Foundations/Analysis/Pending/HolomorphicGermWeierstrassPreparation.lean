/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermNoetherian

/-!
# Weierstrass preparation for holomorphic germs

Source: Gunning--Rossi, *Analytic functions of several complex variables*, II.B,
Theorem 2; Chirka, *Complex analytic sets*, §1.1.  First step of the local
parametrization of analytic sets, which is the missing input behind
`AnalyticIrreducibleComponents.eq_dim_of_regularAtDim`.

Let `G` be holomorphic near `0 ∈ E × ℂ` with `G (0, t) = t^d u(t)`, `u(0) ≠ 0`.  Then
there are a holomorphic `q` with `q 0 ≠ 0` and holomorphic `a_k` on `E` with
`a_k 0 = 0` such that `q G = t^d + ∑_{k<d} a_k(z) t^k` near `0`.

## Proof

Divide `t^d` by `G` (`germWeierstrassDivision`):
`t^d = q G + ∑_{k<d} r_k(z) t^k`.  At `z = 0` this reads
`∑_{k<d} r_k(0) t^k = t^d (1 - q(0,t) u(t))`.  If `r_j(0) = 0` for `j < k`, dividing
by `t^k` and letting `t → 0` through `t ≠ 0` gives `r_k(0) = 0`; so all `r_k(0)`
vanish.  Then `1 = q(0,t) u(t)` for small `t ≠ 0`, and in the limit `q(0) u(0) = 1`.
Put `a_k = -r_k`.
-/

@[expose] public section

open Filter Topology

namespace SGPT.Foundations.Analysis.Pending.HolomorphicGermWeierstrassPreparation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A polynomial `∑_{k<d} c_k t^k` which agrees near `0` with `t^d g(t)`, `g`
continuous at `0`, has all coefficients zero. -/
theorem coeff_eq_zero_of_eventually_eq_pow_mul {d : ℕ} {c : ℕ → ℂ} {g : ℂ → ℂ}
    (hg : ContinuousAt g 0)
    (heq : ∀ᶠ t in 𝓝 (0 : ℂ), ∑ k ∈ Finset.range d, c k * t ^ k = t ^ d * g t) :
    ∀ k < d, c k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  -- for `t ≠ 0` near `0`: `c_k + ∑_{k<j<d} c_j t^{j-k} = t^{d-k} g t`
  have hlow : ∀ t : ℂ, ∑ j ∈ Finset.range d, c j * t ^ j =
      t ^ k * ∑ j ∈ Finset.Ico k d, c j * t ^ (j - k) := by
    intro t
    rw [Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ hk.le]
    have h0 : ∑ j ∈ Finset.range k, c j * t ^ j = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [ih j (Finset.mem_range.mp hj) ((Finset.mem_range.mp hj).trans hk), zero_mul]
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← mul_assoc, mul_comm (t ^ k), mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (Finset.mem_Ico.mp hj).1]
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ∑ j ∈ Finset.Ico k d, c j * t ^ (j - k) = t ^ (d - k) * g t := by
    filter_upwards [nhdsWithin_le_nhds heq, self_mem_nhdsWithin] with t ht htne
    have htk : t ^ k ≠ 0 := pow_ne_zero _ htne
    apply mul_left_cancel₀ htk
    rw [← hlow, ht, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk.le]
  have hL : Tendsto (fun t : ℂ => ∑ j ∈ Finset.Ico k d, c j * t ^ (j - k)) (𝓝[≠] 0)
      (𝓝 (c k)) := by
    have hcont : Continuous fun t : ℂ => ∑ j ∈ Finset.Ico k d, c j * t ^ (j - k) := by
      fun_prop
    have h0 : (∑ j ∈ Finset.Ico k d, c j * (0 : ℂ) ^ (j - k)) = c k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j hj hjk
        have : j - k ≠ 0 := by
          have := (Finset.mem_Ico.mp hj).1
          omega
        simp [zero_pow this]
      · intro h
        exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, hk⟩) h
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [h0] at this
  have hR : Tendsto (fun t : ℂ => t ^ (d - k) * g t) (𝓝[≠] 0) (𝓝 0) := by
    have hpow : Tendsto (fun t : ℂ => t ^ (d - k)) (𝓝 0) (𝓝 0) := by
      have := (continuous_pow (M := ℂ) (d - k)).tendsto 0
      rwa [zero_pow (by omega)] at this
    have := (hpow.mul hg.tendsto).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  exact tendsto_nhds_unique (hL.congr' hev) hR

/-- **Weierstrass preparation theorem.**  If `G` is holomorphic near `0 ∈ E × ℂ` and
`G (0, t) = t^d u(t)` with `u` analytic, `u 0 ≠ 0`, then `q G` is, near `0`, the
Weierstrass polynomial `t^d + ∑_{k<d} a_k(z) t^k` for a holomorphic `q` with
`q 0 ≠ 0` and holomorphic `a_k` vanishing at `0`. -/
theorem exists_weierstrass_preparation {G : E × ℂ → ℂ}
    (hG : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ G x) {d : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hGu : ∀ᶠ t in 𝓝 (0 : ℂ), G (0, t) = t ^ d * u t) :
    ∃ q : E × ℂ → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x) ∧ q 0 ≠ 0 ∧
      ∃ a : ℕ → E → ℂ, (∀ k, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a k) z) ∧
        (∀ k < d, a k 0 = 0) ∧
        (fun x => q x * G x) =ᶠ[𝓝 0]
          fun x => x.2 ^ d + ∑ k ∈ Finset.range d, a k x.1 * x.2 ^ k := by
  have hh : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ (fun x : E × ℂ => x.2 ^ d) x :=
    Eventually.of_forall fun _ => differentiableAt_snd.pow d
  obtain ⟨q, hq, r, hr, hdiv⟩ :=
    germWeierstrassDivision E G hG d u hu hu0 hGu (fun x => x.2 ^ d) hh
  -- restrict the division identity to the slice `z = 0`
  have hslice : Tendsto (fun t : ℂ => ((0 : E), t)) (𝓝 0) (𝓝 (0 : E × ℂ)) := by
    have : Continuous fun t : ℂ => ((0 : E), t) := by fun_prop
    have := this.tendsto 0
    rwa [Prod.mk_zero_zero] at this
  have hdiv0 := hslice.eventually hdiv
  have hqc : ContinuousAt q 0 := continuousAt_zero_of_eventually_differentiableAt hq
  have hq0c : ContinuousAt (fun t : ℂ => q ((0 : E), t)) 0 := by
    have hc : ContinuousAt (fun t : ℂ => ((0 : E), t)) 0 := by fun_prop
    have hqc' : ContinuousAt q ((0 : E), (0 : ℂ)) := by rwa [Prod.mk_zero_zero]
    exact hqc'.comp hc
  have hgc : ContinuousAt (fun t : ℂ => 1 - q ((0 : E), t) * u t) 0 :=
    continuousAt_const.sub (hq0c.mul hu.continuousAt)
  have hpoly : ∀ᶠ t in 𝓝 (0 : ℂ), ∑ k ∈ Finset.range d, r k 0 * t ^ k =
      t ^ d * (1 - q ((0 : E), t) * u t) := by
    filter_upwards [hdiv0, hGu] with t ht hGt
    rw [hGt] at ht
    linear_combination -ht
  have hr0 := coeff_eq_zero_of_eventually_eq_pow_mul hgc hpoly
  -- `q (0, t) u t = 1` for small `t ≠ 0`, hence `q 0 u 0 = 1`
  have hone : ∀ᶠ t in 𝓝[≠] (0 : ℂ), q ((0 : E), t) * u t = 1 := by
    filter_upwards [nhdsWithin_le_nhds hpoly, self_mem_nhdsWithin] with t ht htne
    have hsum : ∑ k ∈ Finset.range d, r k 0 * t ^ k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hr0 k (Finset.mem_range.mp hk), zero_mul]
    rw [hsum] at ht
    have := (mul_eq_zero.mp ht.symm).resolve_left (pow_ne_zero _ htne)
    linear_combination -this
  have hlim : Tendsto (fun t : ℂ => q ((0 : E), t) * u t) (𝓝[≠] 0)
      (𝓝 (q ((0 : E), (0 : ℂ)) * u 0)) :=
    (hq0c.mul hu.continuousAt).tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hq0 : q ((0 : E), (0 : ℂ)) * u 0 = 1 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hone.mono fun _ h => h.symm))
  rw [Prod.mk_zero_zero] at hq0
  refine ⟨q, hq, left_ne_zero_of_mul_eq_one hq0, fun k z => -r k z,
    fun k => (hr k).mono fun _ h => h.neg, fun k hk => by simp [hr0 k hk], ?_⟩
  filter_upwards [hdiv] with x hx
  simp only [neg_mul, Finset.sum_neg_distrib]
  linear_combination -hx

end

end SGPT.Foundations.Analysis.Pending.HolomorphicGermWeierstrassPreparation
