/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RiemannExtension
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicZeroSetThin
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The ring of holomorphic germs is integrally closed

Blueprint node `lag:germ-integrally-closed`. For `x = a / b` in the fraction field of
`𝒪_d = HolGerm (EuclideanSpace ℂ (Fin d))` which is integral over `𝒪_d`, clearing denominators
gives `a ^ k + ∑_{i < k} c_i b ^ (k - i) a ^ i = 0`. Off the zero set of `b` the quotient
`a / b` is then a root of a monic polynomial with locally bounded coefficients, hence locally
bounded; the Riemann extension theorem extends it to a holomorphic `F`, and `b F = a` near `0`
by density of the complement of the zero set of `b`.

## Main declarations

* `norm_le_of_monic_root` : the Cauchy bound `‖w‖ ≤ max 1 (∑ ‖c_i‖)` for roots of monic
  polynomials.
* `exists_eq_mul_of_monic_relation` : the analytic core.
* `isIntegrallyClosed_holGerm` : `𝒪_d` is integrally closed.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending.GermIntegrallyClosed

open Filter Metric Set Polynomial
open scoped Topology

/-- **Cauchy bound.** A root `w` of the monic polynomial `X ^ k + ∑_{i < k} c_i X ^ i`
satisfies `‖w‖ ≤ max 1 (∑_{i < k} ‖c_i‖)`. -/
theorem norm_le_of_monic_root {k : ℕ} {c : ℕ → ℂ} {w : ℂ}
    (hw : w ^ k + ∑ i ∈ Finset.range k, c i * w ^ i = 0) :
    ‖w‖ ≤ max 1 (∑ i ∈ Finset.range k, ‖c i‖) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, hS⟩ := max_lt_iff.1 hlt
  rcases k with _ | m
  · simp at hw
  · have hk : ‖w‖ ^ (m + 1) ≤ (∑ i ∈ Finset.range (m + 1), ‖c i‖) * ‖w‖ ^ m := by
      have heq : w ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), c i * w ^ i :=
        eq_neg_of_add_eq_zero_left hw
      calc ‖w‖ ^ (m + 1) = ‖∑ i ∈ Finset.range (m + 1), c i * w ^ i‖ := by
            rw [← norm_pow, heq, norm_neg]
        _ ≤ ∑ i ∈ Finset.range (m + 1), ‖c i * w ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (m + 1), ‖c i‖ * ‖w‖ ^ m := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_mul, norm_pow]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
        _ = (∑ i ∈ Finset.range (m + 1), ‖c i‖) * ‖w‖ ^ m := by rw [Finset.sum_mul]
    have hpos : 0 < ‖w‖ ^ m := pow_pos (one_pos.trans h1) m
    have : (∑ i ∈ Finset.range (m + 1), ‖c i‖) * ‖w‖ ^ m < ‖w‖ ^ (m + 1) := by
      rw [pow_succ, mul_comm (‖w‖ ^ m)]
      exact mul_lt_mul_of_pos_right hS hpos
    linarith

variable {d : ℕ}

/-- **Analytic core.** If `a`, `b`, `c_i` are holomorphic near `0`, `b` does not vanish
identically near `0`, and `a ^ k + ∑_{i < k} c_i b ^ (k - i) a ^ i = 0` near `0`, then
`a = b F` near `0` for some `F` holomorphic near `0`. -/
theorem exists_eq_mul_of_monic_relation {k : ℕ} {a b : EuclideanSpace ℂ (Fin d) → ℂ}
    {c : ℕ → EuclideanSpace ℂ (Fin d) → ℂ}
    (ha : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ a z) (hb : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ b z)
    (hc : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (c i) z)
    (hb0 : ¬ ∀ᶠ z in 𝓝 0, b z = 0)
    (hrel : ∀ᶠ z in 𝓝 0, a z ^ k + ∑ i ∈ Finset.range k, c i z * b z ^ (k - i) * a z ^ i = 0) :
    ∃ F : EuclideanSpace ℂ (Fin d) → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) ∧
      ∀ᶠ z in 𝓝 0, a z = b z * F z := by
  -- local bound on the coefficients
  set S0 : ℝ := ∑ i ∈ Finset.range k, ‖c i 0‖ with hS0
  have hcont : ContinuousAt (fun z => ∑ i ∈ Finset.range k, ‖c i z‖) 0 := by
    exact tendsto_finsetSum _ fun i _ => ((hc i).self_of_nhds.continuousAt).norm
  have hSev : ∀ᶠ z in 𝓝 0, ∑ i ∈ Finset.range k, ‖c i z‖ < S0 + 1 :=
    hcont.eventually_lt continuousAt_const (by simp [hS0])
  have hdiv : ∀ᶠ z in 𝓝 0, b z ≠ 0 → DifferentiableAt ℂ (fun z => a z / b z) z :=
    (ha.and hb).mono fun z hz hbz => by
      simp only [div_eq_mul_inv]; exact hz.1.fun_mul (hz.2.inv hbz)
  have hbdd : ∀ᶠ z in 𝓝 0, b z ≠ 0 → ‖a z / b z‖ ≤ max 1 (S0 + 1) :=
    (hrel.and hSev).mono fun z hz hbz => by
      have hroot : (a z / b z) ^ k + ∑ i ∈ Finset.range k, c i z * (a z / b z) ^ i = 0 := by
        have hbk : b z ^ k ≠ 0 := pow_ne_zero _ hbz
        have : b z ^ k * ((a z / b z) ^ k + ∑ i ∈ Finset.range k, c i z * (a z / b z) ^ i) =
            a z ^ k + ∑ i ∈ Finset.range k, c i z * b z ^ (k - i) * a z ^ i := by
          rw [mul_add, Finset.mul_sum, div_pow, mul_div_cancel₀ _ hbk]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          have hik : i ≤ k := (Finset.mem_range.1 hi).le
          rw [div_pow, ← Nat.sub_add_cancel hik, pow_add]
          rw [Nat.add_sub_cancel]
          field_simp
        rw [hz.1] at this
        exact (mul_eq_zero.1 this).resolve_left hbk
      exact (norm_le_of_monic_root hroot).trans (max_le_max le_rfl hz.2.le)
  obtain ⟨F, hFd, hFe⟩ := RiemannExtension.exists_extension_euclidean (f := fun z => a z / b z)
    hb hb0 hdiv ⟨_, hbdd⟩
  -- `b F - a` vanishes off the zero set of `b`, hence near `0`
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (((ha.and hb).and hFd).and hFe)
  have hbd : DifferentiableOn ℂ b (ball 0 ρ) := fun z hz =>
    (hball z hz).1.1.2.differentiableWithinAt
  have hgc : ContinuousOn (fun z => b z * F z - a z) (ball 0 ρ) := fun z hz =>
    (((hball z hz).1.1.2.continuousAt.mul (hball z hz).1.2.continuousAt).sub
      (hball z hz).1.1.1.continuousAt).continuousWithinAt
  have hzero := RiemannExtension.eqOn_zero_of_eqOn_zero_compl_zeroSet isOpen_ball
    (convex_ball 0 ρ).isPreconnected hbd (mem_ball_self hρ) hb0 hgc fun z hz hbz => by
      rw [(hball z hz).2 hbz, mul_div_cancel₀ _ hbz, sub_self]
  refine ⟨F, hFd, eventually_of_mem (ball_mem_nhds 0 hρ) fun z hz => ?_⟩
  exact (sub_eq_zero.1 (hzero z hz)).symm

/-- `𝒪_d` is integrally closed. -/
instance isIntegrallyClosed_holGerm (d : ℕ) :
    IsIntegrallyClosed (HolGerm (EuclideanSpace ℂ (Fin d))) := by
  set R := HolGerm (EuclideanSpace ℂ (Fin d))
  refine (isIntegrallyClosed_iff (FractionRing R)).2 fun {x} hx => ?_
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  obtain ⟨p, hpm, hp⟩ := hx
  have hp' : aeval (IsLocalization.mk' (FractionRing R) a (⟨b, hb⟩ : nonZeroDivisors R)) p = 0 :=
    by rwa [aeval_def]
  have hsc := scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero hp'
  rw [aeval_algebraMap_apply, map_eq_zero_iff _ (IsFractionRing.injective R _)] at hsc
  rw [aeval_eq_sum_range' (n := p.natDegree + 1) (by rw [natDegree_scaleRoots]; omega),
    Finset.sum_range_succ] at hsc
  simp only [coeff_scaleRoots, smul_eq_mul] at hsc
  rw [Nat.sub_self, pow_zero, mul_one, hpm.coeff_natDegree, one_mul] at hsc
  generalize p.natDegree = k at hsc
  -- representatives
  obtain ⟨fa, hfa, rfl⟩ := HolGerm.exists_eq_mk a
  obtain ⟨fb, hfb, rfl⟩ := HolGerm.exists_eq_mk b
  choose c hc hceq using fun i => HolGerm.exists_eq_mk (p.coeff i)
  have hb0 : ¬ ∀ᶠ z in 𝓝 0, fb z = 0 := by
    intro H
    apply nonZeroDivisors.ne_zero hb
    rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    exact H
  have hrel : ∀ᶠ z in 𝓝 0,
      fa z ^ k + ∑ i ∈ Finset.range k, c i z * fb z ^ (k - i) * fa z ^ i = 0 := by
    have hd : ∀ i, ∀ᶠ z in 𝓝 0,
        DifferentiableAt ℂ (fun z => c i z * fb z ^ (k - i) * fa z ^ i) z := fun i =>
      eventually_differentiableAt_mul
        (eventually_differentiableAt_mul (hc i)
          (eventually_differentiableAt_pow hfb _))
        (eventually_differentiableAt_pow hfa _)
    have key : HolGerm.mk (fun z => fa z ^ k + ∑ i ∈ Finset.range k,
        c i z * fb z ^ (k - i) * fa z ^ i)
        (eventually_differentiableAt_add (eventually_differentiableAt_pow hfa k)
          (eventually_differentiableAt_sum _ hd)) = HolGerm.mk 0
          eventually_differentiableAt_zero := by
      rw [HolGerm.mk_add _ _ (eventually_differentiableAt_pow hfa k)
        (eventually_differentiableAt_sum _ hd), HolGerm.mk_sum _ _ hd, HolGerm.mk_zero, ← hsc,
        add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hceq i, ← HolGerm.mk_pow fb hfb, ← HolGerm.mk_pow fa hfa, ← HolGerm.mk_mul,
        ← HolGerm.mk_mul]
    exact HolGerm.mk_eq_mk_iff.1 key
  obtain ⟨F, hFd, hFe⟩ := exists_eq_mul_of_monic_relation hfa hfb hc hb0 hrel
  refine ⟨HolGerm.mk F hFd, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_comm, ← HolGerm.mk_mul]
  congr 1
  exact (HolGerm.mk_eq_mk_iff.2 hFe).symm

end SGPT.Foundations.Analysis.Pending.GermIntegrallyClosed
