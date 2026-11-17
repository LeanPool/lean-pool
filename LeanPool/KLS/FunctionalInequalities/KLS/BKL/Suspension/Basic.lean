/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Curvature

/-!
# Convex potentials for finite-copy suspension

Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Proposition 7.1, equations (109)–(110).
For `D²V ≥ a Id` and `‖D²f‖ ≤ M`, the potential
`Σ V(xᵢ) + beta |sigma s - (Σ f(xᵢ)) / sqrt N|` is convex if
`beta * M / sqrt N ≤ a`. A positive finite `N` can always be chosen when `a > 0`.

This is the convexity part of the suspension construction. The joint-law identification,
isotropy, mixed cumulant identity and Taylor estimate of Proposition 7.1 are separate targets.
-/

@[expose] public section

noncomputable section

open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.LogConcave.Suspension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The potential (109) on one auxiliary coordinate and `N` copies of the original space.
In the paper `sigma = sqrt (1 + 2 / beta²)`. Convexity holds for every real `sigma`. -/
def potential (V f : E → ℝ) (beta sigma : ℝ) (N : ℕ) (p : ℝ × (Fin N → E)) : ℝ :=
  (∑ i, V (p.2 i)) + beta * |sigma * p.1 - (∑ i, f (p.2 i)) / Real.sqrt N|

private theorem convexOn_perturbation {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) {a M c : ℝ}
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hc : |c| * M ≤ a) :
    ConvexOn ℝ Set.univ (fun x => V x + c * f x) := by
  apply convexOn_of_hessian_ge (hV.add (hf.const_smul c)) (ρ := 0) le_rfl
  intro x v
  have hF : |bilinearIteratedFDerivTwo ℝ f x v v| ≤ M * ‖v‖ ^ 2 := by
    change |(fderiv ℝ (fderiv ℝ f) x) v v| ≤ _
    calc
      _ = ‖(fderiv ℝ (fderiv ℝ f) x) v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖ * ‖v‖ :=
        (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ v v
      _ ≤ M * ‖v‖ * ‖v‖ := by gcongr; exact hfbound x
      _ = M * ‖v‖ ^ 2 := by ring
  have hsum : bilinearIteratedFDerivTwo ℝ (fun y => V y + c * f y) x v v =
      bilinearIteratedFDerivTwo ℝ V x v v + c * bilinearIteratedFDerivTwo ℝ f x v v := by
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    change iteratedFDeriv ℝ 2 (V + c • f) x ![v, v] = _
    have hcf : ContDiff ℝ 2 (c • f) := hf.const_smul c
    rw [iteratedFDeriv_add_apply (g := c • f) hV.contDiffAt hcf.contDiffAt,
      iteratedFDeriv_const_smul_apply hf.contDiffAt]
    simp
  have hprod : |c * bilinearIteratedFDerivTwo ℝ f x v v| ≤ a * ‖v‖ ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ |c| * (M * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hF (abs_nonneg c)
      _ = (|c| * M) * ‖v‖ ^ 2 := by ring
      _ ≤ a * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖v‖)
  change 0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ (fun y => V y + c * f y) x v v
  rw [hsum, zero_mul]
  have := neg_abs_le (c * bilinearIteratedFDerivTwo ℝ f x v v)
  have := hVlower x v
  linarith

private theorem convexOn_sum_add_linear {g : E → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (N : ℕ) (q : ℝ) :
    ConvexOn ℝ Set.univ (fun p : ℝ × (Fin N → E) => (∑ i, g (p.2 i)) + q * p.1) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hg.2 (Set.mem_univ (x.2 i)) (Set.mem_univ (y.2 i)) hu hv huv)
  simp only [smul_eq_mul] at hsum
  change (∑ i, g (u • x.2 i + v • y.2 i)) + q * (u * x.1 + v * y.1) ≤
    u * ((∑ i, g (x.2 i)) + q * x.1) + v * ((∑ i, g (y.2 i)) + q * y.1)
  calc
    _ ≤ (∑ i, (u * g (x.2 i) + v * g (y.2 i))) + q * (u * x.1 + v * y.1) :=
      add_le_add hsum le_rfl
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The source's convexity argument (109)–(110), with its Hessian condition and constants.
The auxiliary-coordinate scale is unrestricted, and no probability assumptions are needed. -/
theorem convexOn_potential {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    {a M beta sigma : ℝ} (hbeta : 0 ≤ beta)
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (N : ℕ) (hN : beta / Real.sqrt N * M ≤ a) :
    ConvexOn ℝ Set.univ (potential V f beta sigma N) := by
  classical
  have hc : 0 ≤ beta / Real.sqrt N := div_nonneg hbeta (Real.sqrt_nonneg _)
  have hp :=
    convexOn_perturbation hV hf hVlower hfbound (c := beta / Real.sqrt N)
      (by simpa only [abs_of_nonneg hc] using hN)
  have hm :=
    convexOn_perturbation hV hf hVlower hfbound (c := -(beta / Real.sqrt N))
      (by simpa only [abs_neg, abs_of_nonneg hc] using hN)
  have hmax :=
    (convexOn_sum_add_linear hm N (beta * sigma)).sup
      (convexOn_sum_add_linear hp N (-(beta * sigma)))
  apply hmax.congr
  intro p _
  simp only [Pi.sup_apply]
  rw [potential, abs_eq_max_neg]
  rw [mul_max_of_nonneg _ _ hbeta, add_max]
  congr 1 <;> rw [Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring

/-- A positive finite number of copies satisfies (110) for any positive curvature and finite
nonnegative Hessian bound. -/
theorem exists_copies {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 ≤ beta) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((beta * M / a) ^ 2 + 1)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by nlinarith [sq_nonneg (beta * M / a)]
    exact_mod_cast this
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hratio : 0 ≤ beta * M / a := div_nonneg (mul_nonneg hbeta hM) ha.le
  have hsmall : beta * M / a ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hmul : beta * M ≤ a * Real.sqrt (N : ℝ) := by
    have := (div_le_iff₀ ha).1 hsmall
    nlinarith
  refine ⟨N, hNpos, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hspos]
  exact hmul

omit [InnerProductSpace ℝ E] in
/-- The suspension potential is continuous, including along the crease of its absolute value. -/
theorem continuous_potential {V f : E → ℝ} (hV : Continuous V) (hf : Continuous f)
    (beta sigma : ℝ) (N : ℕ) : Continuous (potential V f beta sigma N) := by
  unfold potential
  fun_prop

end FunctionalInequalities.KLS.LogConcave.Suspension
