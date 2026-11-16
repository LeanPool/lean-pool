/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Defect
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.ApproximateEigenfunction
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Curvature
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Iteration.DyadicSummation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.BasisChange

/-!
# The Taylor-coefficient criterion of BKL Theorem 3.1

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Theorem 3.1 (p. 10) and its proof (p. 17):
the final argument that turns the estimates on the iterates `iter Tbar f k` (the source's `h_{k+1}`)
of an approximate first eigenfunction into `C_P(μ) ≤ K R²`.

## What is proved

* `le_of_iterate_bounds`: the final argument for real sequences. From the scalar relations of
  the iterates, with `λ = 1/C`: (36), `v₀ ≥ λ`, `v_k → 0`, `Σ χ ≤ ‖L h₁‖² ≤ (1.1 λ)²`, the
  monotonicity of `‖L h‖²`, (46), (32), the Taylor bound `|T_d(∇₀h)|² ≤ R^{2d} v`, Lemma 3.8 with a
  constant `c ≥ 1` and Lemma 3.9 at `β = 3`, it concludes `C ≤ 100 c² R²`.
* `norm_taylorField_sq_le`: (29) for scalar `L²` classes gives `|T_d u|² ≤ R^{2d} ‖u‖²` for tensor
  fields, componentwise.
* `taylorCriterion`: in the heat model `ν = m.tilted (-U)` (`U` temperate, all exponential
  moments, `∇²U ≥ a > 0`, `∫ ⟪v, x⟫² dν ≤ ‖v‖²`) with (29) for `R ≥ 1`, `C_P(ν) ≤ K R²`;
* `KLS.RegularPotential.poincare_le_of_taylor`: **BKL Theorem 3.1**, the exact statement
  for regular laws on `ℝⁿ` (centered, `Cov ≤ Id`, (29) in the Hilbert–Schmidt norm
  of the standard basis).

The constant is `K = taylorCriterionConstant = 100 c²` with `c = 2^20 max(1, 3)² = 9 · 2^20`, the
constant of Lemma 3.8 at `β = 3`.

## The argument

Let `C = C_P(ν)`, finite by `C_P ≤ 1/a`; if `C = 0` there is nothing to prove. Otherwise take a
centered unit `f ∈ D(A)` with `‖A f - λ f‖ ≤ λ/10` (`exists_centered_approx_eigenfunction`).
Then `v₀ = ‖∇f‖² ≥ λ` by the Poincaré gap and `‖L h₁‖ = ‖A f‖ ≤ 1.1 λ`. Lemma 3.4 makes `‖L h‖²`
nonincreasing and Corollary 3.5 gives `v_k → 0` and `Σ χ ≤ ‖L h₁‖²` (`PoissonIterate/Defect.lean`).
Let `N` be minimal with `v_N < λ/2`. For `j + 1 < N`, `v_{j+1} ≥ λ/2` forces `α_j > 0`, and (46)
gives `α_j² = ‖L h_{j+2}‖² / v_{j+1} ≤ 2.42 λ ≤ 3λ`; also `v_{k+1} ≤ 1.21 λ` for every `k` by
(32) and (46). With `S_d = Σ_{k < N-d} |T_d(∇₀h_{k+1})|²`, Lemma 3.8
(`norm_taylorField_grad0_iter_sq_le`, `PoissonIterate/TaylorRecursion.lean`) for `2d ≤ k + 1`
(each defect is counted in at most `2d` windows) and the Taylor bound for the other indices give
(63) in the form `S_d ≤ (cλ)^d S_{2d} + 5 d c^d λ R^{2d}`. If `100 c² λ R² < 1`, the dyadic
summation `Analysis.le_of_dyadic_recursion` with `x = cλ`, `y = c²λR²` gives `S₁ ≤ 5/90`, and
Lemma 3.9 (`sum_meanGradSq_iter_le`) gives `Σ_{k<N} p_k ≤ 1.21 λ² + 3λ S₁ < λ/2` since `λ ≤ 1/100`,
contradicting `Σ_{k<N} p_k = v₀ - v_N > λ/2` from (36). Hence `C ≤ 100 c² R²`.

The source uses the exact eigenfunction (`v₁ = λ₁`, `‖Lh₁‖ = λ₁`, `α² ≤ 2λ₁`) and obtains
`S_d ≤ (Cλ₁)^d S_{2d} + 4d C^d λ₁ R^{2d}`; here the factors `1.1`, `1.21`, `3` and `5` absorb the
approximation, as recorded in the decision record. The statement of Theorem 3.1 is unchanged.

## What this is not

The explicit value of `K` is a by-product of this proof and is not optimized; Theorem 3.1 only
asserts that some universal `K` exists, and the source does not compute one. Centering of `ν` is not
used in `taylorCriterion`: the second-moment bound `∫ ⟪v, x⟫² dν ≤ ‖v‖²` is what Lemma 3.9 needs;
`poincare_le_of_taylor` keeps the source's centering hypothesis. This is Theorem 3.1 for regular
laws only; Theorem 1.1 (the KLS bound) is not addressed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

/-! ### The final argument for real sequences -/

section Scalar

/-- Each index `j < M` lies in at most `L` of the windows `[k + 1 - L, k)`, `k < M`. -/
private theorem sum_window_le {χ : ℕ → ℝ} (hχ : ∀ j, 0 ≤ χ j) (L M : ℕ) :
    ∑ k ∈ range M, ∑ j ∈ Ico (k + 1 - L) k, χ j ≤ L * ∑ j ∈ range M, χ j := by
  rw [Finset.sum_comm' (t' := range M)
    (s' := fun j => (range M).filter fun k => k + 1 - L ≤ j ∧ j < k)
    (fun k j => by simp only [mem_range, mem_Ico, mem_filter]; omega), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hχ j)
  have hsub : (range M).filter (fun k => k + 1 - L ≤ j ∧ j < k) ⊆ Ioc j (j + L) := by
    intro k hk
    simp only [mem_filter, mem_range, mem_Ioc] at hk ⊢
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc, Nat.add_sub_cancel_left] at hcard
  exact_mod_cast hcard

/-- The first index `N` with `v_N < λ/2` (the source's (53), shifted by one). -/
private theorem exists_first_small {v : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hvlim : Tendsto v atTop (𝓝 0)) :
    ∃ N, v N < l / 2 ∧ ∀ k < N, l / 2 ≤ v k := by
  have hex : ∃ N, v N < l / 2 :=
    ((hvlim.eventually (gt_mem_nhds (half_pos hl))).exists)
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
  exact not_lt.mp (Nat.find_min hex hk)

/-- The step bounds (54) for the steps before `N`: if `v_{j+1} ≥ λ/2` then `α_j > 0` and
`α_j² ≤ 3λ`, from (46), `‖L h‖² ≤ ‖L h₁‖² ≤ (1.1 λ)²` and `α_j ≥ 0`. -/
private theorem scale_bounds {C : ℝ} {v L α : ℕ → ℝ} (hC : 0 < C)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0) {j : ℕ}
    (hvj : C⁻¹ / 2 ≤ v (j + 1)) : 0 < α j ∧ α j ^ 2 ≤ 3 / C := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  refine ⟨lt_of_le_of_ne (hα j) fun h => ?_, ?_⟩
  · have := hα0 j h.symm
    linarith
  · have hLj : L (j + 1) ≤ L 0 := antitone_nat_of_succ_le hL (Nat.zero_le _)
    have h1 : α j ^ 2 * (C⁻¹ / 2) ≤ (11 / 10 * C⁻¹) ^ 2 := by
      calc α j ^ 2 * (C⁻¹ / 2) ≤ α j ^ 2 * v (j + 1) :=
            mul_le_mul_of_nonneg_left hvj (sq_nonneg _)
        _ = L (j + 1) := (h46 j).symm
        _ ≤ _ := hLj.trans hL0
    rw [div_eq_mul_inv]
    by_contra hcon
    replace hcon := not_le.mp hcon
    have h2 := mul_lt_mul_of_pos_right hcon (half_pos hl)
    nlinarith

/-- `v_{k+1} ≤ 1.21 λ` for every `k`: by (32) and (46), `λ v_{k+1} ≤ α_k² v_{k+1} = ‖L h‖² ≤
(1.1 λ)²` when `α_k > 0`, and `v_{k+1} = 0` when `α_k = 0`. -/
private theorem energy_succ_le {C : ℝ} {v L α : ℕ → ℝ} (hC : 0 < C) (hv : ∀ k, 0 ≤ v k)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
    (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2) (k : ℕ) :
    v (k + 1) ≤ 121 / 100 * C⁻¹ := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  rcases (hα k).eq_or_lt with h0 | hpos
  · rw [hα0 k h0.symm]
    positivity
  · have hLk : L (k + 1) ≤ L 0 := antitone_nat_of_succ_le hL (Nat.zero_le _)
    have h1 : C⁻¹ * v (k + 1) ≤ C⁻¹ * (121 / 100 * C⁻¹) := by
      calc C⁻¹ * v (k + 1) ≤ α k ^ 2 * v (k + 1) :=
            mul_le_mul_of_nonneg_right (h32 k hpos) (hv _)
        _ = L (k + 1) := (h46 k).symm
        _ ≤ (11 / 10 * C⁻¹) ^ 2 := hLk.trans hL0
        _ = C⁻¹ * (121 / 100 * C⁻¹) := by ring
    exact le_of_mul_le_mul_left h1 hl

/-- **The recursion (63)** in the operator route. With `λ = 1/C`,
`S_d = Σ_{k < N - d} t_d(k)`, the Lemma 3.8 bound `hJ1` for `2d ≤ k + 1` and the crude bound
`t_d(k) ≤ R^{2d} v_{k+1} ≤ 1.21 λ R^{2d}` for the at most `2d` remaining indices give
`S_d ≤ (cλ)^d S_{2d} + 5 d c^d λ R^{2d}`. -/
private theorem recursion {C c R : ℝ} {v χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ} {N d : ℕ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R) (hd : 1 ≤ d)
    (hvk : ∀ k, v (k + 1) ≤ 121 / 100 * C⁻¹)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2)
    (hαN : ∀ j, j + 1 < N → 0 < α j ∧ α j ^ 2 ≤ 3 / C)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j) :
    ∑ k ∈ range (N - d), t d k ≤
      (c / C) ^ d * ∑ k ∈ range (N - 2 * d), t (2 * d) k +
        5 * d * c ^ d * C⁻¹ * R ^ (2 * d) := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  have hcd : 1 ≤ c ^ d := one_le_pow₀ hc
  have hRd : 0 ≤ R ^ (2 * d) := by positivity
  set P : ℕ → Prop := fun k => 2 * d ≤ k + 1 with hP
  set W : ℕ → ℝ := fun k => ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j with hW
  have hW0 : ∀ k, 0 ≤ W k := fun k => Finset.sum_nonneg fun j _ => hχ j
  rw [← Finset.sum_filter_add_sum_filter_not (range (N - d)) P]
  -- the indices `k + 1 ≥ 2d`, where Lemma 3.8 applies
  have hA : ∑ k ∈ (range (N - d)).filter P, t d k ≤
      (c / C) ^ d * ∑ k ∈ range (N - 2 * d), t (2 * d) k +
        c ^ d * R ^ (2 * d) * C * (2 * d * (11 / 10 * C⁻¹) ^ 2) := by
    have h1 : ∑ k ∈ (range (N - d)).filter P, t d k ≤
        ∑ k ∈ (range (N - d)).filter P,
          ((c / C) ^ d * t (2 * d) (k - d) + c ^ d * R ^ (2 * d) * C * W k) := by
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [mem_filter, mem_range, hP] at hk
      exact hJ1 k d hd hk.2 fun j hj => hαN j (by omega)
    have h2 : ∑ k ∈ (range (N - d)).filter P, t (2 * d) (k - d) ≤
        ∑ k ∈ range (N - 2 * d), t (2 * d) k := by
      rw [← Finset.sum_image (g := fun k => k - d) (f := t (2 * d)) (fun x hx y hy hxy => by
        simp only [mem_filter, mem_range, hP, mem_coe] at hx hy
        simp only at hxy
        omega)]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => ht _ _
      simp only [mem_image, mem_filter, mem_range, hP] at hi ⊢
      omega
    have h3 : ∑ k ∈ (range (N - d)).filter P, W k ≤ 2 * d * (11 / 10 * C⁻¹) ^ 2 := by
      calc ∑ k ∈ (range (N - d)).filter P, W k ≤ ∑ k ∈ range (N - d), W k :=
            Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => hW0 k
        _ ≤ ((2 * d : ℕ) : ℝ) * ∑ j ∈ range (N - d), χ j := sum_window_le hχ _ _
        _ ≤ ((2 * d : ℕ) : ℝ) * L 0 := mul_le_mul_of_nonneg_left (hχsum _) (by positivity)
        _ ≤ ((2 * d : ℕ) : ℝ) * (11 / 10 * C⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_left hL0 (by positivity)
        _ = 2 * d * (11 / 10 * C⁻¹) ^ 2 := by push_cast; ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have hcC : 0 ≤ (c / C) ^ d := by positivity
    have hcR : 0 ≤ c ^ d * R ^ (2 * d) * C := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hcC, mul_le_mul_of_nonneg_left h3 hcR]
  -- the indices `k + 1 < 2d`, at most `2d` of them, each at most `1.21 λ R^{2d}`
  have hB : ∑ k ∈ (range (N - d)).filter (fun k => ¬ P k), t d k ≤
      2 * d * (R ^ (2 * d) * (121 / 100 * C⁻¹)) := by
    have hcard : (((range (N - d)).filter (fun k => ¬ P k)).card : ℝ) ≤ 2 * d := by
      have hsub : (range (N - d)).filter (fun k => ¬ P k) ⊆ range (2 * d) := by
        intro k hk
        simp only [mem_filter, mem_range, hP] at hk ⊢
        omega
      have := Finset.card_le_card hsub
      rw [card_range] at this
      exact_mod_cast this
    calc ∑ k ∈ (range (N - d)).filter (fun k => ¬ P k), t d k
        ≤ ((range (N - d)).filter (fun k => ¬ P k)).card • (R ^ (2 * d) * (121 / 100 * C⁻¹)) :=
          Finset.sum_le_card_nsmul _ _ _ fun k _ =>
            (htaylor d k hd).trans (mul_le_mul_of_nonneg_left (hvk k) hRd)
      _ ≤ 2 * d * (R ^ (2 * d) * (121 / 100 * C⁻¹)) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hCl : C * (11 / 10 * C⁻¹) ^ 2 = 121 / 100 * C⁻¹ := by
    field_simp
    ring
  have hX : 0 ≤ d * R ^ (2 * d) * C⁻¹ := by positivity
  have hcX := mul_le_mul_of_nonneg_left hcd hX
  have hE : c ^ d * R ^ (2 * d) * C * (2 * d * (11 / 10 * C⁻¹) ^ 2) =
      242 / 100 * (c ^ d * (d * R ^ (2 * d) * C⁻¹)) := by
    rw [show c ^ d * R ^ (2 * d) * C * (2 * d * (11 / 10 * C⁻¹) ^ 2) =
      2 * d * c ^ d * R ^ (2 * d) * (C * (11 / 10 * C⁻¹) ^ 2) by ring, hCl]
    ring
  rw [hE] at hA
  nlinarith

/-- The recursion (63) multiplied by `(cλ)^{d-1}`, in the form of `le_of_dyadic_recursion` with
`x = cλ`, `y = c²λR²` and `A = 5`. -/
private theorem dyadic_step {C c R : ℝ} {S : ℕ → ℝ} (hC : 0 < C) (hc : 1 ≤ c) {d : ℕ}
    (hd : 1 ≤ d)
    (hrec : S d ≤ (c / C) ^ d * S (2 * d) + 5 * d * c ^ d * C⁻¹ * R ^ (2 * d)) :
    (c * C⁻¹) ^ (d - 1) * S d ≤ (c * C⁻¹) ^ (2 * d - 1) * S (2 * d) +
      5 * d * (c ^ 2 * C⁻¹ * R ^ 2) ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have hx : 0 ≤ (c * C⁻¹) ^ e := by have := inv_pos.mpr hC; positivity
  rw [div_eq_mul_inv] at hrec
  rw [Nat.add_sub_cancel, show 2 * (e + 1) - 1 = 2 * e + 1 by omega]
  have h1 := mul_le_mul_of_nonneg_left hrec hx
  have hY : 0 ≤ (c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ * R ^ (2 * (e + 1)) := by
    have := inv_pos.mpr hC
    have : 0 ≤ c := by linarith
    have : 0 ≤ R ^ (2 * (e + 1)) := by rw [pow_mul]; positivity
    positivity
  have h2 : (c ^ 2 * C⁻¹ * R ^ 2) ^ (e + 1) =
      c * ((c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ * R ^ (2 * (e + 1))) := by ring
  have h3 := mul_le_mul_of_nonneg_right hc hY
  have he : (0 : ℝ) ≤ (e + 1 : ℕ) := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 he
  calc (c * C⁻¹) ^ e * S (e + 1)
      ≤ (c * C⁻¹) ^ e * ((c * C⁻¹) ^ (e + 1) * S (2 * (e + 1)) +
          5 * ((e + 1 : ℕ) : ℝ) * c ^ (e + 1) * C⁻¹ * R ^ (2 * (e + 1))) := h1
    _ = (c * C⁻¹) ^ (2 * e + 1) * S (2 * (e + 1)) +
          5 * (((e + 1 : ℕ) : ℝ) * (1 * ((c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ *
            R ^ (2 * (e + 1))))) := by ring
    _ ≤ (c * C⁻¹) ^ (2 * e + 1) * S (2 * (e + 1)) +
          5 * (((e + 1 : ℕ) : ℝ) * (c * ((c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ *
            R ^ (2 * (e + 1))))) := by linarith
    _ = (c * C⁻¹) ^ (2 * e + 1) * S (2 * (e + 1)) +
          5 * ((e + 1 : ℕ) : ℝ) * (c ^ 2 * C⁻¹ * R ^ 2) ^ (e + 1) := by rw [h2]; ring

/-- **The final argument of BKL Theorem 3.1, for real sequences** (arXiv:2610.05474v1, p. 17,
in the operator route).

The sequences are the scalar quantities of the iterates `h_{k+1}` of one approximate
eigenfunction, `λ = 1/C`: `v k` the energy `‖∇h_{k+1}‖²`, `p k` the drop `|∫∇h_{k+1}|²`, `χ k` the
defect, `L k = ‖L h_{k+1}‖²`, `α k = α_{k+2}` and `t d k = |T_d(∇₀h_{k+1})|²`. The hypotheses are
(36), `v₀ ≥ λ`, `v_k → 0` and `Σ χ ≤ ‖L h₁‖² ≤ (1.1 λ)²` (Corollary 3.5), the monotonicity of
`‖L h‖²` (Lemma 3.4), (46), (32), `α ≥ 0` with `α_k = 0 ⇒ v_{k+1} = 0`, the Taylor bound
`t_d(k) ≤ R^{2d} v_{k+1}` ((29) and (33)), Lemma 3.8 with constant `c ≥ 1` and Lemma 3.9 (both
with `β = 3`). Then `C ≤ 100 c² R²`. -/
theorem le_of_iterate_bounds {C c R : ℝ} {v p χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R)
    (hv : ∀ k, 0 ≤ v k) (hv0 : C⁻¹ ≤ v 0) (hvlim : Tendsto v atTop (𝓝 0))
    (h36 : ∀ N, v 0 = v N + ∑ k ∈ range N, p k)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
    (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j)
    (hJ2 : ∀ N, (∀ j, j + 1 < N → α j ^ 2 ≤ 3 / C) →
      ∑ k ∈ range N, p k ≤ L 0 + 3 / C * ∑ k ∈ range (N - 1), t 1 k) :
    C ≤ 100 * c ^ 2 * R ^ 2 := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  obtain ⟨N, hN, hmin⟩ := exists_first_small hl hvlim
  have hαN : ∀ j, j + 1 < N → 0 < α j ∧ α j ^ 2 ≤ 3 / C := fun j hj =>
    scale_bounds hC hL0 hL h46 hα hα0 (hmin _ hj)
  have hvk := energy_succ_le hC hv hL0 hL h46 hα hα0 h32
  set S : ℕ → ℝ := fun d => ∑ k ∈ range (N - d), t d k with hS
  by_contra hcon
  replace hcon := not_le.mp hcon
  -- the contradiction hypothesis (64): `y = c²λR² < 1/100`
  have hc0 : 0 < c := by linarith
  have hy : c ^ 2 * C⁻¹ * R ^ 2 < 1 / 100 := by
    have h1 : c ^ 2 * C⁻¹ * R ^ 2 = (100 * c ^ 2 * R ^ 2) * C⁻¹ / 100 := by ring
    rw [h1, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 100)]
    calc 100 * c ^ 2 * R ^ 2 * C⁻¹ < C * C⁻¹ := mul_lt_mul_of_pos_right hcon hl
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have hy0 : 0 ≤ c ^ 2 * C⁻¹ * R ^ 2 := by positivity
  have hcR : 1 ≤ c ^ 2 * R ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc)
    (one_le_pow₀ hR)
  have hlam : C⁻¹ ≤ 1 / 100 := by nlinarith
  -- the dyadic summation of (63) gives `S₁ ≤ 5/90`
  have hS1 : S 1 ≤ 5 / 90 := by
    refine Analysis.le_of_dyadic_recursion (N := N) (x := c * C⁻¹) (A := 5)
      (fun d hd => ?_) (by norm_num) hy0 (by linarith) fun d hd => ?_
    · simp only [hS, Nat.sub_eq_zero_of_le hd, range_zero, sum_empty]
    · exact dyadic_step hC hc hd
        (recursion hC hc hR hd hvk hχ hχsum hL0 hαN ht htaylor hJ1)
  -- Lemma 3.9 against (36): `λ/2 < Σ p ≤ 1.21 λ² + 3 λ S₁ < λ/2`
  have hp := hJ2 N fun j hj => (hαN j hj).2
  have h36N := h36 N
  have hpS : 3 / C * S 1 ≤ 3 / C * (5 / 90) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hsq : (11 / 10 * C⁻¹) ^ 2 ≤ 121 / 100 * (C⁻¹ * (1 / 100)) := by
    have := mul_le_mul_of_nonneg_left hlam hl.le
    nlinarith
  rw [div_eq_mul_inv] at hpS
  change ∑ k ∈ range N, p k ≤ L 0 + 3 / C * S 1 at hp
  rw [div_eq_mul_inv] at hp
  linarith

end Scalar

/-! ### The criterion in the heat model -/

/-- The universal constant of BKL Theorem 3.1 obtained here: `K = 100 c²` with
`c = 2^20 max(1, 3)² = 9 · 2^20`, the constant of Lemma 3.8 at `β = 3`. -/
def taylorCriterionConstant : ℝ := 100 * (2 ^ 20 * max 1 3 ^ 2) ^ 2

section HeatModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "Tbar" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- The scale `α` is nonnegative, and `α_k = 0` forces `v_{k+1} = 0`. -/
private theorem scale_nonneg_and_energy (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    0 ≤ scale Tbar (iter Tbar f k) ∧
      (scale Tbar (iter Tbar f k) = 0 → energy Tbar (iter Tbar f (k + 1)) = 0) := by
  refine ⟨?_, fun h0 => ?_⟩
  · unfold scale
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  · rw [iter_succ, step, energy_smul, h0]
    ring

/-- The initial data of the iterates from an approximate eigenfunction `‖A f - λ f‖ ≤ λ/10`,
`λ = 1/C`, centered and of norm one: `v₀ = ‖∇f‖² ≥ λ` (the Poincaré gap) and
`‖L h₁‖² = ‖A f‖² ≤ (1.1 λ)²`. -/
private theorem initial_bounds {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))
    (f : (adjointComp Tbar).domain) (hfm : L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0)
    (hfn : ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1)
    (hfA : ‖adjointComp Tbar f - (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤
      (C : ℝ)⁻¹ * (1 / 10)) :
    (C : ℝ)⁻¹ ≤ energy Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) 0) ∧
      normSq (genField Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) 0)) ≤
        (11 / 10 * (C : ℝ)⁻¹) ^ 2 := by
  have hC0 : (0 : ℝ) ≤ (C : ℝ)⁻¹ := inv_nonneg.mpr (NNReal.coe_nonneg C)
  constructor
  · rw [energy_eq_sum, Fintype.sum_unique, iter_zero]
    have hgap := norm_sq_le_weakGrad m hν hi hC f.2.2 hfm
    rw [hfn, one_pow] at hgap
    rcases (NNReal.coe_nonneg C).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul] at hgap
      norm_num at hgap
    · calc (C : ℝ)⁻¹ = (C : ℝ)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (C : ℝ)⁻¹ * ((C : ℝ) * ‖weakGrad Tbar (f : Lp ℝ 2 (ν : Measure V))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hgap hC0
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  · rw [normSq, Fintype.sum_unique, genField, iter_zero, gen_of_mem _ f.2, Subtype.coe_eta]
    have h1 : ‖adjointComp Tbar f‖ ≤ 11 / 10 * (C : ℝ)⁻¹ := by
      calc ‖adjointComp Tbar f‖ ≤ ‖adjointComp Tbar f - (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ +
            ‖(C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ := norm_le_norm_sub_add _ _
        _ ≤ (C : ℝ)⁻¹ * (1 / 10) + (C : ℝ)⁻¹ := by
          rw [norm_smul, hfn, mul_one, Real.norm_of_nonneg hC0]
          linarith
        _ = 11 / 10 * (C : ℝ)⁻¹ := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

include hν hi in
/-- The core of the criterion: if `C_P(ν) = C > 0`, then `C ≤ K R²`, by running the iterates of
an approximate eigenfunction (`exists_centered_approx_eigenfunction`, `η = 1/10`) through
`le_of_iterate_bounds`. -/
private theorem coe_le_of_eq
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {R : ℝ} (hR : 1 ≤ R)
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖)
    {C : NNReal} (hCpos : 0 < C) (hCP : Poincare.LocalSlope.Intrinsic.optimalConstant ν = (C : ENNReal)) :
    (C : ℝ) ≤ taylorCriterionConstant * R ^ 2 := by
  have hU2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨f, hfm, hfn, hfA⟩ := exists_centered_approx_eigenfunction m hν hi hνU hU2 hCpos hCP
    (η := 1 / 10) (by norm_num)
  have hCle := hCP.le
  have hF : (f : Lp ℝ 2 (ν : Measure V)) ∈ (adjointComp Tbar).domain := f.2
  obtain ⟨hv0, hL0⟩ := initial_bounds m hν hi hCle f hfm hfn hfA
  have hc : (1 : ℝ) ≤ 2 ^ 20 * max 1 3 ^ 2 := by norm_num
  have key := le_of_iterate_bounds
    (v := fun k => energy Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k))
    (p := fun k => meanGradSq Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k))
    (χ := fun k => defect Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k))
    (L := fun k => normSq (genField Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k)))
    (α := fun k => scale Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k))
    (t := fun d k => ‖taylorField d (grad0 Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k))‖ ^ 2)
    (NNReal.coe_pos.mpr hCpos) hc hR (fun k => energy_nonneg _ _) hv0
    (tendsto_energy_iter_zero m hν hi hνU hU hexp hCle ha hUa hF)
    (energy_iter_zero_eq m hν hi hνU hU2 hCle _) (fun k => normSq_nonneg _)
    (sum_defect_iter_le m hν hi hνU hU hexp hCle ha.le hUa hF) hL0
    (fun k => by
      have h5 := normSq_genField_iter_succ_add_defect_le m hν hi hνU hU hexp hCle hUa hF k
      have h6 : 0 ≤ defect Tbar (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k) := normSq_nonneg _
      have h7 := mul_nonneg ha.le (energy_nonneg (Tbar) (iter Tbar (f : Lp ℝ 2 (ν : Measure V)) k))
      linarith)
    (normSq_genField_iter_succ m hν hi hνU hU2 hCle _)
    (fun k => (scale_nonneg_and_energy m hν hi _ k).1)
    (fun k => (scale_nonneg_and_energy m hν hi _ k).2)
    (fun k hs => inv_le_scale_sq m hν hi hνU hU2 hCle hCpos _ k hs)
    (fun d k => sq_nonneg _)
    (fun d k hd => by
      rw [energy_iter_succ m hν hi hνU hU2 hCle]
      exact norm_taylorField_sq_le (fun g => h29 g d hd) _)
    (fun k d hd hdk hα => norm_taylorField_grad0_iter_sq_le m hν hi hνU hU hexp hCle hCpos h29 hF
      (β := 3) k d hd hdk hα)
    (fun N hN => sum_meanGradSq_iter_le m hν hi hνU hU2 hexp hCle hcov hF (β := 3) N hN)
  rw [taylorCriterionConstant]
  linarith

include hν hi in
/-- **BKL Theorem 3.1 in the heat model** (arXiv:2610.05474v1, p. 10, proof p. 17, in the
operator route). Let `ν = m.tilted (-U)` with `U` of temperate growth, all exponential moments,
`∇²U ≥ a > 0` and `∫ ⟪v, x⟫² dν ≤ ‖v‖²` for every `v` (for centered `ν`, this is `Cov ν ≤ Id`),
and let `R ≥ 1` satisfy the Taylor bound (29) for every `u ∈ L²(ν)` in the Hilbert–Schmidt norm
of the standard basis. Then `C_P(ν) ≤ K R²` with `K = taylorCriterionConstant`.

`C_P(ν) ≤ 1/a` is finite (`literatureConstant_le_inv`); the case `C_P(ν) = 0` is trivial, and
otherwise the iterates of an approximate first eigenfunction give the bound through
`le_of_iterate_bounds`, with Lemma 3.8 from `norm_taylorField_grad0_iter_sq_le` and Lemma 3.9
from `sum_meanGradSq_iter_le`. Centering of `ν` is not needed. -/
theorem taylorCriterion
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {R : ℝ} (hR : 1 ≤ R)
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖) :
    Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤
      ENNReal.ofReal (taylorCriterionConstant * R ^ 2) := by
  have hU2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfin := literatureConstant_le_inv m hν hi hνU hU2 ha hUa
  have hne : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
  set C : NNReal := (Poincare.LocalSlope.Intrinsic.optimalConstant ν).toNNReal with hCdef
  have hCP : Poincare.LocalSlope.Intrinsic.optimalConstant ν = (C : ENNReal) :=
    (ENNReal.coe_toNNReal hne).symm
  rcases eq_zero_or_pos C with hC0 | hCpos
  · rw [hCP, hC0, ENNReal.coe_zero]
    exact zero_le
  · rw [hCP, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (coe_le_of_eq m hν hi hνU hU hexp ha hUa hcov hR
      h29 hCpos hCP)

end HeatModel

end FunctionalInequalities.KLS.LogConcave.PoissonIterate

/-! ### Theorem 3.1 for regular laws -/

namespace FunctionalInequalities.KLS.RegularPotential

open FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate

/-- **BKL Theorem 3.1** (arXiv:2610.05474v1, p. 10, proof p. 17), the exact
statement, with `K = taylorCriterionConstant`: for every regular potential
`V` on `ℝⁿ` (BKL (12)) whose law `μ` is centered with `Cov μ ≤ Id`, and every `R ≥ 1` with
`|T_d f| ≤ R^d ‖f‖_{L²(μ)}` for all `f ∈ L²(μ)` and `d ≥ 1` (29) (Hilbert–Schmidt norm in the
standard basis), `C_P(μ) ≤ K R²`.

The law is `volume.tilted (-V)`; (29) passes from functions to `L²` classes (`Lp.memLp`,
`Lp.norm_def`) and from `EuclideanSpace.basisFun` to `stdOrthonormalBasis`
(`norm_coordTensor_eq`), and `taylorCriterion` applies; the centering hypothesis is not used. -/
theorem poincare_le_of_taylor :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
          (hV : KLS.RegularPotential V a b),
          (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n)))) = 0 →
            (∀ v : EuclideanSpace ℝ (Fin n),
                ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2) →
              ∀ R : ℝ,
                1 ≤ R →
                  (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
                      MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n))) →
                        ∀ d : ℕ,
                          1 ≤ d →
                            ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                                  (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f
                                    d)‖ ≤
                              R ^ d *
                                (eLpNorm f 2
                                    (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal) →
                    Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤
                      ENNReal.ofReal (K * R ^ 2) := by
  refine
    ⟨taylorCriterionConstant, by norm_num [taylorCriterionConstant],
      fun n V a b hV _ hcov R hR h29 => ?_⟩
  have hνU : (hV.law : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-V) := rfl
  refine
    taylorCriterion volume hV.logConcave_law hV.interior_support_law hνU hV.temperate
      hV.integrable_exp_mul_norm hV.pos hV.lower hcov hR (fun u d hd => ?_)
  rw [norm_coordTensor_eq _ (EuclideanSpace.basisFun (Fin n) ℝ), Lp.norm_def]
  exact h29 u (Lp.memLp u) d hd

end FunctionalInequalities.KLS.RegularPotential
