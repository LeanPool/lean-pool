/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Real analyticity from factorial bounds on the derivatives

The quantitative analyticity of `eq:analytic:slice:force` and `eq:analytic:interior:velocity`
is a family of bounds `‖∂^α u‖ ≤ M a^{-|α|} |α|!` on the derivatives. The identity theorem, on
the other hand, is stated for Mathlib's `AnalyticOnNhd`. This file supplies the missing
implication: a smooth function whose iterated derivatives obey `‖D^n f‖ ≤ C K^n n!` on a ball
is real analytic there.

The proof is the classical one. Taylor's formula with the integral remainder,
`map_add_eq_sum_add_integral_iteratedFDeriv`, writes the difference between `f (x + y)` and the
`n`-th Taylor polynomial as an integral over the segment `[x, x + y]`; the factorial bound makes
that remainder at most `C (n + 1) (K‖y‖)^{n + 1}`, which tends to `0` as soon as `K‖y‖ < 1`.
The same bound makes the Taylor series absolutely convergent on that ball, so its sum is
`f (x + y)`, which is a power series expansion of `f` at `x`.

Mathlib has the converse implication (`AnalyticAt` gives Cauchy estimates on the iterated
derivatives) but not this direction, so the criterion is proved here from Taylor's formula.

The last section restricts a space-time field to one time slice, which is the form in which the
criterion is applied to the velocity.
-/

public section

open Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

section Criterion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The Taylor remainder of order `n` at `x` in the direction `y`, estimated from factorial
bounds on the iterated derivatives along the segment from `x` to `x + y`. -/
theorem norm_sub_taylorSum_le {f : E → F} {x y : E} {C K r : ℝ} (n : ℕ)
    (hy : ‖y‖ < r)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball x r))
    (hbound : ∀ m : ℕ, ∀ z ∈ Metric.ball x r,
      ‖iteratedFDeriv ℝ m f z‖ ≤ C * K ^ m * (Nat.factorial m)) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖
      ≤ C * ((n + 1 : ℕ) : ℝ) * (K * ‖y‖) ^ (n + 1) := by
  have hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → x + t • y ∈ Metric.ball x r := by
    intro t ht
    have h : ‖t • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt h hy
  have hcd : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ContDiffAt ℝ (n + 1) f (x + t • y) := fun t ht =>
    (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hseg t ht))).of_le (by exact_mod_cast le_top)
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := y) (n := n) hcd
  have hintegrand : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
        ≤ C * K ^ (n + 1) * (Nat.factorial (n + 1)) * ‖y‖ ^ (n + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hop : ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
        ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ‖y‖ ^ (n + 1) := by
      simpa [Finset.prod_const] using
        (iteratedFDeriv ℝ (n + 1) f (x + t • y)).le_opNorm (fun _ : Fin (n + 1) => y)
    have hb := hbound (n + 1) _ (hseg t ht')
    have habs : |1 - t| ^ n ≤ 1 := by
      refine pow_le_one₀ (abs_nonneg _) ?_
      rw [abs_of_nonneg (by linarith only [ht.2] : (0 : ℝ) ≤ 1 - t)]
      linarith only [ht.1]
    calc ‖(1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
        = |1 - t| ^ n * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ 1 * (C * K ^ (n + 1) * (Nat.factorial (n + 1)) * ‖y‖ ^ (n + 1)) := by
          gcongr
          exact le_trans hop (by gcongr)
      _ = C * K ^ (n + 1) * (Nat.factorial (n + 1)) * ‖y‖ ^ (n + 1) := one_mul _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hintegrand
  have hfac : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rw [htaylor, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_natCast]
  calc (Nat.factorial n : ℝ)⁻¹ *
        ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
      ≤ (Nat.factorial n : ℝ)⁻¹ *
          (C * K ^ (n + 1) * (Nat.factorial (n + 1)) * ‖y‖ ^ (n + 1) * |(1 : ℝ) - 0|) := by
        gcongr
    _ = C * ((n + 1 : ℕ) : ℝ) * (K * ‖y‖) ^ (n + 1) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring

/-- **Real analyticity from factorial bounds on the iterated derivatives.** A smooth function
whose iterated derivatives satisfy `‖D^n f‖ ≤ C K^n n!` on a ball around `x` is real analytic
at `x`: its Taylor series at `x` converges to it on the ball of radius `min r K⁻¹`. -/
theorem analyticAt_of_norm_iteratedFDeriv_le {f : E → F} {x : E} {C K r : ℝ}
    (hr : 0 < r) (hK : 0 < K)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball x r))
    (hbound : ∀ n : ℕ, ∀ z ∈ Metric.ball x r,
      ‖iteratedFDeriv ℝ n f z‖ ≤ C * K ^ n * (Nat.factorial n)) :
    AnalyticAt ℝ f x := by
  have hC : 0 ≤ C := by
    have h0 := hbound 0 x (Metric.mem_ball_self hr)
    simpa using le_trans (norm_nonneg _) h0
  have hpn : ∀ n : ℕ, ‖(Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x‖ ≤ C * K ^ n := by
    intro n
    have hfac : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
    rw [norm_smul, norm_inv, Real.norm_natCast]
    calc (Nat.factorial n : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n f x‖
        ≤ (Nat.factorial n : ℝ)⁻¹ * (C * K ^ n * Nat.factorial n) := by
          gcongr
          exact hbound n x (Metric.mem_ball_self hr)
      _ = C * K ^ n := by field_simp
  set ρ : ℝ := min r K⁻¹ with hρdef
  have hρpos : 0 < ρ := lt_min hr (inv_pos.2 hK)
  have hKρ : K * ρ ≤ 1 := by
    have h : ρ ≤ K⁻¹ := min_le_right _ _
    calc K * ρ ≤ K * K⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hK.ne'
  refine ⟨fun n => (Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x, ENNReal.ofReal ρ, ?_, ?_, ?_⟩
  · have hcoe : ENNReal.ofReal ρ = ((ρ.toNNReal : NNReal) : ℝ≥0∞) := rfl
    rw [hcoe]
    refine FormalMultilinearSeries.le_radius_of_bound _ C fun n => ?_
    rw [Real.coe_toNNReal ρ hρpos.le]
    calc ‖(Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x‖ * ρ ^ n
        ≤ (C * K ^ n) * ρ ^ n := by gcongr; exact hpn n
      _ = C * (K * ρ) ^ n := by rw [mul_pow]; ring
      _ ≤ C * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) hKρ
      _ = C := mul_one C
  · exact ENNReal.ofReal_pos.2 hρpos
  · intro y hy
    have hynorm : ‖y‖ < ρ := by
      have h1 : ‖y‖ₑ < ENNReal.ofReal ρ := mem_eball_zero_iff.1 hy
      rw [← ofReal_norm] at h1
      exact (ENNReal.ofReal_lt_ofReal_iff hρpos).1 h1
    have hyr : ‖y‖ < r := lt_of_lt_of_le hynorm (min_le_left _ _)
    have hq1 : K * ‖y‖ < 1 := by
      have h : ‖y‖ < K⁻¹ := lt_of_lt_of_le hynorm (min_le_right _ _)
      calc K * ‖y‖ < K * K⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hK.ne'
    have hq0 : (0 : ℝ) ≤ K * ‖y‖ := by positivity
    have hterm : ∀ n : ℕ,
        ‖(Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x (fun _ => y)‖
          ≤ C * (K * ‖y‖) ^ n := by
      intro n
      have hop : ‖iteratedFDeriv ℝ n f x (fun _ => y)‖
          ≤ ‖iteratedFDeriv ℝ n f x‖ * ‖y‖ ^ n := by
        simpa [Finset.prod_const] using
          (iteratedFDeriv ℝ n f x).le_opNorm (fun _ : Fin n => y)
      have hfac : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
      rw [norm_smul, norm_inv, Real.norm_natCast]
      calc (Nat.factorial n : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n f x (fun _ => y)‖
          ≤ (Nat.factorial n : ℝ)⁻¹ * ((C * K ^ n * Nat.factorial n) * ‖y‖ ^ n) := by
            gcongr
            exact le_trans hop (by gcongr; exact hbound n x (Metric.mem_ball_self hr))
        _ = C * (K * ‖y‖) ^ n := by rw [mul_pow]; field_simp
    have hsummable : Summable
        (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x (fun _ => y)) := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm ?_)
      exact (summable_geometric_of_lt_one hq0 hq1).mul_left C
    have hshift : Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
          (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)) atTop
        (𝓝 (∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x (fun _ => y))) :=
      hsummable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hbnd : Tendsto (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ) * (K * ‖y‖) ^ (n + 1)))
        atTop (𝓝 0) := by
      have h := ((tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp
        (tendsto_add_atTop_nat 1)).const_mul C
      simpa using h
    have hftendsto : Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
          (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)) atTop
        (𝓝 (f (x + y))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbnd
      rw [norm_sub_rev, ← mul_assoc]
      exact norm_sub_taylorSum_le n hyr hf hbound
    have hsum : (∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f x (fun _ => y))
        = f (x + y) := tendsto_nhds_unique hshift hftendsto
    have hres := hsummable.hasSum
    rw [hsum] at hres
    simpa using hres

/-- The same criterion on an open set, with one pair of constants for the whole set. -/
theorem analyticOnNhd_of_norm_iteratedFDeriv_le {f : E → F} {s : Set E} {C K : ℝ}
    (hs : IsOpen s) (hK : 0 < K) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (hbound : ∀ n : ℕ, ∀ z ∈ s, ‖iteratedFDeriv ℝ n f z‖ ≤ C * K ^ n * (Nat.factorial n)) :
    AnalyticOnNhd ℝ f s := by
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 hs x hx
  exact analyticAt_of_norm_iteratedFDeriv_le hr hK (hf.mono hrs) fun n z hz =>
    hbound n z (hrs hz)

end Criterion

section Vec3Ball

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Analyticity on a ball from locally uniform factorial bounds.** This is the shape in which
the quantitative analyticity `eq:analytic:interior:velocity` is available: on every ball
`B(R')` compactly contained in `B(R)` the iterated derivatives obey a factorial bound, with
constants allowed to degenerate as `R' ↑ R`. The conclusion is analyticity on all of `B(R)`. -/
theorem analyticOnNhd_vec3Ball_of_iteratedFDeriv_bound {G : Vec3 → F} {R : ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (vec3Ball 0 R))
    (hbound : ∀ R' : ℝ, R' < R → ∃ C K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ x ∈ vec3Ball 0 R',
      ‖iteratedFDeriv ℝ n G x‖ ≤ C * K ^ n * (Nat.factorial n)) :
    AnalyticOnNhd ℝ G (vec3Ball 0 R) := by
  intro x hx
  rw [mem_vec3Ball, sub_zero] at hx
  set R' : ℝ := (vec3EuclideanNorm x + R) / 2 with hR'def
  have hR'lt : R' < R := by rw [hR'def]; linarith only [hx]
  have hxR' : x ∈ vec3Ball (0 : Vec3) R' := by
    rw [mem_vec3Ball, sub_zero, hR'def]
    linarith only [hx]
  obtain ⟨C, K, hK, hb⟩ := hbound R' hR'lt
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 (isOpen_vec3Ball (0 : Vec3) R') x hxR'
  have hsub : vec3Ball (0 : Vec3) R' ⊆ vec3Ball 0 R := vec3Ball_mono hR'lt.le
  exact analyticAt_of_norm_iteratedFDeriv_le hr hK (hG.mono (hrs.trans hsub)) fun n z hz =>
    hb n z (hrs hz)

/-- One component of one time slice of a field that is smooth on a space-time cylinder is smooth
on the spatial ball. -/
theorem contDiffOn_slice_component {u : ParabolicPoint → Vec3} {R t t₁ t₂ : ℝ}
    (ht : t ∈ Ioo t₁ t₂)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      (spaceTimeSet (vec3Ball 0 R) (Ioo t₁ t₂)))
    (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i) (vec3Ball 0 R) := by
  have hu' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      ((vec3Ball 0 R) ×ˢ (Ioo t₁ t₂) : Set (Vec3 × ℝ)) := hu
  have hmaps : MapsTo (fun x : Vec3 => (x, t)) (vec3Ball 0 R)
      ((vec3Ball 0 R) ×ˢ (Ioo t₁ t₂) : Set (Vec3 × ℝ)) := fun x hx => ⟨hx, ht⟩
  have hin : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => (x, t)) (vec3Ball 0 R) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).contDiff).comp_contDiffOn
    (hu'.comp hin hmaps)

end Vec3Ball

end CIV
