/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.Young
public import LeanPool.FunctionSpaces.Domains.Interval.Steklov
public import Mathlib.MeasureTheory.Integral.Prod

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smoothing by Steklov averages

For continuous `f`, `r ≥ 1` and `δ > 0` the **Steklov smoothing**

`S_δ f = ∑_{k=1}^r (-1)^(k+1) C(r,k) M_{kδ}^r f`   (`Interval.smooth`)

is `r` times continuously differentiable, and it is close to `f` in terms of differences:

* `f - S_δ f = (-1)^r avg_{v ∈ [0, δ]^r} Δ^r_{v_1 + ⋯ + v_r} f`, so
  `‖f - S_δ f‖_{L_p(J)} ≤ sup_{0 ≤ h ≤ rδ} ‖Δ_h^r f‖_{L_p(J)}` (`Interval.eLpNorm_sub_smooth_le`);
* `(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r,k) (kδ)^(-r) Δ_{kδ}^r f`
  (`Interval.iteratedDeriv_smooth_eq_sum_smul`), so
  `‖(S_δ f)^(r)‖_{L_p(J)} ≤ 2^r δ^(-r) sup_{0 ≤ h ≤ rδ} ‖Δ_h^r f‖_{L_p(J)}`
  (`Interval.eLpNorm_iteratedDeriv_smooth_le`).

The derivative bound holds for any measure and any family `D_h` with `‖D_h‖_{L_p(μ)} ≤ B`
(`Interval.eLpNorm_sum_smoothCoeff_smul_le`); the cube and the whole line use it.

The average over the cube `[0, δ]^r` is built as the `r`-fold average in the step,
`Interval.avgStepIter`, and the `L_p` bound for averages is Minkowski's inequality in the form
`‖δ^(-1) ∫_0^δ K(t, ·) dt‖_p ≤ sup_t ‖K(t, ·)‖_p` (`Interval.eLpNorm_avg_le`), the weighted
average with the weight `δ^(-1) 1_{(0, δ]}` (`MeasureTheory.eLpNorm_integral_kernel_le_of_bound`).
Here `1 ≤ p < ∞`.

With `δ = L / r²` the smoothing at `x` looks at `[x, x + L]`. On a left part `[0, w]` of `[0, b]`
with `w + L ≤ b` this gives `‖f - S_δ f‖_p ≤ ω_r(f, L, [0, b])_p` and
`‖(S_δ f)^(r)‖_p ≤ L^(-r) 2^r r^(2r) ω_r(f, L, [0, b])_p`, and Taylor's theorem gives polynomial
approximations of `S_δ f` on all subintervals (`Interval.exists_left_smoothing`). The reflection
`x ↦ b - x` gives the same on a right part `[b - w, b]` (`Interval.exists_right_smoothing`). These
are the local estimates behind Jackson's and Whitney's inequalities.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal

namespace Interval

variable {α : Type*}

/-- Averaging a function of `(h, x)` in the step: `δ^(-1) ∫_0^δ G(σ + t, x) dt`. The point `x`
lies in any space `α`: the real line for the interval, the cube for slices in one coordinate. -/
noncomputable def avgStep (δ : ℝ) (G : ℝ → α → ℂ) (σ : ℝ) (x : α) : ℂ :=
  ((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, G (σ + t) x

/-- The `m`-fold average in the step. -/
noncomputable def avgStepIter (m : ℕ) (δ : ℝ) (G : ℝ → α → ℂ) : ℝ → α → ℂ := (avgStep δ)^[m] G

/-- `avgStepIter (m+1) = avgStep ∘ avgStepIter m`. -/
theorem avgStepIter_succ (m : ℕ) (δ : ℝ) (G : ℝ → α → ℂ) :
    avgStepIter (m + 1) δ G = avgStep δ (avgStepIter m δ G) := by
  rw [avgStepIter, Function.iterate_succ_apply']
  rfl

/-- The iterated average at a point only sees the values at that point: if `G(h, x) = G'(h, x')`
for all steps `h`, the averages at `x` and at `x'` agree. -/
theorem avgStepIter_congr_point {β : Type*} {G : ℝ → α → ℂ} {G' : ℝ → β → ℂ} {x : α} {x' : β}
    (h : ∀ s, G s x = G' s x') (m : ℕ) (δ σ : ℝ) :
    avgStepIter m δ G σ x = avgStepIter m δ G' σ x' := by
  induction m generalizing σ with
  | zero => exact h σ
  | succ m ih =>
    rw [avgStepIter_succ, avgStepIter_succ]
    simp only [avgStep, ih]

/-- Averages of jointly continuous functions are jointly continuous. -/
theorem continuous_avgStep [TopologicalSpace α] {G : ℝ → α → ℂ}
    (hG : Continuous (Function.uncurry G)) (δ : ℝ) :
    Continuous (Function.uncurry (avgStep δ G)) := by
  have hc : Continuous (Function.uncurry fun (q : ℝ × α) (t : ℝ) => G (q.1 + t) q.2) :=
    hG.comp (by fun_prop : Continuous fun p : (ℝ × α) × ℝ => (p.1.1 + p.2, p.1.2))
  have h : Continuous fun q : ℝ × α => ∫ t in (0 : ℝ)..δ, G (q.1 + t) q.2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 δ
  exact continuous_const.mul h

/-- Iterated averages of jointly continuous functions are jointly continuous. -/
theorem continuous_avgStepIter [TopologicalSpace α] {G : ℝ → α → ℂ}
    (hG : Continuous (Function.uncurry G)) (m : ℕ) (δ : ℝ) :
    Continuous (Function.uncurry (avgStepIter m δ G)) := by
  induction m with
  | zero => exact hG
  | succ m ih => rw [avgStepIter_succ]; exact continuous_avgStep ih δ

/-- **Minkowski's inequality for averages**: for jointly continuous `K`, `δ > 0`,
`1 ≤ p < ∞` and an s-finite measure `μ` on the point space,
`‖δ^(-1) ∫_0^δ K(t, ·) dt‖_{L_p(μ)} ≤ sup_{0 ≤ t ≤ δ} ‖K(t, ·)‖_{L_p(μ)}`: the weighted average
with the weight `Φ = δ^(-1) 1_{(0, δ]}` of total mass `1`
(`MeasureTheory.eLpNorm_integral_kernel_le_of_bound`). -/
theorem eLpNorm_avg_le [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {K : ℝ → α → ℂ} (hK : Continuous (Function.uncurry K)) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (μ : Measure α) [SFinite μ] :
    eLpNorm (fun x => ((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x) p μ ≤
      ⨆ t ∈ Icc 0 δ, eLpNorm (K t) p μ := by
  set Φ : ℝ → ℂ := (Ioc 0 δ).indicator fun _ => ((δ : ℂ))⁻¹
  have hΦ : ∫⁻ t, ‖Φ t‖ₑ = 1 := by
    simp only [Φ, eNorm_indicator_eq_indicator_eNorm]
    rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
      ENNReal.ofReal_inv_of_pos hδ,
      ENNReal.inv_mul_cancel (by simpa using hδ) ENNReal.ofReal_ne_top]
  have heq : (fun x => ((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x) =
      fun x => ∫ t, Φ t * K t x := by
    funext x
    have h : ∀ t, Φ t * K t x =
        (Ioc 0 δ).indicator (fun t => ((δ : ℂ))⁻¹ * K t x) t := fun t => by
      by_cases ht : t ∈ Ioc 0 δ
      · simp only [Φ, indicator_of_mem ht]
      · simp only [Φ, indicator_of_notMem ht, zero_mul]
    simp_rw [h]
    rw [integral_indicator measurableSet_Ioc, integral_const_mul,
      intervalIntegral.integral_of_le hδ.le]
  have hG : Continuous (Function.uncurry fun (x : α) (t : ℝ) => K t x) :=
    hK.comp (by fun_prop : Continuous fun q : α × ℝ => (q.2, q.1))
  have hΦm : AEStronglyMeasurable Φ volume :=
    (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable
  rw [heq]
  refine (eLpNorm_integral_kernel_le_of_bound hp hp' hΦm (by rw [hΦ]; exact one_ne_zero)
    (by rw [hΦ]; exact ENNReal.one_ne_top) hG.measurable fun t ht => ?_).trans_eq
    (by rw [hΦ, one_mul])
  exact le_iSup₂ (f := fun t (_ : t ∈ Icc 0 δ) => eLpNorm (K t) p μ) t
    (Ioc_subset_Icc_self (mem_of_indicator_ne_zero ht))

/-- **Iterated averages are bounded by the sup over the steps**:
`‖avg^m G(σ, ·)‖_{L_p(μ)} ≤ sup_{σ ≤ h ≤ σ + mδ} ‖G(h, ·)‖_{L_p(μ)}`. -/
theorem eLpNorm_avgStepIter_le [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {G : ℝ → α → ℂ} (hG : Continuous (Function.uncurry G)) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (μ : Measure α) [SFinite μ] (m : ℕ)
    (σ : ℝ) :
    eLpNorm (avgStepIter m δ G σ) p μ ≤ ⨆ h ∈ Icc σ (σ + m * δ), eLpNorm (G h) p μ := by
  induction m generalizing σ with
  | zero =>
    exact le_iSup₂ (f := fun h (_ : h ∈ Icc σ (σ + (0 : ℕ) * δ)) => eLpNorm (G h) p μ) σ
      ⟨le_rfl, by simp⟩
  | succ m ih =>
    rw [avgStepIter_succ]
    have hK : Continuous (Function.uncurry fun t x => avgStepIter m δ G (σ + t) x) :=
      (continuous_avgStepIter hG m δ).comp
        (by fun_prop : Continuous fun p : ℝ × α => (σ + p.1, p.2))
    refine (eLpNorm_avg_le hK hδ hp hp' μ).trans (iSup₂_le fun t ht => (ih (σ + t)).trans ?_)
    refine iSup₂_le fun h hh => le_iSup₂_of_le h ⟨?_, ?_⟩ le_rfl
    · linarith [ht.1, hh.1]
    · have := hh.2; push_cast at this ⊢; nlinarith [ht.2]

/-- Averaging a function of `x` alone changes nothing. -/
theorem avgStepIter_const (g : ℝ → ℂ) {δ : ℝ} (hδ : δ ≠ 0) (m : ℕ) :
    avgStepIter m δ (fun _ x => g x) = fun _ x => g x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [avgStepIter_succ, ih]
    funext σ x
    have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
    simp only [avgStep, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    field_simp

/-- **Averaged translates are Steklov averages**: averaging `g(x + k h)` `m` times in the step
gives `M_{kδ}^m g(x + kσ)`, for `k ≥ 1`. -/
theorem avgStepIter_shift (g : ℝ → ℂ) {k : ℕ} (hk : 1 ≤ k) (δ : ℝ) (m : ℕ) :
    avgStepIter m δ (fun h x => g (x + k * h)) =
      fun σ x => steklovIter m (k * δ) g (x + k * σ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [avgStepIter_succ, ih]
    funext σ x
    rw [steklovIter_succ, steklov]
    simp only [avgStep]
    have hsub : ∫ t in (0 : ℝ)..δ, steklovIter m (k * δ) g (x + k * (σ + t)) =
        (k : ℝ)⁻¹ • ∫ τ in (0 : ℝ)..k * δ, steklovIter m (k * δ) g (x + k * σ + τ) := by
      calc ∫ t in (0 : ℝ)..δ, steklovIter m (k * δ) g (x + k * (σ + t))
          = ∫ t in (0 : ℝ)..δ, (fun τ => steklovIter m (k * δ) g (x + k * σ + τ)) (k * t) := by
            congr 1
            funext t
            simp only
            congr 1
            ring
        _ = (k : ℝ)⁻¹ • ∫ τ in (k : ℝ) * 0..(k : ℝ) * δ,
              steklovIter m (k * δ) g (x + k * σ + τ) :=
            intervalIntegral.integral_comp_mul_left
              (fun τ => steklovIter m (k * δ) g (x + k * σ + τ)) hk0
        _ = _ := by rw [mul_zero]
    rw [hsub, Complex.real_smul]
    push_cast
    field_simp

/-- Averages of finite linear combinations. -/
theorem avgStepIter_sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℝ → ℂ}
    (hG : ∀ i ∈ s, Continuous (Function.uncurry (G i))) (c : ι → ℂ) (δ : ℝ) (m : ℕ) :
    avgStepIter m δ (fun h x => ∑ i ∈ s, c i * G i h x) =
      fun σ x => ∑ i ∈ s, c i * avgStepIter m δ (G i) σ x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [avgStepIter_succ, ih]
    funext σ x
    simp only [avgStep, avgStepIter_succ]
    have hint : ∀ i ∈ s, IntervalIntegrable (fun t => c i * avgStepIter m δ (G i) (σ + t) x)
        volume 0 δ := fun i hi => by
      have hcI : Continuous fun t => avgStepIter m δ (G i) (σ + t) x :=
        (continuous_avgStepIter (hG i hi) m δ).comp
          (by fun_prop : Continuous fun t : ℝ => (σ + t, x))
      exact (hcI.const_mul (c i)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_const_mul]
    ring

/-- The **Steklov smoothing** `S_δ f = ∑_{k=1}^r (-1)^(k+1) C(r,k) M_{kδ}^r f`. -/
noncomputable def smooth (r : ℕ) (δ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range r, ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
    steklovIter r ((k + 1 : ℕ) * δ) f x

/-- **`f - S_δ f` is an averaged difference**:
`f - S_δ f = (-1)^r avg^r_{h} Δ_h^r f` at step `0`. -/
theorem sub_smooth_eq {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) :
    f x - smooth r δ f x =
      (-1 : ℂ) ^ r * avgStepIter r δ (fun h y => higherDiff r h f y) 0 x := by
  have hrepr : (fun h y => higherDiff r h f y) = fun h y => ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (y + k * h) :=
    funext fun h => funext fun y => higherDiff_apply r h f y
  have hcont : ∀ k ∈ Finset.range (r + 1),
      Continuous (Function.uncurry fun (h y : ℝ) => f (y + k * h)) := fun k _ =>
    hf.comp (by fun_prop)
  rw [hrepr, avgStepIter_sum _ hcont]
  simp only
  rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
  have h0 : avgStepIter r δ (fun (h y : ℝ) => f (y + ((0 : ℕ) : ℝ) * h)) 0 x = f x := by
    have : (fun (h y : ℝ) => f (y + ((0 : ℕ) : ℝ) * h)) = fun _ y => f y := by
      funext h y; simp
    rw [this, avgStepIter_const f hδ]
  rw [h0]
  have hk : ∀ k ∈ Finset.range r, avgStepIter r δ (fun (h y : ℝ) => f (y + ((k + 1 : ℕ) : ℝ) * h))
      0 x = steklovIter r ((k + 1 : ℕ) * δ) f x := fun k _ => by
    rw [avgStepIter_shift f (by omega) δ]
    simp
  rw [Finset.sum_congr rfl fun k hk' => by rw [hk k hk'], smooth]
  have hsign : ∀ k ∈ Finset.range r, (-1 : ℂ) ^ r * (((-1 : ℂ) ^ (r - (k + 1)) *
      (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x) =
      -(((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x) :=
    fun k hk' => by
      have hkr : k + 1 ≤ r := Finset.mem_range.1 hk'
      have : (-1 : ℂ) ^ r = (-1) ^ (r - (k + 1)) * (-1) ^ (k + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hkr]
      rw [this]
      have h2 : ((-1 : ℂ) ^ (r - (k + 1))) * (-1) ^ (r - (k + 1)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      calc (-1 : ℂ) ^ (r - (k + 1)) * (-1) ^ (k + 1) * ((-1) ^ (r - (k + 1)) *
            ↑(r.choose (k + 1)) * steklovIter r (↑(k + 1) * δ) f x)
          = ((-1 : ℂ) ^ (r - (k + 1)) * (-1) ^ (r - (k + 1))) * (-1) ^ (k + 1) *
              (↑(r.choose (k + 1)) * steklovIter r (↑(k + 1) * δ) f x) := by ring
        _ = _ := by rw [h2, pow_succ (-1 : ℂ) (k + 1)]; ring
  rw [Finset.sum_congr rfl hsign, Finset.sum_neg_distrib]
  have hr0 : (-1 : ℂ) ^ r * ((-1 : ℂ) ^ (r - 0) * (r.choose 0 : ℂ) * f x) = f x := by
    rw [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    simp
  rw [hr0]
  ring

/-- The Steklov smoothing of a continuous function lies in `C^r`. -/
theorem contDiff_smooth {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ) :
    ContDiff ℝ r (smooth r δ f) := by
  change ContDiff ℝ r fun x => ∑ k ∈ Finset.range r,
    ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_steklovIter hf r _)

/-- **The derivative of order `r` of the smoothing is a combination of differences**:
`(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r,k) (kδ)^(-r) Δ_{kδ}^r f`. -/
theorem iteratedDeriv_smooth {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ) :
    iteratedDeriv r (smooth r δ f) = fun x => ∑ k ∈ Finset.range r,
      ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        ((((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r * higherDiff r ((k + 1 : ℕ) * δ) f x) := by
  have : smooth r δ f = ∑ k ∈ Finset.range r, fun x =>
      ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x := by
    funext x; simp [smooth, Finset.sum_apply]
  rw [this]
  funext x
  rw [iteratedDeriv_sum fun k _ =>
    (contDiff_const.mul (contDiff_steklovIter hf r _)).contDiffAt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_steklovIter hf]

/-- Differences of a continuous function are jointly continuous in the step and the point. -/
theorem continuous_higherDiff_uncurry {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) :
    Continuous (Function.uncurry fun (h y : ℝ) => higherDiff r h f y) := by
  have : (Function.uncurry fun (h y : ℝ) => higherDiff r h f y) = fun q : ℝ × ℝ =>
      ∑ k ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (q.2 + k * q.1) :=
    funext fun q => higherDiff_apply r q.1 f q.2
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hf.comp (by fun_prop))

/-- **Differences on a subinterval are bounded by the modulus**: for `a ≤ u`, `w + r (rδ) ≤ b` and
`0 ≤ h ≤ rδ`, `‖Δ_h^r f‖_{L_p[u, w]} ≤ ω_r(f, rδ, [a, b])_p`, since `[u, w]` lies in
`[a, b - rh]`. -/
theorem eLpNorm_higherDiff_Icc_le_modulus {f : ℝ → ℂ} {r : ℕ} {δ : ℝ} {p : ℝ≥0∞}
    {a b u w h : ℝ} (hau : a ≤ u) (hwb : w + r * (r * δ) ≤ b) (h0 : 0 ≤ h) (hh : h ≤ r * δ) :
    eLpNorm (higherDiff r h f) p (volume.restrict (Icc u w)) ≤ modulus r p a b f (r * δ) := by
  refine (eLpNorm_Icc_mono _ p hau ?_).trans (eLpNorm_higherDiff_le_modulus ⟨h0, hh⟩)
  have : (r : ℝ) * h ≤ r * (r * δ) := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg r)
  linarith

/-- **The smoothing is close to `f`**: for `[u, w]` with `a ≤ u` and `w + r² δ ≤ b`,
`‖f - S_δ f‖_{L_p[u, w]} ≤ ω_r(f, rδ, [a, b])_p`. -/
theorem eLpNorm_sub_smooth_le {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {a b u w : ℝ} (hau : a ≤ u)
    (hwb : w + r * (r * δ) ≤ b) :
    eLpNorm (fun x => f x - smooth r δ f x) p (volume.restrict (Icc u w)) ≤
      modulus r p a b f (r * δ) := by
  have heq : (fun x => f x - smooth r δ f x) = ((-1 : ℂ) ^ r) •
      avgStepIter r δ (fun h y => higherDiff r h f y) 0 := by
    funext x
    rw [sub_smooth_eq hf r hδ.ne' x]
    rfl
  rw [heq, eLpNorm_const_smul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul]
  refine (eLpNorm_avgStepIter_le (continuous_higherDiff_uncurry hf r) hδ hp hp' _ r 0).trans ?_
  refine iSup₂_le fun h hh => ?_
  rw [zero_add] at hh
  exact eLpNorm_higherDiff_Icc_le_modulus hau hwb hh.1 hh.2

/-- **The derivative of the smoothing as a sum of functions**: for continuous `f : ℝ → ℂ`,
`(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f`
as an identity of functions `ℝ → ℂ` (`Interval.iteratedDeriv_smooth` at every point), written
with the index `k + 1` for `k < r` and as a sum `∑_k c_k • g_k`, the form to which the triangle
inequality in `L_p` applies. -/
theorem iteratedDeriv_smooth_eq_sum_smul {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ) :
    iteratedDeriv r (smooth r δ f) = ∑ k ∈ Finset.range r,
      (((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • higherDiff r ((k + 1 : ℕ) * δ) f := by
  rw [iteratedDeriv_smooth hf r δ]
  funext x
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

/-- `∑_{k=1}^r C(r, k) ≤ 2^r`, written with the index `k + 1` for `k < r`: the full sum
`∑_{k=0}^r C(r, k)` is `2^r` (Mathlib's `Nat.sum_range_choose`). -/
theorem sum_range_choose_succ_le (r : ℕ) :
    ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ≥0∞) ≤ 2 ^ r := by
  have h := Nat.sum_range_choose r
  rw [Finset.sum_range_succ'] at h
  have h' : ∑ k ∈ Finset.range r, r.choose (k + 1) ≤ 2 ^ r := by omega
  exact_mod_cast h'

/-- **One term of the derivative of the smoothing**: for `k ≥ 1` (written `k + 1`), `δ > 0`, a
measure `μ` and `g` with `‖g‖_{L_p(μ)} ≤ B`,
`‖(-1)^(k+1) C(r, k) (kδ)^(-r) g‖_{L_p(μ)} ≤ C(r, k) δ^(-r) B`, since `(kδ)^(-r) ≤ δ^(-r)`. -/
theorem eLpNorm_smoothCoeff_smul_le [MeasurableSpace α] {μ : Measure α} {r k : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} {g : α → ℂ} {B : ℝ≥0∞} (hg : eLpNorm g p μ ≤ B) :
    eLpNorm ((((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
      (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • g) p μ ≤
      (r.choose (k + 1) : ℝ≥0∞) * ((ENNReal.ofReal δ)⁻¹ ^ r * B) := by
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  rw [eLpNorm_const_smul, eNorm_mul, eNorm_mul, eNorm_pow, eNorm_neg, eNorm_one, one_pow,
    one_mul, mul_assoc]
  refine mul_le_mul' ?_ (mul_le_mul' ?_ hg)
  · rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
  · rw [eNorm_pow, ← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
    gcongr
    exact le_mul_of_one_le_left hδ.le hk1

/-- **The derivative bound of the smoothing, for any measure and any family**: for `δ > 0`,
`1 ≤ p ≤ ∞`, a measure `μ` and functions `D_h` with `‖D_h‖_{L_p(μ)} ≤ B` for `0 ≤ h ≤ rδ`,
`‖∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) D_{kδ}‖_{L_p(μ)} ≤ 2^r δ^(-r) B`, by the triangle
inequality and `∑_{k=1}^r C(r, k) ≤ 2^r`. With `D_h = Δ_h^r f` this bounds `(S_δ f)^(r)`
(`Interval.iteratedDeriv_smooth_eq_sum_smul`) on an interval, on a region of the cube and on the
whole line. -/
theorem eLpNorm_sum_smoothCoeff_smul_le [MeasurableSpace α] {μ : Measure α} {r : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) {D : ℝ → α → ℂ} {B : ℝ≥0∞}
    (hD : ∀ h, 0 ≤ h → h ≤ r * δ → eLpNorm (D h) p μ ≤ B) :
    eLpNorm (∑ k ∈ Finset.range r, (((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
      (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • D ((k + 1 : ℕ) * δ)) p μ ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * B := by
  have hk : ∀ k ∈ Finset.range r, eLpNorm ((((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
      (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • D ((k + 1 : ℕ) * δ)) p μ ≤
      (r.choose (k + 1) : ℝ≥0∞) * ((ENNReal.ofReal δ)⁻¹ ^ r * B) := fun k hk =>
    eLpNorm_smoothCoeff_smul_le hδ (hD _ (by positivity)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.mem_range.1 hk) hδ.le))
  refine ((eLpNorm_sum_le hp).trans (Finset.sum_le_sum hk)).trans ?_
  rw [← Finset.sum_mul, mul_assoc]
  gcongr
  exact sum_range_choose_succ_le r

/-- **The derivative of order `r` of the smoothing**: for `[u, w]` with `a ≤ u` and
`w + r² δ ≤ b`, `‖(S_δ f)^(r)‖_{L_p[u, w]} ≤ 2^r δ^(-r) ω_r(f, rδ, [a, b])_p`. -/
theorem eLpNorm_iteratedDeriv_smooth_le {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) {a b u w : ℝ} (hau : a ≤ u)
    (hwb : w + r * (r * δ) ≤ b) :
    eLpNorm (iteratedDeriv r (smooth r δ f)) p (volume.restrict (Icc u w)) ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * modulus r p a b f (r * δ) := by
  rw [iteratedDeriv_smooth_eq_sum_smul hf r δ]
  exact eLpNorm_sum_smoothCoeff_smul_le (D := fun h => higherDiff r h f) hδ hp
    fun h h0 hh => eLpNorm_higherDiff_Icc_le_modulus hau hwb h0 hh

/-- **The step `δ = L / r²` of the smoothing**: for `r ≥ 1` and `L > 0`, `δ > 0`, `rδ ≤ L` and
`r (rδ) = L`. -/
theorem step_div_sq_bounds {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : 0 < L) :
    0 < L / r ^ 2 ∧ (r : ℝ) * (L / r ^ 2) ≤ L ∧ (r : ℝ) * (r * (L / r ^ 2)) = L := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨by positivity, ?_, by field_simp⟩
  rw [show (r : ℝ) * (L / r ^ 2) = L / r by field_simp]
  exact div_le_self hL.le (by exact_mod_cast hr)

/-- **The constant of the derivative at the step `δ = L / r²`**: for `r ≥ 1`, `L > 0` and
`a ≤ b`, `2^r δ^(-r) a ≤ L^(-r) 2^r r^(2r) b`, since `δ^(-1) = r² L^(-1)`. -/
theorem two_pow_mul_inv_div_sq_pow_mul_le {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : 0 < L)
    {a b : ℝ≥0∞} (hab : a ≤ b) :
    2 ^ r * (ENNReal.ofReal (L / r ^ 2))⁻¹ ^ r * a ≤
      ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * b := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hinv : (ENNReal.ofReal (L / r ^ 2))⁻¹ = (r : ℝ≥0∞) ^ 2 * ENNReal.ofReal L⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), show (L / (r : ℝ) ^ 2)⁻¹ = (r : ℝ) ^ 2 * L⁻¹ by
      field_simp, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg r),
      ENNReal.ofReal_natCast]
  rw [hinv, mul_pow, ← pow_mul]
  calc 2 ^ r * ((r : ℝ≥0∞) ^ (2 * r) * ENNReal.ofReal L⁻¹ ^ r) * a
      ≤ 2 ^ r * ((r : ℝ≥0∞) ^ (2 * r) * ENNReal.ofReal L⁻¹ ^ r) * b := mul_le_mul' le_rfl hab
    _ = _ := by ring

/-- **Taylor polynomials of a reflected function**: if `g` has a polynomial `T` of degree `< r`
with `‖g - T‖_{L_p[c - v, c - u]} ≤ (v - u)^r ‖D‖_{L_p[c - v, c - u]}`, then `T(c - ·)` does the
same for `g(c - ·)` on `[u, v]`, with `D(c - ·)` in place of `D`. -/
theorem exists_eLpNorm_sub_polyFun_reflect_le {g D : ℝ → ℂ} (hg : Measurable g)
    (hD : Measurable D) {r : ℕ} {p : ℝ≥0∞} {c u v : ℝ}
    (h : ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => g x - polyFun T x) p
      (volume.restrict (Icc (c - v) (c - u))) ≤ ENNReal.ofReal ((c - u) - (c - v)) ^ r *
        eLpNorm D p (volume.restrict (Icc (c - v) (c - u)))) :
    ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => g (c - x) - polyFun T x) p (volume.restrict (Icc u v)) ≤
      ENNReal.ofReal (v - u) ^ r * eLpNorm (fun x => D (c - x)) p (volume.restrict (Icc u v)) := by
  obtain ⟨T, hT, hTb⟩ := h
  refine ⟨T.comp (C ((c : ℝ) : ℂ) + C ((-1 : ℝ) : ℂ) * X),
    comp_affine_mem_degreeLT hT _ _, ?_⟩
  have hfun : (fun x => g (c - x) - polyFun (T.comp (C ((c : ℝ) : ℂ) +
      C ((-1 : ℝ) : ℂ) * X)) x) = fun x => (fun y => g y - polyFun T y) (c - x) := by
    funext x
    rw [polyFun_comp_affine]
    congr 2
    ring
  rw [hfun, eLpNorm_comp_sub_Icc (f := fun y => g y - polyFun T y)
    (hg.sub (measurable_polyFun T)) p c u v, eLpNorm_comp_sub_Icc hD p c u v]
  rw [show (c - u) - (c - v) = v - u by ring] at hTb
  exact hTb

/-- **Smoothing on a left part**: for continuous `F`, `r ≥ 1`, a scale `L > 0` and `w + L ≤ b`,
the Steklov smoothing `g = S_δ F`, `δ = L/r²`, and its derivative `D = g^(r)` satisfy
`‖F - g‖_{L_p[0,w]} ≤ ω_r(F, L, [0, b])_p` and
`‖D‖_{L_p[0,w]} ≤ L^(-r) 2^r r^(2r) ω_r(F, L, [0, b])_p`, and for every `u ≤ v` there is `T` of
degree `< r` with `‖g - T‖_{L_p[u,v]} ≤ (v - u)^r ‖D‖_{L_p[u,v]}` (Taylor). -/
theorem exists_left_smoothing {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {b L w : ℝ} (hL : 0 < L) (hwL : w + L ≤ b) :
    ∃ g D : ℝ → ℂ, Measurable g ∧ Measurable D ∧
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc 0 w)) ≤ modulus r p 0 b F L ∧
      eLpNorm D p (volume.restrict (Icc 0 w)) ≤
        ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * modulus r p 0 b F L ∧
      ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc u v)) ≤
          ENNReal.ofReal (v - u) ^ r * eLpNorm D p (volume.restrict (Icc u v)) := by
  obtain ⟨hδ, hrδ, hrrδ⟩ := step_div_sq_bounds hr hL
  have hwb : w + r * (r * (L / r ^ 2)) ≤ b := by rw [hrrδ]; exact hwL
  have hg := contDiff_smooth hF r (L / r ^ 2)
  refine ⟨smooth r (L / r ^ 2) F, iteratedDeriv r (smooth r (L / r ^ 2) F),
    hg.continuous.measurable, (hg.continuous_iteratedDeriv r le_rfl).measurable, ?_, ?_,
    fun u v huv => exists_eLpNorm_sub_polyFun_le hp r hg huv⟩
  · exact (eLpNorm_sub_smooth_le hF r hδ hp hp' le_rfl hwb).trans (modulus_mono r p 0 b F hrδ)
  · exact (eLpNorm_iteratedDeriv_smooth_le hF r hδ hp le_rfl hwb).trans
      (two_pow_mul_inv_div_sq_pow_mul_le hr hL (modulus_mono r p 0 b F hrδ))

/-- **Smoothing on a right part**: the same on `[b - w, b]`, by the reflection `x ↦ b - x`, which
preserves the modulus on `[0, b]` (`Interval.modulus_reflect`). -/
theorem exists_right_smoothing {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {b L w : ℝ} (hL : 0 < L) (hwL : w + L ≤ b) :
    ∃ g D : ℝ → ℂ, Measurable g ∧ Measurable D ∧
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc (b - w) b)) ≤ modulus r p 0 b F L ∧
      eLpNorm D p (volume.restrict (Icc (b - w) b)) ≤
        ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * modulus r p 0 b F L ∧
      ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc u v)) ≤
          ENNReal.ofReal (v - u) ^ r * eLpNorm D p (volume.restrict (Icc u v)) := by
  have hF' : Continuous fun x => F (b - x) := hF.comp (continuous_const.sub continuous_id)
  obtain ⟨G, DG, hGm, hDm, h1, h2, h3⟩ := exists_left_smoothing hF' hr hp hp' hL hwL
  have hmod : modulus r p 0 b (fun x => F (b - x)) L = modulus r p 0 b F L := by
    simpa using modulus_reflect hF.measurable r p 0 b L
  rw [hmod] at h1 h2
  refine ⟨fun x => G (b - x), fun x => DG (b - x), hGm.comp (measurable_const.sub measurable_id),
    hDm.comp (measurable_const.sub measurable_id), ?_, ?_, fun u v huv => ?_⟩
  · have h := eLpNorm_comp_sub_Icc (f := fun y => F (b - y) - G y)
      ((hF'.measurable).sub hGm) p b (b - w) b
    simp only [sub_sub_cancel, sub_self] at h
    rw [h]
    exact h1
  · have h := eLpNorm_comp_sub_Icc hDm p b (b - w) b
    simp only [sub_sub_cancel, sub_self] at h
    rw [h]
    exact h2
  · exact exists_eLpNorm_sub_polyFun_reflect_le hGm hDm (h3 (b - v) (b - u) (by linarith))

end Interval
