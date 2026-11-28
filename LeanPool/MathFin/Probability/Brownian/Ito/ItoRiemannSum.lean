/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.UnifPart
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralL2

/-! # The Riemann–Itô sum

The one left-endpoint sum of the Itô stack: for an integrand `θ : ℝ≥0 → Ω → ℝ` and the uniform
partition of `[0, T]` into `n` cells (`unifPart`),

  `riemannσ θ T n ω = ∑_{k<n} θ(tₖ, ω) · (B_{tₖ₊₁}(ω) − B_{tₖ}(ω))`.

Every Riemann–Itô sum in the library is this sum at a particular integrand: `θ = B` for
the keystone `∫ B dB`, `θ s ω = clamp_m(B_s ω)` for its truncation, `θ s ω = φ(B_s ω)` and
`θ s ω = φ(s, B_s ω)` for the bounded-continuous bridges, an adapted continuous process for the
general bridge, and the integrands of the localised and predictable integrals.

## Main definitions

* `riemannσ`: the uniform-partition Riemann–Itô sum
  `riemannσ θ T n ω = ∑_{k<n} θ(t_k, ω) · (B_{t_{k+1}}(ω) − B_{t_k}(ω))`.

## Main results

* `riemannσ_congr` — it depends only on the integrand on `[0, T]`.
* `riemannσ_sub` — it is linear in the integrand.
* `memLp_riemannσ` — for a bounded adapted integrand the sum is in `L²`.

## Tags

Riemann–Itô sum, left-endpoint sum, uniform partition, stochastic integral, Itô integral, MSC 60H05
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralRiemannBridge

open MeasureTheory ProbabilityTheory ItoIntegralL2
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit hB in
/-- The uniform-partition Riemann–Itô sum for an integrand `θ`:
`∑_{k<n} θ(tₖ)·(B_{t_{k+1}} − B_{tₖ})`. -/
noncomputable def riemannσ (θ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, θ (unifPart T n k) ω
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)

omit hB mΩ in
/-- The Riemann–Itô sum on `[0, T]` depends only on the integrand on `[0, T]`. -/
lemma riemannσ_congr {θ θ' : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (h : ∀ s ∈ Set.Icc 0 T, θ s ω = θ' s ω) (n : ℕ) :
    riemannσ (B := B) θ T n ω = riemannσ (B := B) θ' T n ω :=
  Finset.sum_congr rfl fun k hk ↦ by
    rw [h _ ⟨zero_le, unifPart_le_T (Finset.mem_range.1 hk).le⟩]

omit hB mΩ in
/-- The Riemann–Itô sum is linear in the integrand. -/
lemma riemannσ_sub (θ θ' : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    riemannσ (B := B) θ T n ω - riemannσ (B := B) θ' T n ω
      = ∑ k ∈ Finset.range n, (θ (unifPart T n k) ω - θ' (unifPart T n k) ω)
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) := by
  rw [riemannσ, riemannσ, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

omit [IsProbabilityMeasure μ] in
/-- `MemLp` of the adapted Riemann sum, by **domination**: each term `θ(tₖ)·ΔBₖ` is a bounded
(`|θ| ≤ C`) measurable coefficient times an `L²` increment, hence `L²` (`‖θ·Δ‖ ≤ ‖C·Δ‖`). No
increment-independence / adaptedness needed for membership. -/
lemma memLp_riemannσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (riemannσ (B := B) θ T n) 2 μ := by
  unfold riemannσ
  refine memLp_finsetSum _ fun k _ ↦ ?_
  have hΔ : MemLp (fun ω ↦ B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) 2 μ :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hθm : StronglyMeasurable (θ (unifPart T n k)) :=
    (hadap (unifPart T n k)).mono ((natFiltration hBmeas).le _)
  refine (hΔ.const_mul C).mono
    (hθm.aestronglyMeasurable.mul hΔ.aestronglyMeasurable) (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hbdd (unifPart T n k) ω).trans (le_abs_self C)) (abs_nonneg _)

end ItoIntegralRiemannBridge
end MathFin
