/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# A nonzero holomorphic germ is regular in a suitable direction

Let `g` be complex differentiable near `0` in a complex normed space `E` and not identically
zero near `0`, and let `e ≠ 0`.  After a continuous linear change of coordinates `A` the
restriction `t ↦ g (A (t • e))` has finite order `d` at `0`:
`g (A (t • e)) = t ^ d * u t` with `u` analytic and `u 0 ≠ 0`.  This is the normalization
before Weierstrass division in the proof that holomorphic germs form a Noetherian ring.

The proof.  Pick `w ≠ 0` so small that `g` is differentiable on the ball of radius `2‖w‖`
and `g w ≠ 0`.  Then `φ t = g (t • w)` is holomorphic on the disc of radius `2`, and
`φ 1 ≠ 0`, so by the identity theorem `φ` does not vanish near `0` and has a finite order
there.  Continuous linear equivalences act transitively on nonzero vectors, so some `A`
sends `e` to `w`.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A germ that is continuous at `0` and not eventually zero is nonzero at points `w ≠ 0`
arbitrarily close to `0`. -/
theorem exists_ne_zero_apply_ne_zero_of_not_eventuallyEq {g : E → ℂ} (hg : ContinuousAt g 0)
    (hne : ¬ g =ᶠ[𝓝 0] 0) {e : E} (he : e ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ w : E, w ≠ 0 ∧ ‖w‖ < r ∧ g w ≠ 0 := by
  have : Nontrivial E := ⟨⟨e, 0, he⟩⟩
  by_contra hcon
  push Not at hcon
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : E), g z = 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : E) hr), self_mem_nhdsWithin]
      with z hz hz0
    exact hcon z hz0 (by simpa using hz)
  have hg0 : g 0 = 0 := by
    have hlim : Tendsto g (𝓝[≠] (0 : E)) (𝓝 (g 0)) :=
      hg.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hpunct.mono fun z hz => hz.symm))
  apply hne
  filter_upwards [ball_mem_nhds (0 : E) hr] with z hz
  by_cases hz0 : z = 0
  · simpa [hz0] using hg0
  · exact hcon z hz0 (by simpa using hz)

/-- **Regular direction.**  A holomorphic germ at `0` that is not identically zero has finite
order along the line through `e` after a continuous linear change of coordinates. -/
theorem exists_regular_continuousLinearEquiv {g : E → ℂ}
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) (hne : ¬ g =ᶠ[𝓝 0] 0) {e : E} (he : e ≠ 0) :
    ∃ A : E ≃L[ℂ] E, ∃ d : ℕ, ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), g (A (t • e)) = t ^ d * u t := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg
  obtain ⟨w, hw0, hwr, hgw⟩ := exists_ne_zero_apply_ne_zero_of_not_eventuallyEq
    hg.self_of_nhds.continuousAt hne he (half_pos hr)
  obtain ⟨A, hA⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℂ) he hw0
  set φ : ℂ → ℂ := fun t => g (t • w) with hφ
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) 2) := by
    intro t ht
    have ht' : ‖t‖ < 2 := by simpa using ht
    have hmem : t • w ∈ ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul]
      calc ‖t‖ * ‖w‖ < 2 * (r / 2) := by
            apply mul_lt_mul'' ht' hwr (norm_nonneg _) (norm_nonneg _)
        _ = r := by ring
    exact ((hball _ hmem).comp t
      (differentiableAt_id.smul_const w)).differentiableWithinAt
  have hanal : AnalyticOnNhd ℂ φ (ball (0 : ℂ) 2) := hdiff.analyticOnNhd isOpen_ball
  have h0 : AnalyticAt ℂ φ 0 := hanal 0 (mem_ball_self (by norm_num))
  have hnot : ¬ ∀ᶠ t in 𝓝 (0 : ℂ), φ t = 0 := by
    intro hev
    have := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 2).isPreconnected (mem_ball_self (by norm_num)) hev
    have h1 := this (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by simp)
    exact hgw (by simpa [hφ] using h1)
  obtain ⟨d, u, hu, hu0, hφu⟩ := h0.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hnot
  refine ⟨A, d, u, hu, hu0, ?_⟩
  filter_upwards [hφu] with t ht
  simpa [hφ, map_smul, hA, smul_eq_mul] using ht

end SGPT.Foundations.Analysis.Pending
