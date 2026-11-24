/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermRing
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Zero sets of holomorphic functions are thin; the germ ring is a domain

Let `U` be a preconnected open subset of a complex normed space `E` and `h : E → ℂ` complex
differentiable on `U`, not vanishing identically near some point of `U`.

* `eqOn_zero_of_eventually_eq_zero`: the identity theorem: if `h` vanishes near one point
  of `U`, then it vanishes on `U`. The set of points near which `h` vanishes is open; it is
  closed in `U` by the one-variable identity theorem along complex lines.
* `dense_compl_zeroSet`: `U ⊆ closure (U \ h ⁻¹' {0})`.
* `isDomain_holGerm`: the ring `HolGerm E` of holomorphic germs at `0` is a domain.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending.RiemannExtension

open Filter Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `h` is complex differentiable on the ball `ball z ε` and vanishes near `w`, where
`dist w z < ε / 2`, then `h` vanishes on `ball w (ε / 2)`. -/
theorem eq_zero_on_ball_of_eventually_eq_zero {h : E → ℂ} {z w : E} {ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball z ε)) (hw : dist w z < ε / 2)
    (hw0 : ∀ᶠ v in 𝓝 w, h v = 0) : ∀ y ∈ ball w (ε / 2), h y = 0 := by
  intro y hy
  set ℓ : ℂ → E := fun c => w + c • (y - w) with hℓ
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  set D : Set ℂ := ℓ ⁻¹' ball z ε with hD
  have hDo : IsOpen D := isOpen_ball.preimage hℓc
  have hDc : Convex ℝ D := by
    intro a ha b hb s t hs ht hst
    have key : w + (s • a + t • b) • (y - w) =
        s • (w + a • (y - w)) + t • (w + b • (y - w)) := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hst, one_smul, add_smul, smul_assoc,
        smul_assoc]
    simp only [hD, hℓ, Set.mem_preimage] at ha hb ⊢
    rw [key]
    exact convex_ball z ε ha hb hs ht hst
  have hε : 0 < ε := by linarith [dist_nonneg (x := w) (y := z)]
  have h0D : (0 : ℂ) ∈ D := by
    simp only [hD, hℓ, Set.mem_preimage, zero_smul, add_zero, mem_ball]
    linarith
  have h1D : (1 : ℂ) ∈ D := by
    simp only [hD, hℓ, Set.mem_preimage, one_smul, add_sub_cancel, mem_ball]
    rw [mem_ball] at hy
    linarith [dist_triangle y w z]
  have hℓd : Differentiable ℂ ℓ := (differentiable_const w).add (differentiable_id.smul_const _)
  have hg : AnalyticOnNhd ℂ (h ∘ ℓ) D :=
    (hh.comp hℓd.differentiableOn fun c hc => hc).analyticOnNhd hDo
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 w) := by simpa [hℓ] using hℓc.tendsto 0
  have hev : (h ∘ ℓ) =ᶠ[𝓝 0] 0 := hℓ0.eventually hw0
  have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc.isPreconnected h0D hev h1D
  simpa [hℓ] using this

/-- **Identity theorem.** A function complex differentiable on a preconnected open set `U`
which vanishes near one point of `U` vanishes near every point of `U`. -/
theorem eventually_eq_zero_of_eventually_eq_zero {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) {h : E → ℂ} (hh : DifferentiableOn ℂ h U) {z₀ : E} (hz₀ : z₀ ∈ U)
    (h0 : ∀ᶠ z in 𝓝 z₀, h z = 0) : ∀ z ∈ U, ∀ᶠ w in 𝓝 z, h w = 0 := by
  set u : Set E := {z | ∀ᶠ w in 𝓝 z, h w = 0} with hu
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  refine hUc.subset_of_closure_inter_subset huo ⟨z₀, hz₀, h0⟩ ?_
  rintro z ⟨hzc, hzU⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hzU
  obtain ⟨w, hwu, hwb⟩ := Metric.mem_closure_iff.1 hzc (ε / 2) (half_pos hε)
  have hwz : dist w z < ε / 2 := by rw [dist_comm]; exact hwb
  have hball := eq_zero_on_ball_of_eventually_eq_zero (hh.mono hεU) hwz hwu
  exact eventually_of_mem (isOpen_ball.mem_nhds (by rw [mem_ball]; exact hwb))
    fun y hy => hball y hy

/-- **Zero sets are thin.** If `h` is complex differentiable on a preconnected open set `U`
and does not vanish identically near some point of `U`, then `U \ h⁻¹(0)` is dense in `U`. -/
theorem dense_compl_zeroSet {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) {h : E → ℂ} (hh : DifferentiableOn ℂ h U)
    {z₀ : E} (hz₀ : z₀ ∈ U) (hne : ¬ ∀ᶠ z in 𝓝 z₀, h z = 0) :
    U ⊆ closure (U \ h ⁻¹' {0}) := by
  intro z hzU
  by_contra hz
  have hz0 : ∀ᶠ w in 𝓝 z, h w = 0 := by
    have hn : (closure (U \ h ⁻¹' {0}))ᶜ ∈ 𝓝 z := isClosed_closure.isOpen_compl.mem_nhds hz
    filter_upwards [hn, hU.mem_nhds hzU] with w hw hwU
    by_contra hw0
    exact hw (subset_closure ⟨hwU, hw0⟩)
  exact hne (eventually_eq_zero_of_eventually_eq_zero hU hUc hh hzU hz0 z₀ hz₀)

/-- A function continuous on a preconnected open set `U` on which `h` is complex differentiable
and not identically zero near some point vanishes on `U` as soon as it vanishes off the
zero set of `h`. -/
theorem eqOn_zero_of_eqOn_zero_compl_zeroSet {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) {h g : E → ℂ} (hh : DifferentiableOn ℂ h U)
    {z₀ : E} (hz₀ : z₀ ∈ U) (hne : ¬ ∀ᶠ z in 𝓝 z₀, h z = 0) (hg : ContinuousOn g U)
    (hg0 : ∀ z ∈ U, h z ≠ 0 → g z = 0) : ∀ z ∈ U, g z = 0 := by
  have := Set.EqOn.of_subset_closure (f := g) (g := 0) (s := U \ h ⁻¹' {0}) (t := U)
    (fun z hz => hg0 z hz.1 hz.2) hg continuousOn_const sdiff_subset
    (dense_compl_zeroSet hU hUc hh hz₀ hne)
  exact fun z hz => this hz

/-- The ring of holomorphic germs has no zero divisors. -/
instance noZeroDivisors_holGerm : NoZeroDivisors (HolGerm E) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk a
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk b
    rw [← HolGerm.mk_mul, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff] at hab
    rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff, HolGerm.mk_eq_mk_iff]
    by_cases hf0 : ∀ᶠ z in 𝓝 (0 : E), f z = 0
    · exact Or.inl hf0
    right
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 ((hf.and hg).and hab)
    have hfd : DifferentiableOn ℂ f (ball 0 r) := fun z hz =>
      (hball z hz).1.1.differentiableWithinAt
    have hgc : ContinuousOn g (ball 0 r) := fun z hz =>
      (hball z hz).1.2.continuousAt.continuousWithinAt
    have := eqOn_zero_of_eqOn_zero_compl_zeroSet isOpen_ball (convex_ball 0 r).isPreconnected
      hfd (mem_ball_self hr) hf0 hgc fun z hz hfz => by
        have h2 : f z * g z = 0 := (hball z hz).2
        exact (mul_eq_zero.1 h2).resolve_left hfz
    exact eventually_of_mem (ball_mem_nhds 0 hr) this

/-- **The ring of holomorphic germs is an integral domain.** -/
instance isDomain_holGerm : IsDomain (HolGerm E) :=
  NoZeroDivisors.to_isDomain _

end SGPT.Foundations.Analysis.Pending.RiemannExtension
