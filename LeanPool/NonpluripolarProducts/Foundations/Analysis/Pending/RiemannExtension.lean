/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermNoetherian
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The Riemann extension theorem

Let `h` be holomorphic on a ball `B` centred at `0` in `ℂ^d`, not identically zero near `0`,
and let `f` be holomorphic and bounded on `B \ h⁻¹(0)`. Then `f` agrees off `h⁻¹(0)` with a
function holomorphic on a smaller ball (`exists_extension_of_bounded`).

* `differentiableAt_circleIntegral_param`: `p ↦ ∮_{C(c, ρ)} Ψ (p, τ) dτ` is holomorphic when
  `Ψ` is jointly holomorphic near `{p} × sphere c ρ` (finite-dimensional parameter space),
  by differentiation under the integral sign; the derivative bound comes from continuity of
  `fderiv` (`FirstPass.contDiffOn_of_differentiableOn_complex`) on a compact tube.
* `cauchy_integral_eq_of_bounded`: in one variable, if `ψ` is holomorphic on `ball 0 R` and
  nonvanishing on `‖τ‖ = ρ`, and `φ` is holomorphic and bounded off `ψ⁻¹(0)`, then the Cauchy
  integral of `φ` over `‖τ‖ = ρ` reproduces `φ` on `ball 0 ρ \ ψ⁻¹(0)`. The zeros of `ψ` are
  isolated, so `φ` extends across each of them (`differentiableOn_update_limUnder_of_bddAbove`).
* `exists_extension_prod`: the theorem on `E × ℂ` for `h` regular in the last variable,
  with `F (x, t) = (2πi)⁻¹ ∮_{|τ| = ρ} f (x, τ) / (τ - t) dτ`.
* `exists_extension_euclidean`, `exists_extension_of_bounded`: the general case on `ℂ^d`,
  after a linear change of coordinates (`exists_regular_continuousLinearEquiv`,
  `euclideanSnocCLE`).
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending.RiemannExtension

open Complex Filter Metric Set MeasureTheory
open scoped Real Topology

noncomputable section

section Parametric

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

/-- **Holomorphic dependence of a circle integral on parameters.** If `Ψ` is complex
differentiable on an open set `O ⊆ P × ℂ` containing `{p₀} × sphere c ρ`, then
`p ↦ ∮_{C(c, ρ)} Ψ (p, τ) dτ` is complex differentiable at `p₀`. -/
theorem differentiableAt_circleIntegral_param {Ψ : P × ℂ → ℂ} {O : Set (P × ℂ)}
    (hO : IsOpen O) (hΨ : DifferentiableOn ℂ Ψ O) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) {p₀ : P}
    (hp₀ : ∀ τ ∈ sphere c ρ, (p₀, τ) ∈ O) :
    DifferentiableAt ℂ (fun p => ∮ τ in C(c, ρ), Ψ (p, τ)) p₀ := by
  have hK₀ : IsCompact (({p₀} : Set P) ×ˢ sphere c ρ) :=
    isCompact_singleton.prod (isCompact_sphere c ρ)
  obtain ⟨δ, hδ, hδO⟩ := hK₀.exists_cthickening_subset_open hO (by
    rintro ⟨p, τ⟩ ⟨hp, hτ⟩
    rw [mem_singleton_iff] at hp
    subst hp
    exact hp₀ τ hτ)
  have hKO : closedBall p₀ δ ×ˢ sphere c ρ ⊆ O := by
    rintro ⟨p, τ⟩ ⟨hp, hτ⟩
    refine hδO (Metric.mem_cthickening_of_dist_le _ (p₀, τ) δ _ ⟨rfl, hτ⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨hp, hδ.le⟩
  let : ProperSpace P := FiniteDimensional.proper ℂ P
  have hK : IsCompact (closedBall p₀ δ ×ˢ sphere c ρ) :=
    (isCompact_closedBall p₀ δ).prod (isCompact_sphere c ρ)
  have hcd : ContinuousOn (fderiv ℂ Ψ) O :=
    (FirstPass.contDiffOn_of_differentiableOn_complex hΨ hO).continuousOn_fderiv_of_isOpen hO
      (by simp)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcd.mono hKO)
  have hmem : ∀ p ∈ closedBall p₀ δ, ∀ θ : ℝ, (p, circleMap c ρ θ) ∈ O := fun p hp θ =>
    hKO ⟨hp, circleMap_mem_sphere c hρ θ⟩
  set F : P → ℝ → ℂ := fun p θ => deriv (circleMap c ρ) θ • Ψ (p, circleMap c ρ θ) with hF
  set F' : P → ℝ → P →L[ℂ] ℂ := fun p θ =>
    deriv (circleMap c ρ) θ • (fderiv ℂ Ψ (p, circleMap c ρ θ)).comp
      (ContinuousLinearMap.inl ℂ P ℂ) with hF'
  have hFc : ∀ p ∈ closedBall p₀ δ, Continuous (F p) := fun p hp => by
    simp only [hF, deriv_circleMap]
    exact ((continuous_circleMap 0 ρ).mul continuous_const).smul
      (hΨ.continuousOn.comp_continuous (continuous_const.prodMk (continuous_circleMap c ρ))
        (hmem p hp))
  have hbound : ∀ p ∈ closedBall p₀ δ, ∀ θ, ‖F' p θ‖ ≤ |ρ| * M := fun p hp θ => by
    simp only [hF', deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, norm_I, mul_one]
    gcongr
    calc ‖(fderiv ℂ Ψ (p, circleMap c ρ θ)).comp (ContinuousLinearMap.inl ℂ P ℂ)‖
        ≤ ‖fderiv ℂ Ψ (p, circleMap c ρ θ)‖ * ‖ContinuousLinearMap.inl ℂ P ℂ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℂ Ψ (p, circleMap c ρ θ)‖ * 1 := by
          gcongr
          exact ContinuousLinearMap.norm_inl_le_one ℂ P ℂ
      _ ≤ M := by rw [mul_one]; exact hM _ ⟨hp, circleMap_mem_sphere c hρ θ⟩
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 2 * π) (F := F) (F' := F') (x₀ := p₀)
    (bound := fun _ => |ρ| * M) (ball_mem_nhds p₀ hδ)
    (eventually_of_mem (ball_mem_nhds p₀ hδ) fun p hp =>
      (hFc p (ball_subset_closedBall hp)).aestronglyMeasurable)
    ((hFc p₀ (mem_closedBall_self hδ.le)).intervalIntegrable _ _)
    (by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF', deriv_circleMap]
      refine ((continuous_circleMap 0 ρ).mul continuous_const).smul ?_
      refine Continuous.clm_comp ?_ continuous_const
      exact hcd.comp_continuous (continuous_const.prodMk (continuous_circleMap c ρ))
        (hmem p₀ (mem_closedBall_self hδ.le)))
    (Eventually.of_forall fun θ _ p hp => hbound p (ball_subset_closedBall hp) θ)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ p hp => by
      have hd : HasFDerivAt Ψ (fderiv ℂ Ψ (p, circleMap c ρ θ)) (p, circleMap c ρ θ) :=
        (hΨ.differentiableAt (hO.mem_nhds (hmem p (ball_subset_closedBall hp) θ))).hasFDerivAt
      exact (hd.comp p (hasFDerivAt_prodMk_left (𝕜 := ℂ) p (circleMap c ρ θ))).const_smul
        (deriv (circleMap c ρ) θ))
  exact hderiv.differentiableAt

end Parametric

section OneVariable

/-- **One-variable Riemann extension with a Cauchy formula.** Let `ψ` be holomorphic on
`ball 0 R`, nonvanishing on the circle `‖τ‖ = ρ < R`, and let `φ` be holomorphic and bounded
on `ball 0 R \ ψ⁻¹(0)`. Then the Cauchy integral of `φ` over the circle of radius `ρ`
reproduces `φ` at every point of `ball 0 ρ` off the zero set of `ψ`. -/
theorem cauchy_integral_eq_of_bounded {ψ φ : ℂ → ℂ} {R ρ C : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hψ : DifferentiableOn ℂ ψ (ball 0 R)) (hψρ : ∀ τ ∈ sphere (0 : ℂ) ρ, ψ τ ≠ 0)
    (hφ : ∀ τ ∈ ball (0 : ℂ) R, ψ τ ≠ 0 → DifferentiableAt ℂ φ τ)
    (hφb : ∀ τ ∈ ball (0 : ℂ) R, ψ τ ≠ 0 → ‖φ τ‖ ≤ C) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ρ)
    (hψt : ψ t ≠ 0) :
    ((2 * π * I : ℂ)⁻¹ • ∮ τ in C(0, ρ), (τ - t)⁻¹ • φ τ) = φ t := by
  classical
  set φ' : ℂ → ℂ := fun τ => if ψ τ = 0 then limUnder (𝓝[≠] τ) φ else φ τ with hφ'
  have hψa : AnalyticOnNhd ℂ ψ (ball 0 R) := hψ.analyticOnNhd isOpen_ball
  have hρmem : ((ρ : ℂ)) ∈ sphere (0 : ℂ) ρ := by simp [hρ.le]
  have hne : ∀ τ₀ ∈ ball (0 : ℂ) R, ∀ᶠ τ in 𝓝[≠] τ₀, ψ τ ≠ 0 := by
    intro τ₀ hτ₀
    refine (hψa τ₀ hτ₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun H => ?_
    have := hψa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected hτ₀ H
      (sphere_subset_ball hρR hρmem)
    exact hψρ _ hρmem this
  have hdiff : DifferentiableOn ℂ φ' (ball 0 R) := by
    intro τ₀ hτ₀
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases h0 : ψ τ₀ = 0
    · obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1
        ((eventually_nhdsWithin_iff.1 (hne τ₀ hτ₀)).and (isOpen_ball.mem_nhds hτ₀))
      have hdu := Complex.differentiableOn_update_limUnder_of_bddAbove
        (f := φ) (s := ball τ₀ ε) (c := τ₀) (ball_mem_nhds τ₀ hε)
        (fun τ hτ => (hφ τ (hεs τ hτ.1).2 ((hεs τ hτ.1).1 hτ.2)).differentiableWithinAt)
        ⟨C, by
          rintro _ ⟨τ, hτ, rfl⟩
          exact hφb τ (hεs τ hτ.1).2 ((hεs τ hτ.1).1 hτ.2)⟩
      refine (hdu.differentiableAt (ball_mem_nhds τ₀ hε)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds τ₀ hε] with τ hτ
      by_cases hττ : τ = τ₀
      · subst hττ; simp [hφ', h0]
      · simp [hφ', Function.update_of_ne hττ, (hεs τ hτ).1 hττ]
    · have hev : ∀ᶠ τ in 𝓝 τ₀, ψ τ ≠ 0 :=
        (hψ.differentiableAt (isOpen_ball.mem_nhds hτ₀)).continuousAt.eventually_ne h0
      refine (hφ τ₀ hτ₀ h0).congr_of_eventuallyEq ?_
      filter_upwards [hev] with τ hτ
      simp [hφ', hτ]
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hcauchy := (hdiff.mono hcl).circleIntegral_sub_inv_smul ht
  have hcongr : (∮ τ in C(0, ρ), (τ - t)⁻¹ • φ τ) = ∮ τ in C(0, ρ), (τ - t)⁻¹ • φ' τ :=
    circleIntegral.integral_congr hρ.le fun τ hτ => by simp [hφ', hψρ τ hτ]
  rw [hcongr, hcauchy, inv_smul_smul₀ two_pi_I_ne_zero]
  simp [hφ', hψt]

end OneVariable

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Riemann extension on `E × ℂ`**, for `h` regular in the last variable: `h (0, t) ≠ 0`
for small `t ≠ 0`. A function holomorphic and bounded near `0` off `h⁻¹(0)` agrees near `0`,
off `h⁻¹(0)`, with a function holomorphic near `0`. -/
theorem exists_extension_prod {h f : E × ℂ → ℂ}
    (hh : ∀ᶠ z in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ h z)
    (hreg : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (0, t) ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (0 : E × ℂ), h z ≠ 0 → DifferentiableAt ℂ f z)
    (hbdd : ∃ C, ∀ᶠ z in 𝓝 (0 : E × ℂ), h z ≠ 0 → ‖f z‖ ≤ C) :
    ∃ F : E × ℂ → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) ∧
      ∀ᶠ z in 𝓝 0, h z ≠ 0 → F z = f z := by
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨R, hR, hRs⟩ := Metric.eventually_nhds_iff_ball.1 (hh.and (hf.and hC))
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 hreg)
  set ρ : ℝ := min ε R / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by have := min_le_left ε R; linarith
  have hρR : ρ < R := by have := min_le_right ε R; linarith
  -- the open set where `h ≠ 0`
  set O₁ : Set (E × ℂ) := ball 0 R ∩ h ⁻¹' {0}ᶜ with hO₁
  have hhc : ContinuousOn h (ball 0 R) := fun z hz =>
    (hRs z hz).1.continuousAt.continuousWithinAt
  have hO₁o : IsOpen O₁ := hhc.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hO₁R : ∀ x : E, ∀ τ : ℂ, (x, τ) ∈ O₁ → ‖x‖ < R ∧ ‖τ‖ < R := fun x τ hx => by
    have := mem_ball_zero_iff.1 hx.1
    rw [Prod.norm_def, max_lt_iff] at this
    exact this
  -- tube lemma around `{0} × sphere 0 ρ`
  have hK₀ : IsCompact (({(0 : E)} : Set E) ×ˢ sphere (0 : ℂ) ρ) :=
    isCompact_singleton.prod (isCompact_sphere 0 ρ)
  obtain ⟨r, hr, hrO⟩ := hK₀.exists_cthickening_subset_open hO₁o (by
    rintro ⟨x, τ⟩ ⟨hx, hτ⟩
    rw [mem_singleton_iff] at hx
    subst hx
    have hτn : ‖τ‖ = ρ := mem_sphere_zero_iff_norm.1 hτ
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, hτn, max_lt_iff]
      exact ⟨hR, hρR⟩
    · refine hεs τ (mem_ball_zero_iff.2 (hτn ▸ hρε)) ?_
      rintro rfl
      rw [norm_zero] at hτn
      exact hρ.ne hτn)
  have htube : ∀ x ∈ ball (0 : E) r, ∀ τ ∈ sphere (0 : ℂ) ρ, (x, τ) ∈ O₁ := by
    intro x hx τ hτ
    refine hrO (Metric.mem_cthickening_of_dist_le _ ((0 : E), τ) r _ ⟨rfl, hτ⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_le_iff, dist_zero_right]
    exact ⟨(mem_ball_zero_iff.1 hx).le, hr.le⟩
  -- the extension
  set F : E × ℂ → ℂ := fun z =>
    (2 * π * I : ℂ)⁻¹ • ∮ τ in C(0, ρ), (τ - z.2)⁻¹ • f (z.1, τ) with hF
  have hsmall : ∀ z ∈ ball (0 : E × ℂ) (min r ρ), z.1 ∈ ball (0 : E) r ∧ z.2 ∈ ball (0 : ℂ) ρ :=
    fun z hz => by
      have := mem_ball_zero_iff.1 hz
      rw [Prod.norm_def, max_lt_iff, lt_min_iff, lt_min_iff] at this
      exact ⟨mem_ball_zero_iff.2 this.1.1, mem_ball_zero_iff.2 this.2.2⟩
  have hρmem : ((ρ : ℂ)) ∈ sphere (0 : ℂ) ρ := by simp [hρ.le]
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : E × ℂ) (lt_min hr hρ)] with z hz
    obtain ⟨hz1, hz2⟩ := hsmall z hz
    set O : Set ((E × ℂ) × ℂ) := {q | (q.1.1, q.2) ∈ O₁ ∧ q.2 - q.1.2 ≠ 0} with hO
    have hOo : IsOpen O :=
      (hO₁o.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
        (isOpen_ne_fun (continuous_snd.sub continuous_fst.snd) continuous_const)
    have hΨ : DifferentiableOn ℂ
        (fun q : (E × ℂ) × ℂ => (q.2 - q.1.2)⁻¹ • f (q.1.1, q.2)) O := by
      intro q hq
      refine DifferentiableAt.differentiableWithinAt ?_
      have hfq : DifferentiableAt ℂ f (q.1.1, q.2) := (hRs _ hq.1.1).2.1 hq.1.2
      have h1 : DifferentiableAt ℂ (fun q : (E × ℂ) × ℂ => (q.2 - q.1.2)⁻¹) q :=
        (differentiableAt_snd.sub differentiableAt_fst.snd).inv hq.2
      have h2 : DifferentiableAt ℂ (fun q : (E × ℂ) × ℂ => f (q.1.1, q.2)) q :=
        hfq.comp q (differentiableAt_fst.fst.prodMk differentiableAt_snd)
      exact h1.smul h2
    have := differentiableAt_circleIntegral_param hOo hΨ hρ.le (p₀ := z) fun τ hτ => by
      refine ⟨htube z.1 hz1 τ hτ, sub_ne_zero.2 ?_⟩
      intro heq
      have heq' : τ = z.2 := heq
      rw [mem_sphere_zero_iff_norm, heq'] at hτ
      rw [mem_ball_zero_iff, hτ] at hz2
      exact lt_irrefl _ hz2
    exact (this.const_smul ((2 * π * I : ℂ)⁻¹)).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  · filter_upwards [ball_mem_nhds (0 : E × ℂ) (lt_min hr hρ)] with z hz hz0
    obtain ⟨hz1, hz2⟩ := hsmall z hz
    have hxR : ‖z.1‖ < R := (hO₁R _ _ (htube z.1 hz1 (ρ : ℂ) hρmem)).1
    have hmemR : ∀ τ ∈ ball (0 : ℂ) R, (z.1, τ) ∈ ball (0 : E × ℂ) R := fun τ hτ =>
      mem_ball_zero_iff.2 (by rw [Prod.norm_def, max_lt_iff]; exact ⟨hxR, mem_ball_zero_iff.1 hτ⟩)
    have hline : ∀ τ : ℂ, DifferentiableAt ℂ (fun τ : ℂ => (z.1, τ)) τ := fun τ =>
      (differentiableAt_const _).prodMk differentiableAt_id
    exact cauchy_integral_eq_of_bounded (ψ := fun τ => h (z.1, τ)) (φ := fun τ => f (z.1, τ))
      hρ hρR
      (fun τ hτ => ((hRs _ (hmemR τ hτ)).1.comp τ (hline τ)).differentiableWithinAt)
      (fun τ hτ => (htube z.1 hz1 τ hτ).2)
      (fun τ hτ hne => ((hRs _ (hmemR τ hτ)).2.1 hne).comp τ (hline τ))
      (fun τ hτ hne => (hRs _ (hmemR τ hτ)).2.2 hne) hz2 hz0

end Product

section Transfer

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- The trivial case of the Riemann extension theorem: `h 0 ≠ 0`, and `F = f`. -/
theorem exists_extension_of_apply_zero_ne_zero {h f : E' → ℂ}
    (hh : ∀ᶠ z in 𝓝 (0 : E'), DifferentiableAt ℂ h z) (h0 : h 0 ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (0 : E'), h z ≠ 0 → DifferentiableAt ℂ f z) :
    ∃ F : E' → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) ∧
      ∀ᶠ z in 𝓝 0, h z ≠ 0 → F z = f z := by
  refine ⟨f, ?_, Eventually.of_forall fun _ _ => rfl⟩
  filter_upwards [hf, hh.self_of_nhds.continuousAt.eventually_ne h0] with z hz hz0
  exact hz hz0

/-- **Riemann extension** near `0` in a space `E'` split as `E × ℂ` by a continuous linear
equivalence `L`, for `h` regular in the direction `L (0, 1)`. -/
theorem exists_extension_of_continuousLinearEquiv [FiniteDimensional ℂ E]
    (L : (E × ℂ) ≃L[ℂ] E') {h f : E' → ℂ} (hh : ∀ᶠ z in 𝓝 (0 : E'), DifferentiableAt ℂ h z)
    (hreg : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (L (0, t)) ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (0 : E'), h z ≠ 0 → DifferentiableAt ℂ f z)
    (hbdd : ∃ C, ∀ᶠ z in 𝓝 (0 : E'), h z ≠ 0 → ‖f z‖ ≤ C) :
    ∃ F : E' → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) ∧
      ∀ᶠ z in 𝓝 0, h z ≠ 0 → F z = f z := by
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by simpa using L.continuous.tendsto 0
  have hL' : Tendsto L.symm (𝓝 0) (𝓝 0) := by simpa using L.symm.continuous.tendsto 0
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨F₀, hF₀d, hF₀e⟩ := exists_extension_prod (h := h ∘ L) (f := f ∘ L)
    ((hL.eventually hh).mono fun z hz => hz.comp z L.differentiableAt) hreg
    ((hL.eventually hf).mono fun z hz hz0 => (hz hz0).comp z L.differentiableAt)
    ⟨C, hL.eventually hC⟩
  refine ⟨F₀ ∘ L.symm,
    (hL'.eventually hF₀d).mono fun z hz => hz.comp z L.symm.differentiableAt,
    (hL'.eventually hF₀e).mono fun z hz hz0 => ?_⟩
  have := hz (by simpa using hz0)
  simpa using this

end Transfer

section Euclidean

/-- **Riemann extension theorem**, germ form on `ℂ^d`. -/
theorem exists_extension_euclidean {d : ℕ} {h f : EuclideanSpace ℂ (Fin d) → ℂ}
    (hh : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ h z) (hne : ¬ ∀ᶠ z in 𝓝 0, h z = 0)
    (hf : ∀ᶠ z in 𝓝 0, h z ≠ 0 → DifferentiableAt ℂ f z)
    (hbdd : ∃ C, ∀ᶠ z in 𝓝 0, h z ≠ 0 → ‖f z‖ ≤ C) :
    ∃ F : EuclideanSpace ℂ (Fin d) → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) ∧
      ∀ᶠ z in 𝓝 0, h z ≠ 0 → F z = f z := by
  rcases d with _ | n
  · refine exists_extension_of_apply_zero_ne_zero hh
      (fun h0 => hne (Eventually.of_forall fun z => ?_)) hf
    rwa [Subsingleton.elim z 0]
  · set e : EuclideanSpace ℂ (Fin (n + 1)) := (euclideanSnocCLE n).symm (0, 1) with he
    have he0 : e ≠ 0 := by
      intro H
      have := congrArg (euclideanSnocCLE n) H
      simp [he] at this
    obtain ⟨A, s, u, hu, hu0, hA⟩ := exists_regular_continuousLinearEquiv hh hne he0
    refine exists_extension_of_continuousLinearEquiv ((euclideanSnocCLE n).symm.trans A) hh ?_
      hf hbdd
    have hL : ∀ t : ℂ, ((euclideanSnocCLE n).symm.trans A) (0, t) = A (t • e) := fun t => by
      have h1 : ((0 : EuclideanSpace ℂ (Fin n)), t) =
          t • ((0 : EuclideanSpace ℂ (Fin n)), (1 : ℂ)) := by simp
      rw [ContinuousLinearEquiv.trans_apply, h1, map_smul]
    filter_upwards [nhdsWithin_le_nhds (hA.and (hu.continuousAt.eventually_ne hu0)),
      self_mem_nhdsWithin] with t ht ht0
    rw [hL, ht.1]
    exact mul_ne_zero (pow_ne_zero _ ht0) ht.2

/-- **Riemann extension theorem.** Let `h` be holomorphic on the ball `B = ball 0 r` of `ℂ^d`
and not identically zero near `0`, and let `f` be holomorphic and bounded on `B \ h⁻¹(0)`.
Then there are a smaller ball `ball 0 ρ` and a holomorphic `F` on it with `F = f` off
`h⁻¹(0)`. -/
theorem exists_extension_of_bounded {d : ℕ} {r : ℝ} (hr : 0 < r)
    {h f : EuclideanSpace ℂ (Fin d) → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (hne : ¬ ∀ᶠ z in 𝓝 0, h z = 0)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r \ h ⁻¹' {0}))
    (hbdd : ∃ C, ∀ z ∈ Metric.ball 0 r \ h ⁻¹' {0}, ‖f z‖ ≤ C) :
    ∃ ρ > 0, ∃ F : EuclideanSpace ℂ (Fin d) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧
      ∀ z ∈ Metric.ball 0 ρ, h z ≠ 0 → F z = f z := by
  have hU : IsOpen (ball (0 : EuclideanSpace ℂ (Fin d)) r \ h ⁻¹' {0}) :=
    hh.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨F, hFd, hFe⟩ := exists_extension_euclidean (h := h) (f := f)
    (eventually_of_mem (ball_mem_nhds 0 hr) fun z hz =>
      hh.differentiableAt (isOpen_ball.mem_nhds hz)) hne
    (eventually_of_mem (ball_mem_nhds 0 hr) fun z hz hz0 =>
      hf.differentiableAt (hU.mem_nhds ⟨hz, hz0⟩))
    ⟨C, eventually_of_mem (ball_mem_nhds 0 hr) fun z hz hz0 => hC z ⟨hz, hz0⟩⟩
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.1 (hFd.and hFe)
  exact ⟨ρ, hρ, F, fun z hz => (hρs z hz).1.differentiableWithinAt, fun z hz => (hρs z hz).2⟩

end Euclidean

end

end SGPT.Foundations.Analysis.Pending.RiemannExtension
