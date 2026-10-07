/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.Compact

/-!
# Equicontinuity in time from spatial mollification

This file proves the abstract analytic step behind route D5 for `prop:aniso:small`: a way to
obtain equicontinuity in time of a rescaled potential-vorticity sequence without controlling a
negative-order Sobolev norm of its time derivative.

The setting is a sequence `Θ n : (ℝ × ℝ) × ℝ → ℝ` of functions of a spatial variable in
`ℝ × ℝ` and a time variable in `ℝ`, uniformly Lipschitz in space on a compact set `K`
(hypothesis `hlip`), together with a pairing hypothesis `hpair`: for
every smooth, compactly supported test function `ψ` with support in `interior K` and every
sup-norm budget `B` for `ψ` and its first two derivatives, the time difference of `Θ n`
paired against `ψ` is controlled by `Cₒ * B * |τ − τ'|` for one constant `Cₒ`, independent of
`ψ`, `B`, `n`, `τ`, and `τ'`. This is exactly the estimate integration by parts produces when
`∂_τ Θ n` is a finite sum of spatial derivatives, of order at most two, of quantities bounded
on `K` uniformly in `n`: the constant `Cₒ` collects the number of terms, their bounds, and the
measure of `K`, so it is genuinely independent of the test function used, which is essential
because the argument below applies `hpair` to a whole family of translated test functions
sharing one budget `B`.

The main theorem `equicontinuous_of_lipschitz_of_pairings` derives equicontinuity in time,
locally uniform in space on compact subsets `K'` of `interior K`: mollifying `Θ n (·, τ)`
against a bump `ψ_η` of radius `η` centered at a point `y ∈ K'` gives
`Θ n (y, τ) − Θ n (y, τ') = (Θ n (y, τ) − (Θ n (·, τ) ∗ ψ_η) y) + ((Θ n (·, τ) − Θ n (·, τ')) ∗
ψ_η) y + ((Θ n (·, τ') ∗ ψ_η) y − Θ n (y, τ'))`. The two outer terms are bounded by the spatial
Lipschitz constant times `η` (`abs_sub_integral_mul_le`), independently of the pairing
hypothesis, while the middle term is exactly what `hpair` bounds, applied to the translate of
the fixed profile `ψ_η` (`exists_bump_with_uniform_bound`, `bound_of_translate`). Choosing `η`
small so the outer terms are below `ε / 2`, then `δ` small so the middle term is below `ε / 2`
whenever `|τ − τ'| < δ`, gives the equicontinuity modulus, uniform in `n` and in `y ∈ K'`.
-/

public section

open Function Metric MeasureTheory Set
open scoped Topology

noncomputable section

namespace CIV

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- A continuous function on `ℝ × ℝ` with compact support is bounded, with an explicit
nonnegative bound valid at every point. -/
theorem exists_bound_of_hasCompactSupport {g : ℝ × ℝ → F} (hc : Continuous g)
    (hs : HasCompactSupport g) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M := by
  rcases (tsupport g).eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, le_refl 0, fun x => ?_⟩
    have hg0 : g = 0 := tsupport_eq_empty_iff.mp hempty
    simp [hg0]
  · obtain ⟨z, -, hmax⟩ := hs.exists_isMaxOn hne hc.norm.continuousOn
    refine ⟨‖g z‖, norm_nonneg _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport g
    · exact hmax hx
    · have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this, norm_nonneg]

omit [NormedSpace ℝ F] in
/-- The derivative of a spatial translate is the translated derivative: differentiating
`x ↦ g (x - p)` at `x` gives the same continuous linear map as differentiating `g` itself at
`x - p`. Used twice below, once for the bump profile and once for its own derivative, to show
that a family of translated bump functions shares a common derivative bound. -/
theorem fderiv_sub_const_apply [NormedSpace ℝ F] {g : ℝ × ℝ → F} (hg : Differentiable ℝ g)
    (p x : ℝ × ℝ) : fderiv ℝ (fun x => g (x - p)) x = fderiv ℝ g (x - p) := by
  have hT : HasFDerivAt (fun x : ℝ × ℝ => x - p) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => x) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
      hasFDerivAt_id x
    have h2 : HasFDerivAt (fun _ : ℝ × ℝ => p) (0 : ℝ × ℝ →L[ℝ] ℝ × ℝ) x := hasFDerivAt_const p x
    have h3 := h1.sub h2
    rwa [sub_zero] at h3
  have hg' : HasFDerivAt g (fderiv ℝ g (x - p)) (x - p) := (hg (x - p)).hasFDerivAt
  have hcomp := HasFDerivAt.comp (f := fun x : ℝ × ℝ => x - p) (x := x) hg' hT
  rw [ContinuousLinearMap.comp_id] at hcomp
  exact hcomp.fderiv

/-- A bump function continuous on `ℝ × ℝ` with support in a ball whose closure lies in a
compact set `K` has compact support. -/
theorem hasCompactSupport_of_ball_subset {K : Set (ℝ × ℝ)} (hK : IsCompact K) {p : ℝ × ℝ}
    {η : ℝ} {φ : ℝ × ℝ → ℝ} (hφsupp : Function.support φ ⊆ Metric.ball p η)
    (hballK : Metric.closedBall p η ⊆ K) : HasCompactSupport φ := by
  have hφsupp' : Function.support φ ⊆ K := hφsupp.trans (ball_subset_closedBall.trans hballK)
  have hcl : tsupport φ ⊆ K := closure_minimal hφsupp' hK.isClosed
  exact hK.of_isClosed_subset (isClosed_tsupport φ) hcl

/-- A function continuous on a compact set `K`, multiplied by a continuous bump supported in a
ball whose closure lies in `K`, is (globally) integrable: the product vanishes outside `K`,
where it agrees with a function continuous on the compact set `K`. -/
theorem integrable_mul_of_ball_subset {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hfCont : ContinuousOn f K) {p : ℝ × ℝ} {η : ℝ} {φ : ℝ × ℝ → ℝ} (hφcont : Continuous φ)
    (hφsupp : Function.support φ ⊆ Metric.ball p η) (hballK : Metric.closedBall p η ⊆ K) :
    Integrable (fun y => f y * φ y) := by
  have hφsupp' : Function.support φ ⊆ K := hφsupp.trans (ball_subset_closedBall.trans hballK)
  have hFcont : ContinuousOn (fun y => f y * φ y) K := hfCont.mul hφcont.continuousOn
  have hFsupp : Function.support (fun y => f y * φ y) ⊆ K := by
    intro y hy
    refine hφsupp' fun hy0 => hy ?_
    simp [hy0]
  exact (integrableOn_iff_integrable_of_support_subset hFsupp).mp (hFcont.integrableOn_compact hK)

/-- Mollifying a function that is Lipschitz on a compact set `K` against a nonnegative, mass-one
bump `φ` supported in the ball of radius `η` around a point `p`, with that ball contained in `K`,
changes the value at `p` by at most the Lipschitz constant times `η`. -/
theorem abs_sub_integral_mul_le {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    {L : ℝ} (hL : 0 ≤ L) {p : ℝ × ℝ} (hp : p ∈ K) (hlip : LipschitzOnWith L.toNNReal f K)
    {η : ℝ} {φ : ℝ × ℝ → ℝ} (hφnn : ∀ x, 0 ≤ φ x) (hφcont : Continuous φ)
    (hφsupp : Function.support φ ⊆ Metric.ball p η) (hφint : ∫ x, φ x = 1)
    (hballK : Metric.closedBall p η ⊆ K) :
    |f p - ∫ y, f y * φ y| ≤ L * η := by
  have hφHCS : HasCompactSupport φ := hasCompactSupport_of_ball_subset hK hφsupp hballK
  have hfCont : ContinuousOn f K := hlip.continuousOn
  have hFInt : Integrable (fun y => f y * φ y) :=
    integrable_mul_of_ball_subset hK hfCont hφcont hφsupp hballK
  have hφInt : Integrable φ := hφcont.integrable_of_hasCompactSupport hφHCS
  have hFconstInt : Integrable (fun y => f p * φ y) := hφInt.const_mul (f p)
  have h1 : (fun y => (f p - f y) * φ y) = fun y => f p * φ y - f y * φ y := by
    funext y; ring
  have hEq : f p - ∫ y, f y * φ y = ∫ y, (f p - f y) * φ y := by
    rw [h1, integral_sub hFconstInt hFInt, integral_const_mul, hφint, mul_one]
  rw [hEq]
  have hbound : ∀ y, |(f p - f y) * φ y| ≤ (L * η) * φ y := by
    intro y
    rcases eq_or_ne (φ y) 0 with hφy | hφy
    · simp [hφy]
    · have hyy : y ∈ Function.support φ := hφy
      have hyb : y ∈ Metric.ball p η := hφsupp hyy
      have hyK : y ∈ K := hballK (ball_subset_closedBall hyb)
      have hd : dist (f y) (f p) ≤ (L.toNNReal : ℝ) * dist y p := hlip.dist_le_mul y hyK p hp
      rw [Real.coe_toNNReal L hL] at hd
      have hdist : dist y p < η := hyb
      have hle : |f p - f y| ≤ L * η := by
        have h2 : |f p - f y| = dist (f y) (f p) := by
          rw [Real.dist_eq, abs_sub_comm]
        rw [h2]
        calc dist (f y) (f p) ≤ L * dist y p := hd
          _ ≤ L * η := mul_le_mul_of_nonneg_left hdist.le hL
      calc |(f p - f y) * φ y| = |f p - f y| * φ y := by rw [abs_mul, abs_of_nonneg (hφnn y)]
        _ ≤ (L * η) * φ y := mul_le_mul_of_nonneg_right hle (hφnn y)
  have hSubInt : Integrable (fun y => (f p - f y) * φ y) := by
    rw [h1]; exact hFconstInt.sub hFInt
  have hAbsLe : |∫ y, (f p - f y) * φ y| ≤ ∫ y, |(f p - f y) * φ y| := by
    have := norm_integral_le_integral_norm (fun y => (f p - f y) * φ y) (μ := volume)
    simpa [Real.norm_eq_abs] using this
  have hMono : ∫ y, |(f p - f y) * φ y| ≤ ∫ y, (L * η) * φ y :=
    integral_mono hSubInt.abs (hφInt.const_mul (L * η)) hbound
  have hFinal : ∫ y, (L * η) * φ y = L * η := by rw [integral_const_mul, hφint, mul_one]
  calc |∫ y, (f p - f y) * φ y| ≤ ∫ y, |(f p - f y) * φ y| := hAbsLe
    _ ≤ ∫ y, (L * η) * φ y := hMono
    _ = L * η := hFinal

/-- For every radius `η > 0` there is a smooth, nonnegative, mass-one bump `κ` on `ℝ × ℝ`,
supported in the open ball of radius `η` around the origin, together with a single nonnegative
real number bounding `κ` itself, its derivative, and its second derivative at every point. -/
theorem exists_bump_with_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ κ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) κ ∧ (∀ x, 0 ≤ κ x) ∧ (∫ x, κ x = 1) ∧
      Function.support κ ⊆ Metric.ball (0 : ℝ × ℝ) η ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |κ x| ≤ B ∧ ‖fderiv ℝ κ x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ κ) x‖ ≤ B := by
  let hbump : ContDiffBump (0 : ℝ × ℝ) := ⟨η / 2, η, by positivity, by linarith only [hη]⟩
  set κ := hbump.normed (volume : Measure (ℝ × ℝ)) with hκdef
  have hκSmooth : ContDiff ℝ (⊤ : ℕ∞) κ := hbump.contDiff_normed
  have hκHCS : HasCompactSupport κ := hbump.hasCompactSupport_normed
  obtain ⟨C, hCnn, hC⟩ := hκHCS.exists_bound_iteratedFDeriv hκSmooth 2
  have hC0 := hC 0 (by norm_num)
  have hC1 := hC 1 (by norm_num)
  have hC2 := hC 2 le_rfl
  have hb0 : ∀ x, |κ x| ≤ C := by
    intro x
    have h := hC0 x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hb1 : ∀ x, ‖fderiv ℝ κ x‖ ≤ C := by
    intro x
    have h := hC1 x
    rwa [norm_iteratedFDeriv_one] at h
  have hb2 : ∀ x, ‖fderiv ℝ (fderiv ℝ κ) x‖ ≤ C := by
    intro x
    have hvw : ∀ v w : ℝ × ℝ, ‖(fderiv ℝ (fderiv ℝ κ) x) v w‖ ≤ C * ‖v‖ * ‖w‖ := by
      intro v w
      have heq : (fderiv ℝ (fderiv ℝ κ) x) v w = iteratedFDeriv ℝ 2 κ x ![v, w] := by
        rw [iteratedFDeriv_two_apply]; simp
      rw [heq]
      calc ‖iteratedFDeriv ℝ 2 κ x ![v, w]‖
          ≤ ‖iteratedFDeriv ℝ 2 κ x‖ * ∏ i, ‖(![v, w] : Fin 2 → ℝ × ℝ) i‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ 2 κ x‖ * (‖v‖ * ‖w‖) := by rw [Fin.prod_univ_two]; simp
        _ ≤ C * ‖v‖ * ‖w‖ := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (hC2 x) (by positivity)
    have hinner : ∀ v : ℝ × ℝ, ‖(fderiv ℝ (fderiv ℝ κ) x) v‖ ≤ C * ‖v‖ := fun v =>
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hvw v)
    exact ContinuousLinearMap.opNorm_le_bound _ hCnn hinner
  refine ⟨κ, hκSmooth, hbump.nonneg_normed, hbump.integral_normed, ?_, C, hCnn,
    fun x => ⟨hb0 x, hb1 x, hb2 x⟩⟩
  have hsupp := hbump.support_normed_eq (μ := (volume : Measure (ℝ × ℝ)))
  have hrOut : hbump.rOut = η := rfl
  rw [hrOut] at hsupp
  simpa [hκdef] using hsupp.subset

/-- Translating a bounded bump profile `κ` to be centered at `p` preserves the pointwise bound
`B` on `κ` and on its first two derivatives: the derivative of a translate is the translate of
the derivative, which has the same norm. -/
theorem bound_of_translate {κ : ℝ × ℝ → ℝ} (hκSmooth : ContDiff ℝ (⊤ : ℕ∞) κ)
    {B : ℝ} (hB : ∀ x, |κ x| ≤ B ∧ ‖fderiv ℝ κ x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ κ) x‖ ≤ B)
    (p x : ℝ × ℝ) :
    |κ (x - p)| ≤ B ∧ ‖fderiv ℝ (fun x => κ (x - p)) x‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => κ (x - p))) x‖ ≤ B := by
  have hκDiff : Differentiable ℝ κ := hκSmooth.differentiable (by simp)
  have hd1Smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ κ) :=
    hκSmooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hκDiff2 : Differentiable ℝ (fderiv ℝ κ) := hd1Smooth.differentiable (by simp)
  obtain ⟨hb0, hb1, hb2⟩ := hB (x - p)
  refine ⟨hb0, ?_, ?_⟩
  · rw [fderiv_sub_const_apply hκDiff p x]; exact hb1
  · have heq1 : fderiv ℝ (fun x => κ (x - p)) = fun x => fderiv ℝ κ (x - p) := by
      funext x; exact fderiv_sub_const_apply hκDiff p x
    rw [heq1, fderiv_sub_const_apply hκDiff2 p x]
    exact hb2

/-- Equicontinuity in time, on interior compacts, of a sequence uniformly bounded and uniformly
Lipschitz in space, whose time-difference pairings against admissible test functions obey a
uniform Lipschitz bound in time with a constant depending only on a sup-norm budget for the test
function and its first two derivatives. This is the abstract route around negative Sobolev norms
recorded for `prop:aniso:small`: a spatial mollification at scale `η` controls the outer error by
the spatial Lipschitz constant times `η`, while the pairing hypothesis controls the mollified
difference in time, uniformly over the family of translated test functions used at every point of
the target compact. -/
theorem equicontinuous_of_lipschitz_of_pairings (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (J : Set ℝ) (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ) (L : ℝ)
    (hlip : ∀ n, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
      ∀ B : ℝ, 0 ≤ B → (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ n : ℕ, ∀ τ ∈ J, ∀ τ' ∈ J,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|) :
    ∀ K' : Set (ℝ × ℝ), IsCompact K' → K' ⊆ interior K →
      ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ y ∈ K', ∀ τ ∈ J, ∀ τ' ∈ J,
        |τ - τ'| < δ → |Θ n (y, τ) - Θ n (y, τ')| ≤ ε := by
  obtain ⟨Cₒ, hCₒnn, hpair'⟩ := hpair
  intro K' hK' hKK' ε hε
  obtain ⟨ρ, hρpos, hρ⟩ := hK'.exists_cthickening_subset_open isOpen_interior hKK'
  set L' := max L 0 with hL'def
  have hL'nn : (0 : ℝ) ≤ L' := le_max_right _ _
  have htoNN : Real.toNNReal L = Real.toNNReal L' := by
    rcases le_total 0 L with hLnn | hLnp
    · rw [hL'def, max_eq_left hLnn]
    · rw [hL'def, max_eq_right hLnp, Real.toNNReal_of_nonpos hLnp,
        Real.toNNReal_of_nonpos le_rfl]
  have hlip' : ∀ n, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L') (fun y => Θ n (y, τ)) K := by
    intro n τ hτ
    rw [← htoNN]
    exact hlip n τ hτ
  set η := min ρ (ε / (8 * (L' + 1))) with hηdef
  have hηpos : 0 < η := lt_min hρpos (by positivity)
  have hηρ : η ≤ ρ := min_le_left _ _
  have hη2 : 2 * L' * η ≤ ε / 2 := by
    have hηe : η ≤ ε / (8 * (L' + 1)) := min_le_right _ _
    have h1 : 2 * L' * η ≤ 2 * (L' + 1) * η := by
      have : 2 * L' ≤ 2 * (L' + 1) := by linarith only []
      exact mul_le_mul_of_nonneg_right this hηpos.le
    have h2 : 2 * (L' + 1) * η ≤ 2 * (L' + 1) * (ε / (8 * (L' + 1))) :=
      mul_le_mul_of_nonneg_left hηe (by positivity)
    have h3 : 2 * (L' + 1) * (ε / (8 * (L' + 1))) = ε / 4 := by
      field_simp
      ring
    calc 2 * L' * η ≤ 2 * (L' + 1) * η := h1
      _ ≤ 2 * (L' + 1) * (ε / (8 * (L' + 1))) := h2
      _ = ε / 4 := h3
      _ ≤ ε / 2 := by linarith only [hε]
  obtain ⟨κ, hκSmooth, hκnn, hκInt, hκsupp, B, hBnn, hB⟩ := exists_bump_with_uniform_bound η hηpos
  set δ := ε / (2 * (Cₒ * B) + 2) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδbound : Cₒ * B * δ ≤ ε / 2 := by
    have hCB : 0 ≤ Cₒ * B := mul_nonneg hCₒnn hBnn
    have hpos : (0 : ℝ) < 2 * (Cₒ * B) + 2 := by positivity
    have heq : (2 * (Cₒ * B) + 2) * δ = ε := by
      rw [hδdef]; field_simp
    have hle : Cₒ * B ≤ (2 * (Cₒ * B) + 2) / 2 := by linarith only []
    calc Cₒ * B * δ ≤ ((2 * (Cₒ * B) + 2) / 2) * δ :=
          mul_le_mul_of_nonneg_right hle hδpos.le
      _ = ((2 * (Cₒ * B) + 2) * δ) / 2 := by ring
      _ = ε / 2 := by rw [heq]
  refine ⟨δ, hδpos, ?_⟩
  intro n y hy τ hτ τ' hτ' hττ'
  have hyK : y ∈ K := interior_subset (hKK' hy)
  have hballK : Metric.closedBall y η ⊆ K := by
    have h1 : Metric.closedBall y η ⊆ Metric.cthickening ρ K' :=
      (Metric.closedBall_subset_cthickening hy η).trans
        (Metric.cthickening_mono hηρ K')
    exact h1.trans (hρ.trans interior_subset)
  set ψ : ℝ × ℝ → ℝ := fun x => κ (x - y) with hψdef
  have hκDiff : Differentiable ℝ κ := hκSmooth.differentiable (by simp)
  have hψSmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hκSmooth.comp ((contDiff_id (n := (⊤ : ℕ∞))).sub contDiff_const)
  have hψCont : Continuous ψ := hψSmooth.continuous
  have hψnn : ∀ x, 0 ≤ ψ x := fun x => hκnn (x - y)
  have hψsupp : Function.support ψ ⊆ Metric.ball y η := by
    intro x hx
    have hx' : x - y ∈ Function.support κ := hx
    have hb : dist (x - y) 0 < η := hκsupp hx'
    have heq : dist (x - y) 0 = dist x y := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
    rw [heq] at hb
    exact hb
  have hψHCS : HasCompactSupport ψ := hasCompactSupport_of_ball_subset hK hψsupp hballK
  have hψtsupp : tsupport ψ ⊆ interior K := by
    have h1 : tsupport ψ ⊆ Metric.closedBall y η := by
      have h2 : tsupport ψ ⊆ closure (Metric.ball y η) := closure_mono hψsupp
      exact h2.trans (closure_ball_subset_closedBall)
    have h3 : Metric.closedBall y η ⊆ Metric.cthickening ρ K' :=
      (Metric.closedBall_subset_cthickening hy η).trans
        (Metric.cthickening_mono hηρ K')
    exact h1.trans (h3.trans hρ)
  have hψInt : ∫ x, ψ x = 1 := by
    have hInv : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant :=
      Measure.prod.instIsAddRightInvariant
    rw [hψdef, MeasureTheory.integral_sub_right_eq_self κ y]
    exact hκInt
  have hψbound : ∀ x, |ψ x| ≤ B ∧ ‖fderiv ℝ ψ x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ B :=
    fun x => bound_of_translate hκSmooth hB y x
  have hmiddle := hpair' ψ hψSmooth hψHCS hψtsupp B hBnn hψbound n τ hτ τ' hτ'
  have hFIntτ : Integrable (fun z => Θ n (z, τ) * ψ z) :=
    integrable_mul_of_ball_subset hK (hlip' n τ hτ).continuousOn hψCont hψsupp hballK
  have hFIntτ' : Integrable (fun z => Θ n (z, τ') * ψ z) :=
    integrable_mul_of_ball_subset hK (hlip' n τ' hτ').continuousOn hψCont hψsupp hballK
  have hSplit : ∫ z, (Θ n (z, τ) - Θ n (z, τ')) * ψ z
      = (∫ z, Θ n (z, τ) * ψ z) - ∫ z, Θ n (z, τ') * ψ z := by
    have heq : (fun z => (Θ n (z, τ) - Θ n (z, τ')) * ψ z)
        = fun z => Θ n (z, τ) * ψ z - Θ n (z, τ') * ψ z := by
      funext z; ring
    rw [heq, integral_sub hFIntτ hFIntτ']
  have houter1 : |Θ n (y, τ) - ∫ z, Θ n (z, τ) * ψ z| ≤ L' * η :=
    abs_sub_integral_mul_le hK hL'nn hyK (hlip' n τ hτ) hψnn hψCont hψsupp hψInt hballK
  have houter2 : |Θ n (y, τ') - ∫ z, Θ n (z, τ') * ψ z| ≤ L' * η :=
    abs_sub_integral_mul_le hK hL'nn hyK (hlip' n τ' hτ') hψnn hψCont hψsupp hψInt hballK
  have hmiddle' : |(∫ z, Θ n (z, τ) * ψ z) - ∫ z, Θ n (z, τ') * ψ z| ≤ Cₒ * B * |τ - τ'| := by
    rw [← hSplit]; exact hmiddle
  have hkey : Θ n (y, τ) - Θ n (y, τ')
      = (Θ n (y, τ) - ∫ z, Θ n (z, τ) * ψ z)
        + ((∫ z, Θ n (z, τ) * ψ z) - ∫ z, Θ n (z, τ') * ψ z)
        + ((∫ z, Θ n (z, τ') * ψ z) - Θ n (y, τ')) := by ring
  have hfinal : |Θ n (y, τ) - Θ n (y, τ')| ≤ L' * η + Cₒ * B * |τ - τ'| + L' * η := by
    rw [hkey]
    calc |(Θ n (y, τ) - ∫ z, Θ n (z, τ) * ψ z)
          + ((∫ z, Θ n (z, τ) * ψ z) - ∫ z, Θ n (z, τ') * ψ z)
          + ((∫ z, Θ n (z, τ') * ψ z) - Θ n (y, τ'))|
        ≤ |Θ n (y, τ) - ∫ z, Θ n (z, τ) * ψ z|
          + |(∫ z, Θ n (z, τ) * ψ z) - ∫ z, Θ n (z, τ') * ψ z|
          + |(∫ z, Θ n (z, τ') * ψ z) - Θ n (y, τ')| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ L' * η + Cₒ * B * |τ - τ'| + L' * η := by
          have h5 : |(∫ z, Θ n (z, τ') * ψ z) - Θ n (y, τ')|
              = |Θ n (y, τ') - ∫ z, Θ n (z, τ') * ψ z| := by
            rw [abs_sub_comm]
          rw [h5]
          gcongr
  have hCₒBδ : Cₒ * B * |τ - τ'| ≤ Cₒ * B * δ := by
    have hCBnn : 0 ≤ Cₒ * B := mul_nonneg hCₒnn hBnn
    exact mul_le_mul_of_nonneg_left hττ'.le hCBnn
  calc |Θ n (y, τ) - Θ n (y, τ')| ≤ L' * η + Cₒ * B * |τ - τ'| + L' * η := hfinal
    _ ≤ L' * η + Cₒ * B * δ + L' * η := by gcongr
    _ = 2 * L' * η + Cₒ * B * δ := by ring
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

end CIV
