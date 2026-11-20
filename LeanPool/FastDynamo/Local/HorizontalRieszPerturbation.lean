/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalDeltaResolvent
public import LeanPool.FastDynamo.Local.HorizontalModeContour
public import LeanPool.FastDynamo.Local.HorizontalFormSmallness

/-!
# The Riesz projections of the perturbed horizontal generators

This module carries out the Riesz-projection step of the proof of `prop:local-seed` in the
paper:

> Restricting to `L²` gives the resolvents of `𝓛_{h,δ}` on `Γ`.  Integrating there, we deduce
> `‖P_{h,δ} - P⁰‖_{2→2} ≤ C(h^{1/4} + |δ-1|)`, where `P_{h,δ}` denotes the corresponding Riesz
> projection.

The input is the isolating contour `Γ` of `FastDynamo/Local/HorizontalModeContour.lean` and
the Neumann series of `FastDynamo/Local/HorizontalDeltaResolvent.lean`.  The perturbation is
run not only on `Γ` itself but on the slightly larger *open* annulus
`B(λ,3r/2) ∖ closedBall(λ,r/4)`, whose closure is a compact subset of the punctured ball; this costs
nothing, because the form perturbation of `eq:form-small` is independent of `z`, and the
uniform bounds of the unperturbed inverse are taken on that compact closed annulus.

The quantitative chain is

`‖P_{h,δ} - P⁰‖ ≤ r · ‖j‖ · (Bη(1-Bη)^{-1}) · C`,

with `B` the uniform bound for `𝔸_{V⁰}(z)^{-1} : V^* → V` on the annulus, `C` the uniform
bound for the solution map `𝔸_{V⁰}(z)^{-1}(pivot ·) : L² → H¹`, `η` the bound of
`eq:form-small`, and `r` the contour radius (the contour length `2πr` divided by `2π`).

The last section instantiates this at the smoothed seed family `v_h` and the diffusivity `δ`,
where `eq:form-small` of `FastDynamo/Local/HorizontalFormSmallness.lean` gives
`η ≤ C₁h^{1/4} + (2+N²)|δ-1|`, and produces the thresholds that make
`‖P_{h,δ} - P⁰‖_{2→2} < 1/4`, which together with `re⟨P⁰f_*,f_*⟩ > 3/4` gives the paper's
`re⟨P_δ f_*,f_*⟩ > 1/2` of `eq:local-spectral-witness`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

/-! ## Two generic additions -/

namespace HasResolventOn

universe u v v'

variable {X : Type u} {D : Type v} {D' : Type v'}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup D'] [NormedSpace ℂ D']

omit [CompleteSpace X] in
/-- **The contour-length bound for a difference of Riesz projections**, for two domain
operators with *different* bundled domains.  The statement of
`FastDynamo/Operator/RieszProjectionCalculus.lean` requires one common domain type; the
unperturbed generator `A_{V⁰}` and the perturbed generator `𝓛_{v_h,δ}` have different form
domains, so the same three-line proof is repeated here in the general shape. -/
theorem norm_rieszProjection_sub_le_of_domains {A : DomainOperator X D}
    {B : DomainOperator X D'} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hA : HasResolventOn A (Metric.sphere c R)) (hB : HasResolventOn B (Metric.sphere c R))
    (hbound : ∀ z ∈ Metric.sphere c R, ‖hA.stateResolvent z - hB.stateResolvent z‖ ≤ C) :
    ‖hA.rieszProjection - hB.rieszProjection‖ ≤ R * C := by
  rw [rieszProjection, rieszProjection, ← smul_sub]
  rw [← circleIntegral.integral_sub (hA.circleIntegrable_stateResolvent hR)
    (hB.circleIntegrable_stateResolvent hR)]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR hbound

end HasResolventOn

/-- For a unit vector the real parts of the quadratic forms of two operators differ by at most
their operator-norm distance.  This is the step from `‖P_{h,δ} - P⁰‖_{2→2} < 1/4` to the
witness inequality of `eq:local-spectral-witness`. -/
theorem abs_re_inner_apply_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P Q : H →L[ℂ] H) {f : H} (hf : ‖f‖ = 1) :
    |(inner ℂ (P f) f).re - (inner ℂ (Q f) f).re| ≤ ‖P - Q‖ := by
  have hsub : (inner ℂ (P f) f : ℂ) - inner ℂ (Q f) f = inner ℂ ((P - Q) f) f := by
    rw [sub_apply, inner_sub_left]
  have hre : (inner ℂ (P f) f).re - (inner ℂ (Q f) f).re =
      (inner ℂ ((P - Q) f) f : ℂ).re := by
    rw [← hsub, Complex.sub_re]
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  refine le_trans (norm_inner_le_norm (𝕜 := ℂ) ((P - Q) f) f) ?_
  rw [hf, mul_one]
  refine le_trans ((P - Q).le_opNorm f) ?_
  rw [hf, mul_one]

/-- The witness arithmetic of `eq:local-spectral-witness`: `> 3/4` for the unperturbed
projection and a perturbation `< 1/4` give `> 1/2`. -/
theorem re_inner_gt_half_of_lt_quarter {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {P Q : H →L[ℂ] H} {f : H}
    (hQ : 3 / 4 < (inner ℂ (Q f) f).re)
    (hPQ : |(inner ℂ (P f) f).re - (inner ℂ (Q f) f).re| < 1 / 4) :
    1 / 2 < (inner ℂ (P f) f).re := by
  have h := neg_lt_of_abs_lt hPQ
  linarith

/-- A positive threshold turning a bound on `x` into a bound on `x^{1/4}`, used to convert the
paper's smallness of `h^{1/4}` into a smallness of the smoothing width `h`. -/
theorem exists_pos_rpow_quarter_le {eps : ℝ} (heps : 0 < eps) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : ℝ, 0 ≤ x → x ≤ t → x ^ (1 / 4 : ℝ) ≤ eps := by
  refine ⟨eps ^ (4 : ℕ), by positivity, fun x hx hxt => ?_⟩
  have h1 : x ^ (1 / 4 : ℝ) ≤ (eps ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hx hxt (by norm_num)
  have h2 : (eps ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = eps := by
    rw [← Real.rpow_natCast eps 4, ← Real.rpow_mul heps.le]
    norm_num
  linarith

/-- `K/(4(K+1)) < 1/4` for `K ≥ 0`: the elementary inequality behind the explicit thresholds
`h₁`, `η₁` below. -/
theorem mul_two_inv_eight_add_one_lt {K : ℝ} (hK : 0 ≤ K) :
    K * (2 * (1 / (8 * (K + 1)))) < 1 / 4 := by
  have hKp : (0 : ℝ) < K + 1 := by linarith
  have hrw : K * (2 * (1 / (8 * (K + 1)))) = K / (4 * (K + 1)) := by
    field_simp
    ring
  have h1 : K / (4 * (K + 1)) * (4 * (K + 1)) = K := by field_simp
  rw [hrw]
  nlinarith [h1, hKp]

/-- **Threshold selection.**  For nonnegative `B`, `C₁` and `E` there are positive thresholds
below which the form perturbation `η = C₁x^{1/4} + Ey` of `eq:form-small` obeys the working
smallness `Bη ≤ 1/2` and the linear comparison `η ≤ M(x^{1/4}+y)` with `M = max C₁ E + 1`.
This is the pure real-arithmetic part of the seed perturbation theorem. -/
theorem exists_thresholds_smallness {B C1 E : ℝ} (hB0 : 0 ≤ B) (hC10 : 0 ≤ C1) :
    ∃ h0 eta0 : ℝ, 0 < h0 ∧ 0 < eta0 ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ h0 → y ≤ eta0 →
        B * (C1 * x ^ (1 / 4 : ℝ) + y * E) ≤ 1 / 2 ∧
          C1 * x ^ (1 / 4 : ℝ) + y * E ≤ (max C1 E + 1) * (x ^ (1 / 4 : ℝ) + y) := by
  have hMC1 : C1 ≤ max C1 E + 1 := by have := le_max_left C1 E; linarith
  have hME : E ≤ max C1 E + 1 := by have := le_max_right C1 E; linarith
  have hM1 : (0 : ℝ) < max C1 E + 1 := by
    have : (0 : ℝ) ≤ max C1 E := le_trans hC10 (le_max_left _ _)
    linarith
  have hBs0 : B * (1 / (2 * (B + 1))) ≤ 1 / 2 := by
    have hBp : (0 : ℝ) < B + 1 := by linarith
    have h1 : B / (2 * (B + 1)) * (2 * (B + 1)) = B := by field_simp
    have hrw : B * (1 / (2 * (B + 1))) = B / (2 * (B + 1)) := by field_simp
    rw [hrw]
    nlinarith [h1, hBp]
  have hepspos : (0 : ℝ) < 1 / (2 * (B + 1)) / (2 * (max C1 E + 1)) := by
    have hb : (0 : ℝ) < 2 * (B + 1) := by linarith
    have hm : (0 : ℝ) < 2 * (max C1 E + 1) := by linarith
    positivity
  obtain ⟨t, htpos, ht⟩ := exists_pos_rpow_quarter_le hepspos
  refine ⟨t, 1 / (2 * (B + 1)) / (2 * (max C1 E + 1)), htpos, hepspos,
    fun x y hx hy hxt hyt => ?_⟩
  have hq0 : (0 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx _
  have hq : x ^ (1 / 4 : ℝ) ≤ 1 / (2 * (B + 1)) / (2 * (max C1 E + 1)) := ht x hx hxt
  have hlin : C1 * x ^ (1 / 4 : ℝ) + y * E ≤ (max C1 E + 1) * (x ^ (1 / 4 : ℝ) + y) := by
    have e1 : C1 * x ^ (1 / 4 : ℝ) ≤ (max C1 E + 1) * x ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hMC1 hq0
    have e2 : y * E ≤ y * (max C1 E + 1) := mul_le_mul_of_nonneg_left hME hy
    have e3 : y * (max C1 E + 1) = (max C1 E + 1) * y := mul_comm _ _
    nlinarith [e1, e2, e3]
  refine ⟨?_, hlin⟩
  have hsum : x ^ (1 / 4 : ℝ) + y ≤ 2 * (1 / (2 * (B + 1)) / (2 * (max C1 E + 1))) := by
    linarith
  have e1 : (max C1 E + 1) * (x ^ (1 / 4 : ℝ) + y) ≤
      (max C1 E + 1) * (2 * (1 / (2 * (B + 1)) / (2 * (max C1 E + 1)))) :=
    mul_le_mul_of_nonneg_left hsum hM1.le
  have e2 : (max C1 E + 1) * (2 * (1 / (2 * (B + 1)) / (2 * (max C1 E + 1)))) =
      1 / (2 * (B + 1)) := by field_simp
  have e3 : C1 * x ^ (1 / 4 : ℝ) + y * E ≤ 1 / (2 * (B + 1)) := by linarith
  exact le_trans (mul_le_mul_of_nonneg_left e3 hB0) hBs0

namespace HorizontalWeakForm

namespace HorizontalIsolation

variable {N : ℝ} {w : WholePlaneC3LInf} {lam : ℂ}

/-! ## The Neumann annulus of an isolating contour -/

/-- The closed annulus `{r/4 ≤ |z-λ| ≤ 3r/2}`, a compact subset of the punctured ball on which
the unperturbed inverse `𝔸_w(z)^{-1} : V^* → V` is uniformly bounded. -/
def neumannSet (iso : HorizontalIsolation N w lam) : Set ℂ :=
  Metric.closedBall lam (3 * iso.radius / 2) \ Metric.ball lam (iso.radius / 4)

/-- The open annulus `{r/4 < |z-λ| < 3r/2}`, on which the perturbed resolvent is built.  It
contains the contour `Γ`. -/
def neumannOpen (iso : HorizontalIsolation N w lam) : Set ℂ :=
  Metric.ball lam (3 * iso.radius / 2) \ Metric.closedBall lam (iso.radius / 4)

/-- The closed Neumann annulus is compact. -/
theorem isCompact_neumannSet (iso : HorizontalIsolation N w lam) :
    IsCompact iso.neumannSet := by
  rw [neumannSet, Set.sdiff_eq]
  exact (isCompact_closedBall lam (3 * iso.radius / 2)).inter_right
    Metric.isOpen_ball.isClosed_compl

/-- The open Neumann annulus sits inside the closed one. -/
theorem neumannOpen_subset_neumannSet (iso : HorizontalIsolation N w lam) :
    iso.neumannOpen ⊆ iso.neumannSet := by
  rintro z ⟨hz1, hz2⟩
  exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz1).le,
    fun hmem => hz2 (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hmem).le)⟩

/-- The closed Neumann annulus sits inside the punctured doubled ball. -/
theorem neumannSet_subset_puncturedSet (iso : HorizontalIsolation N w lam) :
    iso.neumannSet ⊆ iso.puncturedSet := by
  rintro z ⟨hz1, hz2⟩
  have hle : dist z lam ≤ 3 * iso.radius / 2 := Metric.mem_closedBall.mp hz1
  have hge : iso.radius / 4 ≤ dist z lam :=
    not_lt.mp fun h => hz2 (Metric.mem_ball.mpr h)
  have hpos := iso.radius_pos
  refine ⟨Metric.mem_ball.mpr (by linarith), ?_⟩
  intro hmem
  rw [Set.mem_singleton_iff.mp hmem, dist_self] at hge
  linarith

/-- Every parameter of the closed Neumann annulus has positive real part. -/
theorem neumannSet_re_pos (iso : HorizontalIsolation N w lam) :
    ∀ z ∈ iso.neumannSet, 0 < z.re :=
  fun z hz => iso.puncturedSet_re_pos z (iso.neumannSet_subset_puncturedSet hz)

/-- The unperturbed shifted form operator is invertible on the closed Neumann annulus. -/
theorem neumannSet_isInvertible (iso : HorizontalIsolation N w lam) :
    ∀ z ∈ iso.neumannSet, (horizontalPencilForm N w z).IsInvertible :=
  fun z hz => iso.puncturedSet_isInvertible z (iso.neumannSet_subset_puncturedSet hz)

/-- The contour `Γ` lies in the open Neumann annulus. -/
theorem sphere_subset_neumannOpen (iso : HorizontalIsolation N w lam) :
    Metric.sphere lam iso.radius ⊆ iso.neumannOpen := by
  intro z hz
  have hdist : dist z lam = iso.radius := Metric.mem_sphere.mp hz
  have hpos := iso.radius_pos
  refine ⟨Metric.mem_ball.mpr ?_, ?_⟩
  · rw [hdist]; linarith
  · intro hmem
    have := Metric.mem_closedBall.mp hmem
    rw [hdist] at this
    linarith

/-- **The uniform bound `B` for `𝔸_w(z)^{-1}` on the Neumann annulus.** -/
theorem exists_neumannInverseBound (iso : HorizontalIsolation N w lam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ iso.neumannSet,
      complexFormInvNorm (horizontalPencilFormInverse N w z) ≤ B :=
  exists_bound_complexFormInvNorm_horizontalPencilFormInverse N w iso.isCompact_neumannSet
    iso.neumannSet_re_pos iso.neumannSet_isInvertible

/-- **The uniform `L² → H¹` bound `C` for the unperturbed solution map on the Neumann
annulus.** -/
theorem exists_neumannSolutionBound (iso : HorizontalIsolation N w lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ iso.neumannSet, ‖horizontalFormSolution N w z‖ ≤ C :=
  exists_bound_norm_horizontalFormSolution N w iso.isCompact_neumannSet
    iso.neumannSet_re_pos iso.neumannSet_isInvertible

/-- The unperturbed state resolvent on the contour. -/
theorem contour_stateResolvent (iso : HorizontalIsolation N w lam) {z : ℂ}
    (hz : z ∈ Metric.sphere lam iso.radius) :
    iso.contourResolvent.stateResolvent z =
      (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) :=
  iso.resolvent_stateResolvent (iso.sphere_subset_puncturedSet hz)

end HorizontalIsolation

/-! ## Neumann data for a perturbation of an isolating contour -/

/-- Unfolding of the perturbed solution map as a composition. -/
theorem horizontalDeltaSolution_eq_comp (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ) :
    horizontalDeltaSolution N delta w' w z =
      (formNeumannFactorInv (horizontalPencilFormInverse N w z)
        (horizontalPencilDifference N delta w' w)).comp (horizontalFormSolution N w z) :=
  rfl

/-- **The uniform `L² → H¹` bound for the perturbed solution map** at one parameter: this is
the form-norm half of `eq:local-continuation-bound` for `𝓛_{w',δ}`. -/
theorem norm_horizontalDeltaSolution_le (N delta : ℝ) (w' w : WholePlaneC3LInf) (z : ℂ)
    {c C : ℝ} (hc : horizontalNeumannSize N delta w' w z ≤ c) (hc1 : c < 1)
    (hC : ‖horizontalFormSolution N w z‖ ≤ C) :
    ‖horizontalDeltaSolution N delta w' w z‖ ≤ (1 - c)⁻¹ * C := by
  have hc0 : 0 ≤ c := le_trans (horizontalNeumannSize_nonneg N delta w' w z) hc
  have hden : (0 : ℝ) < 1 - c := by linarith
  refine le_trans (le_of_eq (congrArg (fun T : WholePlaneC2L2 →L[ℂ] WholePlaneC2H1 => ‖T‖)
    (horizontalDeltaSolution_eq_comp N delta w' w z))) ?_
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul (norm_formNeumannFactorInv_le hc hc1) hC
    (ContinuousLinearMap.opNorm_nonneg (horizontalFormSolution N w z))
    (le_of_lt (inv_pos.mpr hden))

/-- **Data making the Neumann series converge uniformly on the Neumann annulus** of an
isolating contour: the uniform inverse bound `B` of the proof of `prop:local-seed`, the
form-perturbation bound `η` of `eq:form-small`, the uniform solution bound `C`, and the
smallness `Bη < 1`. -/
structure HorizontalNeumannData (N delta : ℝ) (w' w : WholePlaneC3LInf) (lam : ℂ)
    (iso : HorizontalIsolation N w lam) where
  /-- Uniform bound `B` for `𝔸_w(z)^{-1} : V* → V` on the Neumann annulus. -/
  invBound : ℝ
  /-- Bound `η` for the `z`-free form perturbation of `eq:form-small`. -/
  formBound : ℝ
  /-- Uniform bound `C` for the unperturbed solution map `L² → H¹`. -/
  solutionBound : ℝ
  /-- `B` bounds the antidual-valued inverse on the Neumann annulus. -/
  invBound_le : ∀ z ∈ iso.neumannSet,
    complexFormInvNorm (horizontalPencilFormInverse N w z) ≤ invBound
  /-- `η` bounds the `z`-free form perturbation. -/
  formBound_le : complexFormOpNorm (horizontalPencilDifference N delta w' w) ≤ formBound
  /-- `C` bounds the unperturbed solution map on the Neumann annulus. -/
  solutionBound_le : ∀ z ∈ iso.neumannSet, ‖horizontalFormSolution N w z‖ ≤ solutionBound
  /-- The Neumann smallness condition `Bη < 1`. -/
  small : invBound * formBound < 1

namespace HorizontalNeumannData

variable {N delta : ℝ} {w' w : WholePlaneC3LInf} {lam : ℂ}
  {iso : HorizontalIsolation N w lam}

/-- The Neumann smallness quantity is at most `Bη` on the annulus. -/
theorem size_le (nd : HorizontalNeumannData N delta w' w lam iso) {z : ℂ}
    (hz : z ∈ iso.neumannSet) :
    horizontalNeumannSize N delta w' w z ≤ nd.invBound * nd.formBound :=
  horizontalNeumannSize_le N delta w' w z (nd.invBound_le z hz) nd.formBound_le

/-- The Neumann series converges at every parameter of the annulus. -/
theorem size_lt_one (nd : HorizontalNeumannData N delta w' w lam iso) {z : ℂ}
    (hz : z ∈ iso.neumannSet) : horizontalNeumannSize N delta w' w z < 1 :=
  lt_of_le_of_lt (nd.size_le hz) nd.small

/-- **The resolvent of the perturbed generator `𝓛_{w',δ}` on the open Neumann annulus.** -/
def resolvent (nd : HorizontalNeumannData N delta w' w lam iso) :
    HasResolventOn (horizontalFormDeltaOperator N delta w') iso.neumannOpen :=
  horizontalDeltaHasResolventOn N delta w' w iso.neumannOpen
    (fun z hz => iso.neumannSet_re_pos z (iso.neumannOpen_subset_neumannSet hz))
    (fun z hz => iso.neumannSet_isInvertible z (iso.neumannOpen_subset_neumannSet hz))
    (fun _z hz => nd.size_lt_one (iso.neumannOpen_subset_neumannSet hz))

/-- **`Γ ⊂ ρ(𝓛_{w',δ})`**: the resolvent of the perturbed generator restricted to the
contour. -/
def contourResolvent (nd : HorizontalNeumannData N delta w' w lam iso) :
    HasResolventOn (horizontalFormDeltaOperator N delta w') (Metric.sphere lam iso.radius) :=
  nd.resolvent.mono iso.sphere_subset_neumannOpen

/-- The perturbed state resolvent on the contour is `j` composed with the perturbed solution
map. -/
theorem stateResolvent_eq (nd : HorizontalNeumannData N delta w' w lam iso) {z : ℂ}
    (hz : z ∈ Metric.sphere lam iso.radius) :
    nd.contourResolvent.stateResolvent z =
      (wholePlaneH1Embedding C2).comp (horizontalDeltaSolution N delta w' w z) :=
  horizontalDeltaHasResolventOn_stateResolvent N delta w' w iso.neumannOpen
    (fun z hz => iso.neumannSet_re_pos z (iso.neumannOpen_subset_neumannSet hz))
    (fun z hz => iso.neumannSet_isInvertible z (iso.neumannOpen_subset_neumannSet hz))
    (fun _z hz => nd.size_lt_one (iso.neumannOpen_subset_neumannSet hz))
    (iso.sphere_subset_neumannOpen hz)

/-- **The Riesz projection `P_{h,δ}` of the perturbed generator.** -/
def projection (nd : HorizontalNeumannData N delta w' w lam iso) :
    WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 :=
  nd.contourResolvent.rieszProjection

/-- The resolvent difference on the contour. -/
theorem norm_stateResolvent_sub_le (nd : HorizontalNeumannData N delta w' w lam iso) {z : ℂ}
    (hz : z ∈ Metric.sphere lam iso.radius) :
    ‖nd.contourResolvent.stateResolvent z - iso.contourResolvent.stateResolvent z‖ ≤
      ‖wholePlaneH1Embedding C2‖ *
        (nd.invBound * nd.formBound * (1 - nd.invBound * nd.formBound)⁻¹ *
          nd.solutionBound) := by
  have hmem : z ∈ iso.neumannSet :=
    iso.neumannOpen_subset_neumannSet (iso.sphere_subset_neumannOpen hz)
  have h1 : nd.contourResolvent.stateResolvent z - iso.contourResolvent.stateResolvent z =
      (wholePlaneH1Embedding C2).comp (horizontalDeltaSolution N delta w' w z) -
        (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) := by
    rw [nd.stateResolvent_eq hz, iso.contour_stateResolvent hz]
  refine le_trans (le_of_eq (congrArg (fun T : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 => ‖T‖)
    h1)) ?_
  exact norm_horizontalDeltaStateResolvent_sub_le N delta w' w z (nd.size_le hmem) nd.small
    (nd.solutionBound_le z hmem)

/-- **`‖P_{h,δ} - P⁰‖_{2→2} ≤ r‖j‖ Bη(1-Bη)^{-1}C`**, the explicit form of the display
`‖P_{h,δ} - P⁰‖_{2→2} ≤ C(h^{1/4} + |δ-1|)` in the proof of `prop:local-seed`: the contour
length `2πr` divided by `2π` times the uniform resolvent difference. -/
theorem norm_projection_sub_le (nd : HorizontalNeumannData N delta w' w lam iso) :
    ‖nd.projection - iso.projection‖ ≤
      iso.radius * (‖wholePlaneH1Embedding C2‖ *
        (nd.invBound * nd.formBound * (1 - nd.invBound * nd.formBound)⁻¹ *
          nd.solutionBound)) :=
  HasResolventOn.norm_rieszProjection_sub_le_of_domains iso.radius_pos.le
    nd.contourResolvent iso.contourResolvent fun _z hz => nd.norm_stateResolvent_sub_le hz

/-- The resolvent difference on the contour under the working smallness `Bη ≤ 1/2`. -/
theorem norm_stateResolvent_sub_le_two (nd : HorizontalNeumannData N delta w' w lam iso)
    (hhalf : nd.invBound * nd.formBound ≤ 1 / 2)
    (hc0 : 0 ≤ nd.invBound * nd.formBound) (hC0 : 0 ≤ nd.solutionBound) {z : ℂ}
    (hz : z ∈ Metric.sphere lam iso.radius) :
    ‖nd.contourResolvent.stateResolvent z - iso.contourResolvent.stateResolvent z‖ ≤
      2 * ‖wholePlaneH1Embedding C2‖ * (nd.invBound * nd.formBound) * nd.solutionBound := by
  have hden : (0 : ℝ) < 1 - nd.invBound * nd.formBound := by linarith
  have hinvnn : (0 : ℝ) ≤ (1 - nd.invBound * nd.formBound)⁻¹ := le_of_lt (inv_pos.mpr hden)
  have hmul : (1 - nd.invBound * nd.formBound)⁻¹ * (1 - nd.invBound * nd.formBound) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hden)
  have hinvle : (1 - nd.invBound * nd.formBound)⁻¹ ≤ 2 := by
    nlinarith [hmul, hinvnn, hhalf]
  have hj0 : (0 : ℝ) ≤ ‖wholePlaneH1Embedding C2‖ :=
    ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2)
  have e1 : nd.invBound * nd.formBound * (1 - nd.invBound * nd.formBound)⁻¹ *
      nd.solutionBound ≤ nd.invBound * nd.formBound * 2 * nd.solutionBound :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinvle hc0) hC0
  have e2 : ‖wholePlaneH1Embedding C2‖ * (nd.invBound * nd.formBound *
      (1 - nd.invBound * nd.formBound)⁻¹ * nd.solutionBound) ≤
      ‖wholePlaneH1Embedding C2‖ * (nd.invBound * nd.formBound * 2 * nd.solutionBound) :=
    mul_le_mul_of_nonneg_left e1 hj0
  refine le_trans (nd.norm_stateResolvent_sub_le hz) ?_
  linarith [e2]

/-- The projection difference under the working smallness `Bη ≤ 1/2`. -/
theorem norm_projection_sub_le_two (nd : HorizontalNeumannData N delta w' w lam iso)
    (hhalf : nd.invBound * nd.formBound ≤ 1 / 2)
    (hc0 : 0 ≤ nd.invBound * nd.formBound) (hC0 : 0 ≤ nd.solutionBound) :
    ‖nd.projection - iso.projection‖ ≤
      2 * iso.radius * ‖wholePlaneH1Embedding C2‖ * (nd.invBound * nd.formBound) *
        nd.solutionBound := by
  have hden : (0 : ℝ) < 1 - nd.invBound * nd.formBound := by linarith
  have hinvnn : (0 : ℝ) ≤ (1 - nd.invBound * nd.formBound)⁻¹ := le_of_lt (inv_pos.mpr hden)
  have hmul : (1 - nd.invBound * nd.formBound)⁻¹ * (1 - nd.invBound * nd.formBound) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hden)
  have hinvle : (1 - nd.invBound * nd.formBound)⁻¹ ≤ 2 := by
    nlinarith [hmul, hinvnn, hhalf]
  have hj0 : (0 : ℝ) ≤ ‖wholePlaneH1Embedding C2‖ :=
    ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2)
  have e1 : nd.invBound * nd.formBound * (1 - nd.invBound * nd.formBound)⁻¹ *
      nd.solutionBound ≤ nd.invBound * nd.formBound * 2 * nd.solutionBound :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinvle hc0) hC0
  have e2 : ‖wholePlaneH1Embedding C2‖ * (nd.invBound * nd.formBound *
      (1 - nd.invBound * nd.formBound)⁻¹ * nd.solutionBound) ≤
      ‖wholePlaneH1Embedding C2‖ * (nd.invBound * nd.formBound * 2 * nd.solutionBound) :=
    mul_le_mul_of_nonneg_left e1 hj0
  have e3 := mul_le_mul_of_nonneg_left e2 iso.radius_pos.le
  refine le_trans nd.norm_projection_sub_le ?_
  linarith [e3]

end HorizontalNeumannData

end HorizontalWeakForm

namespace HorizontalMode

open HorizontalWeakForm PonomarenkoFreeOmegaInterface

/-- `eq:form-small` in the `z`-free shape that the Neumann series consumes: the form
difference of the smoothed seed family. -/
theorem exists_complexFormOpNorm_horizontalPencilDifference_le (N Omega : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : PonomarenkoSmoothingWidth) (delta : ℝ),
      complexFormOpNorm (horizontalPencilDifference N delta
          (horizontalSmoothedModeVelocity N Omega h) (horizontalModeVelocity N Omega)) ≤
        C * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_complexFormOpNorm_horizontalModePencil_sub_le N Omega
  refine ⟨C, hC0, fun h delta => ?_⟩
  have hbound := hC h delta 0
  have heq : horizontalPencilFormDelta N delta (horizontalSmoothedModeVelocity N Omega h) 0 -
      horizontalPencilFormDelta N 1 (horizontalModeVelocity N Omega) 0 =
      horizontalPencilDifference N delta (horizontalSmoothedModeVelocity N Omega h)
        (horizontalModeVelocity N Omega) := by
    rw [horizontalPencilFormDelta_one]
    exact horizontalPencilFormDelta_sub_eq_difference N delta _ _ 0
  rwa [heq] at hbound

/-- **The Neumann data of the smoothed seed family** at an admissible pair `(h, δ)`: the
uniform inverse bound `B` and solution bound `C` on the Neumann annulus of the seed contour,
together with the form perturbation `η = C₁h^{1/4} + (2+N²)|δ-1|` of `eq:form-small`. -/
def seedNeumannData {N Omega : ℝ} {kappa : ℂ} (hd : CertifiedInterfaceData N Omega kappa)
    (h : PonomarenkoSmoothingWidth) (delta : ℝ) {B Csol C1 : ℝ}
    (hB : ∀ z ∈ (modeIsolation hd).neumannSet,
      complexFormInvNorm
        (horizontalPencilFormInverse N (horizontalModeVelocity N Omega) z) ≤ B)
    (hCsol : ∀ z ∈ (modeIsolation hd).neumannSet,
      ‖horizontalFormSolution N (horizontalModeVelocity N Omega) z‖ ≤ Csol)
    (hC1 : complexFormOpNorm (horizontalPencilDifference N delta
        (horizontalSmoothedModeVelocity N Omega h) (horizontalModeVelocity N Omega)) ≤
      C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2))
    (hsmall : B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) < 1) :
    HorizontalNeumannData N delta (horizontalSmoothedModeVelocity N Omega h)
      (horizontalModeVelocity N Omega) (horizontalEigenvalue N kappa) (modeIsolation hd) where
  invBound := B
  formBound := C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)
  solutionBound := Csol
  invBound_le := hB
  formBound_le := hC1
  solutionBound_le := hCsol
  small := hsmall

/-- **The seed Riesz-projection perturbation** of the proof of `prop:local-seed`.  For
the smoothed seed velocity `v_h` and the diffusivity `δ`, once `h` and `|δ-1|` are below
explicit thresholds the Neumann series converges uniformly on the Neumann annulus of the
contour `Γ` of `HorizontalMode.modeIsolation`, so `𝓛_{v_h,δ}` has a resolvent on `Γ` and a
Riesz projection `P_{h,δ}` with

`‖P_{h,δ} - P⁰‖_{2→2} ≤ K(h^{1/4} + |δ-1|)`. -/
theorem exists_seedNeumannData {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) :
    ∃ h0 eta0 K Kdiff Kres : ℝ, 0 < h0 ∧ 0 < eta0 ∧ 0 ≤ K ∧ 0 ≤ Kdiff ∧ 0 ≤ Kres ∧
      ∀ (h : PonomarenkoSmoothingWidth) (delta : ℝ),
        (h : ℝ) ≤ h0 → |delta - 1| ≤ eta0 →
        (∀ z ∈ Metric.sphere (horizontalEigenvalue N kappa) (modeIsolation hd).radius,
            ‖horizontalDeltaSolution N delta (horizontalSmoothedModeVelocity N Omega h)
              (horizontalModeVelocity N Omega) z‖ ≤ Kres) ∧
          (∀ z ∈ Metric.sphere (horizontalEigenvalue N kappa) (modeIsolation hd).radius,
            ‖(wholePlaneH1Embedding C2).comp (horizontalDeltaSolution N delta
                  (horizontalSmoothedModeVelocity N Omega h)
                  (horizontalModeVelocity N Omega) z) -
                (wholePlaneH1Embedding C2).comp
                  (horizontalFormSolution N (horizontalModeVelocity N Omega) z)‖ ≤
              Kdiff * ((h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1|)) ∧
          ∃ nd : HorizontalNeumannData N delta (horizontalSmoothedModeVelocity N Omega h)
              (horizontalModeVelocity N Omega) (horizontalEigenvalue N kappa)
              (modeIsolation hd),
            nd.invBound * nd.formBound ≤ 1 / 2 ∧
              ‖nd.projection - (modeIsolation hd).projection‖ ≤
                K * ((h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1|) := by
  obtain ⟨B, hB0, hB⟩ := (modeIsolation hd).exists_neumannInverseBound
  obtain ⟨Csol, hCsol0, hCsol⟩ := (modeIsolation hd).exists_neumannSolutionBound
  obtain ⟨C1, hC10, hC1⟩ := exists_complexFormOpNorm_horizontalPencilDifference_le N Omega
  have hj0 : 0 ≤ ‖wholePlaneH1Embedding C2‖ :=
    ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2)
  have hr0 : 0 ≤ (modeIsolation hd).radius := (modeIsolation hd).radius_pos.le
  have hN0 : (0 : ℝ) ≤ 2 + N ^ 2 := by positivity
  have hM1 : (0 : ℝ) < max C1 (2 + N ^ 2) + 1 := by
    have : (0 : ℝ) ≤ max C1 (2 + N ^ 2) := le_trans hC10 (le_max_left _ _)
    linarith
  obtain ⟨h0, eta0, hh0, heta0, hthr⟩ :=
    exists_thresholds_smallness (E := 2 + N ^ 2) hB0 hC10
  refine ⟨h0, eta0,
    2 * (modeIsolation hd).radius * ‖wholePlaneH1Embedding C2‖ * B * Csol *
      (max C1 (2 + N ^ 2) + 1),
    2 * ‖wholePlaneH1Embedding C2‖ * B * Csol * (max C1 (2 + N ^ 2) + 1),
    2 * Csol, hh0, heta0, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hr0) hj0) hB0) hCsol0) hM1.le
  · exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hj0) hB0) hCsol0) hM1.le
  · linarith
  intro h delta hh hdelta
  obtain ⟨hhalf, hetaA_le⟩ := hthr (h : ℝ) |delta - 1| h.2.1.le (abs_nonneg _) hh hdelta
  have hq0 : (0 : ℝ) ≤ (h : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg h.2.1.le _
  have hetaA0 : (0 : ℝ) ≤ C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2) :=
    add_nonneg (mul_nonneg hC10 hq0) (mul_nonneg (abs_nonneg _) hN0)
  have hc0 : (0 : ℝ) ≤ B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) :=
    mul_nonneg hB0 hetaA0
  have hden : (0 : ℝ) <
      1 - B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) := by linarith
  have hinvnn : (0 : ℝ) ≤
      (1 - B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)))⁻¹ :=
    le_of_lt (inv_pos.mpr hden)
  have hmulinv : (1 - B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)))⁻¹ *
      (1 - B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2))) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hden)
  have hinvle : (1 - B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)))⁻¹ ≤ 2 := by
    nlinarith [hmulinv, hinvnn, hhalf]
  have hsize : ∀ z ∈ (modeIsolation hd).neumannSet,
      horizontalNeumannSize N delta (horizontalSmoothedModeVelocity N Omega h)
          (horizontalModeVelocity N Omega) z ≤
        B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) := fun z hz =>
    horizontalNeumannSize_le N delta _ _ z (hB z hz) (hC1 h delta)
  have hmemof : ∀ z ∈ Metric.sphere (horizontalEigenvalue N kappa) (modeIsolation hd).radius,
      z ∈ (modeIsolation hd).neumannSet := fun z hz =>
    (modeIsolation hd).neumannOpen_subset_neumannSet
      ((modeIsolation hd).sphere_subset_neumannOpen hz)
  have hkeyj : ‖wholePlaneH1Embedding C2‖ *
      (B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) * Csol) ≤
      ‖wholePlaneH1Embedding C2‖ *
        (B * ((max C1 (2 + N ^ 2) + 1) * ((h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1|)) * Csol) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hetaA_le hB0) hCsol0) hj0
  have hkeyr := mul_le_mul_of_nonneg_left hkeyj hr0
  refine ⟨fun z hz => ?_, fun z hz => ?_, ?_⟩
  · refine le_trans (norm_horizontalDeltaSolution_le N delta _ _ z (hsize z (hmemof z hz))
      (by linarith) (hCsol z (hmemof z hz))) ?_
    exact mul_le_mul_of_nonneg_right hinvle hCsol0
  · refine le_trans (norm_horizontalDeltaStateResolvent_sub_le N delta _ _ z
      (hsize z (hmemof z hz)) (by linarith) (hCsol z (hmemof z hz))) ?_
    have e1 : B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) *
        (1 - B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)))⁻¹ * Csol ≤
        B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2)) * 2 * Csol :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinvle hc0) hCsol0
    have e2 := mul_le_mul_of_nonneg_left e1 hj0
    linarith [e2, hkeyj]
  · refine ⟨seedNeumannData hd h delta hB hCsol (hC1 h delta) (by linarith), hhalf, ?_⟩
    refine le_trans
      (HorizontalNeumannData.norm_projection_sub_le_two _ hhalf hc0 hCsol0) ?_
    change 2 * (modeIsolation hd).radius * ‖wholePlaneH1Embedding C2‖ *
        (B * (C1 * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2))) * Csol ≤ _
    linarith [hkeyr]

/-- **Explicit thresholds for `eq:local-spectral-witness`.**  Below them the Riesz projection
of the perturbed generator is within `1/4` of `P⁰` in operator norm, hence also in the real
part of the quadratic form on unit vectors.  Combined with `re⟨P⁰f_*,f_*⟩ > 3/4` this gives
the paper's `re⟨P_δ f_*,f_*⟩ > 1/2`. -/
theorem exists_seedThresholds {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) :
    ∃ h1 eta1 : ℝ, 0 < h1 ∧ 0 < eta1 ∧
      ∀ (h : PonomarenkoSmoothingWidth) (delta : ℝ),
        (h : ℝ) ≤ h1 → |delta - 1| ≤ eta1 →
        ∃ nd : HorizontalNeumannData N delta (horizontalSmoothedModeVelocity N Omega h)
            (horizontalModeVelocity N Omega) (horizontalEigenvalue N kappa) (modeIsolation hd),
          ‖nd.projection - (modeIsolation hd).projection‖ < 1 / 4 ∧
            ∀ f : WholePlaneC2L2, ‖f‖ = 1 →
              |(inner ℂ (nd.projection f) f).re -
                (inner ℂ ((modeIsolation hd).projection f) f).re| < 1 / 4 := by
  obtain ⟨h0, eta0, K, _, _, hh0, heta0, hK0, _, _, hmain⟩ := exists_seedNeumannData hd
  have hepspos : (0 : ℝ) < 1 / (8 * (K + 1)) := by
    have : (0 : ℝ) < 8 * (K + 1) := by linarith
    positivity
  obtain ⟨t, htpos, ht⟩ := exists_pos_rpow_quarter_le hepspos
  refine ⟨min h0 t, min eta0 (1 / (8 * (K + 1))), lt_min hh0 htpos,
    lt_min heta0 hepspos, fun h delta hh hdelta => ?_⟩
  obtain ⟨_, _, nd, _, hbound⟩ := hmain h delta (le_trans hh (min_le_left _ _))
    (le_trans hdelta (min_le_left _ _))
  have hq : (h : ℝ) ^ (1 / 4 : ℝ) ≤ 1 / (8 * (K + 1)) :=
    ht (h : ℝ) h.2.1.le (le_trans hh (min_le_right _ _))
  have hdl : |delta - 1| ≤ 1 / (8 * (K + 1)) := le_trans hdelta (min_le_right _ _)
  have hlt : K * ((h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1|) < 1 / 4 := by
    have e1 : K * ((h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1|) ≤
        K * (2 * (1 / (8 * (K + 1)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    exact lt_of_le_of_lt e1 (mul_two_inv_eight_add_one_lt hK0)
  refine ⟨nd, lt_of_le_of_lt hbound hlt, fun f hf => ?_⟩
  exact lt_of_le_of_lt (le_trans (abs_re_inner_apply_sub_le _ _ hf) hbound) hlt

end HorizontalMode

end

end FastDynamo
