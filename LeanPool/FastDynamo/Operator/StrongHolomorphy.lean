/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.Liouville

/-!
# Strong holomorphy and local boundedness imply holomorphy in operator norm

An operator-valued map `T : ℂ → X →L[ℂ] Y` on an open set `U ⊆ ℂ` whose orbits `z ↦ T z x` are
complex-differentiable and which is locally bounded in operator norm is complex-differentiable as a
map into `X →L[ℂ] Y` (`differentiableOn_of_forall_apply`).  This is the step from strong to norm
holomorphy for the analytic extension of a semigroup to a sector (Engel–Nagel, Definition II.4.5)
that enters the proof of `lem:semigroup-spectral-growth` (Lemma A.1).

The argument applies two Cauchy estimates to each orbit, which bound its first two derivatives near
a point uniformly in `‖x‖ ≤ 1`, and the mean value inequality, which turns this into a second-order
Taylor bound uniform in `x`; the operator norm of the Taylor remainder is then `O(|z - z₀|²)`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric Filter Topology Asymptotics

universe u v

section CauchyEstimates

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Cauchy estimate on a half-size ball: if `g` is complex-differentiable on an open
set containing `closedBall c (2 * s)` and bounded by `M` there, then `‖g'(w)‖ ≤ M / s` for every
`w ∈ closedBall(c, s)`. -/
theorem norm_deriv_le_of_closedBall_two_mul {g : ℂ → E} {U : Set ℂ}
    (hg : DifferentiableOn ℂ g U) {c : ℂ} {s M : ℝ} (hs : 0 < s)
    (hU : closedBall c (2 * s) ⊆ U) (hM : ∀ w ∈ closedBall c (2 * s), ‖g w‖ ≤ M) {w : ℂ}
    (hw : w ∈ closedBall c s) : ‖deriv g w‖ ≤ M / s := by
  have hsub : closedBall w s ⊆ closedBall c (2 * s) :=
    closedBall_subset_closedBall' (by linarith [mem_closedBall.1 hw])
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs
    (hg.diffContOnCl_ball (hsub.trans hU)) fun z hz ↦ hM z (hsub (sphere_subset_closedBall hz))

/-- Second-order Taylor bound for a holomorphic map bounded by `M` on `closedBall(c, 4r) ⊆ U`:
`‖g z − g c − (z − c) g'(c)‖ ≤ M / (2 r²) · ‖z − c‖²` for `z ∈ closedBall(c, r)`. -/
theorem norm_sub_sub_smul_deriv_le [CompleteSpace E] {g : ℂ → E} {U : Set ℂ} (hUo : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hU : closedBall c (4 * r) ⊆ U) (hM : ∀ w ∈ closedBall c (4 * r), ‖g w‖ ≤ M) {z : ℂ}
    (hz : z ∈ closedBall c r) :
    ‖g z - g c - (z - c) • deriv g c‖ ≤ M / (2 * r ^ 2) * ‖z - c‖ ^ 2 := by
  have h4 : 2 * (2 * r) = 4 * r := by ring
  have hr1 : closedBall c r ⊆ closedBall c (2 * r) := closedBall_subset_closedBall (by linarith)
  have hr2 : closedBall c (2 * r) ⊆ closedBall c (4 * r) :=
    closedBall_subset_closedBall (by linarith)
  have hdiff : ∀ w ∈ closedBall c (4 * r), DifferentiableAt ℂ g w := fun w hw ↦
    hg.differentiableAt (hUo.mem_nhds (hU hw))
  have hdiff' : ∀ w ∈ closedBall c (4 * r), DifferentiableAt ℂ (deriv g) w := fun w hw ↦
    (hg.deriv hUo).differentiableAt (hUo.mem_nhds (hU hw))
  -- first derivative bounded on `closedBall(c, 2r)`
  have h1 : ∀ w ∈ closedBall c (2 * r), ‖deriv g w‖ ≤ M / (2 * r) := fun w hw ↦
    norm_deriv_le_of_closedBall_two_mul hg (by positivity) (h4 ▸ hU) (h4 ▸ hM) hw
  -- second derivative bounded on `closedBall(c, r)`
  have h2 : ∀ w ∈ closedBall c r, ‖deriv (deriv g) w‖ ≤ M / (2 * r) / r := fun w hw ↦
    norm_deriv_le_of_closedBall_two_mul (hg.deriv hUo) hr (hr2.trans hU) h1 hw
  set ρ := ‖z - c‖ with hρ
  have hρr : ρ ≤ r := by rw [hρ, ← dist_eq_norm]; exact mem_closedBall.1 hz
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hcρ : c ∈ closedBall c ρ := mem_closedBall_self hρ0
  have hzρ : z ∈ closedBall c ρ := by rw [mem_closedBall, dist_eq_norm]
  have hρsub : closedBall c ρ ⊆ closedBall c r := closedBall_subset_closedBall hρr
  -- the derivative varies by at most `M / (2 r²) · ρ` on `closedBall(c, ρ)`
  have h3 : ∀ w ∈ closedBall c ρ, ‖deriv g w - deriv g c‖ ≤ M / (2 * r) / r * ρ := by
    intro w hw
    have := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
      (fun v hv ↦ hdiff' v (hr2 (hr1 hv))) h2 (mem_closedBall_self hr.le) (hρsub hw)
    refine this.trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · rw [← dist_eq_norm]; exact mem_closedBall.1 hw
    · exact (norm_nonneg _).trans (h2 c (mem_closedBall_self hr.le))
  have key := (convex_closedBall c ρ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w ↦ g w - (w - c) • deriv g c) (f' := fun w ↦ deriv g w - deriv g c)
    (fun w hw ↦ by
      have := ((hdiff w (hr2 (hr1 (hρsub hw)))).hasDerivAt.sub
        (((hasDerivAt_id w).sub_const c).smul_const (deriv g c)))
      exact this.hasDerivWithinAt.congr_deriv (by simp)) h3 hcρ hzρ
  have hrw : g z - g c - (z - c) • deriv g c =
      (g z - (z - c) • deriv g c) - (g c - (c - c) • deriv g c) := by simp; abel
  rw [hrw]
  refine key.trans (le_of_eq ?_)
  rw [← hρ]
  field_simp

end CauchyEstimates

/-- **Strong holomorphy and local boundedness imply norm holomorphy.**  A map
`T : ℂ → X →L[ℂ] Y` on an open set `U ⊆ ℂ` such that every orbit `z ↦ T z x` is
complex-differentiable on `U` and `‖T‖` is bounded near every point of `U` is
complex-differentiable on `U` as a map into the Banach space `X →L[ℂ] Y`. -/
theorem differentiableOn_of_forall_apply {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] {U : Set ℂ} (hU : IsOpen U) {T : ℂ → X →L[ℂ] Y}
    (hT : ∀ x : X, DifferentiableOn ℂ (fun z ↦ T z x) U)
    (hb : ∀ z ∈ U, ∃ C : ℝ, ∀ᶠ w in 𝓝 z, ‖T w‖ ≤ C) :
    DifferentiableOn ℂ T U := by
  intro z₀ hz₀
  obtain ⟨C, hC⟩ := hb z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds hz₀) hC)
  set r := ε / 8 with hr_def
  have hr : 0 < r := by positivity
  have hcl : closedBall z₀ (4 * r) ⊆ U ∩ {w | ‖T w‖ ≤ C} :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hcl (mem_closedBall_self (by positivity))).2
  have hbd : ∀ x : X, ∀ w ∈ closedBall z₀ (4 * r), ‖T w x‖ ≤ C * ‖x‖ := fun x w hw ↦
    (T w).le_of_opNorm_le (hcl hw).2 x
  have hd : ∀ x : X, DifferentiableAt ℂ (fun w ↦ T w x) z₀ := fun x ↦
    (hT x).differentiableAt (hU.mem_nhds hz₀)
  have h4 : 2 * (2 * r) = 4 * r := by ring
  let D : X →L[ℂ] Y := LinearMap.mkContinuous
    { toFun := fun x ↦ deriv (fun w ↦ T w x) z₀
      map_add' := fun x y ↦ by simp only [map_add]; exact deriv_add (hd x) (hd y)
      map_smul' := fun a x ↦ by
        simp only [map_smul, RingHom.id_apply]; exact deriv_const_smul a (hd x) }
    (C / (2 * r)) fun x ↦ by
      have := norm_deriv_le_of_closedBall_two_mul (hT x) (s := 2 * r) (by positivity)
        (h4 ▸ fun w hw ↦ (hcl hw).1) (h4 ▸ hbd x) (mem_closedBall_self (by positivity))
      simpa [div_mul_eq_mul_div] using this
  refine (?_ : HasDerivAt T D z₀).differentiableAt.differentiableWithinAt
  rw [hasDerivAt_iff_isLittleO]
  refine IsBigO.trans_isLittleO ?_ (isLittleO_pow_sub_sub z₀ one_lt_two)
  refine IsBigO.of_bound (C / (2 * r ^ 2)) ?_
  filter_upwards [closedBall_mem_nhds z₀ hr] with z hz
  rw [Real.norm_of_nonneg (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have := norm_sub_sub_smul_deriv_le hU (hT x) hr (fun w hw ↦ (hcl hw).1) (hbd x) hz
  simp only [_root_.sub_apply, _root_.smul_apply]
  refine this.trans (le_of_eq ?_)
  ring

end

end FastDynamo
