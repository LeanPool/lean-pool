/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.ConservativeResolvent
public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingLocal
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ExponentialComparison

/-!
# ResolventTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Displacement tails from resolvent tail decay

For a divergence-form generator with rough coefficients the estimate an analysis produces is a
decay of the RESOLVENT away from the region carrying the datum, not a bound on the transition
law.  This file turns the first into the second.

The hypothesis is `SubMarkovKernelSemigroup.HasResolventTail`: at a positive shift `lam`, the
normalized `lam`-potential measure of the complement of the ball of radius `rho` about the
starting point is at most `phi (sqrt lam * rho)`, with `sqrt lam * rho` the parabolic scaling of
the radius.  The conclusion
(`PositiveC0ContractiveResolvent.measure_compl_ball_le_of_hasResolventTail`) is that at the time
`t = 1 / lam` the transition law leaves the ball of radius `4 r` with probability at most
`2 * exp 1 * phi (sqrt lam * r)`.

The proof is the excessive-function comparison of Blumenthal--Getoor.  Let `g` be a radial
cutoff vanishing on the ball of radius `r` and equal to one outside the ball of radius `2 r`,
transported to the one-point compactification by the value one at the added point, so that it
becomes an observable vanishing at infinity there.  Then `v = 2 lam R_lam g` is `lam`-excessive
(`PositiveC0ContractiveResolvent.mul_operator_smul_operator_le`), so the exponential comparison
of `Semigroup/ExponentialComparison.lean` bounds the transition average of any observable below
`v` by `exp 1` times `v` at the starting point.  Tail decay at radius `r` about a point at
distance at least `3 r` makes `v` at least one there, and tail decay at radius `r` about the
starting point, together with conservativity, makes `v` at the starting point at most
`2 phi (sqrt lam * r)`.

The state space is a proper metric space, so that the radial cutoffs have compact support; both
a compact state space and a Euclidean one are covered.  No analytic estimate for a particular
generator is asserted here: the tail decay is the consumer's hypothesis.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

open MarkovProcess

namespace Algsuperdiff.Process

section RadialCutoff

variable {X : Type*} [MetricSpace X]

/-- The radial cutoff about `x`: one on the closed ball of radius `a`, zero outside the ball of
radius `b`, and affine in the distance in between. -/
def radialCutoff (x : X) (a b : ℝ) (z : X) : ℝ :=
  min 1 (max 0 ((b - dist z x) / (b - a)))

/-- The radial cutoff is nonnegative. -/
theorem radialCutoff_nonneg (x : X) (a b : ℝ) (z : X) : 0 ≤ radialCutoff x a b z :=
  le_min zero_le_one (le_max_left _ _)

/-- The radial cutoff is at most one. -/
theorem radialCutoff_le_one (x : X) (a b : ℝ) (z : X) : radialCutoff x a b z ≤ 1 :=
  min_le_left _ _

/-- The radial cutoff is one on the inner ball. -/
theorem radialCutoff_eq_one {x : X} {a b : ℝ} (hab : a < b) {z : X} (hz : dist z x ≤ a) :
    radialCutoff x a b z = 1 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h1 : 1 ≤ (b - dist z x) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith only [hz]
  rw [radialCutoff, max_eq_right (le_trans zero_le_one h1), min_eq_left h1]

/-- The radial cutoff vanishes outside the outer ball. -/
theorem radialCutoff_eq_zero {x : X} {a b : ℝ} (hab : a < b) {z : X} (hz : b ≤ dist z x) :
    radialCutoff x a b z = 0 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h1 : (b - dist z x) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith only [hz]) hba.le
  rw [radialCutoff, max_eq_left h1, min_eq_right zero_le_one]

/-- The radial cutoff is continuous. -/
theorem continuous_radialCutoff (x : X) (a b : ℝ) : Continuous (radialCutoff x a b) :=
  continuous_const.min (continuous_const.max
    ((continuous_const.sub (continuous_id.dist continuous_const)).div_const _))

/-- The radial cutoff as a continuous function vanishing at infinity. -/
def radialCutoffC0 [ProperSpace X] (x : X) (a b : ℝ) (hab : a < b) : C₀(X, ℝ) where
  toFun := radialCutoff x a b
  continuous_toFun := continuous_radialCutoff x a b
  zero_at_infty' := by
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [(isCompact_closedBall x b).compl_mem_cocompact] with z hz
    have hzb : b ≤ dist z x := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hz
      exact hz.le
    exact (radialCutoff_eq_zero hab hzb).symm

/-- The bundled radial cutoff has the values of the radial cutoff. -/
@[simp] theorem radialCutoffC0_apply [ProperSpace X] (x : X) (a b : ℝ) (hab : a < b) (z : X) :
    radialCutoffC0 x a b hab z = radialCutoff x a b z := rfl

end RadialCutoff

namespace SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- **Resolvent tail decay** at a positive shift `lam`, with profile `phi`: at every starting
point the normalized `lam`-potential measure of the complement of a ball centred there is at
most `phi` evaluated at the natural scaling `sqrt lam * rho` of the radius. -/
def HasResolventTail (P : SubMarkovKernelSemigroup X) (lam : ℝ) (phi : ℝ → ℝ) : Prop :=
  ∀ (y : X) (rho : ℝ), 0 < rho →
    ENNReal.ofReal lam * P.resolventPotential lam y (Metric.ball y rho)ᶜ ≤
      ENNReal.ofReal (phi (Real.sqrt lam * rho))

end SubMarkovKernelSemigroup

namespace PositiveC0ContractiveResolvent

open Semigroup MarkovProcess.PositiveC0ContractiveResolvent

section Excessive

variable {Y : Type*} [TopologicalSpace Y]

/-- **Resolvent values are excessive.**  A nonnegative multiple of the resolvent of a nonnegative
observable satisfies, at every larger shift, the pointwise supersolution estimate consumed by
`generatedSemigroup_apply_le_exp_mul`, with the smaller shift as the exponential rate. -/
theorem mul_operator_smul_operator_le (R : PositiveC0ContractiveResolvent Y)
    (mu : PositiveShift) {g : C₀(Y, ℝ)} (hg : ∀ z, 0 ≤ g z) {c : ℝ} (hc : 0 ≤ c)
    (nu : PositiveShift) (hnu : (mu : ℝ) < (nu : ℝ)) (z : Y) :
    (nu : ℝ) * R.toContractiveResolvent.operator nu
        (c • R.toContractiveResolvent.operator mu g) z ≤
      (nu : ℝ) / ((nu : ℝ) - (mu : ℝ)) *
        (c • R.toContractiveResolvent.operator mu g) z := by
  have hden : 0 < (nu : ℝ) - (mu : ℝ) := sub_pos.mpr hnu
  have hB : 0 ≤ R.toContractiveResolvent.operator nu g z := R.isPositive nu g hg z
  have hid := congrArg (fun w : C₀(Y, ℝ) ↦ w z)
    (DFunLike.congr_fun (R.toContractiveResolvent.resolvent_identity nu mu) g)
  simp only [sub_apply, ZeroAtInftyContinuousMap.sub_apply,
    smul_apply, ZeroAtInftyContinuousMap.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul] at hid
  rw [map_smul, ZeroAtInftyContinuousMap.smul_apply, ZeroAtInftyContinuousMap.smul_apply,
    smul_eq_mul, smul_eq_mul]
  set A := R.toContractiveResolvent.operator mu g z with hA
  set B := R.toContractiveResolvent.operator nu g z with hBdef
  set C := R.toContractiveResolvent.operator nu (R.toContractiveResolvent.operator mu g) z
    with hC
  have hCval : C = (A - B) / ((nu : ℝ) - (mu : ℝ)) := by
    field_simp
    linarith only [hid]
  rw [hCval]
  rw [show (nu : ℝ) * (c * ((A - B) / ((nu : ℝ) - (mu : ℝ)))) =
      ((nu : ℝ) * c * (A - B)) / ((nu : ℝ) - (mu : ℝ)) by field_simp]
  rw [show (nu : ℝ) / ((nu : ℝ) - (mu : ℝ)) * (c * A) =
      ((nu : ℝ) * c * A) / ((nu : ℝ) - (mu : ℝ)) by field_simp]
  refine (div_le_div_iff_of_pos_right hden).mpr ?_
  exact mul_le_mul_of_nonneg_left (by linarith only [hB])
    (mul_nonneg nu.property.le hc)

end Excessive

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Tail decay of the potential measure bounds the normalized resolvent of any observable
vanishing at infinity which is at most one and vanishes on the ball. -/
theorem mul_operator_le_of_hasResolventTail (R : PositiveC0ContractiveResolvent X)
    {phi : ℝ → ℝ} (hphi : ∀ s, 0 ≤ phi s) {mu : PositiveShift}
    (htail : SubMarkovKernelSemigroup.HasResolventTail R.kernelSemigroup (mu : ℝ) phi)
    {psi : C₀(X, ℝ)} (hpsi0 : ∀ z, 0 ≤ psi z) (hpsi1 : ∀ z, psi z ≤ 1)
    (y : X) {rho : ℝ} (hrho : 0 < rho) (hvanish : ∀ z, dist z y < rho → psi z = 0) :
    (mu : ℝ) * R.toContractiveResolvent.operator mu psi y ≤
      phi (Real.sqrt (mu : ℝ) * rho) := by
  have hball : MeasurableSet ((Metric.ball y rho)ᶜ) :=
    (Metric.isOpen_ball.measurableSet).compl
  have hle : ∀ z, ENNReal.ofReal (psi z) ≤ (Metric.ball y rho)ᶜ.indicator 1 z := by
    intro z
    by_cases hz : z ∈ Metric.ball y rho
    · rw [hvanish z (Metric.mem_ball.mp hz), ENNReal.ofReal_zero]
      exact zero_le
    · rw [Set.indicator_of_mem hz, Pi.one_apply]
      exact ENNReal.ofReal_le_one.mpr (hpsi1 z)
  have hpot : R.kernelSemigroup.kernelResolvent (mu : ℝ) ((Metric.ball y rho)ᶜ.indicator 1) y =
      R.kernelSemigroup.resolventPotential (mu : ℝ) y ((Metric.ball y rho)ᶜ) := by
    rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
        (measurable_one.indicator hball) y, lintegral_indicator_one hball]
  have hkey : ENNReal.ofReal ((mu : ℝ) * R.toContractiveResolvent.operator mu psi y) ≤
      ENNReal.ofReal (phi (Real.sqrt (mu : ℝ) * rho)) := by
    rw [ENNReal.ofReal_mul mu.property.le,
      ← R.kernelResolvent_ofReal_eq_operator mu psi hpsi0 y]
    calc ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun z ↦ ENNReal.ofReal (psi z)) y
        ≤ ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.kernelResolvent (mu : ℝ)
              ((Metric.ball y rho)ᶜ.indicator 1) y := by
          gcongr
          exact R.kernelSemigroup.kernelResolvent_mono _ hle y
      _ = ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) y ((Metric.ball y rho)ᶜ) := by
          rw [hpot]
      _ ≤ ENNReal.ofReal (phi (Real.sqrt (mu : ℝ) * rho)) := htail y rho hrho
  exact (ENNReal.ofReal_le_ofReal_iff (hphi _)).mp hkey

/-- At a live point the compactified resolvent of the assembled cutoff is one minus the
normalized resolvent of the cutoff. -/
private theorem mul_onePointResolvent_assemble_coe (R : PositiveC0ContractiveResolvent X)
    (mu : PositiveShift) (psi : C₀(X, ℝ)) (y : X) :
    (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu
        (onePointAssemble (-psi) 1) (y : OnePoint X) =
      1 - (mu : ℝ) * R.toContractiveResolvent.operator mu psi y := by
  have hmu : (mu : ℝ) ≠ 0 := mu.property.ne'
  have h := congrArg (fun w : C₀(OnePoint X, ℝ) ↦ w (y : OnePoint X))
    (R.onePointResolvent_operator mu (onePointAssemble (-psi) 1))
  simp only [onePointAssemble_coe, onePointAssemble_infty, onePointRemainder_assemble,
    map_neg, ZeroAtInftyContinuousMap.neg_apply] at h
  rw [h]
  field_simp
  ring

/-- At the added point the compactified resolvent of the assembled cutoff carries the full
weight. -/
private theorem mul_onePointResolvent_assemble_infty (R : PositiveC0ContractiveResolvent X)
    (mu : PositiveShift) (psi : C₀(X, ℝ)) :
    (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu
        (onePointAssemble (-psi) 1) OnePoint.infty = 1 := by
  have hmu : (mu : ℝ) ≠ 0 := mu.property.ne'
  have h := congrArg (fun w : C₀(OnePoint X, ℝ) ↦ w OnePoint.infty)
    (R.onePointResolvent_operator mu (onePointAssemble (-psi) 1))
  simp only [onePointAssemble_infty] at h
  rw [h]
  field_simp


/-- **Displacement tails from resolvent tail decay.**  Let the sub-Markov kernel semigroup
represented by a positive `C₀`-contractive resolvent be conservative, and let its `mu`-potential
measures have the tail decay `phi` in the sense of `HasResolventTail`.  Then at the time
`t = 1 / mu` the transition law started at `x` leaves the ball of radius `4 * r` about `x` with
probability at most `2 * exp 1 * phi (sqrt mu * r)`.

The proof compares the transition law with the excessive function `2 mu R_mu g`, where `g` is a
radial cutoff vanishing on the ball of radius `r` and equal to one outside the ball of radius
`2 r`, extended to the one-point compactification by the value one.  Conservativity enters once,
to turn the tail bound at the starting point into a lower bound for the resolvent of the
complementary cutoff. -/
theorem measure_compl_ball_le_of_hasResolventTail (R : PositiveC0ContractiveResolvent X)
    (hcons : R.kernelSemigroup.IsConservative) {phi : ℝ → ℝ} (hphi : ∀ s, 0 ≤ phi s)
    {mu : PositiveShift} (htail : SubMarkovKernelSemigroup.HasResolventTail R.kernelSemigroup (mu
      : ℝ) phi)
    {t : ℝ≥0} (ht : (mu : ℝ) * (t : ℝ) = 1) (x : X) {r : ℝ} (hr : 0 < r) :
    R.kernelSemigroup t x (Metric.ball x (4 * r))ᶜ ≤
      ENNReal.ofReal (2 * Real.exp 1 * phi (Real.sqrt (mu : ℝ) * r)) := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith only [h]
  by_cases hbig : 1 / 2 ≤ phi (Real.sqrt (mu : ℝ) * r)
  · refine le_trans (R.kernelSemigroup.measure_le_one t x _) ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 : ℝ) ≤ 2 * 2 * (1 / 2) := by norm_num
      _ ≤ 2 * Real.exp 1 * phi (Real.sqrt (mu : ℝ) * r) :=
        mul_le_mul (by linarith only [hexp]) hbig (by norm_num)
          (by linarith only [hexp])
  push Not at hbig
  -- the two radial cutoffs
  have hr2 : r < 2 * r := by linarith only [hr]
  have hr34 : 3 * r < 4 * r := by linarith only [hr]
  obtain ⟨psi, hpsi⟩ : ∃ psi : C₀(X, ℝ), ∀ z, psi z = radialCutoff x r (2 * r) z :=
    ⟨radialCutoffC0 x r (2 * r) hr2, fun _ ↦ rfl⟩
  obtain ⟨chi, hchi⟩ : ∃ chi : C₀(X, ℝ), ∀ z, chi z = radialCutoff x (3 * r) (4 * r) z :=
    ⟨radialCutoffC0 x (3 * r) (4 * r) hr34, fun _ ↦ rfl⟩
  have hpsi0 : ∀ z, 0 ≤ psi z := fun z ↦ by
    rw [hpsi z]; exact radialCutoff_nonneg x r (2 * r) z
  have hpsi1 : ∀ z, psi z ≤ 1 := fun z ↦ by
    rw [hpsi z]; exact radialCutoff_le_one x r (2 * r) z
  have hpsi_one : ∀ z, dist z x ≤ r → psi z = 1 := fun z hz ↦ by
    rw [hpsi z]; exact radialCutoff_eq_one hr2 hz
  have hpsi_zero : ∀ z, 2 * r ≤ dist z x → psi z = 0 := fun z hz ↦ by
    rw [hpsi z]; exact radialCutoff_eq_zero hr2 hz
  have hchi0 : ∀ z, 0 ≤ chi z := fun z ↦ by
    rw [hchi z]; exact radialCutoff_nonneg x (3 * r) (4 * r) z
  have hchi1 : ∀ z, chi z ≤ 1 := fun z ↦ by
    rw [hchi z]; exact radialCutoff_le_one x (3 * r) (4 * r) z
  have hchi_one : ∀ z, dist z x ≤ 3 * r → chi z = 1 := fun z hz ↦ by
    rw [hchi z]; exact radialCutoff_eq_one hr34 hz
  have hchi_zero : ∀ z, 4 * r ≤ dist z x → chi z = 0 := fun z hz ↦ by
    rw [hchi z]; exact radialCutoff_eq_zero hr34 hz
  -- the compactified observables
  obtain ⟨ghat, hghat_coe, hghat_infty, hres_coe, hres_infty⟩ :
      ∃ ghat : C₀(OnePoint X, ℝ),
        (∀ z : X, ghat (z : OnePoint X) = 1 - psi z) ∧ ghat OnePoint.infty = 1 ∧
        (∀ y : X, (mu : ℝ) *
            R.onePointResolvent.toContractiveResolvent.operator mu ghat (y : OnePoint X) =
            1 - (mu : ℝ) * R.toContractiveResolvent.operator mu psi y) ∧
        (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu ghat
            OnePoint.infty = 1 := by
    refine ⟨onePointAssemble (-psi) 1, fun z ↦ ?_, onePointAssemble_infty _ _,
      mul_onePointResolvent_assemble_coe R mu psi, mul_onePointResolvent_assemble_infty R mu psi⟩
    rw [onePointAssemble_coe, ZeroAtInftyContinuousMap.neg_apply]
    ring
  obtain ⟨fhat, hfhat_coe, hfhat_infty⟩ :
      ∃ fhat : C₀(OnePoint X, ℝ),
        (∀ z : X, fhat (z : OnePoint X) = 1 - chi z) ∧ fhat OnePoint.infty = 1 := by
    refine ⟨onePointAssemble (-chi) 1, fun z ↦ ?_, onePointAssemble_infty _ _⟩
    rw [onePointAssemble_coe, ZeroAtInftyContinuousMap.neg_apply]
    ring
  have hghat_nonneg : ∀ z, 0 ≤ ghat z := by
    intro z
    induction z using OnePoint.rec with
    | infty => rw [hghat_infty]; norm_num
    | coe y => rw [hghat_coe]; linarith only [hpsi1 y]
  -- the tail bound away from the starting point
  have hfar : ∀ y : X, 3 * r ≤ dist y x →
      (mu : ℝ) * R.toContractiveResolvent.operator mu psi y ≤
        phi (Real.sqrt (mu : ℝ) * r) := by
    intro y hy
    refine mul_operator_le_of_hasResolventTail R hphi htail hpsi0 hpsi1 y hr fun z hz ↦ ?_
    refine hpsi_zero z ?_
    have h1 : dist y x ≤ dist y z + dist z x := dist_triangle y z x
    have h2 : dist y z = dist z y := dist_comm y z
    linarith only [h1, h2, hy, hz]
  -- the lower bound at the starting point, where conservativity is used
  have hball_meas : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
  have hpotconv : R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r) =
      R.kernelSemigroup.kernelResolvent (mu : ℝ) ((Metric.ball x r).indicator 1) x := by
    rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
      (measurable_one.indicator hball_meas) x, lintegral_indicator_one hball_meas]
  have hindle : ∀ z, (Metric.ball x r).indicator 1 z ≤ ENNReal.ofReal (psi z) := by
    intro z
    by_cases hz : z ∈ Metric.ball x r
    · rw [Set.indicator_of_mem hz, Pi.one_apply,
        hpsi_one z (Metric.mem_ball.mp hz).le, ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  have hpotball : ENNReal.ofReal (mu : ℝ) *
      R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r) ≤
      ENNReal.ofReal ((mu : ℝ) * R.toContractiveResolvent.operator mu psi x) := by
    rw [hpotconv, ENNReal.ofReal_mul hmu.le,
      ← R.kernelResolvent_ofReal_eq_operator mu psi hpsi0 x]
    gcongr
    exact R.kernelSemigroup.kernelResolvent_mono _ hindle x
  have hunit : ENNReal.ofReal (mu : ℝ) *
      R.kernelSemigroup.resolventPotential (mu : ℝ) x Set.univ = 1 := by
    have hconv : R.kernelSemigroup.resolventPotential (mu : ℝ) x Set.univ =
        R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun _ ↦ 1) x := by
      rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ) measurable_const x,
        lintegral_one]
    rw [hconv]
    exact hcons.ofReal_mul_kernelResolvent_one hmu x
  have hcentreE : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal ((mu : ℝ) * R.toContractiveResolvent.operator mu psi x) +
        ENNReal.ofReal (phi (Real.sqrt (mu : ℝ) * r)) := by
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) x Set.univ := hunit.symm
      _ = ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r) +
          ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r)ᶜ := by
          rw [← mul_add, measure_add_measure_compl hball_meas]
      _ ≤ _ := add_le_add hpotball (htail x r hr)
  have hcentre : 1 ≤ (mu : ℝ) * R.toContractiveResolvent.operator mu psi x +
      phi (Real.sqrt (mu : ℝ) * r) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hmu.le (R.isPositive mu psi hpsi0 x)) (hphi _)]
      at hcentreE
    exact ENNReal.one_le_ofReal.mp hcentreE
  -- the excessive function dominating the compactified test observable
  have hval : ∀ w : OnePoint X,
      ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat) w =
        2 * ((mu : ℝ) *
          R.onePointResolvent.toContractiveResolvent.operator mu ghat w) := by
    intro w
    rw [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  have hfv : ∀ z : OnePoint X, fhat z ≤
      ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat) z := by
    intro z
    rw [hval z]
    induction z using OnePoint.rec with
    | infty =>
        rw [hfhat_infty, hres_infty]
        norm_num
    | coe y =>
        have hnn : 0 ≤ 1 - (mu : ℝ) * R.toContractiveResolvent.operator mu psi y := by
          rw [← hres_coe y]
          exact mul_nonneg hmu.le
            (R.onePointResolvent.isPositive mu ghat hghat_nonneg (y : OnePoint X))
        rw [hfhat_coe, hres_coe y]
        by_cases hy : dist y x ≤ 3 * r
        · rw [hchi_one y hy]
          linarith only [hnn]
        · push Not at hy
          have hb := hfar y hy.le
          linarith only [hchi0 y, hb, hbig]
  have hexcess : ∀ nu : PositiveShift, (mu : ℝ) < (nu : ℝ) → ∀ z : OnePoint X,
      (nu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator nu
          ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat) z ≤
        (nu : ℝ) / ((nu : ℝ) - (mu : ℝ)) *
          ((2 * (mu : ℝ)) •
            R.onePointResolvent.toContractiveResolvent.operator mu ghat) z :=
    fun nu hnu z ↦ mul_operator_smul_operator_le R.onePointResolvent mu hghat_nonneg
      (by linarith only [hmu]) nu hnu z
  have hcomp := R.onePointResolvent.integral_kernelSemigroup_le_exp_mul (mu : ℝ)
    ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat)
    hexcess fhat hfv t (x : OnePoint X)
  rw [ht] at hcomp
  have hvx : ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat)
      (x : OnePoint X) ≤ 2 * phi (Real.sqrt (mu : ℝ) * r) := by
    rw [hval, hres_coe x]
    linarith only [hcentre]
  have hsg : R.onePointResolvent.kernelSemigroup = R.onePointKernelSemigroup := rfl
  rw [hsg] at hcomp
  have hfinal : ∫ w, fhat w ∂R.onePointKernelSemigroup t (x : OnePoint X) ≤
      2 * Real.exp 1 * phi (Real.sqrt (mu : ℝ) * r) := by
    calc ∫ w, fhat w ∂R.onePointKernelSemigroup t (x : OnePoint X)
        ≤ Real.exp 1 * ((2 * (mu : ℝ)) •
            R.onePointResolvent.toContractiveResolvent.operator mu ghat)
              (x : OnePoint X) := hcomp
      _ ≤ Real.exp 1 * (2 * phi (Real.sqrt (mu : ℝ) * r)) :=
          mul_le_mul_of_nonneg_left hvx (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 * phi (Real.sqrt (mu : ℝ) * r) := by ring
  -- transport the estimate back to the live space
  let : IsProbabilityMeasure (R.kernelSemigroup t x) := ⟨hcons t x⟩
  have hlaw : R.onePointKernelSemigroup t (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) := by
    rw [R.onePointKernelSemigroup_apply_coe t x, hcons t x, tsub_self, zero_smul, add_zero]
  have hmap : ∫ w, fhat w ∂R.onePointKernelSemigroup t (x : OnePoint X) =
      ∫ z, (1 - chi z) ∂R.kernelSemigroup t x := by
    have hmeas : AEStronglyMeasurable (fun w : OnePoint X ↦ fhat w)
        ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) :=
      (map_continuous fhat).aestronglyMeasurable
    rw [hlaw, integral_map OnePoint.continuous_coe.measurable.aemeasurable hmeas]
    exact integral_congr_ae (Eventually.of_forall hfhat_coe)
  have hSmeas : MeasurableSet ((Metric.ball x (4 * r))ᶜ) :=
    Metric.isOpen_ball.measurableSet.compl
  have hlower : (R.kernelSemigroup t x ((Metric.ball x (4 * r))ᶜ)).toReal ≤
      ∫ z, (1 - chi z) ∂R.kernelSemigroup t x := by
    rw [← measureReal_def, ← integral_indicator_one hSmeas]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hSmeas)
      ((integrable_const (1 : ℝ)).sub (chi.toBCF.integrable _)) fun z ↦ ?_
    by_cases hz : z ∈ (Metric.ball x (4 * r))ᶜ
    · have hz' : 4 * r ≤ dist z x := by
        simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hz
        exact hz
      rw [Set.indicator_of_mem hz, Pi.one_apply, hchi_zero z hz']
      norm_num
    · rw [Set.indicator_of_notMem hz]
      linarith only [hchi1 z]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (R.kernelSemigroup t x) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hmap] at hlower
  exact le_trans hlower hfinal

end PositiveC0ContractiveResolvent

end Algsuperdiff.Process
