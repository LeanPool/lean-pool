/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.LIHLocalSigma
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.Differentiation

/-!
# LocalMeasurability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Point values of a shell field are integral-local

The manuscript's local information `F(U)` is represented on the shell carrier by
the integral-generated `ShellField.lihLocalSigma U`, whose generators are the
entry tests `j ↦ ∫ j(x)_{ik} φ(x) dx` of probes `φ` supported in `U`
(`Algsuperdiff.Assumptions.ShellField.LIHLocalSigma`).  Every gauge of Section
3.3 — the oscillation gauges `localCubeDerivNorm`, `localCubeSecondDerivNorm`
of `e.BoscL.def` in particular — is a supremum of *pointwise* quantities, so
the first thing needed to place those gauges in a local σ-algebra is that a
single point value

`j ↦ j(x)`

is `lihLocalSigma U`-measurable whenever `x` is an interior point of `U`.

This module proves exactly that.  No mollification is required: on the shell
carrier the value map `x ↦ j(x)` is *continuous* by construction, so the
closed-ball averages

`⨍_{B(x,ρ)} j(y)_{ik} dy`

converge to `j(x)_{ik}` as `ρ ↓ 0` for **every** `j` (no Lebesgue
differentiation, no null set), while each of them is a scalar multiple of the
CoarseGraining entry test against the ball indicator — a probe supported in `U`
as soon as the ball is contained in `U`.  A pointwise limit of measurable
functions is measurable, which gives the claim.

## Main results

* `tendsto_setAverage_closedBall`: shrinking closed-ball averages of a
  continuous function converge to its value at the centre.
* `measurable_entry_eval_lihLocalSigma`: each scalar entry `j ↦ j(x)_{ik}` is
  `lihLocalSigma U`-measurable at every interior point `x` of `U`.
* `tendsto_diffQuotient_deriv`: the difference quotients of the values along a
  direction converge to the stored first derivative applied to that direction.
* `measurable_entry_eval_deriv_lihLocalSigma`,
  `measurable_eval_deriv_apply_lihLocalSigma`: the directional first derivative
  `j ↦ (∇j)(x)v` is `lihLocalSigma U`-measurable at every interior point `x`
  of `U`.  The difference quotients only read values at points of the ball
  around `x` already contained in `U`, so no information outside `U` is used.

## References

* ABK26, `sss.bad.cubes` (the events whose gauges are pointwise suprema).
* ABK26 (the volume-normalized Sobolev norm entering `e.BoscL.def`).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open Filter MeasureTheory Topology
open HCPolySupport
open scoped Matrix.Norms.Elementwise
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Shrinking ball averages of a continuous function -/

/-- Averages of a continuous real function over closed balls of radii tending
to zero converge to its value at the common centre.  This is elementary — it
uses only that a closed ball has positive finite volume and that the average of
a function with values in a closed interval lies in that interval — and in
particular it holds at *every* point, not almost everywhere. -/
theorem tendsto_setAverage_closedBall {f : Vec d → ℝ} (hf : Continuous f)
    (x : Vec d) {rho : ℕ → ℝ} (hpos : ∀ n, 0 < rho n)
    (hrho : Tendsto rho atTop (𝓝 0)) :
    Tendsto (fun n => ⨍ y in Metric.closedBall x (rho n), f y ∂volume) atTop
      (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.continuousAt_iff.1 hf.continuousAt (eps / 2) (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hrho) delta hdelta
  refine ⟨N, fun n hn => ?_⟩
  have hlt : rho n < delta := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] at this
    exact this
  set B : Set (Vec d) := Metric.closedBall x (rho n) with hB
  have hBcompact : IsCompact B := isCompact_closedBall x (rho n)
  have hB0 : volume B ≠ 0 :=
    (Metric.measure_closedBall_pos volume x (hpos n)).ne'
  have hBtop : volume B ≠ ⊤ := hBcompact.measure_lt_top.ne
  have hInt : IntegrableOn f B volume :=
    hf.continuousOn.integrableOn_compact hBcompact
  have hmem : ∀ᵐ y ∂volume.restrict B, f y ∈ Set.Icc (f x - eps / 2) (f x + eps / 2) := by
    refine (ae_restrict_iff' hBcompact.measurableSet).2 (Eventually.of_forall fun y hy => ?_)
    have hdist : dist y x < delta := lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hlt
    have := hball hdist
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  have haverage := (convex_Icc (f x - eps / 2) (f x + eps / 2)).set_average_mem
    isClosed_Icc hB0 hBtop hmem hInt
  rw [Set.mem_Icc] at haverage
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [haverage.1, haverage.2, heps]

/-! ## Ball averages of shell entries are integral-local -/

/-- The scalar ball average of a shell entry is a scalar multiple of the
CoarseGraining entry test against the ball indicator, hence `lihLocalSigma
U`-measurable as soon as the ball lies in `U`. -/
theorem measurable_setAverage_entry_lihLocalSigma {U : Set (Vec d)} {x : Vec d}
    {rho : ℝ} (hrho : Metric.closedBall x rho ⊆ U) (i k : Fin d) :
    @Measurable (ShellField d) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j => ⨍ y in Metric.closedBall x rho, j y i k ∂volume) := by
  set B : Set (Vec d) := Metric.closedBall x rho with hB
  have hBcompact : IsCompact B := isCompact_closedBall x rho
  have hprobe : IsProbeR (Set.indicator B (fun _ => (1 : ℝ))) :=
    isProbeR_indicator hBcompact hBcompact.measurableSet
  have hsupport : Function.support (Set.indicator B (fun _ => (1 : ℝ))) ⊆ U :=
    (support_indicator_one_subset B).trans hrho
  have hentry : @Measurable (ShellField d) ℝ (ShellField.lihLocalSigma U) (borel ℝ)
      (fun j => entryTestR i k (Set.indicator B (fun _ => (1 : ℝ)))
        (ShellField.forgetShell j)) :=
    ShellField.measurable_entryTestR_forgetShell_lihLocalSigma U i k hprobe hsupport
  have hrewrite : (fun j : ShellField d => ⨍ y in B, j y i k ∂volume) =
      fun j : ShellField d => (volume B).toReal⁻¹ •
        entryTestR i k (Set.indicator B (fun _ => (1 : ℝ))) (ShellField.forgetShell j) := by
    funext j
    rw [← avgMat_entry_eq_smul_entryTestR i k B hBcompact.measurableSet
      (ShellField.forgetShell j), avgMat_entry_eq_setAverage B
      (ShellField.forgetShell j) i k]
    rfl
  rw [hrewrite]
  exact hentry.const_smul ((volume B).toReal⁻¹)

/-! ## Point values are integral-local -/

/-- **Each scalar entry of a point value is integral-local.**  If some closed
ball around `x` lies in `U`, then `j ↦ j(x)_{ik}` is measurable for the
integral-generated local σ-algebra `lihLocalSigma U`. -/
theorem measurable_entry_eval_lihLocalSigma {U : Set (Vec d)} {x : Vec d} {r : ℝ}
    (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) (i k : Fin d) :
    @Measurable (ShellField d) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j => j x i k) := by
  let : MeasurableSpace (ShellField d) := ShellField.lihLocalSigma U
  set rho : ℕ → ℝ := fun n => r / ((n : ℝ) + 1) with hrhodef
  have hpos : ∀ n, 0 < rho n := fun n => by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos hr this
  have hle : ∀ n, rho n ≤ r := fun n => by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hrhodef]
    exact div_le_self hr.le h1
  have hrho : Tendsto rho atTop (𝓝 0) := by
    simpa [hrhodef, div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r)
  have hsub : ∀ n, Metric.closedBall x (rho n) ⊆ U := fun n =>
    (Metric.closedBall_subset_closedBall (hle n)).trans hrU
  have hmeas : ∀ n : ℕ, Measurable
      (fun j : ShellField d => ⨍ y in Metric.closedBall x (rho n), j y i k ∂volume) :=
    fun n => measurable_setAverage_entry_lihLocalSigma (hsub n) i k
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun j => ?_)
  have hcont : Continuous (fun y : Vec d => j y i k) :=
    (continuous_apply k).comp ((continuous_apply i).comp j.1.1.continuous)
  exact tendsto_setAverage_closedBall hcont x hpos hrho

/-- Every point of an open ball around `x` inherits the interior-point
hypothesis of `measurable_entry_eval_lihLocalSigma`. -/
private theorem measurable_entry_eval_of_dist_lt {U : Set (Vec d)} {x : Vec d}
    {r : ℝ} (hrU : Metric.closedBall x r ⊆ U) {y : Vec d} (hy : dist y x < r)
    (i k : Fin d) :
    @Measurable (ShellField d) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j => j y i k) := by
  refine measurable_entry_eval_lihLocalSigma (r := r - dist y x) (by linarith) ?_ i k
  refine subset_trans ?_ hrU
  intro w hw
  rw [Metric.mem_closedBall] at hw ⊢
  have htri : dist w x ≤ dist w y + dist y x := dist_triangle w y x
  linarith

/-! ## Directional derivatives are integral-local -/

/-- Entry evaluation is `1`-Lipschitz, hence continuous, for the elementwise
matrix norm carried by the frozen shell carrier. -/
private theorem continuous_matEntry (i k : Fin d) :
    Continuous (fun A : Mat d => A i k) := by
  refine (LipschitzWith.of_dist_le_mul (α := Mat d) (β := ℝ) (K := 1)
    (f := fun A : Mat d => A i k) fun A B => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  have h : ‖(A - B) i k‖ ≤ ‖A - B‖ := Matrix.norm_entry_le_entrywise_sup_norm (A - B)
  simpa only [Matrix.sub_apply, Real.norm_eq_abs] using h

/-- The difference quotients of the shell values along a direction `v` converge
to the stored derivative applied to `v`. -/
theorem tendsto_diffQuotient_deriv (j : ShellField d) (x v : Vec d) {rho : ℕ → ℝ}
    (hne : ∀ n, rho n ≠ 0) (hrho : Tendsto rho atTop (𝓝 0)) :
    Tendsto (fun n => (rho n)⁻¹ • (j (x + rho n • v) - j x)) atTop
      (𝓝 (ShellField.deriv j x v)) := by
  have hinner : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have houter : HasFDerivAt (fun y : Vec d => (j : Vec d → Mat d) y)
      (ShellField.deriv j x) ((fun t : ℝ => x + t • v) 0) := by
    rw [show (fun t : ℝ => x + t • v) 0 = x by simp]
    exact ShellField.hasFDerivAt j x
  have hd : HasDerivAt (fun t : ℝ => (j : Vec d → Mat d) (x + t • v))
      (ShellField.deriv j x v) 0 := by
    simpa only [Function.comp_def] using! houter.comp_hasDerivAt 0 hinner
  have hd' := hasDerivAt_iff_tendsto_slope.1 hd
  have hin : Tendsto rho atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hrho, Eventually.of_forall fun n => hne n⟩
  have hcomp := hd'.comp hin
  refine hcomp.congr fun n => ?_
  simp [slope, sub_zero]

/-- **Directional derivatives are integral-local, entrywise.**  If some closed
ball around `x` lies in `U`, then `j ↦ (∇j)(x)v` has `lihLocalSigma U`-measurable
entries. -/
theorem measurable_entry_eval_deriv_lihLocalSigma {U : Set (Vec d)} {x : Vec d}
    {r : ℝ} (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) (v : Vec d)
    (i k : Fin d) :
    @Measurable (ShellField d) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j => ShellField.deriv j x v i k) := by
  let : MeasurableSpace (ShellField d) := ShellField.lihLocalSigma U
  set nv : ℝ := ‖v‖ with hnvdef
  have hnv : 0 ≤ nv := norm_nonneg v
  set rho : ℕ → ℝ := fun n => r / (((n : ℝ) + 1) * (nv + 1)) with hrhodef
  have hden : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1) * (nv + 1) := fun n => by positivity
  have hpos : ∀ n, 0 < rho n := fun n => div_pos hr (hden n)
  have hne : ∀ n, rho n ≠ 0 := fun n => (hpos n).ne'
  have hrho : Tendsto rho atTop (𝓝 0) := by
    have heq : rho = fun n : ℕ => r / (nv + 1) * (1 / ((n : ℝ) + 1)) := by
      funext n
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : nv + 1 ≠ 0 := by positivity
      rw [hrhodef]
      field_simp
    rw [heq]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / (nv + 1))
  have hdist : ∀ n, dist (x + rho n • v) x < r := by
    intro n
    have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hmul : nv + 1 ≤ ((n : ℝ) + 1) * (nv + 1) :=
      le_mul_of_one_le_left (by linarith) hone
    have hlt : rho n * nv < r := by
      rw [hrhodef, div_mul_eq_mul_div, div_lt_iff₀ (hden n)]
      nlinarith [hr, hnv]
    have hnorm : dist (x + rho n • v) x = rho n * nv := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hpos n), hnvdef]
    rw [hnorm]
    exact hlt
  have hmeas : ∀ n : ℕ, Measurable
      (fun j : ShellField d => (rho n)⁻¹ * (j (x + rho n • v) i k - j x i k)) := by
    intro n
    exact ((measurable_entry_eval_of_dist_lt hrU (hdist n) i k).sub
      (measurable_entry_eval_lihLocalSigma hr hrU i k)).const_mul _
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun j => ?_)
  have hMat := tendsto_diffQuotient_deriv j x v hne hrho
  have hentry := ((continuous_matEntry i k).tendsto
    (ShellField.deriv j x v)).comp hMat
  exact hentry.congr fun _ => rfl

/-- **Directional derivatives are integral-local.**  If some closed ball around
`x` lies in `U`, then `j ↦ (∇j)(x)v` is `lihLocalSigma U`-measurable. -/
theorem measurable_eval_deriv_apply_lihLocalSigma {U : Set (Vec d)} {x : Vec d}
    {r : ℝ} (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) (v : Vec d) :
    @Measurable (ShellField d) (Mat d) (ShellField.lihLocalSigma U) inferInstance
      (fun j => ShellField.deriv j x v) := by
  let : MeasurableSpace (ShellField d) := ShellField.lihLocalSigma U
  exact measurable_matrix_of_entries fun i k =>
    measurable_entry_eval_deriv_lihLocalSigma hr hrU v i k

end

end Algsuperdiff.Section3.Provider.BadEvents
