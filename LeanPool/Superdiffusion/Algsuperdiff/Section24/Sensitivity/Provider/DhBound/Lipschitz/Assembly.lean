/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.Mollification
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.DerivativeBounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Assembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `W^{1,∞}`-to-Lipschitz bridge on a convex domain

A function on a bounded open convex domain whose weak partial derivatives are
bounded by `B` in every coordinate direction has a Lipschitz representative with
constant `d * B`.

The proof is the classical mollification argument, carried out with the
CoarseGraining convex-domain smoothing operator
`Homogenization.convexApproxSmoothRepresentative`:

1. Replace the weak derivative fields by their truncations, which are bounded by
   `B` *everywhere* (`Mollification`).
2. Mollify.  The mollified function is smooth, its directional derivatives are
   the mollifications of the truncated derivative fields up to the harmless
   factor `1 - ε`, and mollification does not increase the uniform bound.  Hence
   `‖D u_ε‖ ≤ d * B` pointwise on the domain, and the mean value inequality on a
   convex set gives `LipschitzOnWith (d * B) u_ε U`.
3. The mollifications converge to `u` in `L²(U)`, hence in measure, hence a.e.
   along a subsequence.  A pointwise a.e. limit of uniformly Lipschitz functions
   is Lipschitz on the full-measure set where the limit exists, and
   `LipschitzOnWith.extend_real` turns this into a globally Lipschitz function
   a.e. equal to `u`.

The public results are

* `lipschitzOnWith_convexApproxSmoothRepresentative` (step 2),
* `exists_lipschitzWith_ae_eq_of_hasWeakPartialDeriv_bound` (the bridge), and
* `exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound`, its unbundled
  pointwise-oscillation form.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

open HCPolySupport MeasureTheory
open scoped ENNReal Convolution NNReal

variable {d : ℕ}

/-! ## Pointwise limits preserve a Lipschitz bound -/

/-- A pointwise limit of `K`-Lipschitz functions on `s` is `K`-Lipschitz on `s`. -/
theorem lipschitzOnWith_of_tendsto {α : Type*} [PseudoMetricSpace α] {s : Set α}
    {K : ℝ≥0} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, LipschitzOnWith K (f n) s)
    (hF : ∀ x ∈ s, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (F x))) :
    LipschitzOnWith K F s := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  refine le_of_tendsto ((hF x hx).dist (hF y hy)) (Filter.Eventually.of_forall fun n => ?_)
  exact (hf n).dist_le_mul x hx y hy

/-! ## Step 2: the mollified function is Lipschitz on the domain -/

/-- If the weak partial derivatives of `u` are bounded by `B` everywhere, then
every convex-domain mollification of `u` is `d * B`-Lipschitz on the domain. -/
theorem lipschitzOnWith_convexApproxSmoothRepresentative
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {u : Vec d → ℝ} {g : Fin d → Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu2 : MemLpOn U 2 u) (hgtop : ∀ i, MemLpOn U ∞ (g i))
    (hg2 : ∀ i, MemLpOn U 2 (g i)) (hgbd : ∀ i, ∀ y, |g i y| ≤ B)
    (hweak : ∀ i, HasWeakPartialDerivOn U i u (g i))
    {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    LipschitzOnWith (Real.toNNReal ((d : ℝ) * B))
      (convexApproxSmoothRepresentative U ρ u x0 r ε) U := by
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hdB : (0 : ℝ) ≤ (d : ℝ) * B := mul_nonneg (Nat.cast_nonneg d) hB
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative U ρ u x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hUmeas hρ one_le_two hu2 hr hε0
  have hcontFderiv : Continuous fun y => fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε)
    y :=
    hsmooth.continuous_fderiv (by simp)
  have hbound : ∀ x ∈ U,
      ‖fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x‖ ≤ (d : ℝ) * B := by
    intro x hx
    have hstep : ∀ i : Fin d,
        ‖(fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x) (basisVec i)‖ ≤ B := by
      intro i
      have hae := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
        (i := i) hU hρ (p := 2) one_le_two hu2 (hg2 i) (hweak i) hball hr hε0 hε1
      have hcontL : ContinuousOn
          (fun y => (fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) y) (basisVec i)) U :=
        (hcontFderiv.clm_apply continuous_const).continuousOn
      have hcontR : ContinuousOn
          (fun y => (1 - ε) * convexApproxSmoothRepresentative U ρ (g i) x0 r ε y) U := by
        have : ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative U ρ (g i) x0 r ε) :=
          contDiff_convexApproxSmoothRepresentative hUmeas hρ one_le_two (hg2 i) hr hε0
        exact (continuous_const.mul this.continuous).continuousOn
      have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU.isOpen hcontL hcontR
      have hxval := heq hx
      have hmoll : |convexApproxSmoothRepresentative U ρ (g i) x0 r ε x| ≤ B :=
        abs_convexApproxSmoothRepresentative_le hUmeas hρ (hgtop i) hB
          (fun y _ => hgbd i y) hr hε0 x
      have hfac : |1 - ε| ≤ 1 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)]
        linarith
      calc ‖(fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x) (basisVec i)‖
          = |(1 - ε) * convexApproxSmoothRepresentative U ρ (g i) x0 r ε x| := by
            rw [Real.norm_eq_abs]
            exact congrArg abs hxval
        _ = |1 - ε| * |convexApproxSmoothRepresentative U ρ (g i) x0 r ε x| := abs_mul _ _
        _ ≤ 1 * B := by
            exact mul_le_mul hfac hmoll (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    calc ‖fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x‖
        ≤ ∑ i : Fin d,
            ‖(fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x) (basisVec i)‖ :=
          norm_clm_le_sum_basisVec_apply _
      _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => hstep i
      _ = (d : ℝ) * B := by simp [Finset.sum_const, nsmul_eq_mul]
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (hsmooth.differentiable (by simp)).differentiableAt) ?_ hU.convex
  intro x hx
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hdB]
  exact hbound x hx

/-! ## Step 3: from a uniformly Lipschitz `L²`-approximating sequence -/

/-- If `u` is the `L²(U)` limit of a sequence of uniformly `K`-Lipschitz
functions on `U`, then `u` agrees a.e. on `U` with a globally `K`-Lipschitz
function. -/
theorem exists_lipschitzWith_ae_eq_of_tendsto_eLpNorm
    {U : Set (Vec d)} (hUmeas : MeasurableSet U) {u : Vec d → ℝ} {K : ℝ≥0}
    {W : ℕ → Vec d → ℝ}
    (hlip : ∀ n, LipschitzOnWith K (W n) U)
    (htend : Filter.Tendsto (fun n => eLpNorm (W n - u) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    ∃ v : Vec d → ℝ, LipschitzWith K v ∧ v =ᵐ[volume.restrict U] u := by
  classical
  have htim : TendstoInMeasure (volume.restrict U) W Filter.atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by simp) htend
  obtain ⟨ns, _hns, hns_ae⟩ := htim.exists_seq_tendsto_ae
  set S : Set (Vec d) :=
    {x | x ∈ U ∧ Filter.Tendsto (fun k => W (ns k) x) Filter.atTop (nhds (u x))} with hS_def
  have hSU : S ⊆ U := fun _ hx => hx.1
  have hSae : ∀ᵐ x ∂(volume.restrict U), x ∈ S := by
    filter_upwards [MeasureTheory.ae_restrict_mem hUmeas, hns_ae] with x hx hlim
    exact ⟨hx, hlim⟩
  have hlipS : LipschitzOnWith K u S :=
    lipschitzOnWith_of_tendsto (fun k => (hlip (ns k)).mono hSU) fun _ hx => hx.2
  obtain ⟨v, hv_lip, hv_eq⟩ := hlipS.extend_real
  refine ⟨v, hv_lip, ?_⟩
  filter_upwards [hSae] with x hx
  exact (hv_eq hx).symm

/-! ## The bridge -/

/-- **`W^{1,∞}` implies Lipschitz on a convex domain.**  If `u` has weak partial
derivatives `g i` on the bounded open convex domain `U` and each `g i` is
bounded by `B` almost everywhere, then `u` agrees a.e. on `U` with a globally
`d * B`-Lipschitz function. -/
theorem exists_lipschitzWith_ae_eq_of_hasWeakPartialDeriv_bound
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {g : Fin d → Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : MemLpOn U ∞ u) (hg : ∀ i, MemLpOn U ∞ (g i))
    (hgB : ∀ i, ∀ᵐ x ∂(volume.restrict U), |g i x| ≤ B)
    (hweak : ∀ i, HasWeakPartialDerivOn U i u (g i)) :
    ∃ v : Vec d → ℝ, LipschitzWith (Real.toNNReal ((d : ℝ) * B)) v ∧
      v =ᵐ[volume.restrict U] u := by
  classical
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  rcases Set.eq_empty_or_nonempty U with hUempty | hne
  · refine ⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken zero_le, ?_⟩
    rw [hUempty, MeasureTheory.Measure.restrict_empty]
    simp only [MeasureTheory.ae_zero]
    exact Filter.eventually_bot
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.mp hU.isOpen z hz
  have hr : (0 : ℝ) < r0 / 2 := by linarith
  have hball : Metric.closedBall z (r0 / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball0
  have hfin : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  have hu2 : MemLpOn U 2 u := hu.mono_exponent le_top
  -- truncate the derivative fields to a uniform bound
  have hg'ae : ∀ i, g i =ᵐ[volume.restrict U] boundedTruncation B (g i) := fun i =>
    boundedTruncation_ae_eq (hgB i)
  have hg'bd : ∀ i, ∀ y, |boundedTruncation B (g i) y| ≤ B := fun i y =>
    abs_boundedTruncation_le hB (g i) y
  have hg'top : ∀ i, MemLpOn U ∞ (boundedTruncation B (g i)) := fun i =>
    memLpOn_top_boundedTruncation hB (hg i).aestronglyMeasurable
  have hg'2 : ∀ i, MemLpOn U 2 (boundedTruncation B (g i)) := fun i =>
    (hg'top i).mono_exponent le_top
  have hweak' : ∀ i, HasWeakPartialDerivOn U i u (boundedTruncation B (g i)) := fun i =>
    HasWeakPartialDerivOn.congr_deriv_ae (hweak i) (hg'ae i)
  -- the mollification scales
  have hε0 : ∀ n : ℕ, 0 < unitConvexApproxScale (n + 1) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [unitConvexApproxScale]
    push_cast
    positivity
  have hε1 : ∀ n : ℕ, unitConvexApproxScale (n + 1) < 1 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [unitConvexApproxScale]
    push_cast
    rw [div_lt_one (by linarith)]
    linarith
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  -- step 2
  have hlip : ∀ n : ℕ, LipschitzOnWith (Real.toNNReal ((d : ℝ) * B))
      (convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u z (r0 / 2)
        (unitConvexApproxScale (n + 1))) U := fun n =>
    lipschitzOnWith_convexApproxSmoothRepresentative hU hρ hB hu2 hg'top hg'2 hg'bd hweak'
      hball hr (hε0 n) (hε1 n)
  -- step 3: L² convergence of the mollifications
  have hconv0 := tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
    (p := 2) hU one_le_two (by simp) hu2 hball hr
  have hconv1 : Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (fun x => unitConvexApproxSequence u z (r0 / 2) (n + 1) x - u x) 2 (volume.restrict U))
      Filter.atTop (nhds 0) := hconv0.comp (Filter.tendsto_add_atTop_nat 1)
  have hrep : ∀ n : ℕ,
      (convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u z (r0 / 2)
          (unitConvexApproxScale (n + 1)) - u)
        =ᵐ[volume.restrict U]
        (fun x => unitConvexApproxSequence u z (r0 / 2) (n + 1) x - u x) := by
    intro n
    filter_upwards [MeasureTheory.ae_restrict_mem hUmeas] with x hx
    have := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u) hU hρ hx hball hr (hε0 n) (hε1 n)
    simp [unitConvexApproxSequence, Pi.sub_apply, this]
  have hconv2 : Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u z (r0 / 2)
          (unitConvexApproxScale (n + 1)) - u) 2 (volume.restrict U))
      Filter.atTop (nhds 0) := by
    refine hconv1.congr fun n => ?_
    exact (MeasureTheory.eLpNorm_congr_ae (hrep n)).symm
  exact exists_lipschitzWith_ae_eq_of_tendsto_eLpNorm hUmeas hlip hconv2

/-- Unbundled form of the bridge: the representative is stated through its
pointwise oscillation bound, which is the form consumed by the Besov
estimates. -/
theorem exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {g : Fin d → Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : MemLpOn U ∞ u) (hg : ∀ i, MemLpOn U ∞ (g i))
    (hgB : ∀ i, ∀ᵐ x ∂(volume.restrict U), |g i x| ≤ B)
    (hweak : ∀ i, HasWeakPartialDerivOn U i u (g i)) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * B * ‖x - y‖) ∧
        v =ᵐ[volume.restrict U] u := by
  obtain ⟨v, hv_lip, hv_eq⟩ :=
    exists_lipschitzWith_ae_eq_of_hasWeakPartialDeriv_bound hU hB hu hg hgB hweak
  refine ⟨v, fun x y => ?_, hv_eq⟩
  have hdB : (0 : ℝ) ≤ (d : ℝ) * B := mul_nonneg (Nat.cast_nonneg d) hB
  have := hv_lip.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hdB, ← Real.norm_eq_abs] at this

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
