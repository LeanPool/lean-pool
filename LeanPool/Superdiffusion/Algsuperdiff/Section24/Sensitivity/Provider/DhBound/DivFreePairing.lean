/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.WeakDivergence
public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.Cutoff.OpenSet
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.WeakDerivativeTestClosure
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# DivFreePairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weakly divergence-free fields annihilate `H¹` gradients

Source: ABK26 (`e.sensitivity.basic.split`), closure step of the weak
integration by parts.

A vector field `t` on an open bounded convex carrier `U` that is coordinatewise
square integrable, supported in a compact subset of `U`, and weakly divergence
free (it annihilates every smooth compactly supported test gradient) satisfies
  `∫ t · ∇w = 0`  for every `w ∈ H¹(U)`.

The compact interior support substitutes for the vanishing normal trace.  The
proof smooths `w` with CoarseGraining's convex-domain smoothing operator, cuts
off the smooth representative to a test equal to `w`'s smoothing near the
support of `t`, applies the weak divergence-free hypothesis to the cutoff
product, and passes to the limit in `L²(U)`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound

open HCPolySupport MeasureTheory Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **Divergence-free pairing lemma.**  A coordinatewise `L²` vector field with
compact support inside an open bounded convex carrier that annihilates every
smooth compactly supported test gradient also annihilates every `H¹` gradient.
This is the trace-free mechanism of the weak integration by parts in
`e.sensitivity.basic.split`. -/
theorem integral_vecDot_grad_eq_zero_of_weak_div_free
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hUne : U.Nonempty)
    {t : Vec d → Vec d} (htmem : ∀ j, MemScalarL2 U fun x => t x j)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (htK : ∀ x, x ∉ K → t x = 0)
    (hdivfree : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∑ j, ∫ x in U, t x j * euclideanCoordDeriv j ψ x
        ∂MeasureTheory.volume = 0)
    (w : H1Function U) :
    ∫ x in U, vecDot (t x) (w.grad x) ∂MeasureTheory.volume = 0 := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  -- a smooth cutoff equal to one on a neighborhood of the support of `t`
  obtain ⟨δ, hδpos, hδsub⟩ := hK.exists_cthickening_subset_open hU.isOpen hKU
  have hK₁ : IsCompact (Metric.cthickening δ K) := hK.cthickening
  obtain ⟨χ, hχ_smooth, -, hχ_one, hχ_sub⟩ :=
    exists_contDiff_one_on_compact_tsupport_subset hK₁ hδsub hU.isOpen
  have hχc : HasCompactSupport χ := by
    have hbounded : Bornology.IsBounded (tsupport χ) :=
      hU.isBoundedDomain.isBounded.subset hχ_sub
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport χ) hbounded
  have hVopen : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
  have hKV : K ⊆ Metric.thickening δ K := Metric.self_subset_thickening hδpos K
  have hχ_one_V : ∀ y ∈ Metric.thickening δ K, χ y = 1 := fun y hy =>
    hχ_one (Metric.thickening_subset_cthickening δ K hy)
  -- a closed ball inside the carrier for the smoothing operator
  obtain ⟨x0, hx0U⟩ := hUne
  obtain ⟨r₀, hr₀pos, hball₀⟩ := Metric.isOpen_iff.1 hU.isOpen x0 hx0U
  have hrpos : 0 < r₀ / 2 := half_pos hr₀pos
  have hball : Metric.closedBall x0 (r₀ / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball₀
  -- kernel and scale sequence
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  set ε : ℕ → ℝ := fun n => unitConvexApproxScale (n + 1) with hε_def
  have hεpos : ∀ n, 0 < ε n := fun n => by
    simp only [hε_def, unitConvexApproxScale]
    positivity
  have hεlt : ∀ n, ε n < 1 := fun n => by
    simp only [hε_def, unitConvexApproxScale]
    rw [div_lt_one (by positivity)]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεtend : Tendsto ε atTop (nhds 0) := by
    have hcomp :=
      tendsto_unitConvexApproxScale_zero.comp (tendsto_add_atTop_nat 1)
    simpa [hε_def, Function.comp] using! hcomp
  -- L² data for the target function and its gradient
  have hw2 : MemLpOn U 2 w.toFun := w.memL2
  have hg2 : ∀ j, MemLpOn U 2 (fun x => w.grad x j) := fun j => w.gradMemL2 j
  -- smoothed representatives and their gradients
  set W : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d))
      w.toFun x0 (r₀ / 2) (ε n) with hW_def
  set G : ℕ → Fin d → Vec d → ℝ := fun n j x =>
    (1 - ε n) *
      convexApproxSmoothing (unitConvexApproxKernel (d := d))
        (fun y => w.grad y j) x0 (r₀ / 2) (ε n) x with hG_def
  have hW_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n) := fun n =>
    contDiff_convexApproxSmoothRepresentative (p := 2)
      hU.isOpen.measurableSet hρ (by norm_num) hw2 hrpos (hεpos n)
  have hae : ∀ n j,
      (fun x => euclideanCoordDeriv j (W n) x)
        =ᵐ[MeasureTheory.volume.restrict U] G n j := by
    intro n j
    have h1 := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
      (i := j) (p := 2) hU hρ (by norm_num) hw2 (hg2 j) (w.hasWeakGradient j)
      hball hrpos (hεpos n) (hεlt n)
    have h2 : (fun x => (1 - ε n) *
        convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d))
          (fun y => w.grad y j) x0 (r₀ / 2) (ε n) x)
        =ᵐ[MeasureTheory.volume.restrict U] G n j := by
      filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
      simp only [hG_def]
      rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hrpos (hεpos n) (hεlt n)]
    refine Filter.EventuallyEq.trans ?_ h2
    simpa [hW_def, euclideanCoordDeriv] using h1
  -- L² membership of the smoothed gradients
  have hG_mem : ∀ n j, MemScalarL2 U (G n j) := by
    intro n j
    have hmem := memLpOn_convexApproxSmoothing (p := 2) hU hρ (by norm_num)
      (by norm_num) (hg2 j) hball hrpos (hεpos n) (hεlt n)
    exact hmem.const_mul (1 - ε n)
  -- L² convergence of the smoothed gradients
  have hG_tend : ∀ j,
      Tendsto (fun n =>
          eLpNorm (fun x => G n j x - w.grad x j) 2
            (MeasureTheory.volume.restrict U))
        atTop (nhds 0) := by
    intro j
    have htends :=
      tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
        (p := 2) hU hρ (by norm_num) (by norm_num) (hg2 j) hball hrpos hεtend
        (Filter.Eventually.of_forall hεpos) (Filter.Eventually.of_forall hεlt)
    simpa [hG_def] using htends
  -- the smoothed pairing vanishes for every scale
  have hpair_zero : ∀ n,
      (∑ j, ∫ x in U, t x j * euclideanCoordDeriv j (W n) x
        ∂MeasureTheory.volume) = 0 := by
    intro n
    have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * W n x) :=
      hχ_smooth.mul (hW_smooth n)
    have hψc : HasCompactSupport (fun x => χ x * W n x) := hχc.mul_right
    have hψ_sub : tsupport (fun x => χ x * W n x) ⊆ U :=
      (tsupport_mul_subset_left (f := χ) (g := W n)).trans hχ_sub
    have hzero := hdivfree _ hψ_smooth hψc hψ_sub
    have hpt : ∀ x j,
        t x j * euclideanCoordDeriv j (fun y => χ y * W n y) x =
          t x j * euclideanCoordDeriv j (W n) x := by
      intro x j
      by_cases hx : x ∈ K
      · have hnear : (fun y => χ y * W n y) =ᶠ[nhds x] W n := by
          filter_upwards [hVopen.mem_nhds (hKV hx)] with y hy
          rw [hχ_one_V y hy, one_mul]
        have hfd : fderiv ℝ (fun y => χ y * W n y) x = fderiv ℝ (W n) x :=
          hnear.fderiv_eq
        unfold euclideanCoordDeriv
        rw [hfd]
      · have htx : t x = 0 := htK x hx
        have htxj : t x j = 0 := by rw [htx]; rfl
        rw [htxj]
        ring
    calc
      (∑ j, ∫ x in U, t x j * euclideanCoordDeriv j (W n) x
          ∂MeasureTheory.volume)
          = ∑ j, ∫ x in U,
              t x j * euclideanCoordDeriv j (fun y => χ y * W n y) x
              ∂MeasureTheory.volume := by
            refine Finset.sum_congr rfl fun j _ => ?_
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun x => (hpt x j).symm)
      _ = 0 := hzero
  -- transfer to the smoothing of the gradient
  have hpair_G : ∀ n,
      (∑ j, ∫ x in U, t x j * G n j x ∂MeasureTheory.volume) = 0 := by
    intro n
    rw [← hpair_zero n]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae ?_
    filter_upwards [hae n j] with x hx
    rw [← hx]
  -- pass to the limit against the fixed L² field `t`
  have hlim : ∀ j,
      Tendsto (fun n => ∫ x in U, t x j * G n j x ∂MeasureTheory.volume)
        atTop (nhds (∫ x in U, t x j * w.grad x j ∂MeasureTheory.volume)) := by
    intro j
    refine tendsto_integral_mul_of_tendsto_toScalarL2 (htmem j)
      (fun n => hG_mem n j) (hg2 j) ?_
    exact tendsto_toScalarL2_of_tendsto_eLpNorm (fun n => hG_mem n j) (hg2 j)
      (hG_tend j)
  have hsum_lim :
      Tendsto (fun n => ∑ j, ∫ x in U, t x j * G n j x ∂MeasureTheory.volume)
        atTop
        (nhds (∑ j, ∫ x in U, t x j * w.grad x j ∂MeasureTheory.volume)) :=
    tendsto_finsetSum _ fun j _ => hlim j
  have hsum_zero :
      (∑ j, ∫ x in U, t x j * w.grad x j ∂MeasureTheory.volume) = 0 := by
    have hfun :
        (fun n => ∑ j, ∫ x in U, t x j * G n j x ∂MeasureTheory.volume) =
          fun _ : ℕ => (0 : ℝ) := funext hpair_G
    rw [hfun] at hsum_lim
    exact tendsto_nhds_unique hsum_lim tendsto_const_nhds
  -- expand the dot product
  have hint : ∀ j : Fin d,
      Integrable (fun x => t x j * w.grad x j) (volumeMeasureOn U) := fun j =>
    (htmem j).integrable_mul (hg2 j)
  calc
    (∫ x in U, vecDot (t x) (w.grad x) ∂MeasureTheory.volume)
        = ∫ x in U, ∑ j, t x j * w.grad x j ∂MeasureTheory.volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          rfl
    _ = ∑ j, ∫ x in U, t x j * w.grad x j ∂MeasureTheory.volume :=
          integral_finsetSum _ fun j _ => hint j
    _ = 0 := hsum_zero

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound
