/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Analytic support for the Ehrhart volume inequality

Narrow interfaces for differentiation, lattice counts, complex analysis, and Hilbert-space
arguments.
-/

namespace Ehrhart

open MeasureTheory
open Set Filter
open scoped NNReal Pointwise Topology

/-- Rademacher's theorem for real-valued Lipschitz functions on a finite real product. -/
public theorem ae_differentiableAt_lipschitz_realPi
    {n : ℕ} {C : ℝ≥0} {f : (Fin n → ℝ) → ℝ} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), DifferentiableAt ℝ f x :=
  hf.ae_differentiableAt


/-- Membership in the integer lattice scaled by the reciprocal of a natural number. -/
public theorem mem_scaledIntegerSpan_iff {n k : ℕ} [NeZero k] {x : Fin n → ℝ} :
    x ∈ (k : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) ↔
      ∀ i, (k : ℝ) * x i ∈ Set.range (algebraMap ℤ ℝ) :=
  BoxIntegral.unitPartition.mem_smul_span_iff

/-- Lattice counts in a bounded Jordan-measurable set converge to its volume. -/
public theorem scaledIntegerSpan_count_tendsto_volume {n : ℕ} (s : Set (Fin n → ℝ))
    (hbounded : Bornology.IsBounded s) (hmeasurable : MeasurableSet s)
    (hfrontier : volume (frontier s) = 0) :
    Tendsto
      (fun k : ℕ =>
        (Nat.card ↑(s ∩ (k : ℝ)⁻¹ •
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) : ℝ) /
            (k : ℝ) ^ Fintype.card (Fin n))
      atTop (𝓝 (volume.real s)) :=
  tendsto_card_div_pow_atTop_volume s hbounded hmeasurable hfrontier


/-- Rademacher's theorem restricted to a measurable subset of a finite real product. -/
public theorem ae_differentiableWithinAt_lipschitzOn_realPi
    {n : ℕ} {C : ℝ≥0} {f : (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)}
    (hf : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    ∀ᵐ x ∂(volume.restrict s), DifferentiableWithinAt ℝ f s x :=
  hf.ae_differentiableWithinAt hs

/-- Jensen's inequality for the logarithmic norm of an entire function on the unit circle. -/
public theorem log_norm_le_unitCircle_integral_of_differentiable
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hzero : g 0 ≠ 0) :
    Real.log ‖g 0‖ ≤ (2 * Real.pi)⁻¹ *
      ∫ θ : ℝ in 0..2 * Real.pi, Real.log ‖g (Complex.exp (θ * Complex.I))‖ := by
  have hanalytic : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hmeromorphic : Meromorphic g := fun w => (hg.analyticAt w).meromorphicAt
  have hdivisor : 0 ≤ MeromorphicOn.divisor g (Set.univ : Set ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic
  have hcount := Function.locallyFinsuppWithin.logCounting_nonneg
    hdivisor (by norm_num : (1 : ℝ) ≤ 1)
  have hjensen :=
    Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      hmeromorphic (by norm_num : (1 : ℝ) ≠ 0)
  rw [(hg.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hzero] at hjensen
  rw [hjensen] at hcount
  have hcenter :
      Real.log ‖g 0‖ ≤ Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 1 :=
    sub_nonneg.mp hcount
  simpa only [Real.circleAverage_def, circleMap_zero, Complex.ofReal_one, one_mul,
    smul_eq_mul] using hcenter

/-- The logarithmic norm of an entire function is integrable on every circle. -/
public theorem intervalIntegrable_log_norm_circle_of_differentiable
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) (R : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.log ‖g (c + R * Complex.exp (θ * Complex.I))‖)
      volume 0 (2 * Real.pi) := by
  have hcircle : CircleIntegrable (fun w : ℂ => Real.log ‖g w‖) c R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro w _
    exact (hg.analyticAt w).meromorphicAt
  change IntervalIntegrable
    (fun θ : ℝ => Real.log ‖g (c + R * Complex.exp (θ * Complex.I))‖)
    volume 0 (2 * Real.pi) at hcircle
  exact hcircle


/-- Pointwise compactness and equicontinuity give compactness in the compact-open topology. -/
public theorem isCompact_continuousMap_family_of_pointwise
    {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (S : Set C(X, Y)) (hcompact : IsCompact (ContinuousMap.toFun '' S))
    (hequicontinuous : Equicontinuous ((↑) : S → X → Y)) : IsCompact S :=
  ArzelaAscoli.isCompact_of_equicontinuous S hcompact hequicontinuous


/-- A self-adjoint defect has dense range in the orthogonal complement of its fixed space. -/
public theorem continuousLinearMap_id_sub_range_closure_eq_fixedSpace_orthogonal
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (T : E →L[𝕜] E)
    (hT : ∀ x y, inner 𝕜 (T x) y = inner 𝕜 x (T y)) :
    (ContinuousLinearMap.id 𝕜 E - T).range.topologicalClosure =
      (LinearMap.eqLocus T.toLinearMap 1).orthogonal := by
  let S := ContinuousLinearMap.id 𝕜 E - T
  have hSadj : S.adjoint = S := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff S S).2
    intro x y
    change inner 𝕜 (x - T x) y = inner 𝕜 x (y - T y)
    rw [inner_sub_left, inner_sub_right, hT]
  have hker : S.ker = LinearMap.eqLocus T.toLinearMap 1 := by
    ext x
    change x - T x = 0 ↔ T x = x
    rw [sub_eq_zero]
    exact eq_comm
  calc
    S.range.topologicalClosure = S.ker.orthogonal := by
      simpa only [hSadj] using S.orthogonal_ker.symm
    _ = (LinearMap.eqLocus T.toLinearMap 1).orthogonal := by rw [hker]

/-- A continuous linear map vanishing on a set vanishes on its closed linear span. -/
public theorem continuousLinearMap_eq_zero_of_mem_topologicalClosure_span
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) {s : Set E}
    (hs : ∀ x ∈ s, L x = 0) {x : E}
    (hx : x ∈ (Submodule.span 𝕜 s).topologicalClosure) : L x = 0 := by
  have hspan : Submodule.span 𝕜 s ≤ L.ker := Submodule.span_le.mpr hs
  exact (Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker) hx

/-- A continuous linear map preserves containment in closed linear spans. -/
public theorem continuousLinearMap_map_topologicalClosure_span_le
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) {s : Set E} {t : Set F}
    (h : Set.MapsTo L s t) :
    (Submodule.span 𝕜 s).topologicalClosure.map L.toLinearMap ≤
      (Submodule.span 𝕜 t).topologicalClosure := by
  have hspan : Submodule.span 𝕜 s ≤
      (Submodule.span 𝕜 t).topologicalClosure.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact (Submodule.span 𝕜 t).le_topologicalClosure (Submodule.subset_span (h hx))
  exact Submodule.map_le_iff_le_comap.mpr
    (Submodule.topologicalClosure_minimal _ hspan
      ((Submodule.span 𝕜 t).isClosed_topologicalClosure.preimage L.continuous))


end Ehrhart
