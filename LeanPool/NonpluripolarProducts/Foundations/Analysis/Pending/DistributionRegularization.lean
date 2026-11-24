/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularizationData
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedKernelCoordinates
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedKernelNeighborhood
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedRadialKernel
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# UNPROVED local decreasing regularization of arbitrary distributions

This first-pass interface deliberately leaves its existence proof unfinished.
It belongs only to the Pending layer, outside the verified umbrella.
A successful typecheck of this file does not prove regularization.

Source: Demailly, Complex Analytic and Differential Geometry,
I.4.18--4.20 and I.5.8.

The missing construction must pair arbitrary distributions with smooth families
of translated test functions and prove the smoothness and Levi positivity of
those pairings. It must use normalized kernels radial for an auxiliary Hermitian
norm, prove monotonicity as their radii decrease, and prove weak convergence
against every test function. After shrinking to a relatively compact inner
domain, a fixed smooth cutoff can give globally smooth extensions without
changing their values there; that extension step is also part of the obligation.

The checked almost-everywhere mollification theorem for locally integrable
densities does not supply these missing facts. In particular, no locally
integrable density is presupposed here, and monotonicity of a general smooth
bump family must not be assumed.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Manifold NNReal Topology

namespace SGPT.Foundations.Analysis.Pending

open AdaptedRadialKernel
open FirstPass

/-- A compact subset of an open finite-dimensional real vector space admits a
smooth test-function cutoff which equals one on a neighborhood of the compact
set and takes values in `[0, 1]`. -/
theorem exists_testFunction_eq_one_nhds_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Opens E} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : 𝓓(Ω, ℝ),
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  have hKintV : K ⊆ interior V := by simpa [hVo.interior_eq] using hKV
  obtain ⟨f, hfK, hfV, hfrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (n := (⊤ : ℕ∞)) (𝓘(ℝ, E)) hK.isClosed hKintV
  have hsupp : Function.support f ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx (hfV x hxV)
  let χ : 𝓓(Ω, ℝ) :=
    ⟨f, f.contMDiff.contDiff,
      HasCompactSupport.of_support_subset_isCompact hVc
        (hsupp.trans subset_closure),
      (closure_mono hsupp).trans hVΩ⟩
  exact ⟨χ, hfK, hfrange⟩

section AdaptedKernelData

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- The geometric and cutoff data supporting the canonical adapted radial
kernels around one point of an open domain. -/
structure AdaptedRadialKernelData (μ : Measure E) (Ω : Opens E) (x : E) where
  /-- The positive radius available for regularizing near the point. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- The open neighborhood on which the kernels are used. -/
  inner : Opens E
  /-- A compact set containing the supports used in the construction. -/
  compact : Compacts E
  center_mem : x ∈ inner
  inner_le : inner ≤ Ω
  compact_subset : (compact : Set E) ⊆ Ω
  coordinate_buffer :
    ∀ z ∈ closure (inner : Set E), ∀ y : E,
      ‖adaptedComplexModelEquiv (y - z)‖ ≤ radius → y ∈ compact
  /-- The smooth cutoff that localizes the regularization. -/
  cutoff : 𝓓(Ω, ℝ)
  cutoff_one_on_compact : ∀ y ∈ compact, cutoff y = 1
  cutoff_mem_Icc : ∀ y, cutoff y ∈ Set.Icc (0 : ℝ) 1

/-- The normalized kernel family carried by adapted regularization data. -/
noncomputable def AdaptedRadialKernelData.kernel
    {μ : Measure E} {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) : E → ℝ :=
  adaptedRadialKernel μ D.radius D.radius_pos j

/-- The buffered cutoff is one at every point reached by translating a center
in the closed inner domain by a vector in the adapted coordinate ball. -/
theorem AdaptedRadialKernelData.cutoff_eq_one_of_coordinate_displacement
    {μ : Measure E} {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) {z y : E}
    (hz : z ∈ closure (D.inner : Set E))
    (hy : ‖adaptedComplexModelEquiv (y - z)‖ ≤ D.radius) :
    D.cutoff y = 1 :=
  D.cutoff_one_on_compact y (D.coordinate_buffer z hz y hy)

/-- The closed inner domain is contained in the compact buffer. -/
theorem AdaptedRadialKernelData.closure_inner_subset_compact
    {μ : Measure E} {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) :
    closure (D.inner : Set E) ⊆ D.compact := by
  intro z hz
  exact D.coordinate_buffer z hz z (by simp [D.radius_pos.le])

/-- The adapted regularization data exist around every point of the domain. -/
theorem exists_adaptedRadialKernelData
    (μ : Measure E) {Ω : Opens E} {x : E}
    (hx : x ∈ Ω) : Nonempty (AdaptedRadialKernelData μ Ω x) := by
  let AReal : E ≃L[ℝ] ComplexModel (Module.finrank ℂ E) :=
    ((adaptedComplexModelEquiv (E := E)).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  obtain ⟨R, hR, U, K, hxU, hUΩ, hKΩ, hbuffer⟩ :=
    exists_open_closure_coordinateBall_neighborhood AReal hx
  obtain ⟨χ, hχK, hχrange⟩ :=
    exists_testFunction_eq_one_nhds_compact K.isCompact hKΩ
  refine ⟨{
    radius := R
    radius_pos := hR
    inner := U
    compact := K
    center_mem := hxU
    inner_le := hUΩ
    compact_subset := hKΩ
    coordinate_buffer := by simpa [AReal] using hbuffer
    cutoff := χ
    cutoff_one_on_compact := ?_
    cutoff_mem_Icc := hχrange }⟩
  intro y hy
  exact hχK.self_of_nhdsSet y hy

variable {μ : Measure E} [BorelSpace E] [μ.IsAddHaarMeasure]
  {Ω : Opens E} {x : E}

theorem AdaptedRadialKernelData.kernel_contDiff
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.kernel j) :=
  adaptedRadialKernel_contDiff μ D.radius D.radius_pos j

theorem AdaptedRadialKernelData.kernel_nonneg
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (y : E) :
    0 ≤ D.kernel j y :=
  adaptedRadialKernel_nonneg μ D.radius D.radius_pos j y

theorem AdaptedRadialKernelData.kernel_integral_one
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    ∫ y : E, D.kernel j y ∂μ = 1 :=
  adaptedRadialKernel_integral_one μ D.radius D.radius_pos j

theorem AdaptedRadialKernelData.kernel_hasCompactSupport
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    HasCompactSupport (D.kernel j) :=
  adaptedRadialKernel_hasCompactSupport μ D.radius D.radius_pos j

theorem AdaptedRadialKernelData.kernel_integrable
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    Integrable (D.kernel j) μ :=
  adaptedRadialKernel_integrable μ D.radius D.radius_pos j

theorem AdaptedRadialKernelData.kernel_tsupport_subset
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    tsupport (D.kernel j) ⊆
      {y | ‖adaptedComplexModelEquiv y‖ ≤ D.radius / ((j : ℝ) + 1)} :=
  adaptedRadialKernel_tsupport_subset_norm μ D.radius D.radius_pos j

theorem AdaptedRadialKernelData.kernel_unitary
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (y : E) :
    D.kernel j
        (adaptedComplexModelEquiv.symm (a • adaptedComplexModelEquiv y)) =
      D.kernel j y :=
  adaptedRadialKernel_unitary μ D.radius D.radius_pos j a ha y

theorem AdaptedRadialKernelData.kernel_even
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (y : E) :
    D.kernel j (-y) = D.kernel j y := by
  simpa using D.kernel_unitary j (-1 : ℂ) (by simp) y

theorem AdaptedRadialKernelData.kernel_scale
    (D : AdaptedRadialKernelData μ Ω x) (a b : ℕ) (y : E) :
    D.kernel b y =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ (ComplexModel (Module.finrank ℂ E)) *
        D.kernel a
          (adaptedComplexModelEquiv.symm
            (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
              adaptedComplexModelEquiv y)) :=
  adaptedRadialKernel_scale μ D.radius D.radius_pos a b y

/-- In complex dimension zero the adapted kernel family is constant in its
scale index. -/
theorem AdaptedRadialKernelData.kernel_eq_of_finrank_complex_eq_zero
    (D : AdaptedRadialKernelData μ Ω x) (hE : Module.finrank ℂ E = 0)
    (a b : ℕ) : D.kernel a = D.kernel b := by
  let _ : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  let _ : Subsingleton E := Module.finrank_zero_iff.mp hE
  funext y
  have hs := D.kernel_scale a b y
  have hdim :
      Module.finrank ℝ (ComplexModel (Module.finrank ℂ E)) = 0 := by
    rw [hE]
    exact Module.finrank_zero_of_subsingleton
  have hpoint :
      adaptedComplexModelEquiv.symm
          (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
            adaptedComplexModelEquiv y) = y :=
    Subsingleton.elim _ _
  rw [hdim, pow_zero, one_mul, hpoint] at hs
  exact hs.symm

end AdaptedKernelData

/-- Multiply a translated smooth kernel by a fixed test cutoff.  The cutoff
makes the result an actual test function on `Ω` for every translation
parameter, without any support assumption on the kernel. -/
def cutoffTranslatedTestFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z : E) : 𝓓(Ω, ℝ) :=
  ⟨fun y ↦ χ y * κ (y - z),
    χ.contDiff.mul (hκ.comp (contDiff_id.sub contDiff_const)),
    χ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans χ.tsupport_subset⟩

@[simp]
theorem cutoffTranslatedTestFunction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z y : E) :
    cutoffTranslatedTestFunction χ κ hκ z y = χ y * κ (y - z) := rfl

theorem cutoffTranslatedTestFunction_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z : E) :
    tsupport (cutoffTranslatedTestFunction χ κ hκ z) ⊆ tsupport χ :=
  tsupport_mul_subset_left

/-- On the closed inner domain, the fixed cutoff does not alter the translated
adapted kernel.  This is the local identity that lets the distributional
transpose be computed with a single compact support. -/
theorem AdaptedRadialKernelData.cutoffTranslatedTestFunction_eq_kernel
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {z y : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    cutoffTranslatedTestFunction D.cutoff (D.kernel j) (D.kernel_contDiff j) z y =
      D.kernel j (y - z) := by
  rw [cutoffTranslatedTestFunction_apply]
  by_cases hkernel : D.kernel j (y - z) = 0
  · simp [hkernel]
  have hsupport : y - z ∈ tsupport (D.kernel j) :=
    subset_tsupport (D.kernel j) hkernel
  have hcoordinate := D.kernel_tsupport_subset j hsupport
  have hscale : D.radius / ((j : ℝ) + 1) ≤ D.radius := by
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
    exact div_le_self D.radius_pos.le hj
  have hcutoff : D.cutoff y = 1 :=
    D.cutoff_eq_one_of_coordinate_displacement hz (hcoordinate.trans hscale)
  rw [hcutoff, one_mul]

/-- The same cutoff-translation family bundled in one fixed-support test space.
This is the domain on which the finite-order distribution estimate applies. -/
def cutoffTranslatedKernelSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) :
    ContDiffMapSupportedIn E ℝ ⊤ K :=
  .of_support_subset (f := fun y : E ↦ χ y * κ (y - z))
    (χ.contDiff.mul (hκ.comp (contDiff_id.sub contDiff_const)))
    (subset_closure.trans (tsupport_mul_subset_left.trans hχK))

@[simp]
theorem cutoffTranslatedKernelSupportedIn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z y : E) :
    cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z y =
      χ y * κ (y - z) := by
  rfl

theorem ofSupportedIn_cutoffTranslatedKernelSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E) :
    TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z) =
      cutoffTranslatedTestFunction χ κ hκ z := by
  ext y
  rfl

section LocalizedAdaptedKernel

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

/-- The compact support of the single cutoff used for every translated
adapted kernel. -/
def AdaptedRadialKernelData.cutoffCompact
    (D : AdaptedRadialKernelData μ Ω x) : Compacts E :=
  ⟨tsupport D.cutoff, D.cutoff.hasCompactSupport⟩

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem AdaptedRadialKernelData.cutoffCompact_subset
    (D : AdaptedRadialKernelData μ Ω x) :
    (D.cutoffCompact : Set E) ⊆ Ω :=
  D.cutoff.tsupport_subset

/-- A translated adapted kernel represented in one fixed-support smooth
function space, independently of its center and scale. -/
def AdaptedRadialKernelData.localizedKernelSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (z : E) :
    ContDiffMapSupportedIn E ℝ ⊤ D.cutoffCompact :=
  cutoffTranslatedKernelSupportedIn D.cutoff (D.kernel j)
    (D.kernel_contDiff j) D.cutoffCompact (by rfl) z

@[simp]
theorem AdaptedRadialKernelData.localizedKernelSupportedIn_apply
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (z y : E) :
    D.localizedKernelSupportedIn j z y =
      D.cutoff y * D.kernel j (y - z) :=
  rfl

theorem AdaptedRadialKernelData.ofSupportedIn_localizedKernelSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (z : E) :
    TestFunction.ofSupportedIn D.cutoffCompact_subset
        (D.localizedKernelSupportedIn j z) =
      cutoffTranslatedTestFunction D.cutoff (D.kernel j)
        (D.kernel_contDiff j) z :=
  ofSupportedIn_cutoffTranslatedKernelSupportedIn D.cutoff (D.kernel j)
    (D.kernel_contDiff j) D.cutoffCompact (by rfl) D.cutoffCompact_subset z

/-- On the closed inner domain, the fixed-support representative evaluates to
the untruncated translated adapted kernel. -/
theorem AdaptedRadialKernelData.localizedKernelSupportedIn_eq_kernel
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {z y : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    D.localizedKernelSupportedIn j z y = D.kernel j (y - z) := by
  rw [localizedKernelSupportedIn_apply]
  simpa only [cutoffTranslatedTestFunction_apply] using
    D.cutoffTranslatedTestFunction_eq_kernel j hz

/-- The distributional transpose applied to the fixed-support translated
kernel.  Smoothness and Levi positivity of this scalar function are isolated
as the next regularization obligations. -/
def AdaptedRadialKernelData.distributionRegularizedValue
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (j : ℕ) (z : E) : ℝ :=
  T (TestFunction.ofSupportedIn D.cutoffCompact_subset
    (D.localizedKernelSupportedIn j z))

end LocalizedAdaptedKernel

/-- On a fixed compact set, a distribution is controlled by finitely many of the
standard derivative seminorms on smooth functions supported in that compact set. -/
theorem exists_finite_seminorm_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn E ℝ ⊤ K,
        |T (TestFunction.ofSupportedIn hKΩ φ)| ≤
          (C : ℝ) *
            (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  let TK := T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)
  let q : Seminorm ℝ (ContDiffMapSupportedIn E ℝ ⊤ K) :=
    (normSeminorm ℝ ℝ).comp TK.toLinearMap
  have hq : Continuous q := continuous_norm.comp TK.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q hq
  refine ⟨s, C, hC, fun φ ↦ ?_⟩
  have h := hbound φ
  change |T ((TestFunction.ofSupportedInCLM ℝ hKΩ) φ)| ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ
  change |T ((TestFunction.ofSupportedInCLM ℝ hKΩ) φ)| ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ at h
  exact h

/-- A distribution has finite order on every fixed compact subset of its domain:
one common derivative order controls its value on all smooth functions supported
in that compact set. -/
theorem exists_finite_order_seminorm_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (m : ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn E ℝ ⊤ K,
        |T (TestFunction.ofSupportedIn hKΩ φ)| ≤
          (C : ℝ) *
            ((Finset.Iic m).sup
              (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  obtain ⟨s, C, hC, hbound⟩ := exists_finite_seminorm_bound_on_compact T K hKΩ
  refine ⟨s.sup id, C, hC, fun φ ↦ (hbound φ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  have hseminorm :
      s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) ≤
        (Finset.Iic (s.sup id)).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) :=
    Finset.sup_mono s.subset_Iic_sup_id
  exact hseminorm φ

end SGPT.Foundations.Analysis.Pending
