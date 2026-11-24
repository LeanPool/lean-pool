/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedRadialLeviPreimage
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TestLeviPairing

/-!
# Monotonicity of radial regularizations of positive-Levi distributions

The difference of two adapted radial kernels is the coordinate Levi trace of
a nonnegative compactly supported potential.  After translation this potential
is an honest test function on the buffered domain.  Transposing its real second
derivatives onto the distribution expresses the difference of the two
regularized values as a sum of nonnegative distributional Levi pairings.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending

open AdaptedRadialKernel
open AdaptedRadialLeviPreimage

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Translating a function supported in the first adapted kernel ball keeps
its support in the fixed compact buffer. -/
theorem AdaptedRadialKernelData.translated_tsupport_subset_compact
    (D : AdaptedRadialKernelData μ Ω x) {a : ℕ} {ψ : E → ℝ}
    (hψ : tsupport ψ ⊆ adaptedComplexModelEquiv ⁻¹'
      closedBall 0 (D.radius / ((a : ℝ) + 1)))
    {z : E} (hz : z ∈ closure (D.inner : Set E)) :
    tsupport (fun y : E ↦ ψ (y - z)) ⊆ D.compact := by
  apply closure_minimal
  · intro y hy
    have hyψ : y - z ∈ tsupport ψ :=
      subset_tsupport ψ hy
    have hcoord :
        ‖adaptedComplexModelEquiv (y - z)‖ ≤
          D.radius / ((a : ℝ) + 1) := by
      simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hψ hyψ
    have hscale : D.radius / ((a : ℝ) + 1) ≤ D.radius := by
      have ha : (1 : ℝ) ≤ (a : ℝ) + 1 := by norm_num
      exact div_le_self D.radius_pos.le ha
    exact D.coordinate_buffer z hz y (hcoord.trans hscale)
  · exact D.compact.isCompact.isClosed

/-- In positive complex dimension, a two-scale difference is four times a
finite sum of distributional Levi pairings against one nonnegative translated
test function. -/
theorem AdaptedRadialKernelData.exists_nonnegative_testFunction_value_sub_eq
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (hn : 0 < Module.finrank ℂ E) {a b : ℕ} (hab : a ≤ b)
    {z : E} (hz : z ∈ closure (D.inner : Set E)) :
    ∃ φ : 𝓓(Ω, ℝ), (∀ y, 0 ≤ φ y) ∧
      D.distributionRegularizedValue T a z -
          D.distributionRegularizedValue T b z =
        4 * ∑ j : Fin (Module.finrank ℂ E),
          distributionalLeviCLM
            (adaptedCoordinateVector (E := E) j) T φ := by
  obtain ⟨ψ, _hψradial, hψsmooth, hψnonneg, hψcompact,
      hψsupport, hψtrace⟩ :=
    exists_adaptedRadialScaleDifferenceLeviPreimage
      μ hn D.radius D.radius_pos hab
  have hψK : tsupport (fun y : E ↦ ψ (y - z)) ⊆ D.compact :=
    D.translated_tsupport_subset_compact hψsupport hz
  have hψΩ : tsupport (fun y : E ↦ ψ (y - z)) ⊆ Ω :=
    hψK.trans D.compact_subset
  let φ : 𝓓(Ω, ℝ) :=
    translatedTestFunction ψ hψcompact hψsmooth z hψΩ
  refine ⟨φ, fun y ↦ hψnonneg (y - z), ?_⟩
  let φa : 𝓓(Ω, ℝ) := TestFunction.ofSupportedIn
    D.cutoffCompact_subset (D.localizedKernelSupportedIn a z)
  let φb : 𝓓(Ω, ℝ) := TestFunction.ofSupportedIn
    D.cutoffCompact_subset (D.localizedKernelSupportedIn b z)
  have htest :
      φa - φb =
        ∑ j : Fin (Module.finrank ℂ E),
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
              (adaptedCoordinateVector (E := E) j)
              (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
                (adaptedCoordinateVector (E := E) j) φ) +
            TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
              (Complex.I • adaptedCoordinateVector (E := E) j)
              (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
                (Complex.I • adaptedCoordinateVector (E := E) j) φ)) := by
    ext y
    change D.localizedKernelSupportedIn a z y -
        D.localizedKernelSupportedIn b z y = _
    rw [D.localizedKernelSupportedIn_eq_kernel a hz,
      D.localizedKernelSupportedIn_eq_kernel b hz]
    simp only [sum_apply, add_apply,
      testFunction_lineDerivCLM_lineDerivCLM_apply]
    change D.kernel a (y - z) - D.kernel b (y - z) =
      ∑ j : Fin (Module.finrank ℂ E),
        (realHessian (fun q : E ↦ ψ (q - z)) y
            (adaptedCoordinateVector (E := E) j)
            (adaptedCoordinateVector (E := E) j) +
          realHessian (fun q : E ↦ ψ (q - z)) y
            (Complex.I • adaptedCoordinateVector (E := E) j)
            (Complex.I • adaptedCoordinateVector (E := E) j))
    simp_rw [realHessian_comp_sub]
    have htrace := hψtrace (y - z)
    simp only [leviForm] at htrace
    change adaptedRadialKernel μ D.radius D.radius_pos a (y - z) -
      adaptedRadialKernel μ D.radius D.radius_pos b (y - z) = _
    rw [← htrace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change T φa - T φb = _
  rw [← map_sub, htest, map_sum]
  simp_rw [map_add, distributionalLeviCLM_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Adapted radial regularized values are antitone in the scale index for every
distribution with nonnegative constant-direction Levi derivatives. -/
theorem AdaptedRadialKernelData.distributionRegularizedValue_antitone
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (hT : HasNonnegativeDistributionalLevi T)
    {a b : ℕ} (hab : a ≤ b) {z : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    D.distributionRegularizedValue T b z ≤
      D.distributionRegularizedValue T a z := by
  by_cases hn : 0 < Module.finrank ℂ E
  · obtain ⟨φ, hφ, hdiff⟩ :=
      D.exists_nonnegative_testFunction_value_sub_eq T hn hab hz
    have hsum : 0 ≤ ∑ j : Fin (Module.finrank ℂ E),
        distributionalLeviCLM
          (adaptedCoordinateVector (E := E) j) T φ := by
      exact Finset.sum_nonneg fun j _ ↦ hT _ φ hφ
    have hnonneg : 0 ≤ D.distributionRegularizedValue T a z -
        D.distributionRegularizedValue T b z := by
      rw [hdiff]
      exact mul_nonneg (by norm_num) hsum
    linarith
  · have hzero : Module.finrank ℂ E = 0 := Nat.eq_zero_of_not_pos hn
    have hk : D.kernel a = D.kernel b :=
      D.kernel_eq_of_finrank_complex_eq_zero hzero a b
    have hlocalized : D.localizedKernelSupportedIn a z =
        D.localizedKernelSupportedIn b z := by
      ext y
      simp only [AdaptedRadialKernelData.localizedKernelSupportedIn_apply]
      rw [hk]
    unfold AdaptedRadialKernelData.distributionRegularizedValue
    rw [hlocalized]

end SGPT.Foundations.Analysis.Pending
