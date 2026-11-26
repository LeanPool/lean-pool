/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.EigenLinear
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPGlobal
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSupport
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Smooth compactly supported test functions in the weighted Hilbert space -/

@[expose] public section

open Bundle Filter MeasureTheory Set Manifold
open TauCeti.Manifold
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal Topology

namespace CutoffRigidity.Riemann.Diff

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (M : Type) [EMetricSpace M] [ChartedSpace F M]

/-- `𝒟 = C_c^∞(M)`: smooth functions with compact support. -/
def testSub : Submodule ℝ (M → ℝ) where
  carrier := {f | MSmooth F f ∧ HasCompactSupport f}
  add_mem' := fun {_ _} hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contMDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hf ↦ ⟨(contMDiff_const (c := c)).mul hf.1, hf.2.smul_left⟩

variable {M}

theorem mem_testSub {f : M → ℝ} : f ∈ testSub F M ↔ MSmooth F f ∧ HasCompactSupport f := Iff.rfl

theorem testSub_continuous (f : testSub F M) : Continuous (f : M → ℝ) := f.2.1.continuous

variable [MeasurableSpace M] [BorelSpace M]

theorem testSub_memLp (f : testSub F M) (μ : Measure M) [IsFiniteMeasure μ] :
    MemLp (f : M → ℝ) 2 μ :=
  (testSub_continuous F f).memLp_of_hasCompactSupport f.2.2

omit [MeasurableSpace M] [BorelSpace M] in
theorem testSub_bounded (f : testSub F M) : ∃ C : ℝ, ∀ x, |(f : M → ℝ) x| ≤ C := by
  obtain ⟨C, hC⟩ := (testSub_continuous F f).bounded_above_of_compact_support f.2.2
  exact ⟨C, fun x => by simpa using hC x⟩

/-- The embedding `𝒟 → L²(μ)`. -/
noncomputable def testToL2 (μ : Measure M) [IsFiniteMeasure μ] :
    testSub F M →ₗ[ℝ] (M →₂[μ] ℝ) where
  toFun f := (testSub_memLp F f μ).toLp (f : M → ℝ)
  map_add' f g := MemLp.toLp_add (testSub_memLp F f μ) (testSub_memLp F g μ)
  map_smul' c f := MemLp.toLp_const_smul c (testSub_memLp F f μ)

theorem testToL2_apply (μ : Measure M) [IsFiniteMeasure μ] (f : testSub F M) :
    testToL2 F μ f = (testSub_memLp F f μ).toLp (f : M → ℝ) := rfl

theorem coeFn_testToL2 (μ : Measure M) [IsFiniteMeasure μ] (f : testSub F M) :
    (testToL2 F μ f : M → ℝ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (testSub_memLp F f μ)

section Generator

variable [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

variable [MeasurableSpace F] [BorelSpace F] in
theorem testToL2_injective {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
    (hμ : IsWeightedVolume F μ V) : Function.Injective (testToL2 F μ) := by
  have := isOpenPosMeasure_of_weighted F hV hμ
  intro f g hfg
  apply Subtype.ext
  have h1 := coeFn_testToL2 F μ f
  have h2 := coeFn_testToL2 F μ g
  rw [hfg] at h1
  exact (testSub_continuous F f).ae_eq_iff_eq μ (testSub_continuous F g) |>.1
    (h1.symm.trans h2)

omit [MeasurableSpace M] [BorelSpace M] in
/-- The weighted generator is local, so it preserves compact support. -/
theorem hasCompactSupport_mgenerator (V : M → ℝ) {f : M → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (mgenerator F V f) := by
  have laplacian : HasCompactSupport (mlaplacian F f) := by
    rw [mlaplacian_eq_laplaceBeltrami]
    exact hfc.laplaceBeltrami 𝓘(ℝ, F)
  have drift : HasCompactSupport (fun x ↦ inner ℝ (mgrad F V x) (mgrad F f x)) := by
    simpa only [← mgrad_eq_mgradient, real_inner_comm] using
      hfc.inner_mgradient (I := 𝓘(ℝ, F)) (mgrad F V)
  exact laplacian.sub drift

omit [MeasurableSpace M] [BorelSpace M] in
/-- `𝓛` as a linear endomorphism of `𝒟`. -/
noncomputable def testGen {V : M → ℝ} (hV : MSmooth F V) : testSub F M →ₗ[ℝ] testSub F M where
  toFun f := ⟨fun x => mgenerator F V (f : M → ℝ) x, WReg.msmooth_mgenerator F hV f.2.1,
    hasCompactSupport_mgenerator F V f.2.2⟩
  map_add' f g := Subtype.ext (funext fun x => mgenerator_add F f.2.1 g.2.1 x)
  map_smul' c f := Subtype.ext (funext fun x => mgenerator_const_mul F c f.2.1 x)

omit [MeasurableSpace M] [BorelSpace M] in
theorem testGen_apply {V : M → ℝ} (hV : MSmooth F V) (f : testSub F M) (x : M) :
    (testGen F hV f : M → ℝ) x = mgenerator F V (f : M → ℝ) x := rfl

end Generator

/-- The `L²` inner product of test functions is the integral of their product. -/
theorem inner_testToL2 (μ : Measure M) [IsFiniteMeasure μ] (f g : testSub F M) :
    inner ℝ (testToL2 F μ f) (testToL2 F μ g) = ∫ x, (f : M → ℝ) x * (g : M → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testToL2 F μ f, coeFn_testToL2 F μ g] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

section Green

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

/-- **Green's formula on test functions**: `⟪f, -𝓛g⟫ = ∫ Γ(f,g) dμ`. -/
theorem inner_testGen {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
    (hμ : IsWeightedVolume F μ V) (f g : testSub F M) :
    inner ℝ (testToL2 F μ f) (-(testToL2 F μ (testGen F hV g))) =
      ∫ x, carre F (f : M → ℝ) (g : M → ℝ) x ∂μ := by
  rw [inner_neg_right, inner_testToL2]
  have := weightedIBP_of_isWeightedVolume F hV hμ (f : M → ℝ) (g : M → ℝ) f.2.1 g.2.1 f.2.2
  rw [this]
  rfl

end Green

variable [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- A continuous compactly supported function can be uniformly approximated by test functions. -/
theorem exists_test_approx [SigmaCompactSpace M] {g : M → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : testSub F M, ∀ x, |(h : M → ℝ) x - g x| < δ := by
  obtain ⟨h, hh1, hh2⟩ := hg.exists_contMDiff_approx (I := 𝓘(ℝ, F)) (n := ⊤)
    (ε := fun _ => δ) continuous_const (fun _ => hδ)
  refine ⟨⟨⇑h, h.contMDiff, ?_⟩, fun x => by simpa [Real.dist_eq] using hh1 x⟩
  refine hgc.mono' ?_
  exact hh2.trans subset_closure

variable [SigmaCompactSpace M]

/-- **Density of test functions in `L²(μ)`** (`μ` finite). -/
theorem dense_test {μ : Measure M} [IsFiniteMeasure μ] : DenseRange (testToL2 F μ) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  have : μ.Regular := inferInstance
  rw [Metric.denseRange_iff]
  intro u r hr
  have hu : MemLp (u : M → ℝ) 2 μ := Lp.memLp u
  set c : ℝ≥0∞ := μ univ ^ ((2 : ℝ≥0∞).toReal⁻¹) with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by simp) (measure_ne_top _ _)
  obtain ⟨g, hgc, hgn, hgcont, hgmem⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le
    (p := 2) (by norm_num) (ε := ENNReal.ofReal (r / 4)) (by simpa using hr)
  set δ : ℝ := (r / 4) / (c.toReal + 1) with hδ
  have hδpos : 0 < δ := by
    have := ENNReal.toReal_nonneg (a := c)
    positivity
  obtain ⟨h, hh⟩ := exists_test_approx F hgcont hgc hδpos
  refine ⟨h, ?_⟩
  have hhmem := testSub_memLp F h μ
  have h1 : eLpNorm ((u : M → ℝ) - (h : M → ℝ)) 2 μ ≤ ENNReal.ofReal (r / 2) := by
    have e : (u : M → ℝ) - (h : M → ℝ) =
        ((u : M → ℝ) - g) + (g - (h : M → ℝ)) := (sub_add_sub_cancel _ _ _).symm
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    have h2 : eLpNorm (g - (h : M → ℝ)) 2 μ ≤ ENNReal.ofReal (r / 4) := by
      have := eLpNorm_le_of_ae_bound (p := 2) (μ := μ) (f := g - (h : M → ℝ)) (C := δ)
        (hgmem.aestronglyMeasurable.sub hhmem.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
          exact (hh x).le)
      refine this.trans ?_
      rw [← hc]
      have hmul : c * ENNReal.ofReal δ = ENNReal.ofReal (c.toReal * δ) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcfin]
      rw [hmul]
      apply ENNReal.ofReal_le_ofReal
      rw [hδ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      have := ENNReal.toReal_nonneg (a := c)
      nlinarith
    calc _ ≤ eLpNorm ((u : M → ℝ) - g) 2 μ + eLpNorm (g - (h : M → ℝ)) 2 μ := le_rfl
      _ ≤ ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) := add_le_add hgn h2
      _ = ENNReal.ofReal (r / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  rw [dist_eq_norm]
  have e2 : u - testToL2 F μ h = (hu.sub hhmem).toLp ((u : M → ℝ) - (h : M → ℝ)) := by
    rw [MemLp.toLp_sub hu hhmem, Lp.toLp_coeFn]
    rfl
  rw [e2, Lp.norm_toLp]
  have : (eLpNorm ((u : M → ℝ) - (h : M → ℝ)) 2 μ).toReal ≤ r / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

end CutoffRigidity.Riemann.Diff
