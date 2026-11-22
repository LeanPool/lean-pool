/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPLocalIBP
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPContinuity
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction

/-! # Integration by parts on a weighted manifold (partition of unity)

`weightedIBP_of_isWeightedVolume`: for a finite measure `μ` which is `e^{-V}` vol in every chart,
`∫ Γ(u,v) dμ = -∫ u 𝓛v dμ` for smooth `u, v`, `u` compactly supported.
-/

@[expose] public section
open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem manifoldGradient_add' {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f x) (hg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g x) :
    manifoldGradient 𝓘(ℝ, F) (fun y => f y + g y) x =
      manifoldGradient 𝓘(ℝ, F) f x + manifoldGradient 𝓘(ℝ, F) g x := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_add_left, inner_manifoldGradient, inner_manifoldGradient, inner_manifoldGradient]
  have := mvfderiv_add (I := 𝓘(ℝ, F)) hf hg
  have h2 := congrArg (fun L => L w) this
  exact h2

end CutoffRigidity

namespace CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [MeasurableSpace F]
  [BorelSpace F]
  [MeasurableSpace M]
  [BorelSpace M] in
theorem carre_eq_zero_of_notMem_tsupport {u : M → ℝ} (v : M → ℝ) {x : M} (hx : x ∉ tsupport u) :
    carre F u v x = 0 := by
  change inner ℝ (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) u x) _ = 0
  rw [CutoffRigidity.manifoldGradient_eq_zero_of_eventuallyEq
    (notMem_tsupport_iff_eventuallyEq.mp hx), inner_zero_left]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [MeasurableSpace F]
  [BorelSpace F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [MeasurableSpace M]
  [BorelSpace M] in
theorem mdifferentiableAt_of_msmooth {u : M → ℝ} (hu : MSmooth F u) (x : M) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) u x :=
  (hu x).mdifferentiableAt (by simp)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [MeasurableSpace F]
  [BorelSpace F]
  [MeasurableSpace M]
  [BorelSpace M] in
theorem carre_add {f g : M → ℝ} (v : M → ℝ) (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    carre F (fun y => f y + g y) v x = carre F f v x + carre F g v x := by
  change inner ℝ (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) (fun y => f y + g y) x) _ = _
  rw [CutoffRigidity.manifoldGradient_add' (mdifferentiableAt_of_msmooth F hf x)
    (mdifferentiableAt_of_msmooth F hg x), inner_add_left]
  rfl

omit [MeasurableSpace F] [BorelSpace F] in
theorem integrable_carre {u v : M → ℝ} (hu : MSmooth F u) (hv : MSmooth F v)
    (hK : HasCompactSupport u) (μ : Measure M) [IsFiniteMeasure μ] :
    Integrable (carre F u v) μ :=
  (continuous_carre F hu hv).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK fun _x hx => carre_eq_zero_of_notMem_tsupport F v hx)

omit [MeasurableSpace F] [BorelSpace F] in
theorem integrable_mul_generator {V u v : M → ℝ} (hV : MSmooth F V) (hu : MSmooth F u)
    (hv : MSmooth F v) (hK : HasCompactSupport u) (μ : Measure M) [IsFiniteMeasure μ] :
    Integrable (fun x => u x * mgenerator F V v x) μ := by
  have hc : Continuous (fun x => u x * mgenerator F V v x) :=
    hu.continuous.mul (continuous_iff_continuousAt.mpr (continuousAt_mgenerator F hV hv))
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])

/-- The integration by parts identity for a given `u`. -/
def IBPFor (μ : Measure M) (V v u : M → ℝ) : Prop :=
  MSmooth F u ∧ HasCompactSupport u ∧
    ∫ x, carre F u v x ∂μ = -∫ x, u x * mgenerator F V v x ∂μ

omit [MeasurableSpace F] [BorelSpace F] in
theorem IBPFor.add {μ : Measure M} [IsFiniteMeasure μ] {V v f g : M → ℝ} (hV : MSmooth F V)
    (hv : MSmooth F v) (hf : IBPFor F μ V v f) (hg : IBPFor F μ V v g) :
    IBPFor F μ V v (f + g) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  refine ⟨hf1.add hg1, hf2.add hg2, ?_⟩
  have e1 : (fun x => carre F (f + g) v x) = fun x => carre F f v x + carre F g v x :=
    funext fun x => carre_add F v hf1 hg1 x
  have e2 : (fun x => (f + g) x * mgenerator F V v x) =
      fun x => f x * mgenerator F V v x + g x * mgenerator F V v x :=
    funext fun x => by simp [add_mul]
  rw [e1, e2, integral_add (integrable_carre F hf1 hv hf2 μ) (integrable_carre F hg1 hv hg2 μ),
    integral_add (integrable_mul_generator F hV hf1 hv hf2 μ)
      (integrable_mul_generator F hV hg1 hv hg2 μ), hf3, hg3]
  ring

omit [MeasurableSpace F] [BorelSpace F] [BorelSpace M] in
theorem IBPFor.zero {μ : Measure M} {V v : M → ℝ} : IBPFor F μ V v 0 := by
  refine ⟨contMDiff_const, HasCompactSupport.zero, ?_⟩
  have h1 : ∀ x, carre F (0 : M → ℝ) v x = 0 := fun x =>
    carre_eq_zero_of_notMem_tsupport F v (by simp)
  simp [h1]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [MeasurableSpace F]
  [BorelSpace F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [MeasurableSpace M]
  [BorelSpace M] in
theorem exists_bump (x : M) :
    ∃ ψ : M → ℝ, MSmooth F ψ ∧ HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ 0 < ψ x ∧
      tsupport ψ ⊆ (chartAt F x).source := by
  obtain ⟨f⟩ := (inferInstance : Nonempty (SmoothBumpFunction 𝓘(ℝ, F) x))
  refine ⟨f, f.contMDiff, f.hasCompactSupport, fun y => f.nonneg, ?_,
    f.tsupport_subset_chartAt_source⟩
  rw [f.eq_one]; exact one_pos

/-- **(G1)** Integration by parts for the weighted volume measure. -/
theorem weightedIBP_of_isWeightedVolume {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) [IsFiniteMeasure μ] : WeightedIBP F μ V := by
  classical
  intro u v hu hv hK
  choose ψ hψ1 hψ2 hψ3 hψ4 hψ5 using exists_bump (F := F) (M := M)
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | 0 < ψ x y})
    (fun x _ => (isOpen_lt continuous_const (hψ1 x).continuous).mem_nhds (hψ4 x))
  set Ψ : M → ℝ := fun y => ∑ x ∈ t, ψ x y with hΨ
  have hΨpos : ∀ y ∈ tsupport u, 0 < Ψ y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hcov hy)
    exact Finset.sum_pos' (fun i _ => hψ3 i y) ⟨x, hx, hxy⟩
  have hΨs : MSmooth F Ψ := ContMDiff.sum fun x _ => hψ1 x
  set ux : M → M → ℝ := fun x y => u y * ψ x y / Ψ y with hux
  have hux_smooth : ∀ x, MSmooth F (ux x) := by
    intro x y
    by_cases hy : y ∈ tsupport u
    · exact ((hu.mul (hψ1 x)) y).div₀ (hΨs y) (hΨpos y hy).ne'
    · have : ux x =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hy)] with w hw
        simp [hux, hw]
      exact contMDiffAt_const.congr_of_eventuallyEq this
  have hux_supp : ∀ x, tsupport (ux x) ⊆ tsupport (ψ x) := by
    intro x
    apply closure_mono
    intro y hy
    simp only [Function.mem_support, hux] at hy ⊢
    intro h0
    exact hy (by simp [h0])
  have hux_comp : ∀ x, HasCompactSupport (ux x) := fun x =>
    IsCompact.of_isClosed_subset (hψ2 x) (isClosed_tsupport _) (hux_supp x)
  have hbase : ∀ x ∈ t, IBPFor F μ V v (ux x) := fun x _ =>
    ⟨hux_smooth x, hux_comp x, weightedIBP_of_chart F hV x (hμ x) (hux_smooth x) hv
      (hux_comp x) ((hux_supp x).trans (hψ5 x))⟩
  have hsum : IBPFor F μ V v (∑ x ∈ t, ux x) :=
    Finset.sum_induction _ (IBPFor F μ V v) (fun a b ha hb => IBPFor.add F hV hv ha hb)
      (IBPFor.zero F) hbase
  have hEq : ∑ x ∈ t, ux x = u := by
    funext y
    rw [Finset.sum_apply]
    by_cases hy : y ∈ tsupport u
    · have := (hΨpos y hy).ne'
      simp only [hux]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      change u y * Ψ y / Ψ y = u y
      field_simp
    · have h0 : u y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hux, h0]
  rw [hEq] at hsum
  exact hsum.2.2

end CutCur
