/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Holomorphic maps in actual manifold charts

The coordinate domain records both chart conditions. All differentiability
statements below follow from mathlib's `ContMDiff` predicate. In particular,
complex linearity of the real derivative is proved by restriction of scalars,
not postulated as an additional geometric compatibility condition.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

noncomputable section

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The actual coordinate representative of a map between complex manifolds. -/
def coordinateMap (f : V → M) (e : ComplexChart k V) (d : ComplexChart n M) :
    ComplexModel k → ComplexModel n := d.val ∘ f ∘ e.val.symm

/-- The open domain where both charts in a coordinate representative are valid. -/
def coordinateDomain (f : V → M) (e : ComplexChart k V) (d : ComplexChart n M) :
    Set (ComplexModel k) := e.val.target ∩ e.val.symm ⁻¹' (f ⁻¹' d.val.source)

theorem coordinateDomain_isOpen {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M) :
    IsOpen (coordinateDomain f e d) :=
  e.val.isOpen_inter_preimage_symm (d.val.open_source.preimage hf.continuous)

theorem mem_coordinateDomain {f : V → M} {e : ComplexChart k V}
    {d : ComplexChart n M} {x : V} (hx : x ∈ e.val.source)
    (hfx : f x ∈ d.val.source) : e.val x ∈ coordinateDomain f e d := by
  exact ⟨e.val.map_source hx, by simpa only [mem_preimage, e.val.left_inv hx] using hfx⟩

theorem coordinateMap_mem_target {f : V → M} {e : ComplexChart k V}
    {d : ComplexChart n M} {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    coordinateMap f e d z ∈ d.val.target :=
  d.val.map_source hz.2

theorem coordinateMap_at {f : V → M} {e : ComplexChart k V}
    {d : ComplexChart n M} {x : V} (hx : x ∈ e.val.source) :
    coordinateMap f e d (e.val x) = d.val (f x) := by
  simp only [coordinateMap, Function.comp_apply, e.val.left_inv hx]

variable [IsComplexManifold k V] [IsComplexManifold n M]

theorem coordinateMap_contDiffAt {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    ContDiffAt ℂ ∞ (coordinateMap f e d) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas e.property)
    (IsManifold.subset_maximalAtlas d.property)
    (e.val.map_target hz.1) hz.2).mp (hf (e.val.symm z))
  simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, e.val.right_inv hz.1,
    contDiffWithinAt_univ] using h.2

theorem coordinateMap_contDiffOn {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M) :
    ContDiffOn ℂ ∞ (coordinateMap f e d) (coordinateDomain f e d) :=
  fun _ hz => (coordinateMap_contDiffAt hf e d hz).contDiffWithinAt

theorem coordinateMap_contDiffOn_real {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M) :
    ContDiffOn ℝ ∞ (coordinateMap f e d) (coordinateDomain f e d) :=
  (coordinateMap_contDiffOn hf e d).restrict_scalars ℝ

theorem coordinateMap_contDiffAt_real {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    ContDiffAt ℝ ∞ (coordinateMap f e d) z :=
  (coordinateMap_contDiffAt hf e d hz).restrict_scalars ℝ

theorem coordinateMap_fderiv_restrictScalars {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    fderiv ℝ (coordinateMap f e d) z =
      (fderiv ℂ (coordinateMap f e d) z).restrictScalars ℝ :=
  ((coordinateMap_contDiffAt hf e d hz).differentiableAt (by simp)).fderiv_restrictScalars ℝ

theorem coordinateMap_fderiv_map_smul_complex {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d)
    (c : ℂ) (v : ComplexModel k) :
    fderiv ℝ (coordinateMap f e d) z (c • v) =
      c • fderiv ℝ (coordinateMap f e d) z v := by
  rw [coordinateMap_fderiv_restrictScalars hf e d hz]
  exact (fderiv ℂ (coordinateMap f e d) z).map_smul c v

/-- Atlas changes are holomorphic on their actual overlap. -/
theorem chartTransition_contDiffAt (e e' : ComplexChart k V)
    {z : ComplexModel k} (hz : z ∈ (chartTransition e e').source) :
    ContDiffAt ℂ ∞ (chartTransition e e') z := by
  exact coordinateMap_contDiffAt contMDiff_id e e' hz

theorem chartTransition_contDiffAt_real (e e' : ComplexChart k V)
    {z : ComplexModel k} (hz : z ∈ (chartTransition e e').source) :
    ContDiffAt ℝ ∞ (chartTransition e e') z :=
  (chartTransition_contDiffAt e e' hz).restrict_scalars ℝ

omit [IsComplexManifold k V] [IsComplexManifold n M] in
theorem coordinateMap_mem_transition_source {f : V → M} {e : ComplexChart k V}
    {d d' : ComplexChart n M} {z : ComplexModel k}
    (hz : z ∈ coordinateDomain f e d) (hz' : z ∈ coordinateDomain f e d') :
    coordinateMap f e d z ∈ (chartTransition d d').source := by
  refine ⟨coordinateMap_mem_target hz, ?_⟩
  change d.val.symm (d.val (f (e.val.symm z))) ∈ d'.val.source
  rw [d.val.left_inv hz.2]
  exact hz'.2

omit [IsComplexManifold k V] [IsComplexManifold n M] in
theorem coordinateMap_change_target {f : V → M} {e : ComplexChart k V}
    {d d' : ComplexChart n M} {z : ComplexModel k}
    (hz : z ∈ coordinateDomain f e d) :
    coordinateMap f e d' z = chartTransition d d' (coordinateMap f e d z) := by
  change d'.val (f (e.val.symm z)) =
    d'.val (d.val.symm (d.val (f (e.val.symm z))))
  rw [d.val.left_inv hz.2]

/-- The chain rule for a change of target chart. -/
theorem coordinateMap_fderiv_change_target {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d d' : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d)
    (hz' : z ∈ coordinateDomain f e d') :
    fderiv ℝ (coordinateMap f e d') z =
      (chartTransitionDerivative d d' (coordinateMap f e d z)).comp
        (fderiv ℝ (coordinateMap f e d) z) := by
  have heq : coordinateMap f e d' =ᶠ[𝓝 z]
      (chartTransition d d') ∘ coordinateMap f e d := by
    filter_upwards [(coordinateDomain_isOpen hf e d).mem_nhds hz] with y hy
    exact coordinateMap_change_target hy
  rw [heq.fderiv_eq]
  exact fderiv_comp z
    ((chartTransition_contDiffAt_real d d'
      (coordinateMap_mem_transition_source hz hz')).differentiableAt (by simp))
    ((coordinateMap_contDiffAt_real hf e d hz).differentiableAt (by simp))

omit [IsComplexManifold k V] [IsComplexManifold n M] in
theorem coordinateDomain_change_source {f : V → M} {e e' : ComplexChart k V}
    {d : ComplexChart n M} {z : ComplexModel k}
    (hz : z ∈ (chartTransition e e').source) (hzf : z ∈ coordinateDomain f e d) :
    chartTransition e e' z ∈ coordinateDomain f e' d := by
  change z ∈ e.val.target ∩ e.val.symm ⁻¹' e'.val.source at hz
  refine ⟨e'.val.map_source hz.2, ?_⟩
  change f (e'.val.symm (e'.val (e.val.symm z))) ∈ d.val.source
  rw [e'.val.left_inv hz.2]
  exact hzf.2

omit [IsComplexManifold k V] [IsComplexManifold n M] in
theorem coordinateMap_change_source {f : V → M} {e e' : ComplexChart k V}
    {d : ComplexChart n M} {z : ComplexModel k}
    (hz : z ∈ (chartTransition e e').source) :
    coordinateMap f e d z = coordinateMap f e' d (chartTransition e e' z) := by
  change z ∈ e.val.target ∩ e.val.symm ⁻¹' e'.val.source at hz
  change d.val (f (e.val.symm z)) =
    d.val (f (e'.val.symm (e'.val (e.val.symm z))))
  rw [e'.val.left_inv hz.2]

/-- The chain rule for a change of source chart. -/
theorem coordinateMap_fderiv_change_source {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e e' : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ (chartTransition e e').source)
    (hzf : z ∈ coordinateDomain f e d) :
    fderiv ℝ (coordinateMap f e d) z =
      (fderiv ℝ (coordinateMap f e' d) (chartTransition e e' z)).comp
        (chartTransitionDerivative e e' z) := by
  have heq : coordinateMap f e d =ᶠ[𝓝 z]
      (coordinateMap f e' d) ∘ chartTransition e e' := by
    filter_upwards [(chartTransition e e').open_source.mem_nhds hz] with y hy
    exact coordinateMap_change_source hy
  rw [heq.fderiv_eq]
  exact fderiv_comp z
    ((coordinateMap_contDiffAt_real hf e' d
      (coordinateDomain_change_source hz hzf)).differentiableAt (by simp))
    ((chartTransition_contDiffAt_real e e' hz).differentiableAt (by simp))

end

end SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
