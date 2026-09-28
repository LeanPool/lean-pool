/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Cap.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Analysis.SurfaceMeasure.ArcConvergence`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Arc Convergence
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

/-- Hausdorff convergence with fixed endpoint atoms preserves half-open surface integrals. -/
theorem tendsto_integral_surfaceAreaMeasure_Ioc_of_fixed_atoms
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (ha : ∀ n, surfaceAreaMeasure (K n) {(a : Real.Angle)} =
      surfaceAreaMeasure L {(a : Real.Angle)})
    (hb : ∀ n, surfaceAreaMeasure (K n) {(b : Real.Angle)} =
      surfaceAreaMeasure L {(b : Real.Angle)})
    (f : Real.Angle → ℝ) (hf : Continuous f) :
    Tendsto (fun n ↦ ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
      f u ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b, f u ∂surfaceAreaMeasure L)) := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n), (surfaceAreaMeasure_face_union (K n)).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L, (surfaceAreaMeasure_face_union L).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro g
    exact surfaceAreaMeasure_weak_continuity K L hlim g g.continuous
  exact Real.Angle.tendsto_integral_image_Ioc_of_fixed_endpoint_atoms
    hab hturn hμ ha hb (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

/-- Preserving the two endpoint faces supplies the atomic hypotheses for arc convergence. -/
theorem tendsto_integral_surfaceAreaMeasure_Ioc_of_preserves_faces
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (ha : ∀ n, exposedEdge (K n) (a : Real.Angle) = exposedEdge L (a : Real.Angle))
    (hb : ∀ n, exposedEdge (K n) (b : Real.Angle) = exposedEdge L (b : Real.Angle))
    (f : Real.Angle → ℝ) (hf : Continuous f) :
    Tendsto (fun n ↦ ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
      f u ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b, f u ∂surfaceAreaMeasure L)) := by
  apply tendsto_integral_surfaceAreaMeasure_Ioc_of_fixed_atoms K L hlim hab hturn
    (f := f) (hf := hf)
  · intro n
    rw [(surfaceAreaMeasure_atom_length (K n) _).1,
      (surfaceAreaMeasure_atom_length L _).1, ha n]
  · intro n
    rw [(surfaceAreaMeasure_atom_length (K n) _).1,
      (surfaceAreaMeasure_atom_length L _).1, hb n]

end MovingSofa

end

end

end
