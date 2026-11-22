/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothRegularLevelTransition

/-! # The actual regular zero level as a `C²` manifold
The atlas is built from the proved scalar implicit-function charts. Smooth
compatibility is proved from their actual ambient extensions.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Choose actual smooth IFT data, retaining all the proved smoothness
properties of those coordinates. -/
noncomputable def smoothRegularLevelData {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0) (x : {y : M // f y = 0}) :
    SmoothRegularLevelData (I := I) f x :=
  Classical.choice (nonempty_smoothRegularLevelData x (hf x.val) X (hregular x.val))

/-- The original level subspace topology equipped with the actual smooth IFT
atlas and the common Euclidean model of codimension one. -/
@[instance_reducible] noncomputable def smoothRegularLevelChartedSpace {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) {y : M // f y = 0} where
  atlas := range (fun x ↦ (smoothRegularLevelData hf X hregular x).levelChart)
  chartAt x := (smoothRegularLevelData hf X hregular x).levelChart
  mem_chart_source x := (smoothRegularLevelData hf X hregular x).center_mem_levelChart_source
  chart_mem_atlas x := ⟨x, rfl⟩

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual zero level is a genuine `C²` manifold, with smooth atlas
compatibility derived from the original equation and IFT rather than assumed. -/
theorem isManifold_smoothRegularLevel {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0) :
    letI := smoothRegularLevelChartedSpace hf X hregular
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 2
      {y : M // f y = 0} := by
  let := smoothRegularLevelChartedSpace hf X hregular
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, preimage_id, range_id, inter_univ] using
    (smoothRegularLevelData hf X hregular x).contDiffOn_transition
      (smoothRegularLevelData hf X hregular x')

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The inclusion of the actual zero level into the original manifold is
`C²`, derived from the genuine IFT inverse charts. -/
theorem contMDiff_smoothRegularLevel_inclusion {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0) :
    letI := smoothRegularLevelChartedSpace hf X hregular
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I 2
      (Subtype.val : {y : M // f y = 0} → M) := by
  let := smoothRegularLevelChartedSpace hf X hregular
  intro x
  rw [contMDiffAt_iff_source]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    range_id, contMDiffWithinAt_univ]
  let d := smoothRegularLevelData hf X hregular x
  change ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I 2
    (fun z ↦ (d.levelChart.symm z).val) (d.levelChart x)
  have hz := d.levelChart.map_source d.center_mem_levelChart_source
  have hi := d.contMDiffAt_inverseExtension hz
  apply hi.congr_of_eventuallyEq
  filter_upwards [d.levelChart.open_target.mem_nhds hz] with z hz'
  exact d.levelChart_symm_val z hz'

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual level inclusion has injective tangent derivative, derived from
its actual smooth ambient left coordinates. Thus the level is an immersed
hypersurface, rather than just a manifold carrying the right topology. -/
theorem injective_mfderiv_smoothRegularLevel_inclusion {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0) :
    letI := smoothRegularLevelChartedSpace hf X hregular
    ∀ x : {y : M // f y = 0}, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I
        (Subtype.val : {y : M // f y = 0} → M) x) := by
  let := smoothRegularLevelChartedSpace hf X hregular
  let := isManifold_smoothRegularLevel hf X hregular
  intro x
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)))
  let d := smoothRegularLevelData hf X hregular x
  let inc : {y : M // f y = 0} → M := Subtype.val
  have hinc : MDifferentiableAt J I inc x :=
    ((contMDiff_smoothRegularLevel_inclusion hf X hregular) x).mdifferentiableAt (by norm_num)
  have hy : x.val ∈ d.ambientChart.source :=
    (d.mem_levelChart_source x).mp d.center_mem_levelChart_source
  have hforward := (d.contMDiffAt_forwardExtension hy).mdifferentiableAt (by norm_num)
  have hfun : d.forwardExtension ∘ inc = (extChartAt J x : _ → _) := by
    funext y
    simp only [extChartAt_coe]
    change d.forwardExtension y.val = d.levelChart y
    exact (d.levelChart_apply y).symm
  have hderiv := mfderiv_congr (I := J) (I' := J) (x := x) hfun
  rw [mfderiv_comp x hforward hinc] at hderiv
  have hinvert := isInvertible_mfderiv_extChartAt (I := J) (mem_extChartAt_source x)
  intro v w hvw
  apply hinvert.injective
  rw [← hderiv]
  change (mfderiv I J d.forwardExtension x.val)
      ((mfderiv J I inc x) v) =
    (mfderiv I J d.forwardExtension x.val) ((mfderiv J I inc x) w)
  rw [hvw]

end CutoffRigidity
