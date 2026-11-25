/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.Manifold

/-!
# Source PSH with locally varying complex model dimension

Every chart is an actual mathlib open partial homeomorphism into a concrete
finite-dimensional complex model. Compatibility is actual differentiability
of each overlap transition; no PSH conclusion is an atlas field. The fixed
mathlib manifold atlas embeds into this interface. Local analytic producers
are reused in each chart's concrete dimension.
-/

@[expose] public section

namespace SGPT.PSH

open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u

/-- Genuine holomorphic coordinates with independently specified finite
chart dimensions, actual covering, and actual complex overlap derivatives. -/
structure VariableComplexAtlas (X : Type u) [TopologicalSpace X] where
  /-- The type indexing the atlas charts. -/
  Index : Type u
  /-- The complex dimension associated with each chart. -/
  dimension : Index → ℕ
  /-- The local coordinate equivalence for each index. -/
  chart : (i : Index) → OpenPartialHomeomorph X (ComplexModel (dimension i))
  cover : ∀ x : X, ∃ i, x ∈ (chart i).source
  holomorphic : ∀ i j, DifferentiableOn ℂ ((chart i).symm.trans (chart j))
    ((chart i).symm.trans (chart j)).source

variable {X : Type u} [TopologicalSpace X]

/-- Local nondegeneracy supplies genuine coordinate non-bottom witnesses
for arbitrary open partial homeomorphisms, independently of any fixed atlas. -/
theorem LocallyNondegenerate.exists_coordinate_ne_bot {v : X → EReal}
    (hv : LocallyNondegenerate v) {d : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) {O : Set (ComplexModel d)}
    (hO : IsOpen O) (hOe : O ⊆ e.target) {z : ComplexModel d} (hz : z ∈ O) :
    ∃ y ∈ O, v (e.symm y) ≠ ⊥ := by
  let V := e.source ∩ e ⁻¹' O
  have hV : IsOpen V := e.isOpen_inter_preimage hO
  have hzT := hOe hz
  have hzV : e.symm z ∈ V := by
    refine ⟨e.map_target hzT, ?_⟩
    change e (e.symm z) ∈ O
    simpa only [e.right_inv hzT] using hz
  obtain ⟨y, hy, hfin⟩ := hv (e.symm z) V hV hzV
  exact ⟨e y, hy.2, by simpa only [e.left_inv hy.1] using hfin⟩

namespace VariableComplexAtlas

variable (A : VariableComplexAtlas X)

/-- The actual coordinate representative, restricted only in subsequent tests. -/
noncomputable def coordinate (v : X → EReal) (i : A.Index) : ComplexModel (A.dimension i)
    → EReal :=
  v ∘ (A.chart i).symm

/-- SGPT `def:pshmfd` in actual holomorphic coordinates whose dimensions may
vary. Connected coordinate neighborhoods and non-bottom source witnesses are
part of the local definition, rather than a single global non-bottom point. -/
def IsPSH (v : X → EReal) : Prop :=
  ∀ x : X, ∃ i : A.Index, x ∈ (A.chart i).source ∧
    ∃ V : Set (ComplexModel (A.dimension i)), IsOpen V ∧ IsConnected V ∧
      V ⊆ (A.chart i).target ∧ A.chart i x ∈ V ∧ PSHOn (A.coordinate v i) V

/-- Genuine holomorphic overlap pullback transports singular PSH germs. -/
theorem chart_germ_iff (v : X → EReal) (i j : A.Index) (x : X)
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    SGPT.Foundations.Analysis.PlurisubharmonicAt (A.coordinate v i) (A.chart i x) ↔
      SGPT.Foundations.Analysis.PlurisubharmonicAt (A.coordinate v j) (A.chart j x) := by
  have transport (a b : A.Index) (ha : x ∈ (A.chart a).source)
      (hb : x ∈ (A.chart b).source)
      (hv : SGPT.Foundations.Analysis.PlurisubharmonicAt (A.coordinate v a) (A.chart a x)) :
      SGPT.Foundations.Analysis.PlurisubharmonicAt (A.coordinate v b) (A.chart b x) := by
    let F := (A.chart b).symm.trans (A.chart a)
    have hx : A.chart b x ∈ F.source := by
      refine ⟨(A.chart b).map_source hb, ?_⟩
      change (A.chart b).symm (A.chart b x) ∈ (A.chart a).source
      simpa only [(A.chart b).left_inv hb] using ha
    have hvF : SGPT.Foundations.Analysis.PlurisubharmonicAt (A.coordinate v a)
        (F (A.chart b x)) := by
      simpa only [F, OpenPartialHomeomorph.trans_apply, (A.chart b).left_inv hb] using hv
    have hp :=
      SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicAt_comp_holomorphic
      F.open_source (A.holomorphic b a) hx hvF
    apply hp.congr
    filter_upwards [F.open_source.mem_nhds hx] with y hy
    change v ((A.chart a).symm (A.chart a ((A.chart b).symm y))) = v ((A.chart b).symm y)
    exact congrArg v ((A.chart a).left_inv hy.2)
  exact ⟨transport i j hi hj, transport j i hj hi⟩

variable {A}

/-- Actual local source witnesses give PSH germs in every actual chart. -/
theorem IsPSH.chartPlurisubharmonic {v : X → EReal} (hv : A.IsPSH v) (i : A.Index) :
    SGPT.Foundations.Analysis.PlurisubharmonicOn (A.coordinate v i) (A.chart i).target := by
  intro z hz
  obtain ⟨j, hj, V, hV, _, _, hzV, hvV⟩ := hv ((A.chart i).symm z)
  have hi := (A.chart i).map_target hz
  have hp := (A.chart_germ_iff v j i ((A.chart i).symm z) hj hi).mp
    (hvV.disc.plurisubharmonicOn hV _ hzV)
  simpa only [(A.chart i).right_inv hz] using hp

/-- Reuse the general local-coordinate positive-measure producer. -/
theorem IsPSH.locallyNondegenerate {v : X → EReal} (hv : A.IsPSH v) :
    LocallyNondegenerate v := by
  apply locallyNondegenerate_of_local_coordinate_psh
  intro x
  obtain ⟨i, hi, V, hV, hc, hVe, hz, hvV⟩ := hv x
  exact ⟨A.dimension i, A.chart i, hi, V, hV, hc, hVe, hz, hvV⟩

/-- Every actual manifold value lies in the source's never-top codomain. -/
theorem IsPSH.ne_top {v : X → EReal} (hv : A.IsPSH v) (x : X) : v x ≠ ⊤ := by
  obtain ⟨i, hi⟩ := A.cover x
  have h := (hv.chartPlurisubharmonic i _ ((A.chart i).map_source hi)).ne_top
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using h

/-- Actual coordinate upper semicontinuity gives global upper semicontinuity
through the genuine chart map and its local inverse equation. -/
theorem IsPSH.upperSemicontinuous {v : X → EReal} (hv : A.IsPSH v) :
    UpperSemicontinuous v := by
  intro x a ha
  obtain ⟨i, hi⟩ := A.cover x
  have hc := (hv.chartPlurisubharmonic i _ ((A.chart i).map_source hi)).upperSemicontinuousAt
  have hca : A.coordinate v i (A.chart i x) < a := by
    simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using ha
  have h := ((A.chart i).continuousAt hi).eventually (hc a hca)
  filter_upwards [h, (A.chart i).open_source.mem_nhds hi] with y hy hyS
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hyS] using hy

/-- The source finite-family observation is global, including the empty
family. It uses the same general finite-neighborhood producer as the open-
domain proof, rather than a separate regularization convention. -/
theorem uscSup_eq_iSup_of_finite {I : Type*} [Finite I] {v : I → X → EReal}
    (hv : ∀ j, A.IsPSH (v j)) : uscSup v = fun x ↦ ⨆ j, v j x := by
  funext x
  exact uscSup_eq_iSup_finite isOpen_univ
    (fun j ↦ (hv j).upperSemicontinuous.upperSemicontinuousOn Set.univ) (mem_univ x)

/-- The exact local source predicate agrees with genuine chart germs plus
local nondegeneracy, allowing every chart its own concrete model dimension. -/
theorem psh_iff_chart_and_nondegenerate {v : X → EReal} :
    A.IsPSH v ↔ (∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (A.coordinate v i) (A.chart i).target) ∧ LocallyNondegenerate v := by
  constructor
  · intro hv
    exact ⟨hv.chartPlurisubharmonic, hv.locallyNondegenerate⟩
  · rintro ⟨hcharts, hnd⟩ x
    obtain ⟨i, hi⟩ := A.cover x
    obtain ⟨W, hW, hzW, hdisc⟩ := hcharts i _ ((A.chart i).map_source hi)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hW.inter (A.chart i).open_target)
      (A.chart i x) ⟨hzW, (A.chart i).map_source hi⟩
    have hbe : ball (A.chart i x) r ⊆ (A.chart i).target := fun _ hz ↦ (hball hz).2
    have hnb := LocallyNondegenerate.exists_coordinate_ne_bot hnd (A.chart i) isOpen_ball hbe
      (mem_ball_self hr)
    exact ⟨i, hi, ball (A.chart i x) r, isOpen_ball, isConnected_ball hr, hbe,
      mem_ball_self hr, hdisc.mono (fun _ hz ↦ (hball hz).1), hnb⟩

/-- Pull actual global family bounds back by an actual chart inverse. -/
theorem locallyBounded_coordinateFamily {I : Type*} {v : I → X → EReal}
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range v) Set.univ) (i : A.Index) :
    LocallyUniformlyBoundedAbove (fun j ↦ A.coordinate (v j) i) (A.chart i).target :=
  locallyUniformlyBoundedAbove_comp_of_univ hb (fun _ hz => (A.chart i).continuousAt_symm hz)

/-- Coordinate covariance concerns the actual global neighborhood envelope. -/
theorem uscSup_coordinateFamily {I : Type*} (v : I → X → EReal) (i : A.Index) :
    EqOn (uscSup (fun j ↦ A.coordinate (v j) i)) (A.coordinate (uscSup v) i)
      (A.chart i).target := by
  intro z hz
  exact SGPT.Foundations.Analysis.FirstPass.uscRegularization_comp_openPartialHomeomorph_apply
    (fun x ↦ ⨆ j, v j x) (A.chart i).symm hz

/-- The full source regularized-supremum clause in a genuine variable atlas. -/
theorem psh_uscSup_of_locallyBounded {I : Type*} [Nonempty I]
    {v : I → X → EReal} (hv : ∀ j, A.IsPSH (v j))
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range v) Set.univ) : A.IsPSH (uscSup v) := by
  classical
  apply psh_iff_chart_and_nondegenerate.mpr
  constructor
  · intro i
    have hpsh : ∀ f ∈ Set.range (fun j ↦ A.coordinate (v j) i),
        SGPT.Foundations.Analysis.PlurisubharmonicOn f (A.chart i).target := by
      rintro f ⟨j, rfl⟩
      exact (hv j).chartPlurisubharmonic i
    have hr := SGPT.Foundations.Analysis.FirstPass.plurisubharmonicOn_uscRegularization_sSup
      (A.chart i).open_target hpsh
      (locallyUniformlyBoundedAbove_range_iff.mpr (locallyBounded_coordinateFamily hb i))
    rw [sSup_range_eq] at hr
    exact (hr.discPshOn.congr (uscSup_coordinateFamily v i)).plurisubharmonicOn (A.chart
      i).open_target
  · apply (hv (Classical.arbitrary I)).locallyNondegenerate.mono
    intro x
    exact (le_iSup (fun j ↦ v j x) (Classical.arbitrary I)).trans
      (SGPT.Foundations.Analysis.FirstPass.le_uscRegularization (fun y ↦ ⨆ j, v j y) x)

/-- The full source decreasing-net clause retains actual original components. -/
theorem psh_iInf_of_antitone {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {v : I → X → EReal} (hv : ∀ j, A.IsPSH (v j)) (hanti : ∀ x, Antitone (fun j ↦ v j x))
    (hn : ∀ x : X, ∃ y ∈ connectedComponent x, (⨅ j, v j y) ≠ ⊥) :
    A.IsPSH (fun x ↦ ⨅ j, v j x) := by
  have hcharts : ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (A.coordinate (fun x ↦ ⨅ j, v j x) i) (A.chart i).target := by
    intro i
    have hd := discPshOn_iInf_of_antitone
      (fun j ↦ ((hv j).chartPlurisubharmonic i).discPshOn)
      (fun z _ ↦ hanti ((A.chart i).symm z))
    exact hd.plurisubharmonicOn (A.chart i).open_target
  apply psh_iff_chart_and_nondegenerate.mpr
  refine ⟨hcharts, locallyNondegenerate_of_component_nonbot_of_local_coordinate_psh ?_ hn⟩
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  exact ⟨A.dimension i, A.chart i, hi, hcharts i⟩

/-- Local `L¹` convergence is on the actual coordinate measure in the
concrete dimension of each chart and concerns the whole original net. -/
theorem tendsto_chartLocalL1_iInf {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {v : I → X → EReal} (hv : ∀ j, A.IsPSH (v j)) (hanti : ∀ x, Antitone (fun j ↦ v j x))
    (hn : ∀ x : X, ∃ y ∈ connectedComponent x, (⨅ j, v j y) ≠ ⊥)
    (i : A.Index) {W K : Set (ComplexModel (A.dimension i))}
    (hW : IsOpen W) (hc : IsConnected W) (hWe : W ⊆ (A.chart i).target)
    (μ : Measure (ComplexModel (A.dimension i))) [μ.IsAddHaarMeasure]
    (hK : IsCompact K) (hKW : K ⊆ W) :
    Tendsto (fun j ↦ ∫ z in K, ‖(v j ((A.chart i).symm z)).toReal -
      (⨅ l, v l ((A.chart i).symm z)).toReal‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨z, hz⟩ := hc.nonempty
  have hfamily (j : I) : PSHOn (A.coordinate (v j) i) W :=
    ⟨((hv j).chartPlurisubharmonic i).discPshOn.mono hWe,
      LocallyNondegenerate.exists_coordinate_ne_bot (hv j).locallyNondegenerate (A.chart i)
        hW hWe hz⟩
  have hlimit := psh_iInf_of_antitone hv hanti hn
  have hnb := LocallyNondegenerate.exists_coordinate_ne_bot hlimit.locallyNondegenerate (A.chart
    i) hW hWe hz
  exact tendsto_localL1_iInf hfamily hW hc.isPreconnected
    (fun z _ ↦ hanti ((A.chart i).symm z)) hnb μ hK hKW

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- The existing genuine mathlib complex-manifold atlas embeds into the
variable-dimensional interface without changing its charts or compatibility. -/
noncomputable def ofFixedModel : VariableComplexAtlas M where
  Index := ComplexChart n M
  dimension := fun _ ↦ n
  chart := fun e ↦ e.val
  cover := fun x ↦ ⟨complexChartAt (n := n) x, mem_complexChartAt_source x⟩
  holomorphic := fun e f ↦
    (contMDiffOn_of_mem_contDiffGroupoid
      (StructureGroupoid.compatible (contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n)))
        e.property f.property)).contDiffOn.differentiableOn (by simp)

/-- The general source predicate specializes exactly to the previously
checked fixed-model local definition. -/
theorem ofFixedModel_isPSH_iff (v : M → EReal) :
    (ofFixedModel n M).IsPSH v ↔ ManifoldPSH (n := n) v := Iff.rfl

end VariableComplexAtlas

end SGPT.PSH
