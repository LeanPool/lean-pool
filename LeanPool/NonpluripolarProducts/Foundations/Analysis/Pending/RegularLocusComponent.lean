/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalStatementConnected
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosureDifferenceAnalytic

/-!
# Closures of connected components of the regular locus

Blueprint `ana:regular-component` (Demailly, *Complex analytic and differential geometry*,
II.5.3).

Let `R` be the set of regular points (of any dimension) of an analytic subset `A` of a
complex manifold, and `C` the connected component of `R` through a regular point `c` of
dimension `k`.

* `exists_open_inter_subset_component`, `regularAtDim_of_mem_component`: near each point of
  `C` the set `A` lies in `C`, and all points of `C` are regular of dimension `k`;
* `isComplexAnalyticSubset_closure_component`: `closure C` is analytic (near `p`, it is the
  union of the pieces of (LS) whose connected regular part lies in `C`);
* `isComplexAnalyticallyIrreducible_closure_component`: `closure C` is irreducible
  (identity theorem in flattening coordinates on the connected manifold `C`);
* `regularAtDim_closure_component`: points of `C` are regular points of `closure C` of
  dimension `k`.

The local tool is a `FlatBall`: a flattening `Φ` of `A` at `y` together with a ball in the
target of `Φ`.  On its neighbourhood `W = e_y⁻¹ (Φ⁻¹ ball)`, the set `A ∩ W` is the continuous
image of the convex set `ball ∩ ℂ^j`, consists of `j`-regular points, is relatively closed in
`W`, and local equations vanishing on a nonempty open part of `A ∩ W` vanish on all of it.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RegularLocusComponent

open FirstPass RegularLocusDense

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The regular points of `A`, of any dimension. -/
def regularPoints (A : Set M) : Set M :=
  {x | ∃ k, RegularAtDim (n := n) A x k}

/-- The connected component through `c` of the regular points of `A`. -/
noncomputable def component (A : Set M) (c : M) : Set M :=
  connectedComponentIn (regularPoints (n := n) A) c

/-! ### The coordinate plane -/

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem convex_complexCoordinatePlane (j : ℕ) :
    Convex ℝ (complexCoordinatePlane n j) := by
  intro z hz w hw a b _ _ _ i hi
  simp [hz i hi, hw i hi]

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem isClosed_complexCoordinatePlane (j : ℕ) :
    IsClosed (complexCoordinatePlane n j) := by
  have h : complexCoordinatePlane n j =
      {z | coordinateInclusion n j (coordinateProjection n j z) = z} := by
    ext z
    constructor
    · intro hz
      exact coordinateInclusion_coordinateProjection hz
    · intro hz
      have hz' : coordinateInclusion n j (coordinateProjection n j z) = z := hz
      rw [← hz']
      exact coordinateInclusion_mem_complexCoordinatePlane _
  rw [h]
  exact isClosed_eq ((coordinateInclusion n j).continuous.comp
    (coordinateProjection n j).continuous) continuous_id

/-! ### Flattened balls -/

/-- A flattening of `A` at `y` onto `ℂ^j × {0}` together with a ball inside its target. -/
structure FlatBall (A : Set M) (y : M) (j : ℕ) where
  dim_le : j ≤ n
  /-- The local holomorphic equivalence flattening the analytic subset. -/
  Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)
  source_subset : Φ.source ⊆ (complexChartAt (n := n) y).val.target
  map_center : Φ.toFun ((complexChartAt (n := n) y).val y) = 0
  flat : ∀ {x : M}, x ∈ (complexChartAt (n := n) y).val.source →
    (complexChartAt (n := n) y).val x ∈ Φ.source →
      (x ∈ A ↔ Φ.toFun ((complexChartAt (n := n) y).val x) ∈ complexCoordinatePlane n j)
  /-- The radius of the coordinate ball in the flattened chart. -/
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball (0 : ComplexModel n) radius ⊆ Φ.target

namespace FlatBall

variable {A : Set M} {y : M} {j : ℕ} (F : FlatBall (n := n) A y j)

/-- The neighbourhood `e_y⁻¹ (Φ⁻¹ ball)` of `y`. -/
noncomputable def nbhd : Set M :=
  (complexChartAt (n := n) y).val.source ∩
    (complexChartAt (n := n) y).val ⁻¹'
      (F.Φ.source ∩ F.Φ.toFun ⁻¹' Metric.ball (0 : ComplexModel n) F.radius)

/-- The parametrization `w ↦ e_y⁻¹ (Φ⁻¹ w)`. -/
noncomputable def param (w : ComplexModel n) : M :=
  (complexChartAt (n := n) y).val.symm (F.Φ.invFun w)

omit [IsComplexManifold n M] in
theorem mem_nbhd_iff {x : M} :
    x ∈ F.nbhd ↔ x ∈ (complexChartAt (n := n) y).val.source ∧
      (complexChartAt (n := n) y).val x ∈ F.Φ.source ∧
      F.Φ.toFun ((complexChartAt (n := n) y).val x) ∈
        Metric.ball (0 : ComplexModel n) F.radius :=
  Iff.rfl

omit [IsComplexManifold n M] in
theorem isOpen_nbhd : IsOpen F.nbhd :=
  (complexChartAt (n := n) y).val.continuousOn.isOpen_inter_preimage
    (complexChartAt (n := n) y).val.open_source
    (F.Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage F.Φ.isOpen_source
      Metric.isOpen_ball)

omit [IsComplexManifold n M] in
theorem mem_nbhd : y ∈ F.nbhd := by
  refine F.mem_nbhd_iff.mpr ⟨mem_complexChartAt_source y, F.Φ.center_mem_source, ?_⟩
  rw [F.map_center]
  exact Metric.mem_ball_self F.radius_pos

omit [IsComplexManifold n M] in
theorem invFun_mem_source {w : ComplexModel n}
    (hw : w ∈ Metric.ball (0 : ComplexModel n) F.radius) : F.Φ.invFun w ∈ F.Φ.source :=
  F.Φ.mapsTo_invFun (F.ball_subset hw)

omit [IsComplexManifold n M] in
theorem chart_param {w : ComplexModel n} (hw : w ∈ Metric.ball (0 : ComplexModel n) F.radius) :
    (complexChartAt (n := n) y).val (F.param w) = F.Φ.invFun w :=
  (complexChartAt (n := n) y).val.right_inv (F.source_subset (F.invFun_mem_source hw))

omit [IsComplexManifold n M] in
theorem param_mem_source {w : ComplexModel n}
    (hw : w ∈ Metric.ball (0 : ComplexModel n) F.radius) :
    F.param w ∈ (complexChartAt (n := n) y).val.source :=
  (complexChartAt (n := n) y).val.map_target (F.source_subset (F.invFun_mem_source hw))

omit [IsComplexManifold n M] in
theorem param_mem_nbhd {w : ComplexModel n}
    (hw : w ∈ Metric.ball (0 : ComplexModel n) F.radius) : F.param w ∈ F.nbhd := by
  refine F.mem_nbhd_iff.mpr ⟨F.param_mem_source hw, ?_, ?_⟩
  · rw [F.chart_param hw]
    exact F.invFun_mem_source hw
  · rw [F.chart_param hw, F.Φ.right_inv w (F.ball_subset hw)]
    exact hw

omit [IsComplexManifold n M] in
theorem mem_iff_of_mem_nbhd {x : M} (hx : x ∈ F.nbhd) :
    x ∈ A ↔ F.Φ.toFun ((complexChartAt (n := n) y).val x) ∈ complexCoordinatePlane n j :=
  F.flat (F.mem_nbhd_iff.mp hx).1 (F.mem_nbhd_iff.mp hx).2.1

omit [IsComplexManifold n M] in
theorem param_mem {w : ComplexModel n} (hw : w ∈ Metric.ball (0 : ComplexModel n) F.radius)
    (hwp : w ∈ complexCoordinatePlane n j) : F.param w ∈ A := by
  rw [F.mem_iff_of_mem_nbhd (F.param_mem_nbhd hw), F.chart_param hw,
    F.Φ.right_inv w (F.ball_subset hw)]
  exact hwp

omit [IsComplexManifold n M] in
theorem param_chart {x : M} (hx : x ∈ F.nbhd) :
    F.param (F.Φ.toFun ((complexChartAt (n := n) y).val x)) = x := by
  have hx' := F.mem_nbhd_iff.mp hx
  change (complexChartAt (n := n) y).val.symm
    (F.Φ.invFun (F.Φ.toFun ((complexChartAt (n := n) y).val x))) = x
  rw [F.Φ.left_inv _ hx'.2.1, (complexChartAt (n := n) y).val.left_inv hx'.1]

omit [IsComplexManifold n M] in
theorem inter_nbhd_eq_image :
    A ∩ F.nbhd = F.param '' (Metric.ball (0 : ComplexModel n) F.radius ∩
      complexCoordinatePlane n j) := by
  ext x
  constructor
  · rintro ⟨hxA, hx⟩
    exact ⟨_, ⟨(F.mem_nbhd_iff.mp hx).2.2, (F.mem_iff_of_mem_nbhd hx).mp hxA⟩,
      F.param_chart hx⟩
  · rintro ⟨w, ⟨hw, hwp⟩, rfl⟩
    exact ⟨F.param_mem hw hwp, F.param_mem_nbhd hw⟩

omit [IsComplexManifold n M] in
theorem continuousOn_param :
    ContinuousOn F.param (Metric.ball (0 : ComplexModel n) F.radius) :=
  (complexChartAt (n := n) y).val.continuousOn_symm.comp
    (F.Φ.invFun_holomorphic.continuousOn.mono F.ball_subset)
    (fun _ hw => F.source_subset (F.invFun_mem_source hw))

omit [IsComplexManifold n M] in
theorem isPreconnected_inter_nbhd : IsPreconnected (A ∩ F.nbhd) := by
  rw [F.inter_nbhd_eq_image]
  exact ((convex_ball _ _).inter (convex_complexCoordinatePlane j)).isPreconnected.image _
    (F.continuousOn_param.mono inter_subset_left)

theorem regularAtDim_of_mem {x : M} (hxA : x ∈ A) (hx : x ∈ F.nbhd) :
    RegularAtDim (n := n) A x j :=
  RegularPatchNeighborhood.regularAtDim_of_flattening F.dim_le F.Φ F.flat hxA
    (F.mem_nbhd_iff.mp hx).1 (F.mem_nbhd_iff.mp hx).2.1

omit [IsComplexManifold n M] in
/-- `A ∩ W` is relatively closed in `W`. -/
theorem nbhd_inter_closure_subset : F.nbhd ∩ closure (A ∩ F.nbhd) ⊆ A := by
  rintro x ⟨hx, hxcl⟩
  have hx' := F.mem_nbhd_iff.mp hx
  rw [F.mem_iff_of_mem_nbhd hx]
  by_contra hxp
  have hcont : ContinuousAt (fun z => F.Φ.toFun ((complexChartAt (n := n) y).val z)) x :=
    (F.Φ.toFun_holomorphic.continuousOn.continuousAt
      (F.Φ.isOpen_source.mem_nhds hx'.2.1)).comp
      ((complexChartAt (n := n) y).val.continuousAt hx'.1)
  have hev : (fun z => F.Φ.toFun ((complexChartAt (n := n) y).val z)) ⁻¹'
      (complexCoordinatePlane n j)ᶜ ∈ 𝓝 x :=
    hcont.preimage_mem_nhds
      ((isClosed_complexCoordinatePlane j).isOpen_compl.mem_nhds hxp)
  obtain ⟨z, hz, hzA, hzW⟩ := mem_closure_iff_nhds.mp hxcl _ hev
  exact hz ((F.mem_iff_of_mem_nbhd hzW).mp hzA)

/-- **Identity theorem on a flattened ball.**  If the local equations of `B` at `y` are
defined on the image of the ball, and `B` contains a nonempty relatively open part of
`A ∩ W`, then `B` contains `A ∩ W`. -/
theorem inter_nbhd_subset_of_isOpen {B : Set M} (P : ComplexAnalyticPresentationAt (n := n) B y)
    (hN : ∀ w ∈ Metric.ball (0 : ComplexModel n) F.radius,
      F.Φ.invFun w ∈ P.coordinateNeighborhood)
    {O : Set M} (hO : IsOpen O) (hne : (O ∩ (A ∩ F.nbhd)).Nonempty)
    (hOB : O ∩ (A ∩ F.nbhd) ⊆ B) : A ∩ F.nbhd ⊆ B := by
  have hD : IsOpen (coordinateInclusion n j ⁻¹' Metric.ball (0 : ComplexModel n) F.radius) :=
    Metric.isOpen_ball.preimage (coordinateInclusion n j).continuous
  have hDc : Convex ℝ
      (coordinateInclusion n j ⁻¹' Metric.ball (0 : ComplexModel n) F.radius) := by
    intro u hu v hv a b ha hb hab
    have hu' : coordinateInclusion n j u ∈ Metric.ball (0 : ComplexModel n) F.radius := hu
    have hv' : coordinateInclusion n j v ∈ Metric.ball (0 : ComplexModel n) F.radius := hv
    have h := convex_ball (0 : ComplexModel n) F.radius hu' hv' ha hb hab
    change coordinateInclusion n j (a • u + b • v) ∈ Metric.ball (0 : ComplexModel n) F.radius
    rw [map_add, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.map_smul_of_tower]
    exact h
  obtain ⟨z, hzO, hzA, hzW⟩ := hne
  have hzW' := F.mem_nbhd_iff.mp hzW
  obtain ⟨u₀, hu₀⟩ : ∃ u, coordinateInclusion n j u =
      F.Φ.toFun ((complexChartAt (n := n) y).val z) :=
    ⟨_, coordinateInclusion_coordinateProjection ((F.mem_iff_of_mem_nbhd hzW).mp hzA)⟩
  have hcont : ContinuousOn (fun u => F.param (coordinateInclusion n j u))
      (coordinateInclusion n j ⁻¹' Metric.ball (0 : ComplexModel n) F.radius) :=
    F.continuousOn_param.comp (coordinateInclusion n j).continuous.continuousOn
      (fun _ hu => hu)
  have hD'o := hcont.isOpen_inter_preimage hD hO
  have hu₀D : u₀ ∈ coordinateInclusion n j ⁻¹' Metric.ball (0 : ComplexModel n) F.radius ∩
      (fun u => F.param (coordinateInclusion n j u)) ⁻¹' O := by
    refine ⟨?_, ?_⟩
    · change coordinateInclusion n j u₀ ∈ Metric.ball (0 : ComplexModel n) F.radius
      rw [hu₀]
      exact hzW'.2.2
    · change F.param (coordinateInclusion n j u₀) ∈ O
      rw [hu₀, F.param_chart hzW]
      exact hzO
  have hvanish : ∀ i, EqOn (fun u => P.generator i (F.Φ.invFun (coordinateInclusion n j u))) 0
      (coordinateInclusion n j ⁻¹' Metric.ball (0 : ComplexModel n) F.radius) := by
    intro i
    refine eqOn_zero_of_isOpen_convex hD hDc ?_ hD'o inter_subset_left ⟨u₀, hu₀D⟩ ?_
    · exact (P.generator_holomorphic i).comp
        (F.Φ.invFun_holomorphic.comp (coordinateInclusion n j).differentiableOn
          (fun u hu => F.ball_subset hu))
        (fun u hu => hN _ hu)
    · intro u hu
      have hwb : coordinateInclusion n j u ∈ Metric.ball (0 : ComplexModel n) F.radius := hu.1
      have hq : F.param (coordinateInclusion n j u) ∈ B :=
        hOB ⟨hu.2, F.param_mem hwb (coordinateInclusion_mem_complexCoordinatePlane u),
          F.param_mem_nbhd hwb⟩
      have hmem : (complexChartAt (n := n) y).val (F.param (coordinateInclusion n j u)) ∈
          P.coordinateNeighborhood := by
        rw [F.chart_param hwb]
        exact hN _ hwb
      have h := (P.zeroLocus (F.param_mem_source hwb) hmem).mp hq i
      rw [F.chart_param hwb] at h
      simpa using h
  rintro x ⟨hxA, hxW⟩
  have hxW' := F.mem_nbhd_iff.mp hxW
  obtain ⟨u, hu⟩ : ∃ u, coordinateInclusion n j u =
      F.Φ.toFun ((complexChartAt (n := n) y).val x) :=
    ⟨_, coordinateInclusion_coordinateProjection ((F.mem_iff_of_mem_nbhd hxW).mp hxA)⟩
  have hNx : (complexChartAt (n := n) y).val x ∈ P.coordinateNeighborhood := by
    have h := hN _ hxW'.2.2
    rwa [F.Φ.left_inv _ hxW'.2.1] at h
  refine (P.zeroLocus hxW'.1 hNx).mpr fun i => ?_
  have huD : u ∈ coordinateInclusion n j ⁻¹' Metric.ball (0 : ComplexModel n) F.radius := by
    change coordinateInclusion n j u ∈ Metric.ball (0 : ComplexModel n) F.radius
    rw [hu]
    exact hxW'.2.2
  have h := hvanish i huD
  simp only [hu, F.Φ.left_inv _ hxW'.2.1, Pi.zero_apply] at h
  exact h

end FlatBall

omit [IsComplexManifold n M] in
/-- Every regular point carries flattened balls whose inverse images lie in any prescribed
open coordinate neighbourhood. -/
theorem exists_flatBall {A : Set M} {x : M} {j : ℕ} (hx : RegularAtDim (n := n) A x j)
    {N : Set (ComplexModel n)} (hN : IsOpen N)
    (hxN : (complexChartAt (n := n) x).val x ∈ N) :
    ∃ F : FlatBall (n := n) A x j,
      ∀ w ∈ Metric.ball (0 : ComplexModel n) F.radius, F.Φ.invFun w ∈ N := by
  obtain ⟨hk, -, Φ, hsub, hzero, hflat⟩ := hx
  have h0 : (0 : ComplexModel n) ∈ Φ.target := hzero ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = (complexChartAt (n := n) x).val x := by
    rw [← hzero, Φ.left_inv _ Φ.center_mem_source]
  have hT : IsOpen (Φ.target ∩ Φ.invFun ⁻¹' N) :=
    Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target hN
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hT 0
    ⟨h0, by rw [mem_preimage, hinv0]; exact hxN⟩
  exact ⟨⟨hk, Φ, hsub, hzero, hflat, r, hr, fun w hw => (hball hw).1⟩,
    fun w hw => (hball hw).2⟩

/-! ### Components -/

omit [IsComplexManifold n M] in
theorem regularPoints_subset (A : Set M) : regularPoints (n := n) A ⊆ A :=
  fun _ ⟨_, hx⟩ => hx.2.1

omit [IsComplexManifold n M] in
theorem component_subset_regularPoints (A : Set M) (c : M) :
    component (n := n) A c ⊆ regularPoints (n := n) A :=
  connectedComponentIn_subset _ _

omit [IsComplexManifold n M] in
theorem component_subset (A : Set M) (c : M) : component (n := n) A c ⊆ A :=
  (component_subset_regularPoints (n := n) A c).trans (regularPoints_subset (n := n) A)

omit [IsComplexManifold n M] in
theorem mem_component_self {A : Set M} {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k) :
    c ∈ component (n := n) A c :=
  mem_connectedComponentIn ⟨k, hc⟩

omit [IsComplexManifold n M] in
/-- A preconnected set of regular points meeting the component lies in it. -/
theorem subset_component_of_isPreconnected {A S : Set M} {c : M}
    (hS : IsPreconnected S) (hSR : S ⊆ regularPoints (n := n) A)
    (hne : (S ∩ component (n := n) A c).Nonempty) : S ⊆ component (n := n) A c := by
  obtain ⟨y, hyS, hyC⟩ := hne
  have h := hS.subset_connectedComponentIn hyS hSR
  rwa [← connectedComponentIn_eq hyC] at h

theorem FlatBall.inter_nbhd_subset_component {A : Set M} {c y : M} {j : ℕ}
    (F : FlatBall (n := n) A y j) (hy : y ∈ component (n := n) A c) :
    A ∩ F.nbhd ⊆ component (n := n) A c :=
  subset_component_of_isPreconnected F.isPreconnected_inter_nbhd
    (fun _ hx => ⟨j, F.regularAtDim_of_mem hx.1 hx.2⟩)
    ⟨y, ⟨component_subset (n := n) A c hy, F.mem_nbhd⟩, hy⟩

/-- Near a point of the component, `A` lies in the component, consists of regular points of
one dimension, and is relatively closed. -/
theorem exists_isOpen_inter_subset {A : Set M} {c y : M} {j : ℕ}
    (hy : y ∈ component (n := n) A c) (hyj : RegularAtDim (n := n) A y j) :
    ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ A ∩ W ⊆ component (n := n) A c ∧
      A ∩ W ⊆ regularLocus (n := n) A j ∧ W ∩ closure (A ∩ W) ⊆ A := by
  obtain ⟨F, -⟩ := exists_flatBall hyj (N := univ) isOpen_univ (mem_univ _)
  exact ⟨F.nbhd, F.isOpen_nbhd, F.mem_nbhd, F.inter_nbhd_subset_component hy,
    fun x hx => F.regularAtDim_of_mem hx.1 hx.2, F.nbhd_inter_closure_subset⟩

theorem exists_open_inter_subset_component {A : Set M} {c : M} {k : ℕ}
    (_hc : RegularAtDim (n := n) A c k) {y : M} (hy : y ∈ component (n := n) A c) :
    ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ A ∩ W ⊆ component (n := n) A c := by
  obtain ⟨j, hj⟩ := component_subset_regularPoints (n := n) A c hy
  obtain ⟨W, hW, hyW, hWC, -, -⟩ := exists_isOpen_inter_subset hy hj
  exact ⟨W, hW, hyW, hWC⟩

theorem regularAtDim_of_mem_component {A : Set M} {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) {y : M} (hy : y ∈ component (n := n) A c) :
    RegularAtDim (n := n) A y k := by
  have hdim : ∀ x ∈ component (n := n) A c, ∃ j W, IsOpen W ∧ x ∈ W ∧
      A ∩ W ⊆ regularLocus (n := n) A j := by
    intro x hx
    obtain ⟨j, hj⟩ := component_subset_regularPoints (n := n) A c hx
    obtain ⟨W, hW, hxW, -, hWj, -⟩ := exists_isOpen_inter_subset hx hj
    exact ⟨j, W, hW, hxW, hWj⟩
  let u := ⋃₀ {W : Set M | IsOpen W ∧ A ∩ W ⊆ regularLocus (n := n) A k}
  let v := ⋃₀ {W : Set M | IsOpen W ∧ ∃ j, j ≠ k ∧ A ∩ W ⊆ regularLocus (n := n) A j}
  have hu : IsOpen u := isOpen_sUnion fun W hW => hW.1
  have hv : IsOpen v := isOpen_sUnion fun W hW => hW.1
  have hCuv : component (n := n) A c ⊆ u ∪ v := by
    intro x hx
    obtain ⟨j, W, hW, hxW, hWj⟩ := hdim x hx
    by_cases hjk : j = k
    · exact Or.inl (mem_sUnion.mpr ⟨W, ⟨hW, hjk ▸ hWj⟩, hxW⟩)
    · exact Or.inr (mem_sUnion.mpr ⟨W, ⟨hW, j, hjk, hWj⟩, hxW⟩)
  have hdisj : component (n := n) A c ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hxC, hxu, hxv⟩
    obtain ⟨W, ⟨-, hWk⟩, hxW⟩ := mem_sUnion.mp hxu
    obtain ⟨W', ⟨-, j, hjk, hW'j⟩, hxW'⟩ := mem_sUnion.mp hxv
    have hxA : x ∈ A := component_subset (n := n) A c hxC
    exact hjk (RegularPointDimension.eq_of_regularAtDim (hW'j ⟨hxA, hxW'⟩) (hWk ⟨hxA, hxW⟩))
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn u v hu hv
      hCuv hdisj with hCu | hCv
  · obtain ⟨W, ⟨-, hWk⟩, hyW⟩ := mem_sUnion.mp (hCu hy)
    exact hWk ⟨component_subset (n := n) A c hy, hyW⟩
  · exfalso
    obtain ⟨W', ⟨-, j, hjk, hW'j⟩, hcW'⟩ := mem_sUnion.mp (hCv (mem_component_self hc))
    exact hjk (RegularPointDimension.eq_of_regularAtDim (hW'j ⟨hc.2.1, hcW'⟩) hc)

theorem isComplexAnalyticSubset_closure_component {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (_hc : RegularAtDim (n := n) A c k) :
    IsComplexAnalyticSubset (n := n) (closure (component (n := n) A c)) := by
  classical
  have hCA := component_subset (n := n) A c
  intro p
  by_cases hp : p ∈ A
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hA.isClosed
      (closure_minimal hCA hA.isClosed) hp
  obtain ⟨D, ⟨G⟩⟩ := LocalStatementConnected.exists_connectedParts hA hp
  have hΩo : IsOpen (D.nbhd ∩ ⋂ i, G.core i) :=
    D.isOpen_nbhd.inter (isOpen_iInter_of_finite G.isOpen_core)
  have hpΩ : p ∈ D.nbhd ∩ ⋂ i, G.core i := ⟨D.mem_nbhd, mem_iInter.mpr G.mem_core⟩
  have hSopen : IsOpen (D.nbhd \ ⋃ i, ⋃ (_ : G.good i ⊆ component (n := n) A c), D.piece i) := by
    have h : D.nbhd \ ⋃ i, ⋃ (_ : G.good i ⊆ component (n := n) A c), D.piece i =
        D.nbhd ∩ ⋂ i, ⋂ (_ : G.good i ⊆ component (n := n) A c), (D.nbhd \ D.piece i) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion,
        not_exists]
      exact ⟨fun h => ⟨h.1, fun i hi => ⟨h.1, h.2 i hi⟩⟩,
        fun h => ⟨h.1, fun i hi => (h.2 i hi).2⟩⟩
    rw [h]
    exact D.isOpen_nbhd.inter (isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun _ => D.isOpen_nbhd_diff_piece i)
  have hgood : ∀ i, (G.good i ∩ component (n := n) A c).Nonempty →
      G.good i ⊆ component (n := n) A c := fun i hne =>
    subset_component_of_isPreconnected (G.isPreconnected_good i)
      (fun z hz => ⟨D.dim i, G.regularAtDim_of_mem_good i z hz⟩) hne
  have hCS : component (n := n) A c ∩ (D.nbhd ∩ ⋂ i, G.core i) ⊆
      closure (⋃ i, ⋃ (_ : G.good i ⊆ component (n := n) A c), D.piece i) := by
    rintro x ⟨hxC, hxΩ⟩
    obtain ⟨j, hj⟩ := component_subset_regularPoints (n := n) A c hxC
    obtain ⟨W, hW, hxW, hWC, -, -⟩ := exists_isOpen_inter_subset hxC hj
    refine mem_closure_iff.mpr fun O hO hxO => ?_
    obtain ⟨i, O', hO', hO'sub, ⟨w, hwO', hwA⟩, hO'i⟩ :=
      D.exists_isOpen_subset_piece ((hO.inter hΩo).inter hW) ⟨⟨hxO, hxΩ⟩, hxW⟩ (hCA hxC)
        hxΩ.1
    have hw := hO'sub hwO'
    have hwi : w ∈ D.piece i := hO'i ⟨hwO', hwA⟩
    have hwcore : w ∈ G.core i := mem_iInter.mp hw.1.2.2 i
    obtain ⟨g, hgO', hgi⟩ :=
      mem_closure_iff.mp (G.subset_closure_good i ⟨hwi, hwcore⟩) O' hO' hwO'
    have hgA : g ∈ A := (G.regularAtDim_of_mem_good i g hgi).2.1
    have hgC : g ∈ component (n := n) A c := hWC ⟨hgA, (hO'sub hgO').2⟩
    exact ⟨w, hw.1.1, mem_iUnion₂.mpr ⟨i, hgood i ⟨g, hgi, hgC⟩, hwi⟩⟩
  have heq : ∀ y ∈ D.nbhd ∩ ⋂ i, G.core i, y ∈ closure (component (n := n) A c) ↔
      y ∈ ⋃ i, ⋃ (_ : G.good i ⊆ component (n := n) A c), D.piece i := by
    intro y hyΩ
    constructor
    · intro hycl
      have h1 : y ∈ closure ((D.nbhd ∩ ⋂ i, G.core i) ∩ component (n := n) A c) :=
        hΩo.inter_closure ⟨hyΩ, hycl⟩
      have h2 := closure_minimal ((inter_comm _ _).subset.trans hCS) isClosed_closure h1
      by_contra hyS
      obtain ⟨z, hz, hzS⟩ := mem_closure_iff.mp h2 _ hSopen ⟨hyΩ.1, hyS⟩
      exact hz.2 hzS
    · intro hyS
      obtain ⟨i, hiC, hyi⟩ := mem_iUnion₂.mp hyS
      exact closure_mono hiC (G.subset_closure_good i ⟨hyi, mem_iInter.mp hyΩ.2 i⟩)
  refine ClosureDifferenceAnalytic.nonempty_presentation_of_eq_on_nhds hΩo hpΩ
    (fun z hz => D.nbhd_subset_source hz.1) D.eqnCount D.eqn
    (fun i j => (D.eqn_holomorphic i j).mono (image_mono inter_subset_left))
    (fun i => G.good i ⊆ component (n := n) A c) ?_
  intro y hy
  rw [heq y hy]
  simp only [mem_iUnion, exists_prop]
  exact exists_congr fun i => and_congr_right fun _ => D.mem_piece_iff i y hy.1

/-- **Identity theorem along the component.**  The union `V` of the open sets `O` with
`O ∩ C ⊆ B` is relatively closed in `C`. -/
theorem mem_openPart_of_mem_closure {A B : Set M} {c : M}
    (hB : IsComplexAnalyticSubset (n := n) B) {x : M} (hxC : x ∈ component (n := n) A c)
    (hx : x ∈ closure (component (n := n) A c ∩
      ⋃₀ {O : Set M | IsOpen O ∧ O ∩ component (n := n) A c ⊆ B})) :
    x ∈ ⋃₀ {O : Set M | IsOpen O ∧ O ∩ component (n := n) A c ⊆ B} := by
  obtain ⟨j, hj⟩ := component_subset_regularPoints (n := n) A c hxC
  obtain ⟨P⟩ := hB x
  obtain ⟨F, hN⟩ := exists_flatBall hj P.isOpen_coordinateNeighborhood
    P.center_mem_coordinateNeighborhood
  have hWC := F.inter_nbhd_subset_component hxC
  obtain ⟨z, hzW, hzC, hzV⟩ := mem_closure_iff.mp hx F.nbhd F.isOpen_nbhd F.mem_nbhd
  obtain ⟨O₀, ⟨hO₀, hO₀B⟩, hzO₀⟩ := mem_sUnion.mp hzV
  have hAW : A ∩ F.nbhd ⊆ B :=
    F.inter_nbhd_subset_of_isOpen P hN hO₀ ⟨z, hzO₀, component_subset (n := n) A c hzC, hzW⟩
      fun q hq => hO₀B ⟨hq.1, hWC hq.2⟩
  exact mem_sUnion.mpr ⟨F.nbhd, ⟨F.isOpen_nbhd,
    fun q hq => hAW ⟨component_subset (n := n) A c hq.2, hq.1⟩⟩, F.mem_nbhd⟩

/-- An analytic set containing a nonempty relatively open part of the component contains the
whole component. -/
theorem component_subset_of_isOpen {A B : Set M} {c : M}
    (hB : IsComplexAnalyticSubset (n := n) B) {O : Set M} (hO : IsOpen O)
    (hne : (O ∩ component (n := n) A c).Nonempty) (hOB : O ∩ component (n := n) A c ⊆ B) :
    component (n := n) A c ⊆ B := by
  let V := ⋃₀ {O : Set M | IsOpen O ∧ O ∩ component (n := n) A c ⊆ B}
  have hV : IsOpen V := isOpen_sUnion fun W hW => hW.1
  have hV' : IsOpen (closure (component (n := n) A c ∩ V))ᶜ := isClosed_closure.isOpen_compl
  have hcover : component (n := n) A c ⊆ V ∪ (closure (component (n := n) A c ∩ V))ᶜ := by
    intro x hxC
    by_cases hx : x ∈ closure (component (n := n) A c ∩ V)
    · exact Or.inl (mem_openPart_of_mem_closure hB hxC hx)
    · exact Or.inr hx
  have hdisj : component (n := n) A c ∩ (V ∩ (closure (component (n := n) A c ∩ V))ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hxC, hxV, hxcl⟩
    exact hxcl (subset_closure ⟨hxC, hxV⟩)
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn V _ hV hV'
      hcover hdisj with hCV | hCV
  · intro x hxC
    obtain ⟨W, ⟨-, hWB⟩, hxW⟩ := mem_sUnion.mp (hCV hxC)
    exact hWB ⟨hxW, hxC⟩
  · exfalso
    obtain ⟨z, hzO, hzC⟩ := hne
    have hzV : z ∈ V := mem_sUnion.mpr ⟨O, ⟨hO, hOB⟩, hzO⟩
    exact hCV hzC (subset_closure ⟨hzC, hzV⟩)

theorem isComplexAnalyticallyIrreducible_closure_component {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) :
    IsComplexAnalyticallyIrreducible (n := n) (closure (component (n := n) A c)) := by
  have hcC := mem_component_self hc
  refine ⟨isComplexAnalyticSubset_closure_component hA hc, ⟨c, subset_closure hcC⟩, ?_⟩
  intro B₁ B₂ hB₁ hB₂ hB₁C hB₂C hunion
  by_cases h₁ : ∃ O : Set M, IsOpen O ∧ (O ∩ component (n := n) A c).Nonempty ∧
      O ∩ component (n := n) A c ⊆ B₁
  · obtain ⟨O, hO, hne, hOB⟩ := h₁
    exact Or.inl (Subset.antisymm
      (closure_minimal (component_subset_of_isOpen hB₁ hO hne hOB) hB₁.isClosed) hB₁C)
  by_cases h₂ : ∃ O : Set M, IsOpen O ∧ (O ∩ component (n := n) A c).Nonempty ∧
      O ∩ component (n := n) A c ⊆ B₂
  · obtain ⟨O, hO, hne, hOB⟩ := h₂
    exact Or.inr (Subset.antisymm
      (closure_minimal (component_subset_of_isOpen hB₂ hO hne hOB) hB₂.isClosed) hB₂C)
  exfalso
  have hsub : B₂ᶜ ∩ component (n := n) A c ⊆ B₁ := by
    rintro z ⟨hz₂, hzC⟩
    have hz : z ∈ B₁ ∪ B₂ := hunion ▸ subset_closure hzC
    exact hz.resolve_right hz₂
  have hempty : ¬ (B₂ᶜ ∩ component (n := n) A c).Nonempty := fun hne =>
    h₁ ⟨B₂ᶜ, hB₂.isClosed.isOpen_compl, hne, hsub⟩
  have hC₂ : component (n := n) A c ⊆ B₂ := by
    intro z hzC
    by_contra hz₂
    exact hempty ⟨z, hz₂, hzC⟩
  exact h₂ ⟨univ, isOpen_univ, ⟨c, mem_univ c, hcC⟩, fun z hz => hC₂ hz.2⟩

theorem regularAtDim_closure_component {A : Set M} {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) {y : M} (hy : y ∈ component (n := n) A c) :
    RegularAtDim (n := n) (closure (component (n := n) A c)) y k := by
  have hyk := regularAtDim_of_mem_component hc hy
  obtain ⟨W, hW, hyW, hWC, -, hWcl⟩ := exists_isOpen_inter_subset hy hyk
  refine RegularPointDimension.regularAtDim_of_inter_eq hW hyW ?_ hyk
  apply Subset.antisymm
  · exact fun x hx => ⟨subset_closure (hWC hx), hx.2⟩
  · rintro x ⟨hxcl, hxW⟩
    have h1 : x ∈ closure (W ∩ component (n := n) A c) := hW.inter_closure ⟨hxW, hxcl⟩
    have h2 : W ∩ component (n := n) A c ⊆ A ∩ W :=
      fun z hz => ⟨component_subset (n := n) A c hz.2, hz.1⟩
    exact ⟨hWcl ⟨hxW, closure_mono h2 h1⟩, hxW⟩

end SGPT.Foundations.Analysis.Pending.RegularLocusComponent
