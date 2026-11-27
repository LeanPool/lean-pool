/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.SmoothDomain
public import LeanPool.FunctionSpaces.Domains.Traces.HalfSpaceTrace
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on the boundary of a compact manifold

Let `M` be a compact manifold with boundary modelled on the half-space `𝓡∂ n`. The boundary of
the half-space is the hyperplane `H₀ = {y : y_0 = 0}` (`Manifold.bdry`), and the changes of charts
map `H₀` into itself (`Manifold.coordChange_mem_bdry`): a point is mapped to the interior of the
half-space by one chart iff by every chart (Mathlib's
`ModelWithCorners.mem_interior_range_iff_of_mem_atlas`). Restricted to `H₀`, a change of charts
with a cut-off is a smooth change of variables with a cut-off on the whole hyperplane
(`Manifold.boundaryChartChange`).

The **boundary pieces** of `g : M → ℂ` are the restrictions of the chart pieces to `H₀`
(`Manifold.BesovAtlas.boundaryPiece`), and `g ∈ B^s_{p,q}(∂M)` if every boundary piece agrees
almost everywhere with a function of finite Besov quasi-norm on `H₀`
(`Manifold.BesovAtlas.MemBoundaryBesov`). This does not depend on the atlas
(`Manifold.BesovAtlas.memBoundaryBesov_iff_memBoundaryBesov`): the boundary pieces of two atlases
are related by the boundary changes of charts, which are bounded on `B^s_{p,q}(H₀)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

open ENNReal (lqNorm dyadicWeight)

namespace Manifold

variable {n : ℕ} [NeZero n]

/-! ### The boundary hyperplane -/

/-- The flat graph domain `{y : y_0 > 0}` of `ℝ^n`. -/
noncomputable abbrev flatDomain (n : ℕ) [NeZero n] :
    Rd.LipschitzGraph (EuclideanSpace ℝ (Fin n)) :=
  Rd.LipschitzGraph.flat Rd.e0 Rd.norm_e0

/-- The **boundary hyperplane** `H₀ = e₀^⊥ = {y : y_0 = 0}` of the half-space. -/
noncomputable abbrev bdry (n : ℕ) [NeZero n] : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (flatDomain n).hyperplane

/-- `y ∈ H₀ ↔ y_0 = 0`. -/
theorem mem_bdry_iff {y : EuclideanSpace ℝ (Fin n)} : y ∈ bdry n ↔ y 0 = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm,
    Rd.coord_zero_eq_inner]
  rfl

/-- The boundary hyperplane lies in the half-space. -/
theorem bdry_subset_range :
    ((bdry n : Set (EuclideanSpace ℝ (Fin n)))) ⊆ range (𝓡∂ n) := fun y hy => by
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact (mem_bdry_iff.1 hy).ge

/-- The projection onto `H₀` is the identity on `H₀`. -/
theorem coe_proj_of_mem_bdry {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ bdry n) :
    ((flatDomain n).proj y : EuclideanSpace ℝ (Fin n)) = y := by
  have h := (flatDomain n).proj_coe ⟨y, hy⟩
  rw [show ((⟨y, hy⟩ : bdry n) : EuclideanSpace ℝ (Fin n)) = y from rfl] at h
  rw [h]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]

omit [ChartedSpace (EuclideanHalfSpace n) M] in
/-- **Interior points of a chart target**: a point of the target of an extended chart lies in its
interior iff its first coordinate is positive. -/
theorem mem_interior_extend_target_iff {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (e.extend (𝓡∂ n)).target) :
    y ∈ interior (e.extend (𝓡∂ n)).target ↔ 0 < y 0 := by
  constructor
  · intro h
    have h1 := interior_mono e.extend_target_subset_range h
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h1
    exact h1
  · intro h
    rw [e.extend_target] at hy ⊢
    refine mem_interior.2 ⟨{w | 0 < w 0} ∩ (𝓡∂ n).symm ⁻¹' e.target, fun w hw => ⟨hw.2, ?_⟩,
      (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0))).inter
        ((𝓡∂ n).continuous_symm.isOpen_preimage _ e.open_target), h, hy.1⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact le_of_lt (show (0 : ℝ) < w 0 from hw.1)

/-- **Changes of charts preserve the boundary hyperplane**: if `y_0 = 0` in the source of the
change of charts from `e` to `e'`, the image has first coordinate `0`. -/
theorem coordChange_mem_bdry [IsManifold (𝓡∂ n) ∞ M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} (he : e ∈ atlas _ M)
    (he' : e' ∈ atlas _ M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ ((𝓡∂ n).extendCoordChange e e').source) (hyb : y ∈ bdry n) :
    (𝓡∂ n).extendCoordChange e e' y ∈ bdry n := by
  obtain ⟨hy1, hy2⟩ := (mem_coordChange_source e e').1 hy
  set x := (e.extend (𝓡∂ n)).symm y
  have hx : x ∈ e.source := by
    have := (e.extend (𝓡∂ n)).map_target hy1
    rwa [e.extend_source] at this
  have hxy : e.extend (𝓡∂ n) x = y := (e.extend (𝓡∂ n)).right_inv hy1
  have hx' : e'.extend (𝓡∂ n) x ∈ (e'.extend (𝓡∂ n)).target :=
    (e'.extend (𝓡∂ n)).map_source (by rwa [e'.extend_source])
  have hiff := (𝓡∂ n).mem_interior_range_iff_of_mem_atlas (n := ∞) (by simp) he he' hx hy2
  rw [hxy, mem_interior_extend_target_iff hy1, mem_interior_extend_target_iff hx'] at hiff
  have h0 : ¬ 0 < y 0 := by rw [mem_bdry_iff.1 hyb]; exact lt_irrefl 0
  have hge : 0 ≤ e'.extend (𝓡∂ n) x 0 := by
    have := (e'.extend_target_subset_range (I := 𝓡∂ n)) hx'
    rwa [range_modelWithCornersEuclideanHalfSpace] at this
  rw [coordChange_apply, mem_bdry_iff]
  exact le_antisymm (not_lt.1 fun h => h0 (hiff.2 h)) hge

/-! ### Changes of charts on the boundary -/

section BoundaryChange

variable [IsManifold (𝓡∂ n) ∞ M] [CompactSpace M]
  {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} (he : e ∈ atlas _ M)
  (he' : e' ∈ atlas _ M) (c : M → ℝ) (hc : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ c)
  (hcs : tsupport c ⊆ e.source ∩ e'.source)

omit [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [CompactSpace M] in
/-- A point of `H₀` lies in `range I ∩ U` iff it lies in the source of the change of charts. -/
theorem mem_coordChange_source_iff_of_bdry (x' : bdry n) :
    (x' : EuclideanSpace ℝ (Fin n)) ∈ (𝓡∂ n).symm ⁻¹' (e.symm ≫ₕ e').source ↔
      (x' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').source := by
  rw [← range_inter_coordChange_source]
  exact ⟨fun h => ⟨bdry_subset_range x'.2, h⟩, fun h => h.2⟩

omit [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [CompactSpace M] in
/-- A point of `H₀` lies in `range I ∩ U'` iff it lies in the target of the change of charts. -/
theorem mem_coordChange_target_iff_of_bdry (y' : bdry n) :
    (y' : EuclideanSpace ℝ (Fin n)) ∈ (𝓡∂ n).symm ⁻¹' (e.symm ≫ₕ e').target ↔
      (y' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').target := by
  rw [← range_inter_coordChange_target]
  exact ⟨fun h => ⟨bdry_subset_range y'.2, h⟩, fun h => h.2⟩

omit [CompactSpace M] in
include he he' in
/-- The change of charts maps the boundary part of its source into `H₀`. -/
theorem coe_proj_coordChange {x' : bdry n}
    (hx : (x' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').source) :
    ((flatDomain n).proj ((𝓡∂ n).extendCoordChange e e' x') : EuclideanSpace ℝ (Fin n)) =
      (𝓡∂ n).extendCoordChange e e' x' :=
  coe_proj_of_mem_bdry (coordChange_mem_bdry he he' hx x'.2)

omit [CompactSpace M] in
include he he' in
/-- The inverse change of charts maps the boundary part of its target into `H₀`. -/
theorem coe_proj_coordChange_symm {y' : bdry n}
    (hy : (y' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').target) :
    ((flatDomain n).proj (((𝓡∂ n).extendCoordChange e e').symm y') :
      EuclideanSpace ℝ (Fin n)) = ((𝓡∂ n).extendCoordChange e e').symm y' := by
  have hy' : (y' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e' e).source := hy
  exact coe_proj_coordChange he' he hy'

/-- The boundary hyperplane is closed. -/
theorem isClosed_bdry : IsClosed ((bdry n : Set (EuclideanSpace ℝ (Fin n)))) :=
  Submodule.isClosed_of_finiteDimensional _

/-- The **boundary change of charts with a cut-off**: the restriction of the change of charts with
a cut-off to the boundary hyperplane `H₀`, a smooth change of variables with a cut-off on all of
`H₀`. -/
noncomputable def boundaryChartChange : Rd.CutoffDiffeo (Set.univ : Set (bdry n)) where
  U := (fun x' : bdry n => (x' : EuclideanSpace ℝ (Fin n))) ⁻¹'
    ((𝓡∂ n).symm ⁻¹' (e.symm ≫ₕ e').source)
  U' := (fun y' : bdry n => (y' : EuclideanSpace ℝ (Fin n))) ⁻¹'
    ((𝓡∂ n).symm ⁻¹' (e.symm ≫ₕ e').target)
  isOpen_U := (BesovAtlas.chartChange he he' c hc hcs).isOpen_U.preimage continuous_subtype_val
  isOpen_U' := (BesovAtlas.chartChange he he' c hc hcs).isOpen_U'.preimage continuous_subtype_val
  Phi x' := (flatDomain n).proj ((𝓡∂ n).extendCoordChange e e' x')
  Psi y' := (flatDomain n).proj (((𝓡∂ n).extendCoordChange e e').symm y')
  chi y' := (BesovAtlas.chartChange he he' c hc hcs).chi y'
  K0 := (fun y' : bdry n => (y' : EuclideanSpace ℝ (Fin n))) ⁻¹'
    (BesovAtlas.chartChange he he' c hc hcs).K0
  contDiffOn_Phi := by
    refine (flatDomain n).proj.contDiff.comp_contDiffOn
      ((BesovAtlas.chartChange he he' c hc hcs).contDiffOn_Phi.comp
        (bdry n).subtypeL.contDiff.contDiffOn fun x' hx' => ?_)
    exact ⟨bdry_subset_range x'.2, hx'.2⟩
  contDiffOn_Psi := by
    refine (flatDomain n).proj.contDiff.comp_contDiffOn
      ((BesovAtlas.chartChange he he' c hc hcs).contDiffOn_Psi.comp
        (bdry n).subtypeL.contDiff.contDiffOn fun y' hy' => ?_)
    exact ⟨bdry_subset_range y'.2, hy'.2⟩
  contDiffOn_chi := by
    refine (BesovAtlas.chartChange he he' c hc hcs).contDiffOn_chi.comp
      (bdry n).subtypeL.contDiff.contDiffOn fun y' hy' => ?_
    exact ⟨bdry_subset_range y'.2, hy'.2⟩
  mapsTo_Phi x' hx' := by
    have hx : (x' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').source :=
      (mem_coordChange_source_iff_of_bdry x').1 hx'.2
    refine ⟨mem_univ _, ?_⟩
    change (((flatDomain n).proj ((𝓡∂ n).extendCoordChange e e' x') : bdry n) :
      EuclideanSpace ℝ (Fin n)) ∈ (𝓡∂ n).symm ⁻¹' (e.symm ≫ₕ e').target
    rw [coe_proj_coordChange he he' hx]
    have := (BesovAtlas.chartChange he he' c hc hcs).mapsTo_Phi ⟨bdry_subset_range x'.2, hx'.2⟩
    exact this.2
  mapsTo_Psi y' hy' := by
    have hy : (y' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').target :=
      (mem_coordChange_target_iff_of_bdry y').1 hy'.2
    refine ⟨mem_univ _, ?_⟩
    change (((flatDomain n).proj (((𝓡∂ n).extendCoordChange e e').symm y') : bdry n) :
      EuclideanSpace ℝ (Fin n)) ∈ (𝓡∂ n).symm ⁻¹' (e.symm ≫ₕ e').source
    rw [coe_proj_coordChange_symm he he' hy]
    have := (BesovAtlas.chartChange he he' c hc hcs).mapsTo_Psi ⟨bdry_subset_range y'.2, hy'.2⟩
    exact this.2
  left_inv x' hx' := by
    have hx : (x' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').source :=
      (mem_coordChange_source_iff_of_bdry x').1 hx'.2
    apply Subtype.ext
    have h1 := coe_proj_coordChange he he' hx
    have hmem : ((𝓡∂ n).extendCoordChange e e' x') ∈ ((𝓡∂ n).extendCoordChange e e').target :=
      ((𝓡∂ n).extendCoordChange e e').map_source hx
    have h2 := coe_proj_coordChange_symm he he'
      (y' := (flatDomain n).proj ((𝓡∂ n).extendCoordChange e e' x')) (by rw [h1]; exact hmem)
    change (((flatDomain n).proj (((𝓡∂ n).extendCoordChange e e').symm
      (((flatDomain n).proj ((𝓡∂ n).extendCoordChange e e' x') : bdry n) :
        EuclideanSpace ℝ (Fin n))) : bdry n) : EuclideanSpace ℝ (Fin n)) = x'
    rw [h2, h1, ((𝓡∂ n).extendCoordChange e e').left_inv hx]
  right_inv y' hy' := by
    have hy : (y' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').target :=
      (mem_coordChange_target_iff_of_bdry y').1 hy'.2
    apply Subtype.ext
    have h1 := coe_proj_coordChange_symm he he' hy
    have hmem : ((𝓡∂ n).extendCoordChange e e').symm y' ∈
        ((𝓡∂ n).extendCoordChange e e').source :=
      ((𝓡∂ n).extendCoordChange e e').map_target hy
    have h2 := coe_proj_coordChange he he'
      (x' := (flatDomain n).proj (((𝓡∂ n).extendCoordChange e e').symm y')) (by rw [h1]; exact hmem)
    change (((flatDomain n).proj ((𝓡∂ n).extendCoordChange e e'
      (((flatDomain n).proj (((𝓡∂ n).extendCoordChange e e').symm y') : bdry n) :
        EuclideanSpace ℝ (Fin n))) : bdry n) : EuclideanSpace ℝ (Fin n)) = y'
    rw [h2, h1, ((𝓡∂ n).extendCoordChange e e').right_inv hy]
  isCompact_K0 :=
    (isClosed_bdry.isClosedEmbedding_subtypeVal).isCompact_preimage
      (BesovAtlas.chartChange he he' c hc hcs).isCompact_K0
  K0_subset y' hy' := by
    have h := (BesovAtlas.chartChange he he' c hc hcs).K0_subset hy'
    exact ⟨mem_univ _, h.2⟩
  chi_eq_zero y' _ hy' :=
    (BesovAtlas.chartChange he he' c hc hcs).chi_eq_zero _ (bdry_subset_range y'.2) hy'

/-- **The change of charts on the boundary**: on `H₀`, the change of charts with a cut-off acts as
its restriction to `H₀`. -/
theorem chartChange_apply_coe (G : EuclideanSpace ℝ (Fin n) → ℂ) (x' : bdry n) :
    (BesovAtlas.chartChange he he' c hc hcs).apply G x' =
      (boundaryChartChange he he' c hc hcs).apply (fun y' => G y') x' := by
  by_cases hx : (x' : EuclideanSpace ℝ (Fin n)) ∈ ((𝓡∂ n).extendCoordChange e e').source
  · rw [BesovAtlas.chartChange_apply, indicator_of_mem hx, Rd.CutoffDiffeo.apply,
      indicator_of_mem]
    swap
    · exact ⟨mem_univ _, (mem_coordChange_source_iff_of_bdry x').2 hx⟩
    change _ = (BesovAtlas.chartChange he he' c hc hcs).chi
      (((flatDomain n).proj ((𝓡∂ n).extendCoordChange e e' x') : bdry n) :
        EuclideanSpace ℝ (Fin n)) * G (((flatDomain n).proj
          ((𝓡∂ n).extendCoordChange e e' x') : bdry n) : EuclideanSpace ℝ (Fin n))
    rw [coe_proj_coordChange he he' hx]
  · rw [BesovAtlas.chartChange_apply, indicator_of_notMem hx, Rd.CutoffDiffeo.apply,
      indicator_of_notMem fun h : x' ∈ univ ∩ (boundaryChartChange he he' c hc hcs).U =>
        hx ((mem_coordChange_source_iff_of_bdry x').1 h.2)]

end BoundaryChange

/-! ### Boundary pieces and the Besov space of the boundary -/

namespace BesovAtlas

variable (A : BesovAtlas (𝓡∂ n) M)

/-- The **boundary pieces** of `g : M → ℂ`: the restrictions of the chart pieces to `H₀`. -/
noncomputable def boundaryPiece (i : Fin A.n) (g : M → ℂ) : bdry n → ℂ :=
  fun x' => A.piece i g x'

variable [IsManifold (𝓡∂ n) ∞ M] [CompactSpace M] (A' : BesovAtlas (𝓡∂ n) M)

/-- The **boundary change of charts** from the `i`-th chart of `A` to the `j`-th chart of `A'`. -/
noncomputable def boundaryTransition (i : Fin A.n) (j : Fin A'.n) :
    Rd.CutoffDiffeo (Set.univ : Set (bdry n)) :=
  boundaryChartChange (A.chart_mem i) (A'.chart_mem j) (fun x => A.psi i x * A'.theta j x)
    ((A.contMDiff_psi i).mul (A'.contMDiff_theta j)) (A.tsupport_psi_mul_theta_subset A' i j)

/-- **The boundary pieces of two atlases**: `∂piece_i g = ∑_j T^∂_{ij}(∂piece'_j g)`. -/
theorem boundaryPiece_eq_sum (i : Fin A.n) (g : M → ℂ) (x' : bdry n) :
    A.boundaryPiece i g x' =
      ∑ j, (A.boundaryTransition A' i j).apply (A'.boundaryPiece j g) x' := by
  rw [boundaryPiece, A.piece_eq_sum_apply A' i g x']
  exact Finset.sum_congr rfl fun j _ => chartChange_apply_coe _ _ _ _ _ _ x'

/-- The **Besov space of the boundary** for a Besov atlas: `g : M → ℂ` whose boundary pieces agree
almost everywhere with functions on `H₀` of finite Besov quasi-norm of order `⌊s⌋ + 1`. -/
def MemBoundaryBesov (p : ℝ≥0∞) [Fact (1 ≤ p)] (s : ℝ) (q : ℝ≥0∞) (g : M → ℂ) : Prop :=
  ∀ i, ∃ G : Lp ℂ p (volume : Measure (bdry n)), (G : bdry n → ℂ) =ᵐ[volume] A.boundaryPiece i g ∧
    ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p (⌊s⌋₊ + 1) G k) < ⊤

/-- The whole hyperplane has nonempty interior in itself. -/
theorem interior_univ_bdry_nonempty : (interior (Set.univ : Set (bdry n))).Nonempty := by
  rw [interior_univ]
  exact univ_nonempty

/-- **The Besov space of the boundary does not depend on the atlas**: the boundary pieces of `A`
are sums of boundary changes of charts of those of `A'`, which are bounded on `B^s_{p,q}(H₀)`. -/
theorem MemBoundaryBesov.of_atlas {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {g : M → ℂ} (h : A'.MemBoundaryBesov p s q g) :
    A.MemBoundaryBesov p s q g := by
  intro i
  choose G' hG'ae hG'fin using h
  set r := ⌊s⌋₊ + 1
  have hr : 1 ≤ r := Nat.le_add_left 1 _
  have hsr : s < r := by
    push_cast [r]
    exact Nat.lt_floor_add_one s
  set T := fun j => A.boundaryTransition A' i j
  choose C hC hT using fun j => (T j).modNormOn_applyLp_le convex_univ
    interior_univ_bdry_nonempty MeasurableSet.univ hp hr hs hsr hq
  refine ⟨∑ j, (T j).applyLp convex_univ interior_univ_bdry_nonempty MeasurableSet.univ hp (G' j),
    ?_, ?_⟩
  · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => (T j).applyLp convex_univ
      interior_univ_bdry_nonempty MeasurableSet.univ hp (G' j)),
      ae_all_iff.2 fun j => ((T j).applyLp_ae convex_univ interior_univ_bdry_nonempty
        MeasurableSet.univ hp (G' j)).trans ((T j).apply_ae_eq ((hG'ae j).mono fun y hy _ => hy))]
      with x' h1 h2
    rw [h1, A.boundaryPiece_eq_sum A' i g x']
    exact Finset.sum_congr rfl fun j _ => h2 j
  · rw [← Rd.modNormOn_univ]
    refine (Rd.modNormOn_finsetSum_le MeasurableSet.univ r s hq _ _).trans_lt
      (ENNReal.sum_lt_top.2 fun j _ => ?_)
    exact (hT j (G' j)).trans_lt (ENNReal.mul_lt_top (hC j).lt_top (hG'fin j))

/-- **The Besov space of the boundary does not depend on the atlas**. -/
theorem memBoundaryBesov_iff_memBoundaryBesov {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {s : ℝ}
    (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) (g : M → ℂ) :
    A.MemBoundaryBesov p s q g ↔ A'.MemBoundaryBesov p s q g :=
  ⟨fun h => MemBoundaryBesov.of_atlas A' A hp hs hq h,
    fun h => MemBoundaryBesov.of_atlas A A' hp hs hq h⟩

end BesovAtlas

end Manifold
