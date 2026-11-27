/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.SmoothMeasure
public import LeanPool.FunctionSpaces.Domains.Lipschitz.HalfSpace
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Algebra.Order.Chebyshev

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov atlases

A **Besov atlas** of a manifold `M` (`Manifold.BesovAtlas`) consists of finitely many charts
`e_i` of the atlas, a smooth partition of unity `(ψ_i)` with `tsupport ψ_i ⊆ e_i.source`, and
smooth cut-offs `θ_i` with `θ_i = 1` on `tsupport ψ_i` and `tsupport θ_i ⊆ e_i.source`. Every
compact manifold has one (`Manifold.BesovAtlas.nonempty`): finitely many chart sources cover `M`,
Mathlib's smooth partitions of unity are subordinate to them
(`SmoothPartitionOfUnity.exists_isSubordinate`), and smooth cut-offs exist for every compact set
inside an open set (`Manifold.exists_contMDiff_eq_one_tsupport_subset`).

The squares of the partition of unity satisfy `∑_i ψ_i² ≥ 1/N` for `N` charts
(`Manifold.BesovAtlas.inv_card_le_sum_sq_psi`). The **chart piece** `(ψ_i g) ∘ κ_i⁻¹` vanishes
outside the carrier `κ_i(tsupport ψ_i)`, compact on a compact manifold
(`Manifold.BesovAtlas.isCompact_pieceCarrier`, `Manifold.BesovAtlas.piece_eq_zero_of_notMem`), and
is continuous on `range I` for continuous `g` (`Manifold.BesovAtlas.continuousOn_piece`).

A smooth function on `M` read in an extended chart is smooth within the target of the chart
(`Manifold.contDiffOn_comp_extend_symm`). Conversely, a function `F` on `E` gives the **lift from
a chart** `θ · F ∘ κ` on `M` (`Manifold.chartLift`). It is linear in `F`, depends only on the
class of `F` (`Manifold.chartLift_ae_eq`), is bounded from `L_p(E)` to `L_p(μ)`
(`Manifold.exists_eLpNorm_chartLift_le`, `Manifold.memLp_chartLift`), and its pieces are the images
of `F` under the changes of charts (`Manifold.BesovAtlas.piece_chartLift`).

A change of charts `κ' ∘ κ⁻¹` has a measurable source (`Manifold.measurableSet_coordChange_source`)
and maps the part of a set `B` inside its source onto the points `y` of the target of `κ'` with
`κ'⁻¹ y ∈ e.source` and `κ(κ'⁻¹ y) ∈ B` (`Manifold.image_coordChange_inter`).

The change of charts `T_{ij}` acts at `y = κ_i x` with `x` in the source of `κ'_j` by
`T_{ij} G (y) = ψ_i(x) θ'_j(x) G(κ'_j x)` and vanishes at other points
(`Manifold.BesovAtlas.transition_apply_of_mem`, `Manifold.BesovAtlas.transition_apply_of_notMem`).
The pieces of one atlas are sums of the pieces of another transported by the changes of charts
(`Manifold.BesovAtlas.pieceLp_eq_sum`) for every real model `I` whose range is a Besov domain: the
half-space, `E`, and the quadrant of manifolds with corners
(`Rd.BesovDomain.range_euclideanQuadrant` in `FunctionSpaces.Domains.Lipschitz.BesovDomains`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A **Besov atlas**: finitely many charts of the atlas, a smooth partition of unity `(ψ_i)`
subordinate to their sources, and smooth cut-offs `θ_i` with `θ_i = 1` on `tsupport ψ_i` and
`tsupport θ_i` inside the source of the `i`-th chart. -/
structure BesovAtlas where
  /-- The number of charts. -/
  n : ℕ
  /-- The charts. -/
  chart : Fin n → OpenPartialHomeomorph M H
  chart_mem : ∀ i, chart i ∈ atlas H M
  /-- The partition of unity. -/
  psi : Fin n → M → ℝ
  contMDiff_psi : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (psi i)
  nonneg_psi : ∀ i x, 0 ≤ psi i x
  tsupport_psi_subset : ∀ i, tsupport (psi i) ⊆ (chart i).source
  sum_psi : ∀ x, ∑ i, psi i x = 1
  /-- The cut-offs. -/
  theta : Fin n → M → ℝ
  contMDiff_theta : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (theta i)
  theta_eq_one : ∀ i, ∀ x ∈ tsupport (psi i), theta i x = 1
  tsupport_theta_subset : ∀ i, tsupport (theta i) ⊆ (chart i).source

variable {M} in
/-- **Smooth cut-offs**: for a compact set `K` inside an open set `U` of a σ-compact Hausdorff
manifold there is a smooth `θ : M → ℝ` with `θ = 1` on `K` and `tsupport θ ⊆ U`: Mathlib's
smooth function with support an open `V` and equal to `1` exactly on `K`
(`exists_contMDiff_support_eq_eq_one_iff`), for `K ⊆ V` and `closure V ⊆ U`
(`exists_open_between_and_isCompact_closure`). -/
theorem exists_contMDiff_eq_one_tsupport_subset [T2Space M] [SigmaCompactSpace M]
    [IsManifold I ∞ M] {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ (∀ x ∈ K, θ x = 1) ∧ tsupport θ ⊆ U := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨V, hVo, hKV, hVU, -⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨θ, hθ, -, hsupp, h1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff I (n := ⊤) hVo hK.isClosed hKV
  exact ⟨θ, hθ, fun x hx => (h1 x).1 hx, by rw [tsupport, hsupp]; exact hVU⟩

/-- **Every compact manifold has a Besov atlas**: finitely many chart sources cover `M`, a smooth
partition of unity is subordinate to them, and the cut-off `θ_i` is a smooth function equal to
`1` on `tsupport ψ_i` with `tsupport θ_i ⊆ e_i.source`
(`Manifold.exists_contMDiff_eq_one_tsupport_subset`). -/
theorem BesovAtlas.nonempty [CompactSpace M] [T2Space M] [IsManifold I ∞ M] :
    Nonempty (BesovAtlas I M) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source) (fun x _ => mem_iUnion.2 ⟨x, mem_chart_source H x⟩)
  set pt : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  have hcover : (univ : Set M) ⊆ ⋃ i, (chartAt H (pt i)).source := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
    refine mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simpa [pt] using hxy
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i => (chartAt H (pt i)).source) (fun i => (chartAt H (pt i)).open_source) hcover
  have hθ : ∀ i, ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ (∀ x ∈ tsupport (f i), θ x = 1) ∧
      tsupport θ ⊆ (chartAt H (pt i)).source := fun i =>
    exists_contMDiff_eq_one_tsupport_subset I (isClosed_tsupport _).isCompact
      (chartAt H (pt i)).open_source (hf i)
  choose θ hθs hθ1 hθsub using hθ
  exact ⟨{ n := t.card
           chart := fun i => chartAt H (pt i)
           chart_mem := fun i => chart_mem_atlas H _
           psi := fun i => f i
           contMDiff_psi := fun i => (f i).contMDiff
           nonneg_psi := fun i x => f.nonneg i x
           tsupport_psi_subset := hf
           sum_psi := fun x => by
             have h := f.sum_eq_one (mem_univ x)
             rwa [finsum_eq_sum_of_fintype] at h
           theta := θ
           contMDiff_theta := hθs
           theta_eq_one := hθ1
           tsupport_theta_subset := hθsub }⟩

variable {I M}

omit [FiniteDimensional ℝ E] in
/-- **Smooth functions in a chart**: for a chart `e` of the atlas and a smooth `g : M → ℝ`,
`g ∘ κ⁻¹` is smooth within the target of the extended chart `κ = e.extend I`. -/
theorem contDiffOn_comp_extend_symm [IsManifold I ∞ M] {e : OpenPartialHomeomorph M H}
    (he : e ∈ atlas H M) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) :
    ContDiffOn ℝ ∞ (g ∘ (e.extend I).symm) (e.extend I).target := by
  have h := (contMDiffOn_iff_of_mem_maximalAtlas' (IsManifold.subset_maximalAtlas he)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (0 : ℝ)) subset_rfl
    (fun x _ => by simp [chartAt_self_eq])).1 hg.contMDiffOn
  rw [← e.extend_target_eq_image_source] at h
  simpa [chartAt_self_eq, Function.comp_def] using h

/-! ### Changes of charts -/

section CoordChange

omit [FiniteDimensional ℝ E] [ChartedSpace H M]

variable (e e' : OpenPartialHomeomorph M H)

/-- The source of the change of charts is the relatively open set `range I ∩ U`. -/
theorem range_inter_coordChange_source :
    range I ∩ I.symm ⁻¹' (e.symm ≫ₕ e').source = (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source, I.image_eq, inter_comm]

/-- The target of the change of charts is the relatively open set `range I ∩ U'`. -/
theorem range_inter_coordChange_target :
    range I ∩ I.symm ⁻¹' (e.symm ≫ₕ e').target = (I.extendCoordChange e e').target := by
  rw [I.extendCoordChange_target, I.image_eq, inter_comm]

/-- `y` lies in the source of the change of charts iff it lies in the target of `e.extend I`
and its preimage lies in the source of `e'`. -/
theorem mem_coordChange_source {y : E} :
    y ∈ (I.extendCoordChange e e').source ↔
      y ∈ (e.extend I).target ∧ (e.extend I).symm y ∈ e'.source := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
    e'.extend_source]
  rfl

/-- The target of the change of charts is the image of `e.source ∩ e'.source` under
`e'.extend I`. -/
theorem coordChange_target_eq_image :
    (I.extendCoordChange e e').target = e'.extend I '' (e'.source ∩ e.source) := by
  rw [← PartialEquiv.symm_source, ModelWithCorners.extendCoordChange_symm,
    OpenPartialHomeomorph.extend_image_source_inter]

/-- The change of charts is `e'.extend I ∘ (e.extend I).symm`. -/
theorem coordChange_apply (y : E) :
    I.extendCoordChange e e' y = e'.extend I ((e.extend I).symm y) := rfl

/-- **The image of a set under a change of charts**: for charts `e`, `e'` with extended charts
`κ`, `κ'` and the change of charts `Φ = κ' ∘ κ⁻¹`, the image of `B ∩ source Φ` under `Φ` is the set
of points `y` of the target of `κ'` with `κ'⁻¹ y ∈ e.source` and `κ(κ'⁻¹ y) ∈ B` (Mathlib's
`PartialEquiv.image_source_inter_eq'`, with `Φ⁻¹` the change of charts from `e'` to `e`). -/
theorem image_coordChange_inter (B : Set E) :
    I.extendCoordChange e e' '' (B ∩ (I.extendCoordChange e e').source) =
      (e'.extend I).target ∩ (e'.extend I).symm ⁻¹' (e.source ∩ e.extend I ⁻¹' B) := by
  rw [inter_comm, PartialEquiv.image_source_inter_eq', ← (I.extendCoordChange e e').symm_source,
    ModelWithCorners.extendCoordChange_symm]
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_coordChange_source, coordChange_apply, and_assoc]

/-- The source of a change of charts is measurable: it is the intersection of the closed range
of `I` with an open set (`Manifold.range_inter_coordChange_source`). -/
theorem measurableSet_coordChange_source [MeasurableSpace E] [BorelSpace E] :
    MeasurableSet (I.extendCoordChange e e').source := by
  rw [← range_inter_coordChange_source]
  exact I.isClosed_range.measurableSet.inter
    (I.continuous_symm.isOpen_preimage _ (OpenPartialHomeomorph.open_source _)).measurableSet

end CoordChange

namespace BesovAtlas

variable (A : BesovAtlas I M)

/-- The extended chart `κ_i = e_i.extend I`. -/
noncomputable abbrev ext (i : Fin A.n) : PartialEquiv M E := (A.chart i).extend I

omit [FiniteDimensional ℝ E] in
/-- `ψ_i ≤ 1`. -/
theorem psi_le_one (i : Fin A.n) (x : M) : A.psi i x ≤ 1 := by
  rw [← A.sum_psi x]
  exact Finset.single_le_sum (fun j _ => A.nonneg_psi j x) (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] in
/-- `θ_i ψ_i = ψ_i`, since `θ_i = 1` on `tsupport ψ_i`. -/
theorem theta_mul_psi (i : Fin A.n) (x : M) : A.theta i x * A.psi i x = A.psi i x := by
  by_cases hx : x ∈ tsupport (A.psi i)
  · rw [A.theta_eq_one i x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

omit [FiniteDimensional ℝ E] in
/-- **The squares of the partition of unity are bounded below**: `∑_i ψ_i(x)² ≥ 1/N` at every
point `x`, for the `N` charts of the atlas, since `1 = (∑_i ψ_i(x))² ≤ N ∑_i ψ_i(x)²` by the
Cauchy–Schwarz inequality (Mathlib's `sq_sum_le_card_mul_sum_sq`). This bounds the weights
of the principal part `∑_i (ψ_i ∘ κ_i⁻¹)² |∇(u ∘ κ_i⁻¹)|²` of the chart form from below. -/
theorem inv_card_le_sum_sq_psi (x : M) : (A.n : ℝ)⁻¹ ≤ ∑ i, A.psi i x ^ 2 := by
  have h : (∑ i, A.psi i x) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, A.psi i x ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [A.sum_psi x, one_pow, Finset.card_univ, Fintype.card_fin] at h
  have hn : (A.n : ℝ) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact absurd h (by norm_num)
  exact (inv_le_iff_one_le_mul₀' ((Nat.cast_nonneg _).lt_of_ne (Ne.symm hn))).2 h

/-- The **chart piece** `(ψ_i g) ∘ κ_i⁻¹` on the target of `κ_i`, `0` outside. -/
noncomputable def piece (i : Fin A.n) (g : M → ℂ) : E → ℂ :=
  (A.ext i).target.indicator fun y => (A.psi i ((A.ext i).symm y) : ℂ) * g ((A.ext i).symm y)

/-- **The carrier of the `i`-th piece**: the set `κ_i(tsupport ψ_i) ⊆ range I`, outside which
the piece `(ψ_i g) ∘ κ_i⁻¹` vanishes; it is compact on a compact manifold. -/
noncomputable def pieceCarrier (i : Fin A.n) : Set E :=
  A.ext i '' tsupport (A.psi i)

omit [FiniteDimensional ℝ E] in
/-- The carrier of a piece is compact, the image of the compact `tsupport ψ_i` under the chart. -/
theorem isCompact_pieceCarrier [CompactSpace M] (i : Fin A.n) : IsCompact (A.pieceCarrier i) :=
  (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart i).continuousOn_extend.mono
    (by rw [OpenPartialHomeomorph.extend_source]; exact A.tsupport_psi_subset i))

omit [FiniteDimensional ℝ E] in
/-- The carrier of a piece lies in `range I`, since the extended charts take values there. -/
theorem pieceCarrier_subset_range (i : Fin A.n) : A.pieceCarrier i ⊆ range I := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨A.chart i x, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **The piece vanishes off its carrier** (pointwise): `piece_i g (y) = 0` for
`y ∉ κ_i(tsupport ψ_i)`. -/
theorem piece_eq_zero_of_notMem (i : Fin A.n) (g : M → ℂ) {y : E} (hy : y ∉ A.pieceCarrier i) :
    A.piece i g y = 0 := by
  by_cases hyt : y ∈ (A.ext i).target
  · have hψ : A.psi i ((A.ext i).symm y) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, (A.ext i).right_inv hyt⟩
    rw [piece, indicator_of_mem hyt, hψ, Complex.ofReal_zero, zero_mul]
  · rw [piece, indicator_of_notMem hyt]

omit [FiniteDimensional ℝ E] in
/-- **Pieces of continuous functions are continuous on the model range**: on a compact manifold,
for continuous `g : M → ℂ` the piece `(ψ_i g) ∘ κ_i⁻¹`, extended by `0`, is continuous on
`range I`. Near a point of the carrier it is `(ψ_i g) ∘ κ_i⁻¹` on the target of the extended
chart, a neighbourhood within `range I` (Mathlib's
`OpenPartialHomeomorph.extend_target_mem_nhdsWithin`); off the compact carrier it vanishes
(`Manifold.BesovAtlas.piece_eq_zero_of_notMem`). -/
theorem continuousOn_piece [CompactSpace M] (i : Fin A.n) {g : M → ℂ} (hg : Continuous g) :
    ContinuousOn (A.piece i g) (range I) := by
  intro y _
  by_cases hyK : y ∈ A.pieceCarrier i
  · obtain ⟨x, hx, rfl⟩ := hyK
    have hxs : x ∈ (A.chart i).source := A.tsupport_psi_subset i hx
    have hU := (A.chart i).extend_target_mem_nhdsWithin (I := I) hxs
    have hyt : A.ext i x ∈ (A.ext i).target :=
      (A.ext i).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hxs)
    have hcont : ContinuousOn (fun y => (A.psi i ((A.ext i).symm y) : ℂ) * g ((A.ext i).symm y))
        (A.ext i).target :=
      (Complex.continuous_ofReal.comp_continuousOn ((A.contMDiff_psi i).continuous.comp_continuousOn
        (A.chart i).continuousOn_extend_symm)).mul
          (hg.comp_continuousOn (A.chart i).continuousOn_extend_symm)
    refine ((hcont _ hyt).mono_of_mem_nhdsWithin hU).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hU] with z hz
      rw [piece, indicator_of_mem hz]
    · rw [piece, indicator_of_mem hyt]
  · have hev : A.piece i g =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(A.isCompact_pieceCarrier i).isClosed.isOpen_compl.mem_nhds hyK] with z hz
      exact A.piece_eq_zero_of_notMem i g hz
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-! ### Pieces in `L_p` -/

section Lp

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]

/-- The pieces of strongly measurable functions are almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_piece (i : Fin A.n) {g : M → ℂ} (hg : StronglyMeasurable g) :
    AEStronglyMeasurable (A.piece i g) volume := by
  have hT := measurableSet_extend_target I (A.chart i)
  refine (aestronglyMeasurable_indicator_iff hT).2 ?_
  have hκ : AEMeasurable (A.ext i).symm (volume.restrict (A.ext i).target) :=
    ((A.chart i).continuousOn_extend_symm (I := I)).aemeasurable hT
  have hψ : ContinuousOn (fun y => (A.psi i ((A.ext i).symm y) : ℂ)) (A.ext i).target :=
    Complex.continuous_ofReal.comp_continuousOn ((A.contMDiff_psi i).continuous.comp_continuousOn
      (A.chart i).continuousOn_extend_symm)
  exact (hψ.aestronglyMeasurable hT).mul (hg.aestronglyMeasurable.comp_aemeasurable hκ)

variable [CompactSpace M] (μ : Measure M) [IsSmoothMeasure I μ]

/-- **The pieces are bounded in `L_p`**: `‖piece_i g‖_{L_p(E)} ≤ C ‖g‖_{L_p(μ)}`, since
`0 ≤ ψ_i ≤ 1` and the `L_p` norms on `M` and in the chart are comparable on `tsupport ψ_i`
(`Manifold.IsSmoothMeasure.exists_eLpNorm_chart_le`). -/
theorem exists_eLpNorm_piece_le (i : Fin A.n) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : M → ℂ, StronglyMeasurable g →
      eLpNorm (A.piece i g) p volume ≤ C * eLpNorm g p μ := by
  obtain ⟨c, _, hc, -, hcmp⟩ := IsSmoothMeasure.exists_eLpNorm_chart_le (I := I) μ (A.chart_mem i)
    (isClosed_tsupport _).isCompact (A.tsupport_psi_subset i) hp0 hp (F := ℂ)
  refine ⟨c, hc, fun g hg => ?_⟩
  have hψg : StronglyMeasurable fun x => (A.psi i x : ℂ) * g x :=
    ((A.contMDiff_psi i).continuous.measurable.complex_ofReal.mul hg.measurable).stronglyMeasurable
  refine (hcmp _ hψg fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]).1.trans
      (mul_le_mul' le_rfl (eLpNorm_mono hψg.aestronglyMeasurable fun x => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (A.nonneg_psi i x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (A.psi_le_one i x)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)

include hp in
/-- The pieces of `f ∈ L_p(μ)` are in `L_p(E)`. -/
theorem memLp_piece (i : Fin A.n) (f : Lp ℂ p μ) : MemLp (A.piece i f) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨C, hC, hle⟩ := A.exists_eLpNorm_piece_le μ i hp0 hp
  exact memLp_iff.2 ((hle f (Lp.stronglyMeasurable f)).trans_lt
    (ENNReal.mul_lt_top hC.lt_top (Lp.eLpNorm_lt_top f)))

/-- The **chart piece** of `f ∈ L_p(μ)` as an element of `L_p(E)`. -/
noncomputable def pieceLp (i : Fin A.n) (f : Lp ℂ p μ) : Lp ℂ p (volume : Measure E) :=
  (A.memLp_piece μ hp i f).toLp _

/-- The chart piece in `L_p(E)` agrees with `(ψ_i f) ∘ κ_i⁻¹` almost everywhere. -/
theorem pieceLp_ae (i : Fin A.n) (f : Lp ℂ p μ) : A.pieceLp μ hp i f =ᵐ[volume] A.piece i f :=
  MemLp.coeFn_toLp _

end Lp

/-! ### The change of charts with a cut-off -/

section Transition

variable [IsManifold I ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] in
/-- **The change of charts with a cut-off** from a chart `e` to a chart `e'` of the atlas, with a
smooth cut-off `c` on `M` whose support lies in both sources: `Φ = κ' ∘ κ⁻¹` with
`χ = c ∘ κ'⁻¹`, as a smooth change of variables with a cut-off on `range I`. -/
noncomputable def chartChange {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (he' : e' ∈ atlas H M) (c : M → ℝ) (hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ c)
    (hcs : tsupport c ⊆ e.source ∩ e'.source) : Rd.CutoffDiffeo (range I) where
  U := I.symm ⁻¹' (e.symm ≫ₕ e').source
  U' := I.symm ⁻¹' (e.symm ≫ₕ e').target
  isOpen_U := I.continuous_symm.isOpen_preimage _ (OpenPartialHomeomorph.open_source _)
  isOpen_U' := I.continuous_symm.isOpen_preimage _ (OpenPartialHomeomorph.open_target _)
  Phi := I.extendCoordChange e e'
  Psi := (I.extendCoordChange e e').symm
  chi := (e'.extend I).target.indicator fun y => (c ((e'.extend I).symm y) : ℂ)
  K0 := e'.extend I '' tsupport c
  contDiffOn_Phi := by
    rw [range_inter_coordChange_source]
    exact I.contDiffOn_extendCoordChange (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he')
  contDiffOn_Psi := by
    rw [range_inter_coordChange_target]
    exact I.contDiffOn_extendCoordChange_symm (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he')
  contDiffOn_chi := by
    rw [range_inter_coordChange_target]
    have hsub : (I.extendCoordChange e e').target ⊆ (e'.extend I).target := by
      rw [coordChange_target_eq_image]
      rintro _ ⟨x, hx, rfl⟩
      exact (e'.extend I).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hx.1)
    have hsm := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_comp_extend_symm he' hc)
    refine (hsm.mono hsub).congr fun y hy => ?_
    rw [indicator_of_mem (hsub hy)]
    rfl
  mapsTo_Phi := by
    rw [range_inter_coordChange_source, range_inter_coordChange_target]
    exact (I.extendCoordChange e e').mapsTo
  mapsTo_Psi := by
    rw [range_inter_coordChange_source, range_inter_coordChange_target]
    exact (I.extendCoordChange e e').mapsTo_symm
  left_inv x hx := by
    rw [range_inter_coordChange_source] at hx
    exact (I.extendCoordChange e e').left_inv hx
  right_inv y hy := by
    rw [range_inter_coordChange_target] at hy
    exact (I.extendCoordChange e e').right_inv hy
  isCompact_K0 := (isClosed_tsupport c).isCompact.image_of_continuousOn
    (e'.continuousOn_extend.mono (by
      rw [OpenPartialHomeomorph.extend_source]
      exact hcs.trans inter_subset_right))
  K0_subset := by
    rw [range_inter_coordChange_target, coordChange_target_eq_image]
    exact image_mono fun x hx => ⟨(hcs hx).2, (hcs hx).1⟩
  chi_eq_zero y _ hyK := by
    by_cases hy : y ∈ (e'.extend I).target
    · rw [indicator_of_mem hy]
      by_contra h
      have hne : c ((e'.extend I).symm y) ≠ 0 := fun h0 => h (by rw [h0, Complex.ofReal_zero])
      exact hyK ⟨(e'.extend I).symm y, subset_tsupport _ hne, (e'.extend I).right_inv hy⟩
    · exact indicator_of_notMem hy _

omit [FiniteDimensional ℝ E] in
/-- The change of charts with a cut-off acts on the source of the change of charts:
`T G = 1_{κ(s ∩ s')} (χ G) ∘ Φ`. -/
theorem chartChange_apply {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (he' : e' ∈ atlas H M) (c : M → ℝ) (hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ c)
    (hcs : tsupport c ⊆ e.source ∩ e'.source) (G : E → ℂ) (y : E) :
    (chartChange he he' c hc hcs).apply G y = (I.extendCoordChange e e').source.indicator
      (fun y => (chartChange he he' c hc hcs).chi (I.extendCoordChange e e' y) *
        G (I.extendCoordChange e e' y)) y := by
  rw [Rd.CutoffDiffeo.apply, ← range_inter_coordChange_source]
  rfl

variable (A' : BesovAtlas I M)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] in
/-- The cut-off `ψ_i θ'_j` of two atlases has its support in both sources. -/
theorem tsupport_psi_mul_theta_subset (i : Fin A.n) (j : Fin A'.n) :
    tsupport (fun x => A.psi i x * A'.theta j x) ⊆ (A.chart i).source ∩ (A'.chart j).source :=
  subset_inter (tsupport_mul_subset_left.trans (A.tsupport_psi_subset i))
    (tsupport_mul_subset_right.trans (A'.tsupport_theta_subset j))

/-- The **change of charts** from the `i`-th chart of `A` to the `j`-th chart of `A'`, with the
cut-off `(ψ_i θ'_j) ∘ κ'_j⁻¹`, as a smooth change of variables with a cut-off on `range I`. -/
noncomputable def transition (i : Fin A.n) (j : Fin A'.n) : Rd.CutoffDiffeo (range I) :=
  chartChange (A.chart_mem i) (A'.chart_mem j) (fun x => A.psi i x * A'.theta j x)
    ((A.contMDiff_psi i).mul (A'.contMDiff_theta j)) (A.tsupport_psi_mul_theta_subset A' i j)

omit [FiniteDimensional ℝ E] in
/-- The change of charts acts on the source of the change of charts:
`T_{ij} G = 1_{κ_i(s_i ∩ s'_j)} (χ G) ∘ Φ`. -/
theorem transition_apply (i : Fin A.n) (j : Fin A'.n) (G : E → ℂ) (y : E) :
    (A.transition A' i j).apply G y =
      (I.extendCoordChange (A.chart i) (A'.chart j)).source.indicator
        (fun y => (A.transition A' i j).chi (I.extendCoordChange (A.chart i) (A'.chart j) y) *
          G (I.extendCoordChange (A.chart i) (A'.chart j) y)) y := by
  exact chartChange_apply _ _ _ _ _ G y

omit [FiniteDimensional ℝ E] in
/-- **The change of charts at a point of both sources**: for `y = κ_i x` with `x` in the source
of `κ'_j`, `T_{ij} G (y) = ψ_i(x) θ'_j(x) G(κ'_j x)`. -/
theorem transition_apply_of_mem (i : Fin A.n) (j : Fin A'.n) (G : E → ℂ) {y : E}
    (hy : y ∈ (A.ext i).target) (hx : (A.ext i).symm y ∈ (A'.chart j).source) :
    (A.transition A' i j).apply G y = ((A.psi i ((A.ext i).symm y) *
      A'.theta j ((A.ext i).symm y) : ℝ) : ℂ) * G (A'.ext j ((A.ext i).symm y)) := by
  have hx' : (A.ext i).symm y ∈ (A'.ext j).source := by rwa [OpenPartialHomeomorph.extend_source]
  rw [transition_apply, indicator_of_mem ((mem_coordChange_source _ _).2 ⟨hy, hx⟩),
    coordChange_apply]
  simp only [transition, chartChange]
  rw [indicator_of_mem ((A'.ext j).map_source hx'), (A'.ext j).left_inv hx']

omit [FiniteDimensional ℝ E] in
/-- **The change of charts off the common sources**: `T_{ij} G (y) = 0` unless `y = κ_i x` with `x`
in the source of `κ'_j`. -/
theorem transition_apply_of_notMem (i : Fin A.n) (j : Fin A'.n) (G : E → ℂ) {y : E}
    (h : y ∈ (A.ext i).target → (A.ext i).symm y ∉ (A'.chart j).source) :
    (A.transition A' i j).apply G y = 0 := by
  rw [transition_apply, indicator_of_notMem fun h' => ?_]
  obtain ⟨h1, h2⟩ := (mem_coordChange_source _ _).1 h'
  exact h h1 h2

omit [FiniteDimensional ℝ E] in
/-- **The pieces of two atlases** (pointwise): `piece_i g = ∑_j T_{ij}(piece'_j g)`, since
`ψ_i g = ∑_j ψ_i ψ'_j g` and `θ'_j ψ'_j = ψ'_j` (`Manifold.BesovAtlas.transition_apply_of_mem`). -/
theorem piece_eq_sum_apply (i : Fin A.n) (g : M → ℂ) (y : E) :
    A.piece i g y = ∑ j, (A.transition A' i j).apply (A'.piece j g) y := by
  by_cases hy : y ∈ (A.ext i).target
  · set x := (A.ext i).symm y
    have hterm : ∀ j, (A.transition A' i j).apply (A'.piece j g) y =
        (A.psi i x : ℂ) * (A'.psi j x : ℂ) * g x := fun j => by
      by_cases hxj : x ∈ (A'.chart j).source
      · have hxj' : x ∈ (A'.ext j).source := by rwa [OpenPartialHomeomorph.extend_source]
        rw [A.transition_apply_of_mem A' i j _ hy hxj, piece,
          indicator_of_mem ((A'.ext j).map_source hxj'), (A'.ext j).left_inv hxj']
        push_cast
        have h := congrArg (fun t : ℝ => (t : ℂ)) (A'.theta_mul_psi j x)
        push_cast at h
        linear_combination (A.psi i x : ℂ) * g x * h
      · have hψ : A'.psi j x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hxj (A'.tsupport_psi_subset j h)
        rw [A.transition_apply_of_notMem A' i j _ fun _ => hxj, hψ, Complex.ofReal_zero, mul_zero,
          zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Complex.ofReal_sum, A'.sum_psi, Complex.ofReal_one, mul_one, piece, indicator_of_mem hy]
  · rw [piece, indicator_of_notMem hy]
    exact (Finset.sum_eq_zero fun j _ =>
      A.transition_apply_of_notMem A' i j _ fun h => (hy h).elim).symm

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
  [IsSmoothMeasure I μ] [hB : Rd.BesovDomain (range I)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)

/-- **The pieces of two atlases in `L_p`**: `piece_i f = ∑_j T_{ij}(piece'_j f)`, with the changes
of charts acting on `L_p(E)`. -/
theorem pieceLp_eq_sum (i : Fin A.n) (f : Lp ℂ p μ) :
    A.pieceLp μ hp i f = ∑ j, (A.transition A' i j).applyLp hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp (A'.pieceLp μ hp j f) := by
  refine Lp.ext ?_
  have h3 : ∀ᵐ y ∂volume, ∀ j, (A.transition A' i j).applyLp hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp (A'.pieceLp μ hp j f) y =
        (A.transition A' i j).apply (A'.piece j f) y :=
    ae_all_iff.2 fun j => ((A.transition A' i j).applyLp_ae hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp _).trans
        ((A.transition A' i j).apply_ae_eq ((A'.pieceLp_ae μ hp j f).mono fun y hy _ => hy))
  filter_upwards [A.pieceLp_ae μ hp i f, Lp.coeFn_fun_finsetSum Finset.univ
    (fun j => (A.transition A' i j).applyLp hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp (A'.pieceLp μ hp j f)), h3] with y hy1 hy2 hy3
  rw [hy1, hy2, A.piece_eq_sum_apply A' i f y]
  exact Finset.sum_congr rfl fun j _ => (hy3 j).symm

end Transition

end BesovAtlas

/-! ### Functions from a chart -/

section ChartLift

variable (I) in
/-- The **lift from a chart**: `θ · F ∘ κ` on the source of the chart `e`, `0` outside, for a
cut-off `θ` on `M` and `F : E → ℂ`. -/
noncomputable def chartLift (e : OpenPartialHomeomorph M H) (θ : M → ℝ) (F : E → ℂ) : M → ℂ :=
  e.source.indicator fun x => (θ x : ℂ) * F (e.extend I x)

omit [FiniteDimensional ℝ E] [ChartedSpace H M] in
/-- The lift from a chart is additive in the function on `E`. -/
theorem chartLift_add (e : OpenPartialHomeomorph M H) (θ : M → ℝ) (F G : E → ℂ) :
    chartLift I e θ (F + G) = chartLift I e θ F + chartLift I e θ G := by
  funext x
  by_cases hx : x ∈ e.source
  · simp only [chartLift, indicator_of_mem hx, Pi.add_apply, mul_add]
  · simp only [chartLift, indicator_of_notMem hx, Pi.add_apply, add_zero]

omit [FiniteDimensional ℝ E] [ChartedSpace H M] in
/-- The lift from a chart is homogeneous in the function on `E`. -/
theorem chartLift_smul (e : OpenPartialHomeomorph M H) (θ : M → ℝ) (c : ℂ) (F : E → ℂ) :
    chartLift I e θ (c • F) = c • chartLift I e θ F := by
  funext x
  by_cases hx : x ∈ e.source
  · simp only [chartLift, indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [chartLift, indicator_of_notMem hx, Pi.smul_apply, smul_zero]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]

omit [FiniteDimensional ℝ E] [ChartedSpace H M] in
/-- The lift from a chart is strongly measurable for continuous `θ` and strongly measurable `F`,
since `κ`, set to `0` off the open source, is measurable
(`Manifold.measurable_piecewise_extend`). -/
theorem stronglyMeasurable_chartLift (e : OpenPartialHomeomorph M H) {θ : M → ℝ}
    (hθ : Continuous θ) {F : E → ℂ} (hF : StronglyMeasurable F) :
    StronglyMeasurable (chartLift I e θ F) := by
  classical
  have h : chartLift I e θ F = e.source.indicator fun x =>
      (θ x : ℂ) * F (e.source.piecewise (e.extend I) (fun _ => (0 : E)) x) := by
    funext x
    by_cases hx : x ∈ e.source
    · rw [chartLift, indicator_of_mem hx, indicator_of_mem hx, piecewise_eq_of_mem _ _ _ hx]
    · rw [chartLift, indicator_of_notMem hx, indicator_of_notMem hx]
  rw [h]
  exact ((Complex.continuous_ofReal.comp hθ).stronglyMeasurable.mul
    (hF.comp_measurable (measurable_piecewise_extend I e))).indicator
    e.open_source.measurableSet

/-- **The lift from a chart sees only classes**: if `F = G` almost everywhere on `E`, then
`θ · F ∘ κ = θ · G ∘ κ` `μ`-almost everywhere, for every `θ` with `tsupport θ ⊆ e.source`
(`Manifold.IsSmoothMeasure.ae_comp_extend` on `tsupport θ`). -/
theorem chartLift_ae_eq [CompactSpace M] {μ : Measure M} [IsSmoothMeasure I μ]
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {θ : M → ℝ}
    (hθs : tsupport θ ⊆ e.source) {F G : E → ℂ} (h : F =ᵐ[volume] G) :
    chartLift I e θ F =ᵐ[μ] chartLift I e θ G := by
  filter_upwards [IsSmoothMeasure.ae_comp_extend (I := I) (μ := μ) he (isClosed_tsupport θ) hθs h]
    with x hx
  by_cases hxs : x ∈ e.source
  · simp only [chartLift, indicator_of_mem hxs]
    by_cases hxt : x ∈ tsupport θ
    · rw [hx hxt]
    · rw [image_eq_zero_of_notMem_tsupport hxt, Complex.ofReal_zero, zero_mul, zero_mul]
  · simp only [chartLift, indicator_of_notMem hxs]

/-- **The lift from a chart is bounded in `L_p`**: for a chart `e` of the atlas, a continuous
cut-off `θ` with `tsupport θ ⊆ e.source`, a smooth measure `μ` and `0 < p < ∞` there is `C < ∞`
with `‖θ · F ∘ κ‖_{L_p(μ)} ≤ C ‖F‖_{L_p(E)}` for every strongly measurable `F`. The `L_p` norms on
`M` and in the chart are comparable on `tsupport θ`
(`Manifold.IsSmoothMeasure.exists_eLpNorm_chart_le`), and `|θ| ≤ B` on the compact `M`. -/
theorem exists_eLpNorm_chartLift_le [CompactSpace M] (μ : Measure M) [IsSmoothMeasure I μ]
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {θ : M → ℝ} (hθ : Continuous θ)
    (hθs : tsupport θ ⊆ e.source) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : E → ℂ, StronglyMeasurable F →
      eLpNorm (chartLift I e θ F) p μ ≤ C * eLpNorm F p volume := by
  obtain ⟨_, C, -, hC, hle⟩ := IsSmoothMeasure.exists_eLpNorm_chart_le (I := I) μ he
    (isClosed_tsupport θ).isCompact hθs hp0 hp (F := ℂ)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hθ.continuousOn
  refine ⟨C * ENNReal.ofReal (max B 0), ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top,
    fun F hF => ?_⟩
  have hm := stronglyMeasurable_chartLift (I := I) e hθ hF
  have hT := measurableSet_extend_target I e
  have hmT : AEStronglyMeasurable ((e.extend I).target.indicator
      fun y => chartLift I e θ F ((e.extend I).symm y)) volume :=
    (aestronglyMeasurable_indicator_iff hT).2 (hm.aestronglyMeasurable.comp_aemeasurable
      ((e.continuousOn_extend_symm (I := I)).aemeasurable hT))
  refine (hle _ hm fun x hx => ?_).2.trans ?_
  · by_cases hxs : x ∈ e.source
    · rw [chartLift, indicator_of_mem hxs, image_eq_zero_of_notMem_tsupport hx,
        Complex.ofReal_zero, zero_mul]
    · rw [chartLift, indicator_of_notMem hxs]
  rw [mul_assoc]
  refine mul_le_mul' le_rfl (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmT (ae_of_all _ fun y => ?_) p)
  by_cases hy : y ∈ (e.extend I).target
  · have hx : (e.extend I).symm y ∈ e.source := by
      simpa only [e.extend_source] using (e.extend I).map_target hy
    rw [indicator_of_mem hy, chartLift, indicator_of_mem hx, (e.extend I).right_inv hy,
      norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right ((hB _ (mem_univ _)).trans (le_max_left B 0))
      (norm_nonneg _)
  · rw [indicator_of_notMem hy, norm_zero]
    exact mul_nonneg (le_max_right B 0) (norm_nonneg _)

/-- **The lift from a chart is in `L_p(μ)`** for `F ∈ L_p(E)`, a continuous cut-off `θ` with
`tsupport θ ⊆ e.source` and a smooth measure `μ`, by the `L_p` bound
(`Manifold.exists_eLpNorm_chartLift_le`). -/
theorem memLp_chartLift [CompactSpace M] (μ : Measure M) [IsSmoothMeasure I μ]
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {θ : M → ℝ} (hθ : Continuous θ)
    (hθs : tsupport θ ⊆ e.source) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {F : E → ℂ}
    (hFm : StronglyMeasurable F) (hF : MemLp F p volume) : MemLp (chartLift I e θ F) p μ := by
  obtain ⟨C, hC, hle⟩ := exists_eLpNorm_chartLift_le (I := I) μ he hθ hθs hp0 hp
  exact memLp_iff.2 ((hle F hFm).trans_lt (ENNReal.mul_lt_top hC.lt_top hF.eLpNorm_lt_top))

end ChartLift

namespace BesovAtlas

variable (A : BesovAtlas I M) [IsManifold I ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] in
/-- **The pieces of a lift from a chart**: `piece_i (θ_k · F ∘ κ_k) = T_{ik} F` pointwise, for the
change of charts `T_{ik}` with the cut-off `ψ_i θ_k` (`Manifold.BesovAtlas.transition_apply_of_mem`,
`Manifold.BesovAtlas.transition_apply_of_notMem`). -/
theorem piece_chartLift (i k : Fin A.n) (F : E → ℂ) :
    A.piece i (chartLift I (A.chart k) (A.theta k) F) = (A.transition A i k).apply F := by
  funext y
  by_cases hy : y ∈ (A.ext i).target
  · by_cases hxk : (A.ext i).symm y ∈ (A.chart k).source
    · rw [A.transition_apply_of_mem A i k F hy hxk, piece, indicator_of_mem hy, chartLift,
        indicator_of_mem hxk]
      push_cast
      ring
    · rw [A.transition_apply_of_notMem A i k F fun _ => hxk, piece, indicator_of_mem hy, chartLift,
        indicator_of_notMem hxk, mul_zero]
  · rw [A.transition_apply_of_notMem A i k F fun h => (hy h).elim, piece, indicator_of_notMem hy]

end BesovAtlas

end Manifold
