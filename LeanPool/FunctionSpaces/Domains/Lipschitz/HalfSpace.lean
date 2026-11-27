/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.DiffeoInvariance
public import LeanPool.FunctionSpaces.Domains.Lipschitz.BoundedLipschitz
public import Mathlib.Geometry.Manifold.Instances.Real

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The half-space as a Besov domain

Lipschitz graph domains have the extension property (`Rd.LipschitzGraph.hasBesovExtension`):
Rychkov's extension agrees with `f` on the domain and is bounded by a constant times the intrinsic
quasi-norm (`Rd.LipschitzGraph.modNorm_extension_le_modNormOn`).

The closed half-space `{x : 0 ≤ ⟪x, e⟫}` for a unit vector `e` (`Rd.closedHalfSpace`) is a Besov
domain (`Rd.BesovDomain.closedHalfSpace`): it differs from the flat Lipschitz graph domain
`{x : 0 < ⟪x, e⟫}` (`Rd.LipschitzGraph.flat`) by the null set `e^⊥`
(`Rd.volume_orthogonal_singleton_eq_zero`, `Rd.closedHalfSpace_ae_eq`), and the extension property
is the same for sets that agree up to a null set (`Rd.HasBesovExtension.congr_set`,
`Rd.BesovDomain.of_ae_eq`).

The models of manifolds are Besov domains: the range of a model with corners is one if it agrees
up to a null set with a set with the extension property (`Rd.BesovDomain.range_of_ae_eq`); the
range of the model with corners of the Euclidean half-space is the closed half-space
`{y : 0 ≤ ⟪y, e₀⟫}` for the unit vector `e₀ = (1, 0, …, 0)` (`Rd.e0`, `Rd.norm_e0`,
`Manifold.range_eq_closedHalfSpace`, `Rd.BesovDomain.range_euclideanHalfSpace`), and the range `V`
of a model without boundary is the whole space (`Rd.BesovDomain.range_of_boundaryless`). The first
coordinate is `⟪y, e₀⟫` (`Rd.coord_zero_eq_inner`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Hyperplanes are null sets -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `e ≠ 0` the orthogonal complement `e^⊥` is a proper subspace: `Kᗮ = ⊤` only for `K = ⊥`
(Mathlib's `Submodule.orthogonal_eq_top_iff`), and `ℝ e = ⊥` only for `e = 0` (Mathlib's
`Submodule.span_singleton_eq_bot`). -/
theorem orthogonal_singleton_ne_top {e : V} (he : e ≠ 0) : (ℝ ∙ e)ᗮ ≠ ⊤ := by
  simpa using he

/-- **A hyperplane is a null set**: `e^⊥` has Lebesgue measure zero for `e ≠ 0` (Mathlib's
`MeasureTheory.Measure.addHaar_submodule`). -/
theorem volume_orthogonal_singleton_eq_zero {e : V} (he : e ≠ 0) :
    volume ((ℝ ∙ e)ᗮ : Set V) = 0 :=
  Measure.addHaar_submodule volume _ (orthogonal_singleton_ne_top he)

/-! ### The extension property of Lipschitz graph domains -/

/-- **Lipschitz graph domains have the extension property**: Rychkov's extension agrees with `f`
on the domain (`Rd.LipschitzGraph.cutoff_extension_of_modNormOn`) and is bounded by a constant
times the intrinsic quasi-norm (`Rd.LipschitzGraph.modNorm_extension_le_modNormOn`); the proof
takes `C = G.coneBump.synthConst r s * G.intrinsicConst r`. -/
theorem LipschitzGraph.hasBesovExtension (G : LipschitzGraph V) :
    HasBesovExtension G.measurableSet_domain := by
  intro p _ hp r s hs hsr q hq
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (Nat.cast_pos.1 (hs.trans hsr)).ne'
  exact ⟨G.coneBump.synthConst r s * G.intrinsicConst r, ENNReal.mul_ne_top
    (G.coneBump.synthConst_ne_top hs hsr) (G.intrinsicConst_ne_top r), fun f hf =>
    ⟨G.extension hp r f, G.cutoff_extension_of_modNormOn hp hr hs hq hf,
      G.modNorm_extension_le_modNormOn hp r hs hq hf⟩⟩

/-! ### The half-space -/

/-- The **closed half-space** `{x : 0 ≤ ⟪x, e⟫}`. -/
def closedHalfSpace (e : V) : Set V := {x | 0 ≤ inner ℝ x e}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The closed half-space is closed. -/
theorem isClosed_closedHalfSpace (e : V) : IsClosed (closedHalfSpace e) :=
  isClosed_le continuous_const (continuous_id.inner continuous_const)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The closed half-space is convex. -/
theorem convex_closedHalfSpace (e : V) : Convex ℝ (closedHalfSpace e) := by
  intro x hx y hy a b ha hb _
  change 0 ≤ inner ℝ (a • x + b • y) e
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A nonzero `e` lies in the interior of its closed half-space. -/
theorem mem_interior_closedHalfSpace {e : V} (he : e ≠ 0) : e ∈ interior (closedHalfSpace e) := by
  refine mem_interior.2 ⟨{x | 0 < inner ℝ x e}, fun x (hx : 0 < inner ℝ x e) => hx.le,
    isOpen_lt continuous_const (continuous_id.inner continuous_const), ?_⟩
  change 0 < inner ℝ e e
  rw [real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.2 he) 2

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The **flat Lipschitz graph domain**: the open half-space `{x : 0 < ⟪x, e⟫}` for a unit
vector `e`, with graph function `0`. -/
def LipschitzGraph.flat (e : V) (he : ‖e‖ = 1) : LipschitzGraph V where
  e := e
  norm_e := he
  M := 0
  M_nonneg := le_rfl
  phi := 0
  lipschitz _ _ := by simp
  const _ _ := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The flat domain is the open half-space. -/
theorem LipschitzGraph.flat_domain (e : V) (he : ‖e‖ = 1) :
    (LipschitzGraph.flat e he).domain = {x | 0 < inner ℝ x e} := rfl

/-- **The closed half-space is the open one up to a null set**: they differ by the hyperplane
`e^⊥`, a proper subspace. -/
theorem closedHalfSpace_ae_eq {e : V} (he : ‖e‖ = 1) :
    closedHalfSpace e =ᵐ[volume] (LipschitzGraph.flat e he).domain := by
  have he0 : e ≠ 0 := fun h => by simp [h] at he
  have hnull := volume_orthogonal_singleton_eq_zero he0
  refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) hnull, ?_⟩
  · have h1 : 0 ≤ inner ℝ x e := hx.1
    have h2 : ¬ 0 < inner ℝ x e := hx.2
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact le_antisymm (not_lt.1 h2) h1
  · have hsub : (LipschitzGraph.flat e he).domain ⊆ closedHalfSpace e :=
      fun x (hx : 0 < inner ℝ x e) => hx.le
    rw [sdiff_eq_empty.2 hsub, measure_empty]

/-- **The closed half-space is a Besov domain**: it agrees up to a null set with the flat Lipschitz
graph domain (`Rd.closedHalfSpace_ae_eq`), which has the extension property
(`Rd.LipschitzGraph.hasBesovExtension`). -/
theorem BesovDomain.closedHalfSpace {e : V} (he : ‖e‖ = 1) : BesovDomain (closedHalfSpace e) :=
  of_ae_eq (convex_closedHalfSpace e) (isClosed_closedHalfSpace e)
    ⟨e, mem_interior_closedHalfSpace fun h => by simp [h] at he⟩
    (LipschitzGraph.flat e he).hasBesovExtension (closedHalfSpace_ae_eq he)

/-! ### The models of manifolds -/

section FirstAxis

variable {n : ℕ} [NeZero n]

/-- The unit vector `e₀ = (1, 0, …, 0)` of `ℝ^n`. -/
noncomputable def e0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1

/-- `‖e₀‖ = 1`. -/
theorem norm_e0 : ‖(e0 : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simp [e0]

/-- The first coordinate is the inner product with `e₀`. -/
theorem coord_zero_eq_inner (y : EuclideanSpace ℝ (Fin n)) : y 0 = inner ℝ y e0 := by
  simp [e0, EuclideanSpace.inner_single_right]

open scoped Manifold in
/-- The range of the half-space model is the closed half-space `{y : 0 ≤ ⟪y, e₀⟫}`. -/
theorem _root_.Manifold.range_eq_closedHalfSpace :
    range (𝓡∂ n) = Rd.closedHalfSpace (Rd.e0 : EuclideanSpace ℝ (Fin n)) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  ext y
  simp [Rd.closedHalfSpace, Rd.e0, EuclideanSpace.inner_single_right]

end FirstAxis

/-- **Models of manifolds as Besov domains**: the range of a model with corners is a Besov domain
if it agrees up to a null set with a set with the extension property. The range is closed, convex
and has nonempty interior for every real model with corners (Mathlib's
`ModelWithCorners.isClosed_range`, `ModelWithCorners.convex_range`,
`ModelWithCorners.nonempty_interior`). -/
theorem BesovDomain.range_of_ae_eq {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
    {U : Set V} {hU : MeasurableSet U} (h : HasBesovExtension hU) (hae : range I =ᵐ[volume] U) :
    BesovDomain (range I) :=
  of_ae_eq I.convex_range I.isClosed_range I.nonempty_interior h hae

/-- **The Euclidean half-space model is a Besov domain**: the range of the model with corners
`𝓡∂ n` is the closed half-space `{y : 0 ≤ ⟪y, e₀⟫}` (`Manifold.range_eq_closedHalfSpace`). -/
instance BesovDomain.range_euclideanHalfSpace (n : ℕ) [NeZero n] :
    BesovDomain (Set.range (modelWithCornersEuclideanHalfSpace n)) := by
  rw [Manifold.range_eq_closedHalfSpace]
  exact BesovDomain.closedHalfSpace norm_e0

/-- **A model without boundary is a Besov domain**: its range is the whole space. -/
instance BesovDomain.range_of_boundaryless {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ V H) [I.Boundaryless] : BesovDomain (Set.range I) := by
  rw [I.range_eq_univ]
  infer_instance

end Rd
