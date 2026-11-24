/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BlowupSequences
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularLocusDense
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PureDimension
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveDimensionalComponent

/-!
# Irreducible components of analytic subsets

Source: the analytic-geometry facts used in Copy-4, `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`): "a connected complex manifold is
irreducible", and "if `E_nK(α)` has no isolated points, each of its irreducible
components is positive-dimensional"; blueprint `ana:irreducible-components`.
These are standard (Grauert--Remmert, *Coherent analytic sheaves*, Ch. 9;
Demailly, *Complex analytic and differential geometry*, II.5).

* `isComplexAnalyticallyIrreducible_univ`: a nonempty connected complex manifold
  is analytically irreducible (identity theorem: a proper analytic subset of a
  connected manifold is nowhere dense).  Proved in
  `FirstPass.AnalyticSubsetTopology`.
* `regularAtDim_univ`, `exists_subvariety_univ`: the manifold itself is a closed
  irreducible analytic subvariety of dimension `n`.
* `eq_univ_of_isClosedConnectedSubmanifold_self`: a closed connected submanifold of
  full dimension of a connected manifold is the whole manifold.
* `exists_isIrreducibleComponent_pos_dim_of_accPt`: every non-isolated point of an
  analytic subset lies on a positive-dimensional irreducible component.  (The
  global irreducible components form a locally finite family of maximal
  irreducible analytic subsets; the germ at a non-isolated point has positive
  dimension, so some component through it does, and irreducible analytic sets are
  pure-dimensional.)  Derived in `Pending.PositiveDimensionalComponent` (blueprint
  `ana:irreducible-components`) from (LS) with connected regular parts and the closures of
  the connected components of the regular locus.
* `eq_dim_of_regularAtDim`: an irreducible analytic subvariety is pure-dimensional,
  i.e. every regular point has the certified dimension (Chirka, §5.3--5.4).  Derived in
  `Pending.PureDimension` from the local statement (LS)
  `AnalyticLocalStatement.exists_localDecomposition`, itself proved from the local
  parametrization theorem (`GermParametrization.exists_localParametrization`).
* `exists_mem_regularLocus_not_mem_of_not_subset`: an irreducible analytic
  subvariety not contained in an analytic subset `A` has a point, regular of the
  certified dimension, outside `A`.  PROVED from pure dimensionality and density of
  the regular locus (`FirstPass.RegularLocusDense.exists_regularAtDim_mem_nhds`,
  sorry-free): `V \ A` is a nonempty relatively open subset of `V`.  Used for
  positivity of restricted volumes.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

open FirstPass FirstPass.NonKahlerLocus FirstPass.BlowupSequences

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A connected complex manifold is analytically irreducible.** -/
theorem isComplexAnalyticallyIrreducible_univ [ConnectedSpace M] :
    IsComplexAnalyticallyIrreducible (n := n) (univ : Set M) :=
  isComplexAnalyticallyIrreducible_univ_of_connectedSpace

omit [IsComplexManifold n M] in
/-- Every point of the manifold is a regular point of `univ` of dimension `n`. -/
theorem regularAtDim_univ (x : M) : RegularAtDim (n := n) (univ : Set M) x n := by
  set e := (complexChartAt (n := n) x).val
  set p := e x
  refine ⟨le_rfl, mem_univ x, ?_⟩
  let Φ : LocalHolomorphicEquivAt (n := n) p :=
    { source := e.target
      target := (fun w => w + p) ⁻¹' e.target
      isOpen_source := e.open_target
      isOpen_target := e.open_target.preimage (continuous_id.add continuous_const)
      center_mem_source := e.map_source (mem_complexChartAt_source x)
      toFun := fun z => z - p
      invFun := fun w => w + p
      toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
      invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
      mapsTo_toFun := fun z hz => by simpa using hz
      mapsTo_invFun := fun w hw => hw
      left_inv := fun z _ => by simp
      right_inv := fun w _ => by simp }
  refine ⟨Φ, subset_rfl, sub_self p, ?_⟩
  intro y _ _
  simp only [mem_univ, true_iff]
  intro i hi
  exact absurd i.2 (not_lt.mpr hi)

/-- The manifold itself, as a closed irreducible analytic subvariety of
dimension `n`. -/
theorem exists_subvariety_univ [ConnectedSpace M] :
    ∃ V : ClosedIrreducibleAnalyticSubvariety n M, V.carrier = univ ∧ V.dim = n := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  exact ⟨⟨univ, isClosed_univ, isComplexAnalyticallyIrreducible_univ, n, le_rfl,
    ⟨x, regularAtDim_univ x⟩⟩, rfl, rfl⟩

omit [IsComplexManifold n M] in
/-- **The only certified dimension of `univ` is `n`.**

A regular point of `univ` of dimension `k` carries a biholomorphic flattening
`Φ` whose target is an open set containing `0` and contained in the coordinate
plane `{z : ∀ i ≥ k, z i = 0}`: every `w ∈ Φ.target` is `Φ.toFun (Φ.invFun w)`
with `Φ.invFun w ∈ Φ.source`, and the flattening equation applies to every point
of the source because every point of the manifold lies in `univ`.  A nonempty
open subset of `ℂ^n` inside that plane forces `k = n`, since otherwise a small
multiple of the `k`-th basis vector would lie in it with nonzero `k`-th
coordinate. -/
theorem eq_of_regularAtDim_univ {x : M} {k : ℕ}
    (h : RegularAtDim (n := n) (univ : Set M) x k) : k = n := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨hk, -, Φ, hsub, hzero, hflat⟩ := h
  -- the flattening sends its whole source into the coordinate plane
  have hplane : ∀ z ∈ Φ.source, Φ.toFun z ∈ complexCoordinatePlane n k := by
    intro z hz
    have hzt : z ∈ e.target := hsub hz
    have hy : e.symm z ∈ e.source := e.map_target hzt
    have hez : e (e.symm z) ∈ Φ.source := by rwa [e.right_inv hzt]
    have hmem := (hflat hy hez).mp (mem_univ _)
    rwa [e.right_inv hzt] at hmem
  -- hence the (open) target lies in the coordinate plane
  have htarget : Φ.target ⊆ complexCoordinatePlane n k := by
    intro w hw
    have hmem := hplane (Φ.invFun w) (Φ.mapsTo_invFun hw)
    rwa [Φ.right_inv w hw] at hmem
  have hzeromem : (0 : ComplexModel n) ∈ Φ.target := by
    have hmem := Φ.mapsTo_toFun Φ.center_mem_source
    rwa [hzero] at hmem
  -- a nonempty open subset of the plane forces `k = n`
  refine le_antisymm hk (not_lt.mp fun hlt => ?_)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Φ.isOpen_target 0 hzeromem
  set i : Fin n := ⟨k, hlt⟩ with hi
  set z : ComplexModel n := EuclideanSpace.single i ((ε / 2 : ℝ) : ℂ) with hz
  have hznorm : ‖z‖ = ε / 2 := by
    rw [hz, PiLp.norm_single]
    simp [hε.le]
  have hzball : z ∈ Metric.ball (0 : ComplexModel n) ε := by
    rw [Metric.mem_ball, dist_zero_right, hznorm]
    linarith
  have hzi : z i = 0 := htarget (hball hzball) i le_rfl
  rw [hz] at hzi
  simp at hzi
  linarith

/-- The certified dimension of the whole manifold, as a subvariety, is `n`. -/
theorem dim_eq_of_carrier_eq_univ (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hV : V.carrier = univ) : V.dim = n := by
  obtain ⟨y, hy⟩ := V.regularLocus_nonempty
  rw [mem_regularLocus, hV] at hy
  exact eq_of_regularAtDim_univ hy

omit [IsComplexManifold n M] in
/-- A set that is regular of full dimension at each of its points is open. -/
theorem isOpen_of_forall_regularAtDim_self {W : Set M}
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x n) : IsOpen W := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  obtain ⟨_, _, Φ, _, _, hflat⟩ := hW x hx
  have hS : IsOpen ((complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹' Φ.source) :=
    (complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Φ.isOpen_source
  refine mem_of_superset (hS.mem_nhds ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩) ?_
  intro y hy
  refine (hflat hy.1 hy.2).mpr ?_
  intro i hi
  exact absurd i.2 (not_lt.mpr hi)

omit [IsComplexManifold n M] in
/-- A closed connected submanifold of full dimension of a connected manifold is the
whole manifold. -/
theorem eq_univ_of_isClosedConnectedSubmanifold_self [ConnectedSpace M] {W : Set M}
    (hW : IsClosedConnectedSubmanifold n W n) : W = univ :=
  IsClopen.eq_univ ⟨hW.1, isOpen_of_forall_regularAtDim_self hW.2.2⟩ hW.2.1.nonempty

/-- **Positive-dimensional components through non-isolated points.** A point of an
analytic subset `A` which is not isolated in `A` lies on a positive-dimensional
irreducible component of `A`. -/
theorem exists_isIrreducibleComponent_pos_dim_of_accPt {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {x : M}
    (hacc : AccPt x (𝓟 A)) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
      IsIrreducibleComponent V A ∧ 0 < V.dim ∧ x ∈ V.carrier :=
  PositiveDimensionalComponent.exists_isIrreducibleComponent_pos_dim_of_accPt hA hacc

/-- **Irreducible analytic sets are pure-dimensional.**
At every point where an irreducible analytic subvariety `V` is regular, its dimension is
the certified dimension `dim V`.

Classically the regular locus of an irreducible analytic set is a connected manifold
(Chirka, *Complex Analytic Sets*, §5.3--5.4; Grauert--Remmert, *Coherent analytic
sheaves*, Ch. 9, §1--2); equivalently, the closures of the dimension strata of the regular
locus are analytic and irreducibility selects one of them.  This replaces (run 0031 r3)
the former input `exists_mem_regularLocus_not_mem_of_not_subset`, whose density half is
proved in `FirstPass.RegularLocusDense`.  Derived in `Pending.PureDimension` (blueprint
`ana:pure-dimension`) from the local statement (LS),
`AnalyticLocalStatement.exists_localDecomposition`. -/
theorem eq_dim_of_regularAtDim (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M}
    {k : ℕ} (hx : RegularAtDim (n := n) V.carrier x k) : k = V.dim :=
  PureDimension.eq_dim_of_regularAtDim V hx

/-- **Top-dimensional regular points off a proper analytic subset.**
An irreducible analytic subvariety `V` not contained in an analytic subset `A` has a point
outside `A` at which `V` is regular of dimension `dim V`.

`A` is closed, so `V \ A` is a nonempty relatively open subset of `V`; the regular locus is
dense (`RegularLocusDense.exists_regularAtDim_mem_nhds`, sorry-free), so `V` is regular of
some dimension at a point of `Aᶜ`, and that dimension is `dim V` by pure dimensionality
(`eq_dim_of_regularAtDim`). -/
theorem exists_mem_regularLocus_not_mem_of_not_subset
    (V : ClosedIrreducibleAnalyticSubvariety n M) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hV : ¬ V.carrier ⊆ A) :
    ∃ x ∈ regularLocus (n := n) V.carrier V.dim, x ∉ A := by
  obtain ⟨y, hyV, hyA⟩ := not_subset.mp hV
  obtain ⟨x, hxA, k, hx⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen V.analytic
    hA.isClosed.isOpen_compl hyV hyA
  exact ⟨x, (eq_dim_of_regularAtDim V hx) ▸ hx, hxA⟩

end

end SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
