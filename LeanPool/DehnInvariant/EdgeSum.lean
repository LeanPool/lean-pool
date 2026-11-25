/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.ConeAngles
public import LeanPool.DehnInvariant.EdgeData
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

/-!
Lean study 10 of the shape-language canon (DICTO, 19 Nov 2026), part AF: the set-defined Dehn
invariant is
the classical sum over the edges, for every convex polytope.

The edges, the facets through an edge and the interior dihedral angle are defined from the solid
`P` as a set
of points, with no half-space description:
* `faceIn P n`: the points of `P` where ⟪n, ·⟫ is largest (the exposed face in the direction `n`);
* `IsEdge P F`: `F` is an exposed face of `P` (Mathlib's `IsExposed`) and a segment with two
  different ends;
* `facetNormals P F`: the unit vectors `n` whose face `faceIn P n` contains `F` and is not
  contained in a line
  (Mathlib's `Collinear`): the outward unit normals of the facets through `F`;
* `dihedral P F`: π minus the largest angle between two such normals.

* `IsEdge.facetNormals_eq_pair`: through every edge of a convex polytope with interior points pass
  exactly two
  facets; their outward unit normals `n₁`, `n₂` are linearly independent, and
  `dihedral P F = π − angle n₁ n₂`, strictly between 0 and π.
* `edges_finite`: a convex polytope has finitely many edges.
* `dehnSet_eq_edge_sum` (**the classical form**): for every convex polytope `P` (bounded
  intersection of
  finitely many closed half-spaces) with interior points,
  `dehnSet P = Σ over the edges F of P of (length of F) ⊗ (dihedral P F mod ℚπ)`.
  This is the invariant of Dehn (1901) in the tensor form of Jessen (Math. Scand. 22 (1968)
  241–256).
* `IsEdge.length`: the length (1-dimensional Hausdorff measure) of the edge with ends `u`, `v` is
  `dist u v`.

The half-space formula `dehnSet_eq_sum_faceSet` sums the invariant of `sol a b` over the sets
`A` of
constraints: (length of the points where exactly `A` is tight) ⊗ (angle class of the cone of `A`).
The
half-space description may be redundant in every way (repeated, never tight, tight only along an
edge or at a
corner, zero normals). A set `A` contributes only if its direction space is a line and it is the
tight set of
some point. For such `A`:
- the points where at least `A` is tight are a segment with two different ends
  (`tightSet_eq_segment`: a
  compact convex set of the line), an exposed face (`isExposed_tightSet`: the functional Σ_{i ∈ A}
  ⟪a i, ·⟫),
  hence an edge; every edge arises so, from the tight set of its midpoint
  (`exists_tight_of_edge`); different
  such `A` give different edges (`tightSet_inj`);
- the cone of `A` is the cone of two of its constraints with independent normals
  (`exists_pair_cone`, by study
  4's `two_extreme`: the normals of `A` lie in the plane perpendicular to the edge, on one side of
  a line
  because the solid has an interior point), so its angle is π − angle of these two normals (study
  3's
  `theta_pair`, from the sector area);
- these two normals, scaled to length 1, are exactly the facet normals at the edge
  (`facetNormals_tightSet`).

Credits: Dehn (1901); Jessen (1968) for the form Σ length ⊗ angle; Mathlib `IsExposed`, `Collinear`,
`collinear_iff_of_mem`, `eq_Icc_of_connected_compact`, `Convex.isConnected`,
`Convex.affine_preimage`,
`image_segment`, `image_openSegment`, `segment_eq_Icc`, `openSegment_eq_Ioo`, `finrank_eq_one_iff'`,
`finrank_span_eq_card`, `Submodule.eq_of_le_of_finrank_eq`, `Submodule.mem_span_pair`,
`LinearIndependent.pair_symm_iff`, `LinearIndependent.pair_iff'`, `Finset.sum_eq_sum_iff_of_le`,
`hausdorffMeasure_segment`, `finsum_mem_eq_of_bijOn`, `finsum_mem_inter_support_eq`,
`InnerProductGeometry.angle_smul_left_of_pos`, `InnerProductGeometry.angle_smul_right_of_pos`,
`InnerProductGeometry.angle_eq_zero_iff`, `InnerProductGeometry.angle_eq_pi_iff`;
study 2's `tcone_sol`, `cone_lin`; study 3's `theta_pair`; study 4's `two_extreme`,
`finrank_linCone_ne_one_of_perp`, `dehnSet_eq_sum_faceSet`, `hausdorff_openSegment`.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace Real
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Faces, edges, facet normals and the dihedral angle of a set -/

/-- The face of `P` in the direction `n`: the points of `P` where ⟪n, ·⟫ is largest. -/
def faceIn (P : Set E) (n : E) : Set E := {x | x ∈ P ∧ ∀ y ∈ P, ⟪n, y⟫ ≤ ⟪n, x⟫}

/-- A face in a direction is an exposed face in Mathlib's sense. -/
lemma isExposed_faceIn (P : Set E) (n : E) : IsExposed ℝ P (faceIn P n) := by
  intro _
  refine ⟨innerSL ℝ n, ?_⟩
  ext x
  simp only [faceIn, innerSL_apply_apply]

/-- **An edge** of `P`: an exposed face of `P` that is a segment with two different ends. -/
def IsEdge (P F : Set E) : Prop := IsExposed ℝ P F ∧ ∃ u v : E, u ≠ v ∧ F = segment ℝ u v

/-- The set of the edges of `P`. -/
def edges (P : Set E) : Set (Set E) := {F | IsEdge P F}

/-- **The outward unit normals of the facets of `P` through `F`**: the unit vectors `n` whose face
contains
`F` and is not contained in a line. -/
def facetNormals (P F : Set E) : Set E :=
  {n | ‖n‖ = 1 ∧ F ⊆ faceIn P n ∧ ¬ Collinear ℝ (faceIn P n)}

/-- **The interior dihedral angle of `P` at `F`**: π minus the largest angle between two outward
unit normals
of facets through `F`. -/
noncomputable def dihedral (P F : Set E) : ℝ :=
  π - sSup ((fun p : E × E => InnerProductGeometry.angle p.1 p.2) ''
    (facetNormals P F ×ˢ facetNormals P F))

/-- If exactly two facets pass through `F`, with outward unit normals `n₁`, `n₂`, the dihedral
angle at `F`
is π − angle(n₁, n₂). -/
lemma dihedral_eq_of_pair {P F : Set E} {n₁ n₂ : E} (h : facetNormals P F = {n₁, n₂}) :
    dihedral P F = π - InnerProductGeometry.angle n₁ n₂ := by
  have hne : ∀ n ∈ facetNormals P F, n ≠ 0 := fun n hn h0 => by
    have := hn.1; rw [h0, norm_zero] at this; exact zero_ne_one this
  have h1 : n₁ ∈ facetNormals P F := by rw [h]; exact mem_insert _ _
  have h2 : n₂ ∈ facetNormals P F := by rw [h]; exact mem_insert_of_mem _ rfl
  unfold dihedral
  congr 1
  apply le_antisymm
  · refine csSup_le ⟨_, ⟨(n₁, n₂), ⟨h1, h2⟩, rfl⟩⟩ ?_
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hx' : x = n₁ ∨ x = n₂ := by
      have : x ∈ ({n₁, n₂} : Set E) := h ▸ hx
      exact this
    have hy' : y = n₁ ∨ y = n₂ := by
      have : y ∈ ({n₁, n₂} : Set E) := h ▸ hy
      exact this
    change InnerProductGeometry.angle x y ≤ _
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;> rw [hx', hy']
    · rw [InnerProductGeometry.angle_self (hne _ h1)]; exact InnerProductGeometry.angle_nonneg _ _
    · exact (InnerProductGeometry.angle_comm _ _).le
    · rw [InnerProductGeometry.angle_self (hne _ h2)]; exact InnerProductGeometry.angle_nonneg _ _
  · exact le_csSup ⟨π, by rintro _ ⟨p, -, rfl⟩; exact InnerProductGeometry.angle_le_pi _ _⟩
      ⟨(n₁, n₂), ⟨h1, h2⟩, rfl⟩

/-- Two independent vectors: a direction perpendicular to the first, on the inner side of the
second. -/
lemma exists_perp_neg {x y : E} (h : LinearIndependent ℝ ![x, y]) :
    ∃ w : E, ⟪x, w⟫ = 0 ∧ ⟪y, w⟫ < 0 := by
  have hx : x ≠ 0 := by simpa using h.ne_zero 0
  have hxx : ⟪x, x⟫ ≠ 0 := inner_self_ne_zero.2 hx
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ⟪x, y⟫ / ⟪x, x⟫ := ⟨_, rfl⟩
  obtain ⟨w0, hw⟩ : ∃ w0 : E, w0 = y - c • x := ⟨_, rfl⟩
  have h1 : ⟪x, w0⟫ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hc, div_mul_cancel₀ _ hxx, sub_self]
  have hw0 : w0 ≠ 0 := by
    intro h0
    have h2 := (LinearIndependent.pair_iff.1 h) (-c) 1 (by
      rw [neg_smul, one_smul, neg_add_eq_sub, ← hw, h0])
    exact one_ne_zero h2.2
  have hy : y = w0 + c • x := by rw [hw, sub_add_cancel]
  have h2 : ⟪y, w0⟫ = ⟪w0, w0⟫ := by
    conv_lhs => rw [hy]
    rw [inner_add_left, real_inner_smul_left, h1, mul_zero, add_zero]
  refine ⟨-w0, by rw [inner_neg_right, h1, neg_zero], ?_⟩
  rw [inner_neg_right, h2]
  exact neg_neg_of_pos (real_inner_self_pos.2 hw0)

/-! ### A solid given by half-spaces: the sets of tight constraints that are edges -/

variable {ι : Type} {a : ι → E} {b : ι → ℝ}

/-- The points of the solid where at least the constraints in `A` hold with equality (a closed
face). -/
def tightSet (a : ι → E) (b : ι → ℝ) (A : Set ι) : Set E := {x | x ∈ sol a b ∧ A ⊆ act a b x}

lemma faceSet_subset_tightSet (a : ι → E) (b : ι → ℝ) (A : Set ι) : faceSet a b A ⊆ tightSet a b A
    :=
  fun _ hx => ⟨hx.1, hx.2.ge⟩

/-- Different sets of constraints, each the tight set of some point, have different closed faces. -/
lemma tightSet_inj {A B : Set ι} (hA : (faceSet a b A).Nonempty) (hB : (faceSet a b B).Nonempty)
    (h : tightSet a b A = tightSet a b B) : A = B := by
  obtain ⟨x, hx, hxA⟩ := hA
  obtain ⟨y, hy, hyB⟩ := hB
  have h1 : x ∈ tightSet a b B := by rw [← h]; exact ⟨hx, hxA.ge⟩
  have h2 : y ∈ tightSet a b A := by rw [h]; exact ⟨hy, hyB.ge⟩
  exact Subset.antisymm (hyB ▸ h2.2) (hxA ▸ h1.2)

/-- **A line of tight constraints gives a segment.** If `A` is the tight set of the point `x` and
the common
direction space of `A` is the line of `d`, then the points where at least `A` is tight form a
segment with
two different ends, and inside the segment exactly `A` is tight. -/
lemma tightSet_eq_segment [Finite ι] (hb : Bornology.IsBounded (sol a b)) {A : Set ι} {x d : E}
    (hx : x ∈ faceSet a b A) (hd0 : d ≠ 0) (hd : d ∈ linCone a A)
    (hspan : ∀ w ∈ linCone a A, ∃ r : ℝ, w = r • d) :
    ∃ u v : E, u ≠ v ∧ tightSet a b A = segment ℝ u v ∧ openSegment ℝ u v ⊆ faceSet a b A := by
  obtain ⟨hxs, hact⟩ := hx
  have hxA : ∀ i ∈ A, ⟪a i, x⟫ = b i := fun i hi => (hact ▸ hi : i ∈ act a b x)
  let φ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + d)
  have hφ : ∀ t : ℝ, φ t = x + t • d := by
    intro t; simp [φ, AffineMap.lineMap_apply, add_comm]
  have hcont : Continuous φ := by
    rw [show (φ : ℝ → E) = fun t => x + t • d from funext hφ]; fun_prop
  obtain ⟨T, hT⟩ : ∃ T : Set ℝ, T = φ ⁻¹' sol a b := ⟨_, rfl⟩
  have hmemT : ∀ t : ℝ, t ∈ T ↔ x + t • d ∈ sol a b := by
    intro t; rw [hT, mem_preimage, hφ]
  have hTc : Convex ℝ T := by rw [hT]; exact (convex_sol a b).affine_preimage φ
  have hTcl : IsClosed T := by rw [hT]; exact (isClosed_sol a b).preimage hcont
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : E)
  have hTb : Bornology.IsBounded T := by
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := (R + ‖x‖) / ‖d‖)).subset fun t ht => ?_
    have h1 : ‖x + t • d‖ ≤ R := mem_closedBall_zero_iff.1 (hR ((hmemT t).1 ht))
    have h2 : ‖t • d‖ ≤ R + ‖x‖ := by
      calc ‖t • d‖ = ‖(x + t • d) - x‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x + t • d‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ R + ‖x‖ := by linarith
    rw [norm_smul] at h2
    rw [mem_closedBall_zero_iff, le_div_iff₀ (norm_pos_iff.2 hd0)]
    exact h2
  have hTk : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTcl hTb
  have h0 : (0 : ℝ) ∈ T := by rw [hmemT, zero_smul, add_zero]; exact hxs
  have hIcc := eq_Icc_of_connected_compact (hTc.isConnected ⟨0, h0⟩) hTk
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℝ, t0 = sInf T := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ : ∃ t1 : ℝ, t1 = sSup T := ⟨_, rfl⟩
  rw [← ht0, ← ht1] at hIcc
  have hstep : ∀ w ∈ linCone a A, ∃ t : ℝ, 0 < t ∧ x + t • w ∈ sol a b := by
    intro w hw
    have hwt : w ∈ tcone (sol a b) x := by
      rw [tcone_sol a b hxs, hact]; intro i hi; exact (hw i hi).le
    exact hwt.2
  obtain ⟨s1, hs1, hs1m⟩ := hstep d hd
  obtain ⟨s2, hs2, hs2m⟩ := hstep (-d) (neg_mem hd)
  have m1 : s1 ∈ Icc t0 t1 := by rw [← hIcc, hmemT]; exact hs1m
  have m2 : -s2 ∈ Icc t0 t1 := by
    rw [← hIcc, hmemT, neg_smul, ← smul_neg]; exact hs2m
  have ht01 : t0 < t1 := by linarith [m1.2, m2.1]
  have ht0T : t0 ∈ T := by rw [hIcc]; exact left_mem_Icc.2 ht01.le
  have ht1T : t1 ∈ T := by rw [hIcc]; exact right_mem_Icc.2 ht01.le
  have htight : ∀ t : ℝ, ∀ i ∈ A, ⟪a i, x + t • d⟫ = b i := by
    intro t i hi
    rw [inner_add_right, inner_smul_right, hd i hi, mul_zero, add_zero]; exact hxA i hi
  refine ⟨φ t0, φ t1, ?_, ?_, ?_⟩
  · rw [hφ, hφ]
    intro h
    have h' : (t1 - t0) • d = 0 := by
      rw [sub_smul, sub_eq_zero]; exact (add_left_cancel h).symm
    rcases smul_eq_zero.1 h' with h'' | h''
    · linarith
    · exact hd0 h''
  · rw [← image_segment, segment_eq_Icc ht01.le, ← hIcc]
    ext y; constructor
    · rintro ⟨hy, hA⟩
      have hw : y - x ∈ linCone a A := by
        intro i hi
        rw [inner_sub_right, show ⟪a i, y⟫ = b i from hA hi, hxA i hi, sub_self]
      obtain ⟨r, hr⟩ := hspan _ hw
      have hyr : x + r • d = y := by rw [← hr, add_sub_cancel]
      exact ⟨r, (hmemT r).2 (hyr ▸ hy), by rw [hφ, hyr]⟩
    · rintro ⟨t, ht, rfl⟩
      rw [hφ]
      exact ⟨(hmemT t).1 ht, fun i hi => htight t i hi⟩
  · rw [← image_openSegment, openSegment_eq_Ioo ht01]
    rintro _ ⟨t, ht, rfl⟩
    have htT : t ∈ T := by rw [hIcc]; exact ⟨ht.1.le, ht.2.le⟩
    rw [hφ]
    refine ⟨(hmemT t).1 htT, ?_⟩
    ext k; constructor
    · intro hk
      by_contra hkA
      have hk' : ⟪a k, x + t • d⟫ = b k := hk
      rw [inner_add_right, inner_smul_right] at hk'
      have hxlt : ⟪a k, x⟫ < b k :=
        lt_of_le_of_ne (hxs k) (fun h => hkA (hact ▸ (h : k ∈ act a b x)))
      have e0 : ⟪a k, x + t0 • d⟫ ≤ b k := (hmemT t0).1 ht0T k
      have e1 : ⟪a k, x + t1 • d⟫ ≤ b k := (hmemT t1).1 ht1T k
      rw [inner_add_right, inner_smul_right] at e0 e1
      have hc1 : (t1 - t) * ⟪a k, d⟫ ≤ 0 := by linarith
      have hc0 : (t0 - t) * ⟪a k, d⟫ ≤ 0 := by linarith
      have hc : ⟪a k, d⟫ = 0 := by
        apply le_antisymm
        · by_contra hpos
          push Not at hpos
          nlinarith [mul_pos (sub_pos.2 ht.2) hpos]
        · by_contra hneg
          push Not at hneg
          nlinarith [mul_pos_of_neg_of_neg (sub_neg.2 ht.1) hneg]
      rw [hc, mul_zero, add_zero] at hk'
      exact hxlt.ne hk'
    · intro hk
      exact htight t k hk

/-- **The closed face of a tight set is an exposed face** (exposed by the sum of the normals of
`A`). -/
lemma isExposed_tightSet [Finite ι] {A : Set ι} {x₀ : E} (hx₀ : x₀ ∈ faceSet a b A) :
    IsExposed ℝ (sol a b) (tightSet a b A) := by
  classical
  let := Fintype.ofFinite ι
  intro _
  refine ⟨innerSL ℝ (∑ i ∈ A.toFinset, a i), ?_⟩
  have hl : ∀ y : E, innerSL ℝ (∑ i ∈ A.toFinset, a i) y = ∑ i ∈ A.toFinset, ⟪a i, y⟫ := by
    intro y; rw [innerSL_apply_apply, sum_inner]
  ext x; constructor
  · rintro ⟨hx, hA⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [hl, hl]
    apply Finset.sum_le_sum
    intro i hi
    rw [show ⟪a i, x⟫ = b i from hA (Set.mem_toFinset.1 hi)]
    exact hy i
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun i hi => ?_⟩
    have h1 := hmax x₀ hx₀.1
    rw [hl, hl] at h1
    have h2 : ∀ j ∈ A.toFinset, ⟪a j, x₀⟫ = b j := fun j hj =>
      (hx₀.2 ▸ Set.mem_toFinset.1 hj : j ∈ act a b x₀)
    rw [Finset.sum_congr rfl h2] at h1
    have h3 : ∀ j ∈ A.toFinset, ⟪a j, x⟫ ≤ b j := fun j _ => hx j
    have h4 : ∑ j ∈ A.toFinset, ⟪a j, x⟫ = ∑ j ∈ A.toFinset, b j :=
      le_antisymm (Finset.sum_le_sum h3) h1
    exact (Finset.sum_eq_sum_iff_of_le h3).1 h4 i (Set.mem_toFinset.2 hi)

/-- **Every edge is the closed face of a tight set whose direction space is a line**: the tight
set of the
midpoint of the edge. -/
lemma exists_tight_of_edge [Finite ι] {F : Set E} (hF : IsEdge (sol a b) F) :
    ∃ A : Set ι, finrank ℝ (linCone a A) = 1 ∧ (faceSet a b A).Nonempty ∧ tightSet a b A = F := by
  obtain ⟨hexp, u, v, huv, hFs⟩ := hF
  obtain ⟨m, hm⟩ : ∃ m : E, m = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v := ⟨_, rfl⟩
  have hmF : m ∈ F := by
    rw [hFs, hm]; exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  obtain ⟨l, hl⟩ := hexp ⟨m, hmF⟩
  have hFsol : F ⊆ sol a b := fun y hy => by rw [hl] at hy; exact hy.1
  have hms : m ∈ sol a b := hFsol hmF
  have hmmax : ∀ y ∈ sol a b, l y ≤ l m := by
    have h := hmF; rw [hl] at h; exact h.2
  have hT : tightSet a b (act a b m) = F := by
    apply Subset.antisymm
    · rintro x ⟨hx, hA⟩
      have hw : m - x ∈ tcone (sol a b) m := by
        rw [tcone_sol a b hms]; intro i hi
        rw [inner_sub_right, show ⟪a i, m⟫ = b i from hi, show ⟪a i, x⟫ = b i from hA hi, sub_self]
      obtain ⟨-, t, ht, hmem⟩ := hw
      have h1 := hmmax _ hmem
      rw [map_add, map_smul, map_sub, smul_eq_mul] at h1
      have hle : l m ≤ l x := by
        by_contra hlt
        push Not at hlt
        nlinarith [mul_pos ht (sub_pos.2 hlt)]
      rw [hl]
      exact ⟨hx, fun y hy => (hmmax y hy).trans hle⟩
    · intro x hxF
      refine ⟨hFsol hxF, fun i hi => ?_⟩
      have hi' : ⟪a i, m⟫ = b i := hi
      have hxF' := hxF
      rw [hFs] at hxF'
      obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hxF'
      have hx' : β • u + α • v ∈ sol a b :=
        hFsol (by rw [hFs]; exact ⟨β, α, hβ, hα, by linarith, rfl⟩)
      have e1 := hFsol hxF i
      have e2 := hx' i
      rw [hm, inner_add_right, inner_smul_right, inner_smul_right] at hi'
      rw [inner_add_right, inner_smul_right, inner_smul_right] at e1 e2
      change ⟪a i, α • u + β • v⟫ = b i
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have e3 : (α + β) * (⟪a i, u⟫ + ⟪a i, v⟫) = ⟪a i, u⟫ + ⟪a i, v⟫ := by rw [hab, one_mul]
      apply le_antisymm e1
      nlinarith
  have huT : u ∈ tightSet a b (act a b m) := by rw [hT, hFs]; exact left_mem_segment ℝ u v
  have hvT : v ∈ tightSet a b (act a b m) := by rw [hT, hFs]; exact right_mem_segment ℝ u v
  have hd : v - u ∈ linCone a (act a b m) := by
    intro i hi
    rw [inner_sub_right, show ⟪a i, v⟫ = b i from hvT.2 hi, show ⟪a i, u⟫ = b i from huT.2 hi,
        sub_self]
  refine ⟨act a b m, ?_, ⟨m, hms, rfl⟩, hT⟩
  refine finrank_eq_one_iff'.2 ⟨⟨v - u, hd⟩, ?_, fun w => ?_⟩
  · intro h
    have h' : v - u = 0 := congrArg Subtype.val h
    exact huv (sub_eq_zero.1 h').symm
  · obtain ⟨w, hw⟩ := w
    have hwt : w ∈ tcone (sol a b) m := by
      rw [tcone_sol a b hms]; intro i hi; exact (hw i hi).le
    obtain ⟨-, t, ht, hmem⟩ := hwt
    have hmt : m + t • w ∈ tightSet a b (act a b m) := by
      refine ⟨hmem, fun i hi => ?_⟩
      change ⟪a i, m + t • w⟫ = b i
      rw [inner_add_right, inner_smul_right, hw i hi, mul_zero, add_zero]; exact hi
    rw [hT, hFs] at hmt
    obtain ⟨α, β, hα, hβ, hab, hEq⟩ := hmt
    have hα' : α = 1 - β := by linarith
    have key : t • w = (β - 1 / 2) • (v - u) := by
      have h1 : t • w = α • u + β • v - m := by rw [hEq, add_sub_cancel_left]
      rw [h1, hm, hα']
      module
    refine ⟨(β - 1 / 2) / t, Subtype.ext ?_⟩
    change ((β - 1 / 2) / t) • (v - u) = w
    rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

variable [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)]

/-- **The cone at an edge is the cone of two of its constraints**, with independent normals. The
solid has an
interior point; `A` is the tight set of the point `x`, and its direction space is a line. -/
lemma exists_pair_cone [Finite ι] (hint : (interior (sol a b)).Nonempty) {A : Set ι} {x : E}
    (hx : x ∈ faceSet a b A) (hfin : finrank ℝ (linCone a A) = 1) :
    ∃ p ∈ A, ∃ q ∈ A, LinearIndependent ℝ ![a p, a q] ∧ cone a A = cone a {p, q} := by
  classical
  obtain ⟨z, hz⟩ := hint
  obtain ⟨hxs, hact⟩ := hx
  have hzlt : ∀ i, a i ≠ 0 → ⟪a i, z⟫ < b i := by
    intro i hi
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
    have hn : 0 < ‖a i‖ := norm_pos_iff.2 hi
    have hmem : z + (ε / (2 * ‖a i‖)) • a i ∈ sol a b := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hε hn])
    have h1 := hmem i
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h2 : 0 < ε / (2 * ‖a i‖) * ‖a i‖ ^ 2 := by positivity
    linarith
  have hv0 : ∀ i ∈ A, a i ≠ 0 → ⟪a i, z - x⟫ < 0 := by
    intro i hi hne
    have h1 : ⟪a i, x⟫ = b i := (hact ▸ hi : i ∈ act a b x)
    rw [inner_sub_right, h1]; linarith [hzlt i hne]
  exact cone_eq_pair_of_strict a hfin hv0

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] in
/-- The unit normal of one of the two constraints of an edge is the normal of a facet through the
edge. -/
lemma unit_mem_facetNormals [Finite ι] {A : Set ι} {x u v : E} {p q : ι} (hx : x ∈ faceSet a b A)
    (hp : p ∈ A) (hq : q ∈ A) (hli : LinearIndependent ℝ ![a p, a q]) (hcone : cone a A
        = cone a {p, q})
    (huv : u ≠ v) (hseg : tightSet a b A = segment ℝ u v) :
    (‖a p‖⁻¹ : ℝ) • a p ∈ facetNormals (sol a b) (tightSet a b A) := by
  obtain ⟨hxs, hact⟩ := hx
  have hap : a p ≠ 0 := by simpa using hli.ne_zero 0
  have hn : 0 < ‖a p‖ := norm_pos_iff.2 hap
  have inF : ∀ y ∈ sol a b, ⟪a p, y⟫ = b p → y ∈ faceIn (sol a b) ((‖a p‖⁻¹ : ℝ) • a p) := by
    intro y hy hyp
    refine ⟨hy, fun z hz => ?_⟩
    rw [real_inner_smul_left, real_inner_smul_left, hyp]
    exact mul_le_mul_of_nonneg_left (hz p) (inv_nonneg.2 hn.le)
  refine ⟨norm_smul_inv_norm hap, fun y hy => inF y hy.1 (hy.2 hp), ?_⟩
  intro hcol
  obtain ⟨w, hw1, hw2⟩ := exists_perp_neg hli
  have hwc : w ∈ tcone (sol a b) x := by
    rw [tcone_sol a b hxs, hact, hcone]
    intro i hi
    rcases hi with rfl | rfl
    · exact hw1.le
    · exact hw2.le
  obtain ⟨-, t, ht, hz⟩ := hwc
  have hxp : ⟪a p, x⟫ = b p := (hact ▸ hp : p ∈ act a b x)
  have hxq : ⟪a q, x⟫ = b q := (hact ▸ hq : q ∈ act a b x)
  have huT : u ∈ tightSet a b A := by rw [hseg]; exact left_mem_segment ℝ u v
  have hvT : v ∈ tightSet a b A := by rw [hseg]; exact right_mem_segment ℝ u v
  have huF := inF u huT.1 (huT.2 hp)
  have hvF := inF v hvT.1 (hvT.2 hp)
  have hzF := inF _ hz (by rw [inner_add_right, inner_smul_right, hxp, hw1, mul_zero, add_zero])
  obtain ⟨dir, hdir⟩ := (collinear_iff_of_mem huF).1 hcol
  obtain ⟨r1, hr1⟩ := hdir v hvF
  obtain ⟨r2, hr2⟩ := hdir _ hzF
  rw [vadd_eq_add] at hr1 hr2
  have hr1ne : r1 ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hr1
    exact huv hr1.symm
  have huq : ⟪a q, u⟫ = b q := huT.2 hq
  have e1 : ⟪a q, v⟫ = b q := hvT.2 hq
  rw [hr1, inner_add_right, inner_smul_right, huq] at e1
  have hd0 : ⟪a q, dir⟫ = 0 := by
    have h3 : r1 * ⟪a q, dir⟫ = 0 := by linarith
    exact (mul_eq_zero.1 h3).resolve_left hr1ne
  have e2 := congrArg (fun y => ⟪a q, y⟫) hr2
  simp only [inner_add_right, inner_smul_right, hd0, mul_zero, zero_add, hxq, huq] at e2
  nlinarith [mul_neg_of_pos_of_neg ht hw2]

/-- A facet normal at an edge is the unit normal of one of the two constraints of the edge. -/
lemma eq_of_mem_facetNormals [Finite ι] {A : Set ι} {x : E} {p q : ι} (hx : x ∈ faceSet a b A)
    (hfin : finrank ℝ (linCone a A) = 1) (hp : p ∈ A) (hq : q ∈ A)
    (hli : LinearIndependent ℝ ![a p, a q]) (hcone : cone a A = cone a {p, q}) {n : E}
    (hn : n ∈ facetNormals (sol a b) (tightSet a b A)) :
    n = (‖a p‖⁻¹ : ℝ) • a p ∨ n = (‖a q‖⁻¹ : ℝ) • a q := by
  obtain ⟨hxs, hact⟩ := hx
  obtain ⟨hn1, hsub, hncol⟩ := hn
  have hxA : ∀ i ∈ A, ⟪a i, x⟫ = b i := fun i hi => (hact ▸ hi : i ∈ act a b x)
  have hxF : x ∈ faceIn (sol a b) n := hsub ⟨hxs, hact.ge⟩
  have hdual : ∀ w ∈ cone a A, ⟪n, w⟫ ≤ 0 := by
    intro w hw
    have hwt : w ∈ tcone (sol a b) x := by rw [tcone_sol a b hxs, hact]; exact hw
    obtain ⟨-, t, ht, hz⟩ := hwt
    have h1 := hxF.2 _ hz
    rw [inner_add_right, inner_smul_right] at h1
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos ht hpos]
  have hW := finrank_orthogonal_linCone a A hfin
  have hmem : ∀ i ∈ A, a i ∈ (linCone a A)ᗮ := fun _ => normal_mem_linCone_orthogonal a
  have hnW : n ∈ (linCone a A)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    have h1 := hdual w ((cone_lin a A w).2 hw).1
    have h2 := hdual (-w) ((cone_lin a A w).2 hw).2
    rw [inner_neg_right] at h2
    linarith
  have hspan : Submodule.span ℝ (Set.range ![a p, a q]) = (linCone a A)ᗮ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hmem p hp
      · exact hmem q hq
    · rw [finrank_span_eq_card hli, hW]; rfl
  rw [← hspan, Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hnW
  obtain ⟨α, β, rfl⟩ := hnW
  obtain ⟨wp, hwp1, hwp2⟩ := exists_perp_neg hli
  obtain ⟨wq, hwq1, hwq2⟩ := exists_perp_neg (LinearIndependent.pair_symm_iff.1 hli)
  have hβ : 0 ≤ β := by
    have h := hdual wp (by
      rw [hcone]; intro i hi
      rcases hi with rfl | rfl
      · exact hwp1.le
      · exact hwp2.le)
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hwp1, mul_zero, zero_add] at h
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos_of_neg_of_neg hneg hwp2]
  have hα : 0 ≤ α := by
    have h := hdual wq (by
      rw [hcone]; intro i hi
      rcases hi with rfl | rfl
      · exact hwq2.le
      · exact hwq1.le)
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hwq1, mul_zero, add_zero] at h
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos_of_neg_of_neg hneg hwq2]
  have hprod : α = 0 ∨ β = 0 := by
    by_contra hno
    push Not at hno
    have hα' : 0 < α := lt_of_le_of_ne hα (Ne.symm hno.1)
    have hβ' : 0 < β := lt_of_le_of_ne hβ (Ne.symm hno.2)
    apply hncol
    obtain ⟨d, -, hd⟩ := finrank_eq_one_iff'.1 hfin
    rw [collinear_iff_of_mem hxF]
    refine ⟨(d : E), fun y hy => ?_⟩
    have hp0 : ⟪a p, y - x⟫ ≤ 0 := by rw [inner_sub_right, hxA p hp]; linarith [hy.1 p]
    have hq0 : ⟪a q, y - x⟫ ≤ 0 := by rw [inner_sub_right, hxA q hq]; linarith [hy.1 q]
    have e1 : ⟪α • a p + β • a q, y - x⟫ = 0 := by
      rw [inner_sub_right]; linarith [hy.2 x hxs, hxF.2 y hy.1]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at e1
    have hp1 : ⟪a p, y - x⟫ = 0 := by
      apply le_antisymm hp0
      by_contra h
      push Not at h
      nlinarith [mul_neg_of_pos_of_neg hα' h, mul_nonpos_of_nonneg_of_nonpos hβ'.le hq0]
    have hq1 : ⟪a q, y - x⟫ = 0 := by
      rw [hp1, mul_zero, zero_add] at e1
      exact (mul_eq_zero.1 e1).resolve_left hβ'.ne'
    have hlin : y - x ∈ linCone a A := by
      rw [← cone_lin a A, hcone]
      constructor
      · intro i hi
        rcases hi with rfl | rfl
        · exact hp1.le
        · exact hq1.le
      · intro i hi
        rcases hi with rfl | rfl
        · rw [inner_neg_right, hp1, neg_zero]
        · rw [inner_neg_right, hq1, neg_zero]
    obtain ⟨c, hc⟩ := hd ⟨y - x, hlin⟩
    have hc' : c • (d : E) = y - x := congrArg Subtype.val hc
    exact ⟨c, by rw [vadd_eq_add, hc', sub_add_cancel]⟩
  rcases hprod with h0 | h0
  · right
    subst h0
    rw [zero_smul, zero_add] at hn1 ⊢
    rw [norm_smul, Real.norm_of_nonneg hβ] at hn1
    rw [eq_inv_of_mul_eq_one_left hn1]
  · left
    subst h0
    rw [zero_smul, add_zero] at hn1 ⊢
    rw [norm_smul, Real.norm_of_nonneg hα] at hn1
    rw [eq_inv_of_mul_eq_one_left hn1]

/-- **Exactly two facets pass through an edge**: their outward unit normals are the unit normals
of the two
constraints of `exists_pair_cone`. -/
lemma facetNormals_tightSet [Finite ι] {A : Set ι} {x u v : E} {p q : ι} (hx : x ∈ faceSet a b A)
    (hfin : finrank ℝ (linCone a A) = 1) (hp : p ∈ A) (hq : q ∈ A)
    (hli : LinearIndependent ℝ ![a p, a q]) (hcone : cone a A = cone a {p, q})
    (huv : u ≠ v) (hseg : tightSet a b A = segment ℝ u v) :
    facetNormals (sol a b) (tightSet a b A) = {(‖a p‖⁻¹ : ℝ) • a p, (‖a q‖⁻¹ : ℝ) • a q} := by
  ext n; constructor
  · exact eq_of_mem_facetNormals hx hfin hp hq hli hcone
  · rintro (rfl | rfl)
    · exact unit_mem_facetNormals hx hp hq hli hcone huv hseg
    · exact unit_mem_facetNormals hx hq hp (LinearIndependent.pair_symm_iff.1 hli)
        (by rw [hcone, Set.pair_comm]) huv hseg

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] in
/-- A nonempty active face with a line of common directions has a closed segment as its
closure. Its open segment is contained in the active face. -/
lemma edge_segment_of_tight [Finite ι] (hb : Bornology.IsBounded (sol a b))
    {A : Set ι} {x : E} (hx : x ∈ faceSet a b A) (hfin : finrank ℝ (linCone a A) = 1) :
    ∃ u v : E, u ≠ v ∧ tightSet a b A = segment ℝ u v ∧ openSegment ℝ u v ⊆ faceSet a b A := by
  obtain ⟨d, hd0, hd⟩ := finrank_eq_one_iff'.1 hfin
  have hd0' : (d : E) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hspan : ∀ w ∈ linCone a A, ∃ r : ℝ, w = r • (d : E) := by
    intro w hw
    obtain ⟨c, hc⟩ := hd ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  exact tightSet_eq_segment hb hx hd0' d.2 hspan

private lemma normalized_facets_of_tight [Finite ι]
    (interior_nonempty : (interior (sol a b)).Nonempty) {A : Set ι} {x u v : E}
    (hx : x ∈ faceSet a b A) (rank_one : finrank ℝ (linCone a A) = 1)
    (distinct : u ≠ v) (segment_eq : tightSet a b A = segment ℝ u v) :
    ∃ p q, LinearIndependent ℝ ![a p, a q] ∧ cone a A = cone a {p, q} ∧
      0 < ‖a p‖⁻¹ ∧ 0 < ‖a q‖⁻¹ ∧
      LinearIndependent ℝ ![‖a p‖⁻¹ • a p, ‖a q‖⁻¹ • a q] ∧
      facetNormals (sol a b) (tightSet a b A) = {‖a p‖⁻¹ • a p, ‖a q‖⁻¹ • a q} := by
  obtain ⟨p, hp, q, hq, independent, cone_eq⟩ := exists_pair_cone interior_nonempty hx rank_one
  have hp0 : a p ≠ 0 := by simpa using independent.ne_zero 0
  have hq0 : a q ≠ 0 := by simpa using independent.ne_zero 1
  have hp_pos : 0 < ‖a p‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hp0)
  have hq_pos : 0 < ‖a q‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hq0)
  exact ⟨p, q, independent, cone_eq, hp_pos, hq_pos,
    (LinearIndependent.pair_smul_smul_iff hp_pos.ne'.isUnit hq_pos.ne'.isUnit).2 independent,
    facetNormals_tightSet hx rank_one hp hq independent cone_eq distinct segment_eq⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- The length and angle class computed from an active face agree with its closed edge. -/
lemma edge_measure_and_angle [Finite ι] (hb : Bornology.IsBounded (sol a b))
    (hint : (interior (sol a b)).Nonempty) {A : Set ι} (hfin : finrank ℝ (linCone a A) = 1)
    (hne : (faceSet a b A).Nonempty) :
    (μH[1] (faceSet a b A)).toReal = (μH[1] (tightSet a b A)).toReal ∧
      theta (cone a A) = (Submodule.Quotient.mk (dihedral (sol a b) (tightSet a b A)) : Angle) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨u, v, huv, hseg, hopen⟩ := edge_segment_of_tight hb hx hfin
  obtain ⟨p, q, hli, hcone, hnp, hnq, _, hfac⟩ := normalized_facets_of_tight hint hx hfin huv hseg
  constructor
  · have hfinite : μH[1] (segment ℝ u v) ≠ ⊤ := by
      rw [hausdorffMeasure_segment]
      exact edist_ne_top _ _
    have hsub : faceSet a b A ⊆ segment ℝ u v := hseg ▸ faceSet_subset_tightSet a b A
    have hle := measure_mono (μ := μH[1]) hsub
    rw [hseg]
    apply le_antisymm (ENNReal.toReal_mono hfinite hle)
    have h1 : (μH[1] (segment ℝ u v)).toReal = (μH[1] (openSegment ℝ u v)).toReal := by
      rw [hausdorff_openSegment huv, hausdorffMeasure_segment, edist_dist,
        ENNReal.toReal_ofReal dist_nonneg]
    rw [h1]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top hfinite hle) (measure_mono hopen)
  · rw [hcone, theta_pair a rfl hli, dihedral_eq_of_pair hfac,
      InnerProductGeometry.angle_smul_left_of_pos _ _ hnp,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hnq]

/-- The sets of constraints that give the edges. -/
def edgeSets (a : ι → E) (b : ι → ℝ) : Set (Set ι) :=
  {A | finrank ℝ (linCone a A) = 1 ∧ (faceSet a b A).Nonempty}

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] [MeasurableSpace E] [BorelSpace E] in
lemma bijOn_tightSet [Finite ι] (hb : Bornology.IsBounded (sol a b)) :
    Set.BijOn (tightSet a b) (edgeSets a b) (edges (sol a b)) := by
  refine ⟨fun A hA => ?_, fun A hA B hB h => tightSet_inj hA.2 hB.2 h, fun F hF => ?_⟩
  · obtain ⟨x, hx⟩ := hA.2
    obtain ⟨u, v, distinct, segment_eq, _⟩ := edge_segment_of_tight hb hx hA.1
    exact ⟨isExposed_tightSet hx, u, v, distinct, segment_eq⟩
  · obtain ⟨A, hfin, hne, hT⟩ := exists_tight_of_edge hF
    exact ⟨A, ⟨hfin, hne⟩, hT⟩

/-- The edge sum for a solid given by half-spaces. -/
theorem dehnSet_sol_eq_edge_sum [Finite ι] (hb : Bornology.IsBounded (sol a b))
    (hint : (interior (sol a b)).Nonempty) :
    dehnSet (sol a b) = ∑ᶠ F ∈ edges (sol a b),
      (μH[1] F).toReal ⊗ₜ[ℚ] (Submodule.Quotient.mk (dihedral (sol a b) F) : Angle) := by
  classical
  let := Fintype.ofFinite ι
  let t : Set ι → DehnSpace := fun A => (μH[1] (faceSet a b A)).toReal ⊗ₜ[ℚ] theta (cone a A)
  have hsupp : Function.support t ⊆ edgeSets a b := by
    intro A hA
    by_contra hno
    apply hA
    change (μH[1] (faceSet a b A)).toReal ⊗ₜ[ℚ] theta (cone a A) = 0
    by_cases hfin : finrank ℝ (linCone a A) = 1
    · have he : faceSet a b A = ∅ := Set.not_nonempty_iff_eq_empty.1 (fun h => hno ⟨hfin, h⟩)
      rw [he, measure_empty, ENNReal.toReal_zero, TensorProduct.zero_tmul]
    · unfold theta
      rw [linSpace_cone, ite_eq_right hfin, TensorProduct.tmul_zero]
  have hterm : ∀ A ∈ edgeSets a b, t A = (μH[1] (tightSet a b A)).toReal ⊗ₜ[ℚ]
      (Submodule.Quotient.mk (dihedral (sol a b) (tightSet a b A)) : Angle) := by
    intro A hA
    obtain ⟨hlen, hth⟩ := edge_measure_and_angle hb hint hA.1 hA.2
    change (μH[1] (faceSet a b A)).toReal ⊗ₜ[ℚ] theta (cone a A) = _
    rw [hlen, hth]
  calc dehnSet (sol a b) = ∑ A : Set ι, t A := dehnSet_eq_sum_faceSet a b hb
    _ = ∑ᶠ A, t A := (finsum_eq_sum_of_fintype t).symm
    _ = ∑ᶠ A ∈ (Set.univ : Set (Set ι)), t A := (finsum_mem_univ t).symm
    _ = ∑ᶠ A ∈ edgeSets a b, t A :=
        finsum_mem_inter_support_eq t _ _ (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp])
    _ = _ := finsum_mem_eq_of_bijOn (tightSet a b) (bijOn_tightSet hb) hterm

/-! ### The statements for a convex polytope, with no half-spaces in them -/

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] [MeasurableSpace E] [BorelSpace E] in
/-- A convex polytope has finitely many edges, including when its interior is empty. -/
theorem edges_finite {P : Set E} (hP : IsPoly P) : (edges P).Finite := by
  obtain ⟨_, ι, _, a, b, rfl⟩ := hP
  refine (Set.finite_range (tightSet a b)).subset ?_
  intro F hF
  obtain ⟨A, _, _, equality⟩ := exists_tight_of_edge hF
  exact ⟨A, equality⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exactly two facets pass through every edge of a convex polytope** with interior points;
their outward
unit normals `n₁`, `n₂` are independent, and the interior dihedral angle at the edge is π −
angle(n₁, n₂),
strictly between 0 and π. -/
theorem IsEdge.facetNormals_eq_pair {P F : Set E} (hP : IsPoly P) (hint : (interior P).Nonempty)
    (hF : IsEdge P F) :
    ∃ n₁ n₂ : E, LinearIndependent ℝ ![n₁, n₂] ∧ facetNormals P F = {n₁, n₂} ∧
      dihedral P F = π - InnerProductGeometry.angle n₁ n₂ ∧ 0 < dihedral P F
          ∧ dihedral P F < π := by
  obtain ⟨hb, ι, _, a, b, rfl⟩ := hP
  obtain ⟨A, hfin, hne, rfl⟩ := exists_tight_of_edge hF
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, _, distinct, segment_eq, _⟩ := edge_segment_of_tight hb hx hfin
  obtain ⟨p, q, _, _, _, _, independent, hfac⟩ :=
    normalized_facets_of_tight hint hx hfin distinct segment_eq
  let n₁ := (‖a p‖⁻¹ : ℝ) • a p
  let n₂ := (‖a q‖⁻¹ : ℝ) • a q
  have hli : LinearIndependent ℝ ![n₁, n₂] := independent
  have hd := dihedral_eq_of_pair hfac
  have hpair := LinearIndependent.pair_iff.1 hli
  have h0 : InnerProductGeometry.angle n₁ n₂ ≠ 0 := by
    intro h
    obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h
    have h1 := (hpair r (-1) (by rw [hr, neg_smul, one_smul, add_neg_cancel])).2
    norm_num at h1
  have hpi : InnerProductGeometry.angle n₁ n₂ ≠ π := by
    intro h
    obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h
    have h1 := (hpair r (-1) (by rw [hr, neg_smul, one_smul, add_neg_cancel])).2
    norm_num at h1
  have h0' := lt_of_le_of_ne (InnerProductGeometry.angle_nonneg n₁ n₂) (Ne.symm h0)
  have hpi' := lt_of_le_of_ne (InnerProductGeometry.angle_le_pi n₁ n₂) hpi
  exact ⟨n₁, n₂, hli, hfac, hd, by rw [hd]; linarith, by rw [hd]; linarith⟩

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] in
/-- The length of an edge is the distance of its two ends. -/
theorem IsEdge.length {F : Set E} {u v : E} (hF : F = segment ℝ u v) :
    (μH[1] F).toReal = dist u v := by
  rw [hF, hausdorffMeasure_segment, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- **The set-defined Dehn invariant is the classical edge sum** (Dehn 1901, in Jessen's tensor
form). For
every convex polytope `P` in 3-space (a bounded intersection of finitely many closed half-spaces)
with
interior points, the Dehn invariant `dehnSet P` of study 2, defined from the set `P` by cones of
directions and
sector areas, is the sum over the edges `F` of `P` of

  (length of `F`) ⊗ (interior dihedral angle of `P` at `F`, modulo rational multiples of π).

The edges (`edges`, `IsEdge`: the exposed faces that are segments) and the dihedral angle
(`dihedral`: π minus
the angle between the outward unit normals of the two facets through the edge,
`IsEdge.facetNormals_eq_pair`) are defined from `P` alone. The sum is finite (`edges_finite`). -/
theorem dehnSet_eq_edge_sum {P : Set E} (hP : IsPoly P) (hint : (interior P).Nonempty) :
    dehnSet P = ∑ᶠ F ∈ edges P,
      (μH[1] F).toReal ⊗ₜ[ℚ] (Submodule.Quotient.mk (dihedral P F) : Angle) := by
  obtain ⟨hb, ι, _, a, b, rfl⟩ := hP
  exact dehnSet_sol_eq_edge_sum hb hint

end DehnCanon.Library
