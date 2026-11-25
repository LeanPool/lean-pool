/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.Dissection
public import LeanPool.DehnInvariant.EuclideanSpace
public import LeanPool.DehnInvariant.RationalAngles
public import LeanPool.DehnInvariant.Simplex
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
Lean study 3 of the shape-language canon (DICTO, 19 Nov 2026), part J: the cube and the regular
tetrahedron.

With the angle evaluation of part I (`wedgeAngle_two_planes`) this file evaluates the set
invariant `dehnSet`
of study 2 on the two solids of Dehn's theorem, closing gaps 2 and 3 of study 2:

* `dehnSet_cube`: the Dehn invariant of the cube `[-s, s]³` is zero (every edge angle is π/2).
* `dehnSet_tetra`: the Dehn invariant of the regular tetrahedron with corners (−1,−1,−1),
  (1,1,−1), (1,−1,1),
  (−1,1,1) is study 1's value for six edges of length 2√2 at arccos(1/3).
* `tetra_not_scissorsCongruent_cube` (**Dehn's theorem**): the regular tetrahedron is not scissors
  congruent to
  any cube.

Method. At a point of a polytope the angle class is read off from the constraints that hold with
equality
there (`edgeAngle_sol`, study 2). If their common direction space is a line, then in both solids
exactly two
constraints are tight (`pair_of_finrank_one`), and the angle is π minus the angle between the two
normals
(`theta_pair`, from part I). For the tetrahedron the points with two tight constraints are the six
open
segments between the corners (`IsTetraData.openSegment_iff`); their length is Mathlib's
`MeasureTheory.hausdorffMeasure_segment`.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-- Outward face normals of the regular tetrahedron with corners (−1,−1,−1), (1,1,−1), (1,−1,1),
(−1,1,1). -/
def tetN : Fin 4 → R3 := ![!₂[1, 1, 1], !₂[-1, -1, 1], !₂[-1, 1, -1], !₂[1, -1, -1]]

/-- The regular tetrahedron with corners (−1,−1,−1), (1,1,−1), (1,−1,1), (−1,1,1) (edge 2√2). -/
noncomputable def tetraSet : Set R3 := sol tetN (fun _ => 1)

/-- Outward face normals of a cube: ± the three coordinate directions. -/
noncomputable def cubeN : Fin 3 × Bool → R3 :=
  fun p => if p.2 then EuclideanSpace.single p.1 1 else -EuclideanSpace.single p.1 1

/-- The cube `[-s, s]³` (edge 2s). -/
noncomputable def cubeSet (s : ℝ) : Set R3 := sol cubeN (fun _ => s)

theorem isPoly_cube (s : ℝ) : IsPoly (cubeSet s) := by
  refine ⟨bounded_of_coords s (fun x hx i => ?_), Fin 3 × Bool, inferInstance, cubeN, _, rfl⟩
  have h1 : ⟪(EuclideanSpace.single i (1 : ℝ) : R3), x⟫ ≤ s := hx (i, true)
  have h2 : ⟪(-EuclideanSpace.single i (1 : ℝ) : R3), x⟫ ≤ s := hx (i, false)
  rw [inner_neg_left] at h2
  rw [EuclideanSpace.inner_single_left] at h1 h2
  simp only [map_one, one_mul] at h1 h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### The cube -/

lemma cubeN_apply (p : Fin 3 × Bool) (m : Fin 3) :
    cubeN p m = if m = p.1 then (if p.2 then 1 else -1) else 0 := by
  unfold cubeN
  by_cases hb : p.2 = true <;> by_cases hm : m = p.1 <;> simp [hb, hm]

lemma inner_cubeN (p : Fin 3 × Bool) (v : R3) :
    ⟪cubeN p, v⟫ = if p.2 then v p.1 else -v p.1 := by
  unfold cubeN
  by_cases hb : p.2 = true
  · rw [ite_eq_left hb, ite_eq_left hb, EuclideanSpace.inner_single_left]; simp
  · rw [ite_eq_right hb, ite_eq_right hb, inner_neg_left, EuclideanSpace.inner_single_left]; simp

lemma cubeN_inner_self (p : Fin 3 × Bool) : ⟪cubeN p, cubeN p⟫ = 1 := by
  rw [inner_cubeN, cubeN_apply, ite_eq_left rfl]
  cases p.2 <;> norm_num

lemma cubeN_ne_zero (p : Fin 3 × Bool) : cubeN p ≠ 0 := by
  intro zero
  have one := cubeN_inner_self p
  rw [zero, inner_zero_left] at one
  exact zero_ne_one one

lemma cubeN_angle (p q : Fin 3 × Bool) :
    InnerProductGeometry.angle (cubeN p) (cubeN q) ∈ ratPi := by
  have gram : ⟪cubeN p, cubeN q⟫ ^ 2 = if p.1 = q.1 then 1 else 0 := by
    rw [inner_cubeN, cubeN_apply]
    by_cases same : p.1 = q.1 <;> cases p.2 <;> cases q.2 <;> norm_num [same]
  by_cases same : p.1 = q.1
  · apply angle_mem_ratPi_of_gram (cubeN_ne_zero p) (cubeN_ne_zero q) (k := 4) (by decide)
    rw [gram, ite_eq_left same, cubeN_inner_self, cubeN_inner_self]
    norm_num
  · apply angle_mem_ratPi_of_gram (cubeN_ne_zero p) (cubeN_ne_zero q) (k := 0) (by decide)
    rw [gram, ite_eq_right same]
    norm_num

/-- Every point of the cube has angle class zero. -/
lemma edgeAngle_cube (s : ℝ) (x : R3) : edgeAngle (cubeSet s) x = 0 := by
  by_cases hx : x ∈ cubeSet s
  · rw [show edgeAngle (cubeSet s) x = _ from edgeAngle_sol _ _ hx]
    exact theta_cone_eq_zero_of_rational cubeN _ cubeN_ne_zero cubeN_angle
  · exact edgeAngle_of_notMem hx

/-- The Dehn invariant of the cube is zero for every offset. -/
theorem dehnSet_cube (s : ℝ) : dehnSet (cubeSet s) = 0 :=
  dehnSet_sol_eq_zero_of_rational cubeN (fun _ => s) cubeN_ne_zero cubeN_angle

/-! ### The regular tetrahedron -/

/-- The Gram matrix of the four outward normals. -/
lemma tetN_inner (k l : Fin 4) : ⟪tetN k, tetN l⟫ = if k = l then 3 else -1 := by
  fin_cases k <;> fin_cases l <;>
    norm_num [tetN, inner3, EuclideanSpace.norm_eq, Real.sq_sqrt, Fin.sum_univ_three]

lemma tet_sum (v : R3) : ⟪tetN 0, v⟫ + ⟪tetN 1, v⟫ + ⟪tetN 2, v⟫ + ⟪tetN 3, v⟫ = 0 := by
  simp [tetN, inner3]; ring

lemma tet_inj {v : R3} (h : ∀ m, ⟪tetN m, v⟫ = 0) : v = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [tetN, inner3] at h0 h1 h2
  ext m
  change v m = 0
  fin_cases m
  · change v 0 = 0; linarith
  · change v 1 = 0; linarith
  · change v 2 = 0; linarith

/-- The face functionals of the regular tetrahedron give its barycentric coordinates. -/
theorem regularTetrahedronData :
    IsTetraData tetN (fun m => -tetN m) (fun _ => 1) (fun _ => 1 / 4) where
  w_pos _ := by norm_num
  delta m k := by
    rw [inner_neg_right, tetN_inner]
    split_ifs <;> norm_num
  sum_one x := by
    simp only [Fin.sum_univ_four]
    linarith [tet_sum x]
  rebuild x := by
    apply sub_eq_zero.mp
    apply tet_inj
    intro m
    rw [inner_sub_right, inner_sum]
    fin_cases m <;>
      norm_num [Fin.sum_univ_four, inner_smul_right, inner_neg_right, tetN_inner] <;>
      linarith [tet_sum x]

/-- The regular tetrahedron is a bounded intersection of its four half-spaces. -/
theorem isPoly_tetra : IsPoly tetraSet := regularTetrahedronData.isPoly

/-- The angle class where two faces of the tetrahedron meet: arccos(1/3). -/
lemma tet_theta {A : Set (Fin 4)} {i j : Fin 4} (hij : i ≠ j) (hA : A = {i, j}) :
    theta (cone tetN A) = (Submodule.Quotient.mk tetDihedral : Angle) := by
  rw [theta_pair_of_gram tetN hA (X := 3) (Y := 3) (d := 1) (by norm_num)
    (by rw [tetN_inner, ite_eq_left rfl]) (by rw [tetN_inner, ite_eq_left rfl])
    (by rw [tetN_inner, ite_eq_right hij]) (by norm_num)]
  unfold tetDihedral
  rw [← sq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]

/-- **Gap 3 of study 2, closed (tetrahedron).** The Dehn invariant of the regular tetrahedron with
corners
(−1,−1,−1), (1,1,−1), (1,−1,1), (−1,1,1), as a set, is study 1's edge-list value for six edges of
length 2√2
at arccos(1/3). -/
theorem dehnSet_tetra : dehnSet tetraSet = dehn (tetrahedron (2 * √2)) := by
  change dehnSet (sol tetN (fun _ => 1)) = _
  rw [regularTetrahedronData.dehnSet_eq]
  have length {k l : Fin 4} (distinct : k ≠ l) : dist (-tetN k) (-tetN l) = 2 * √2 := by
    rw [dist_eq_norm, norm_eq_sqrt_real_inner]
    have square : ⟪-tetN k - -tetN l, -tetN k - -tetN l⟫ = 8 := by
      simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, tetN_inner,
        ite_eq_right distinct, ite_eq_right distinct.symm, ite_true]
      norm_num
    rw [square, show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have terms : ∀ q ∈ tetPairs,
      dist (-tetN q.1) (-tetN q.2) ⊗ₜ[ℚ] theta (cone tetN ({q.1, q.2}ᶜ : Set (Fin 4))) =
        (2 * √2 : ℝ) ⊗ₜ[ℚ] (Submodule.Quotient.mk tetDihedral : Angle) := by
    intro q hq
    have ordered : q.1 < q.2 := (Finset.mem_filter.1 hq).2
    obtain ⟨i, j, distinct, complementary⟩ := fin4_compl_pair q.1 q.2 ordered.ne
    rw [length ordered.ne, tet_theta distinct (compl_pair_eq complementary)]
  rw [Finset.sum_congr rfl terms, Finset.sum_const, tetPairs_card]
  unfold tetrahedron
  rw [dehn_const, List.sum_replicate]
  rfl

/-- **Dehn's theorem.** The regular tetrahedron is not scissors congruent to any cube: it cannot
be cut into
finitely many convex polytopes that, moved rigidly, fill a cube. -/
theorem tetra_not_scissorsCongruent_cube (s : ℝ) :
    ¬ ScissorsCongruent tetraSet (cubeSet s) := by
  apply not_scissorsCongruent_of_dehnSet_ne isPoly_tetra (isPoly_cube s)
  rw [dehnSet_tetra, dehnSet_cube s]
  exact dehn_tetrahedron_ne_zero (by positivity)

end DehnCanon.Library
