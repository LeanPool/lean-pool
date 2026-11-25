/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.EuclideanSpace
public import LeanPool.DehnInvariant.Simplex
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Separation.CompletelyRegular

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
segments between the corners (`tet_openSegment_iff`); their length is Mathlib's
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

lemma inner_cubeN_eq_zero {p : Fin 3 × Bool} {v : R3} (h : ⟪cubeN p, v⟫ = 0) : v p.1 = 0 := by
  rw [inner_cubeN] at h
  by_cases hb : p.2 = true
  · rwa [ite_eq_left hb] at h
  · rw [ite_eq_right hb] at h; linarith

lemma fin3_cover : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → ∀ m, m = a ∨ m = b ∨ m = c := by decide

/-- Every point of the cube has angle class 0: where two faces meet, the angle is π/2. -/
lemma edgeAngle_cube (s : ℝ) (hs : 0 < s) (x : R3) : edgeAngle (cubeSet s) x = 0 := by
  by_cases hx : x ∈ cubeSet s
  swap
  · exact edgeAngle_of_notMem hx
  change edgeAngle (sol cubeN fun _ => s) x = 0
  rw [edgeAngle_sol _ _ hx]
  set A := act cubeN (fun _ => s) x with hAdef
  by_cases hfin : finrank ℝ (linCone cubeN A) = 1
  swap
  · unfold theta; rw [linSpace_cone, ite_eq_right hfin]
  -- two tight constraints on one axis would be the two opposite faces
  have hcons : ∀ p ∈ A, ∀ q ∈ A, p.1 = q.1 → p = q := by
    rintro ⟨i, b⟩ hp ⟨j, c⟩ hq hij
    have hij' : i = j := hij
    subst hij'
    have hp' : ⟪cubeN (i, b), x⟫ = s := hp
    have hq' : ⟪cubeN (i, c), x⟫ = s := hq
    rw [inner_cubeN] at hp' hq'
    cases b <;> cases c <;> simp at hp' hq' ⊢ <;> linarith
  have hind : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, p ≠ q → p ≠ r → q ≠ r →
      ∀ v : R3, ⟪cubeN p, v⟫ = 0 → ⟪cubeN q, v⟫ = 0 → ⟪cubeN r, v⟫ = 0 → v = 0 := by
    intro p hp q hq r hr hpq hpr hqr v h1 h2 h3
    have e1 := inner_cubeN_eq_zero h1
    have e2 := inner_cubeN_eq_zero h2
    have e3 := inner_cubeN_eq_zero h3
    ext m
    change v m = 0
    rcases fin3_cover p.1 q.1 r.1 (fun h => hpq (hcons p hp q hq h)) (fun h => hpr (hcons p hp r
        hr h))
      (fun h => hqr (hcons q hq r hr h)) m with rfl | rfl | rfl
    · exact e1
    · exact e2
    · exact e3
  obtain ⟨p, q, hpq, hA⟩ := pair_of_finrank_one cubeN hfin hind
  have hpA : p ∈ A := by rw [hA]; exact mem_insert _ _
  have hqA : q ∈ A := by rw [hA]; exact mem_insert_of_mem _ rfl
  have hax : p.1 ≠ q.1 := fun h => hpq (hcons p hpA q hqA h)
  have i12 : ⟪cubeN p, cubeN q⟫ = 0 := by
    rw [inner_cubeN, cubeN_apply, ite_eq_right hax]; simp
  have i11 : ⟪cubeN p, cubeN p⟫ = 1 := by
    rw [inner_cubeN, cubeN_apply, ite_eq_left rfl]
    by_cases hb : p.2 = true <;> simp [hb]
  have i22 : ⟪cubeN q, cubeN q⟫ = 1 := by
    rw [inner_cubeN, cubeN_apply, ite_eq_left rfl]
    by_cases hb : q.2 = true <;> simp [hb]
  have hli : LinearIndependent ℝ ![cubeN p, cubeN q] :=
    linIndep_pair_of_gram (by rw [i11, i22, i12]; norm_num)
  rw [theta_pair cubeN hA hli, (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).1
      i12,
    Submodule.Quotient.mk_eq_zero, mem_ratPi_iff]
  exact ⟨1 / 2, by push_cast; ring⟩

/-- **Gap 2 of study 2, closed (cube).** The Dehn invariant of the cube `[-s, s]³`, as a set, is
zero. -/
theorem dehnSet_cube (s : ℝ) (hs : 0 < s) : dehnSet (cubeSet s) = 0 := by
  rw [dehnSet_eq_single (cubeSet s) 0 (fun x => Or.inl (edgeAngle_cube s hs x)),
      TensorProduct.tmul_zero]

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

/-- Three distinct face normals have no common perpendicular direction. -/
theorem isPoly_tetra : IsPoly tetraSet := regularTetrahedronData.isPoly

lemma tet_three {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {v : R3}
    (hi : ⟪tetN i, v⟫ = 0) (hj : ⟪tetN j, v⟫ = 0) (hk : ⟪tetN k, v⟫ = 0) : v = 0 :=
  regularTetrahedronData.three hij hik hjk hi hj hk

/-- Two tight faces describe the open segment joining the opposite corners. -/
lemma tet_openSegment_iff {k l : Fin 4} (hkl : k ≠ l) (x : R3) :
    x ∈ openSegment ℝ (-tetN k) (-tetN l) ↔
      x ∈ tetraSet ∧ act tetN (fun _ => 1) x = ({k, l}ᶜ : Set (Fin 4)) :=
  regularTetrahedronData.openSegment_iff hkl x

/-- The angle class where two faces of the tetrahedron meet: arccos(1/3). -/
lemma tet_theta {A : Set (Fin 4)} {i j : Fin 4} (hij : i ≠ j) (hA : A = {i, j}) :
    theta (cone tetN A) = (Submodule.Quotient.mk tetDihedral : Angle) := by
  have hli : LinearIndependent ℝ ![tetN i, tetN j] :=
    linIndep_pair_of_gram (by
      rw [tetN_inner, tetN_inner, tetN_inner, ite_eq_left rfl, ite_eq_left rfl,
          ite_eq_right hij]; norm_num)
  rw [theta_pair tetN hA hli]
  congr 1
  unfold InnerProductGeometry.angle tetDihedral
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, tetN_inner, tetN_inner, tetN_inner,
      ite_eq_left rfl,
    ite_eq_left rfl, ite_eq_right hij, Real.mul_self_sqrt (by norm_num),
    show (-1 : ℝ) / 3 = -(1 / 3) by norm_num, Real.arccos_neg]
  ring

lemma tet_nonempty_fin4 : Nonempty (Fin 4) := ⟨0⟩

/-- At a point of the tetrahedron whose tight faces have a line as common direction space, exactly
two faces
are tight. -/
lemma tet_pair {x : R3} (hfin : finrank ℝ (linCone tetN (act tetN (fun _ => 1) x)) = 1) :
    ∃ i j, i ≠ j ∧ act tetN (fun _ => 1) x = {i, j} :=
  pair_of_finrank_one tetN hfin
    (fun _ _ _ _ _ _ hij hik hjk _ hi hj hk => tet_three hij hik hjk hi hj hk)

/-- The angle class of the tetrahedron is arccos(1/3) or 0 at every point. -/
lemma edgeAngle_tetra_cases (x : R3) :
    edgeAngle tetraSet x = (Submodule.Quotient.mk tetDihedral : Angle) ∨ edgeAngle tetraSet x
        = 0 := by
  by_cases hx : x ∈ tetraSet
  swap
  · exact Or.inr (edgeAngle_of_notMem hx)
  have he : edgeAngle tetraSet x = theta (cone tetN (act tetN (fun _ => 1) x))
      := edgeAngle_sol _ _ hx
  rw [he]
  by_cases hfin : finrank ℝ (linCone tetN (act tetN (fun _ => 1) x)) = 1
  · obtain ⟨i, j, hij, hA⟩ := tet_pair hfin
    exact Or.inl (tet_theta hij hA)
  · right; unfold theta; rw [linSpace_cone, ite_eq_right hfin]

lemma tetDihedral_class_ne_zero : (Submodule.Quotient.mk tetDihedral : Angle) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]; exact tetDihedral_not_ratPi

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
theorem tetra_not_scissorsCongruent_cube (s : ℝ) (hs : 0 < s) :
    ¬ ScissorsCongruent tetraSet (cubeSet s) := by
  apply not_scissorsCongruent_of_dehnSet_ne isPoly_tetra (isPoly_cube s)
  rw [dehnSet_tetra, dehnSet_cube s hs]
  exact dehn_tetrahedron_ne_zero (by positivity)

end DehnCanon.Library
