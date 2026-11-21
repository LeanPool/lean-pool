/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.MainTheorem
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


/-!
# Noperts

A *nopert* is a convex polyhedron without the Rupert property. Here a
convex polyhedron is given, as in {name}`IsRupert`
(`MainTheorem.lean`), by a finite set of points {lit}`V` of {lit}`ℝ³`:
the polyhedron is their convex hull. For it to be a genuine solid, the
points must not all lie in one plane ({name}`Coplanar`), which is the
same as the hull having nonempty interior
({lit}`not_coplanar_iff_interior_convexHull_nonempty`).

Also here: `Noperts.det3` and `Noperts.not_coplanar_of_det3_ne_zero`, a
concrete way to check that a set of points is not coplanar (and
`Noperts.affineIndependent_of_det3_ne_zero`).
-/

@[expose] public section

namespace RupertMinimality

open scoped RealInnerProductSpace

/-- A *nopert*: a finite set of points that do not all lie in one plane (so
their convex hull is a genuine solid) and whose convex hull is not Rupert. -/
def IsNopert (V : Finset ℝ³) : Prop :=
  ¬ Coplanar ℝ (V : Set ℝ³) ∧ ¬ IsRupert V

/-- A finite-dimensional convex hull in three-space has interior exactly
when its generating points are not contained in a plane. -/
theorem not_coplanar_iff_interior_convexHull_nonempty (S : Set ℝ³) :
    ¬ Coplanar ℝ S ↔ (interior (convexHull ℝ S)).Nonempty := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [coplanar_empty]
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top, coplanar_iff_finrank_le_two, not_le]
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne]
  have h3 := Submodule.finrank_le (vectorSpan ℝ S)
  rw [finrank_euclideanSpace_fin] at h3
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_euclideanSpace_fin]
    omega
  · intro h
    rw [h, finrank_top, finrank_euclideanSpace_fin]
    norm_num

/-- A nopert's convex hull has nonempty interior. -/
theorem IsNopert.interior_nonempty {V : Finset ℝ³} (h : IsNopert V) :
    (interior (convexHull ℝ (V : Set ℝ³))).Nonempty :=
  (not_coplanar_iff_interior_convexHull_nonempty _).mp h.1

/-- {name}`IsNopert` has a convex hull with nonempty interior and fails Rupert’s property. -/
theorem isNopert_iff (V : Finset ℝ³) :
    IsNopert V ↔ (interior (convexHull ℝ (V : Set ℝ³))).Nonempty ∧ ¬ IsRupert V := by
  rw [IsNopert, not_coplanar_iff_interior_convexHull_nonempty]

namespace Noperts

/-- The determinant of the `3 × 3` matrix with rows `u`, `v`, `w` (the triple
product `u ⬝ (v × w)`). -/
noncomputable def det3 (u v w : ℝ³) : ℝ :=
  Matrix.det !![u 0, u 1, u 2; v 0, v 1, v 2; w 0, w 1, w 2]

/-- A set containing four points `a, b, c, d` that span a tetrahedron of
nonzero volume (`det3 (b - a) (c - a) (d - a) ≠ 0`) is not coplanar. -/
theorem not_coplanar_set_of_det3_ne_zero {S : Set ℝ³} {a b c d : ℝ³}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (h : det3 (b - a) (c - a) (d - a) ≠ 0) : ¬ Coplanar ℝ S := by
  intro hS
  set K := vectorSpan ℝ S
  have hK : K ≠ ⊤ := by
    intro hK
    rw [coplanar_iff_finrank_le_two, show vectorSpan ℝ S = ⊤ from hK, finrank_top,
      finrank_euclideanSpace_fin] at hS
    omega
  obtain ⟨N, hN, hN0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot fun h0 => hK (Submodule.orthogonal_eq_bot_iff.mp h0)
  have hperp : ∀ x ∈ S, ⟪x - a, N⟫ = 0 := fun x hx =>
    Submodule.inner_right_of_mem_orthogonal (vsub_mem_vectorSpan ℝ hx ha) hN
  have e1 := hperp b hb
  have e2 := hperp c hc
  have e3 := hperp d hd
  simp only [PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply, RCLike.inner_apply,
    conj_trivial] at e1 e2 e3
  apply h
  rw [det3, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨WithLp.ofLp N, fun h0 => hN0 (by ext i; simpa using congrFun h0 i), ?_⟩
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    linarith

/-- A finite set containing four points `a, b, c, d` that span a tetrahedron of
nonzero volume (`det3 (b - a) (c - a) (d - a) ≠ 0`) is not coplanar. -/
theorem not_coplanar_of_det3_ne_zero {V : Finset ℝ³} {a b c d : ℝ³}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (h : det3 (b - a) (c - a) (d - a) ≠ 0) : ¬ Coplanar ℝ (V : Set ℝ³) :=
  not_coplanar_set_of_det3_ne_zero (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
    (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hd) h

/-- Four points with `det3 (b - a) (c - a) (d - a) ≠ 0` are affinely independent. -/
theorem affineIndependent_of_det3_ne_zero {a b c d : ℝ³}
    (h : det3 (b - a) (c - a) (d - a) ≠ 0) : AffineIndependent ℝ ![a, b, c, d] := by
  rw [affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (n := 3) (by simp)]
  have hnc := not_coplanar_set_of_det3_ne_zero (S := Set.range ![a, b, c, d])
    ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ h
  rw [coplanar_iff_finrank_le_two, not_le] at hnc
  have := Submodule.finrank_le (vectorSpan ℝ (Set.range ![a, b, c, d]))
  rw [finrank_euclideanSpace_fin] at this
  omega

end Noperts

end RupertMinimality
