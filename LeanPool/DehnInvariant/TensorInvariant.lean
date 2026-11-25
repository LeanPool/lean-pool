/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.NumberTheory.Niven
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
Lean study 1 of the shape-language canon (DICTO, 19 Nov 2026: "Dehn's own theorem in lean could
prove to be the backbone").
Layer (a): the Dehn invariant in its textbook (Jessen) form, D = Σ L ⊗ θ in ℝ ⊗[ℚ] (ℝ / ℚπ), on
edge lists.
Credits: Dehn (1901); Jessen's tensor form; Niven's theorem from Mathlib (Meiburg–Broshi 2025)
gives the key irrationality;
FormalBook ch. 10 (PR #157, merged 6 Oct 2026) proves Hilbert's third problem by the Proofs from
THE BOOK route in an abstract
segment-and-angle model. Not here (layer b, the bridge): that cutting and regluing a real solid
keeps D.
Edge lists are inputs in this layer; only the tetrahedron's dihedral is derived from its face
normals.
-/

@[expose] public section

open Real TensorProduct

namespace DehnCanon.Library

/-- The rational multiples of π, a ℚ-subspace of ℝ. -/
noncomputable def ratPi : Submodule ℚ ℝ := Submodule.span ℚ {π}

/-- Angles modulo rational multiples of π. -/
abbrev Angle := ℝ ⧸ ratPi

/-- Where Dehn invariants live. -/
abbrev DehnSpace := ℝ ⊗[ℚ] Angle

/-- One edge: length `L`, interior dihedral angle `θ`. -/
noncomputable def edgeTerm (L θ : ℝ) : DehnSpace := L ⊗ₜ[ℚ] (Submodule.Quotient.mk θ : Angle)

/-- The Dehn invariant of a solid given by its edges (length, dihedral angle). -/
noncomputable def dehn (E : List (ℝ × ℝ)) : DehnSpace := (E.map fun e => edgeTerm e.1 e.2).sum

lemma mem_ratPi_iff (θ : ℝ) : θ ∈ ratPi ↔ ∃ q : ℚ, θ = q * π := by
  unfold ratPi
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, by rw [Rat.smul_def]⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, by rw [Rat.smul_def]⟩

lemma edgeTerm_rat (L : ℝ) (q : ℚ) : edgeTerm L (q * π) = 0 := by
  have h : (Submodule.Quotient.mk ((q : ℝ) * π) : Angle) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ((mem_ratPi_iff _).2 ⟨q, rfl⟩)
  unfold edgeTerm
  rw [h, TensorProduct.tmul_zero]

lemma edgeTerm_add (a b θ : ℝ) : edgeTerm (a + b) θ = edgeTerm a θ + edgeTerm b θ := by
  unfold edgeTerm; rw [TensorProduct.add_tmul]

/-- An edge of nonzero length at an angle that is not a rational multiple of π contributes a
nonzero term. -/
theorem edgeTerm_ne_zero {L θ : ℝ} (hL : L ≠ 0) (hθ : θ ∉ ratPi) : edgeTerm L θ ≠ 0 := by
  intro h
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℚ ℝ, f L ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL ((Module.forall_dual_apply_eq_zero_iff ℚ L).1 hc)
  have hx : (Submodule.Quotient.mk θ : Angle) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]; exact hθ
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℚ Angle, g (Submodule.Quotient.mk θ) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℚ _).1 hc)
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℚ ℚ).compl₁₂ f g)) h
  simp only [edgeTerm, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      map_zero] at h2
  exact mul_ne_zero hf hg h2

/-- **Rational angles say nothing.** If every dihedral angle is a rational multiple of π, the Dehn
invariant is zero,
whatever the edge lengths. (Cube, rhombic dodecahedron, every cube ∩ rhombic dodecahedron solid
incl. the fair 18-face die.) -/
theorem dehn_eq_zero_of_rational (E : List (ℝ × ℝ)) (h : ∀ e ∈ E, ∃ q : ℚ, e.2 = q * π) : dehn E
    = 0 := by
  unfold dehn
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨q, hq⟩ := h e he
  rw [hq]
  exact edgeTerm_rat _ _

/-- Edges that all share one angle add their lengths. -/
lemma dehn_const (Ls : List ℝ) (θ : ℝ) : dehn (Ls.map fun L => (L, θ)) = edgeTerm Ls.sum θ := by
  induction Ls with
  | nil => simp [dehn, edgeTerm]
  | cons L Ls ih =>
    simp only [dehn, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [edgeTerm_add, ← ih]

/-- The regular tetrahedron's dihedral angle. -/
noncomputable def tetDihedral : ℝ := arccos (1 / 3)

/-- It comes from the face normals: (1,1,1) and (1,−1,−1) are outward normals of two faces of the
tetrahedron
with corners (−1,−1,−1), (−1,1,1), (1,−1,1), (1,1,−1); cos of the angle between them is −1/3, and
the interior
dihedral is π minus that angle. -/
theorem tetDihedral_from_normals :
    let n₁ : Fin 3 → ℝ := ![1, 1, 1]
    let n₂ : Fin 3 → ℝ := ![1, -1, -1]
    π - arccos ((∑ i, n₁ i * n₂ i) / (Real.sqrt (∑ i, n₁ i ^ 2) * Real.sqrt (∑ i, n₂ i ^ 2)))
        = tetDihedral := by
  intro n₁ n₂
  have h1 : (∑ i, n₁ i * n₂ i) = -1 := by simp [n₁, n₂, Fin.sum_univ_three]
  have h2 : (∑ i, n₁ i ^ 2) = 3 := by simp [n₁, Fin.sum_univ_three]; norm_num
  have h3 : (∑ i, n₂ i ^ 2) = 3 := by simp [n₂, Fin.sum_univ_three]; norm_num
  rw [h1, h2, h3, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [show (-1 : ℝ) / 3 = -(1 / 3) by norm_num, Real.arccos_neg]
  unfold tetDihedral; ring

/-- **Dehn's key fact** (via Niven): the tetrahedron's dihedral angle is not a rational multiple
of π. -/
theorem tetDihedral_not_ratPi : tetDihedral ∉ ratPi := by
  rw [mem_ratPi_iff]
  rintro ⟨r, hr⟩
  have hcos : cos tetDihedral = 1 / 3 := by
    unfold tetDihedral; rw [cos_arccos] <;> norm_num
  have hn := niven (θ := tetDihedral) ⟨r, hr⟩ ⟨1 / 3, by rw [hcos]; norm_num⟩
  rw [hcos] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  norm_num at hn

/-- The regular tetrahedron of edge `a`: six edges at the tetrahedral dihedral angle. -/
noncomputable def tetrahedron (a : ℝ) : List (ℝ × ℝ) := (List.replicate 6 a).map fun L => (L,
    tetDihedral)

/-- The cube of edge `s`: twelve edges at π/2. -/
noncomputable def cube (s : ℝ) : List (ℝ × ℝ) := (List.replicate 12 s).map fun L => (L, π / 2)

/-- The rhombic dodecahedron of edge `s`: twenty-four edges at 2π/3. -/
noncomputable def rhombicDodecahedron (s : ℝ) : List (ℝ × ℝ) := (List.replicate 24 s).map fun L =>
    (L, 2 * π / 3)

theorem dehn_cube (s : ℝ) : dehn (cube s) = 0 :=
  dehn_eq_zero_of_rational _ (by
    intro e he; simp only [cube, List.mem_map, List.mem_replicate] at he
    obtain ⟨L, _, rfl⟩ := he; exact ⟨1 / 2, by push_cast; ring⟩)

theorem dehn_rhombicDodecahedron (s : ℝ) : dehn (rhombicDodecahedron s) = 0 :=
  dehn_eq_zero_of_rational _ (by
    intro e he; simp only [rhombicDodecahedron, List.mem_map, List.mem_replicate] at he
    obtain ⟨L, _, rfl⟩ := he; exact ⟨2 / 3, by push_cast; ring⟩)

/-- Every solid whose dihedral angles are among 90°, 120°, 135° (the cube ∩ rhombic dodecahedron
family, the fair
18-face die among them) has Dehn invariant zero, for any edge lengths. -/
theorem dehn_cube_rd_family (E : List (ℝ × ℝ)) (h : ∀ e ∈ E, e.2 = π / 2 ∨ e.2 = 2 * π / 3 ∨ e.2
    = 3 * π / 4) :
    dehn E = 0 :=
  dehn_eq_zero_of_rational E (by
    intro e he
    rcases h e he with h1 | h1 | h1
    · exact ⟨1 / 2, by rw [h1]; push_cast; ring⟩
    · exact ⟨2 / 3, by rw [h1]; push_cast; ring⟩
    · exact ⟨3 / 4, by rw [h1]; push_cast; ring⟩)

theorem dehn_tetrahedron_ne_zero {a : ℝ} (ha : a ≠ 0) : dehn (tetrahedron a) ≠ 0 := by
  unfold tetrahedron
  rw [dehn_const, List.sum_replicate, nsmul_eq_mul]
  exact edgeTerm_ne_zero (by push_cast; exact mul_ne_zero (by norm_num) ha) tetDihedral_not_ratPi

/-- **Dehn's theorem, layer (a):** no regular tetrahedron has the Dehn invariant of any cube.
With layer (b) (D is unchanged by cutting and regluing) this says no regular tetrahedron can be
cut into pieces
that reassemble into a cube. -/
theorem dehn_tetrahedron_ne_cube {a : ℝ} (ha : a ≠ 0) (s : ℝ) : dehn (tetrahedron a)
    ≠ dehn (cube s) := by
  rw [dehn_cube]; exact dehn_tetrahedron_ne_zero ha

end DehnCanon.Library
