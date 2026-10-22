/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-!
# Auxiliary nonmultiples

The determinant method produces an *auxiliary polynomial* `g` for an equation `f`: a nonzero
polynomial that is not a multiple of `f` but vanishes on the points to be counted, so that these
points lie on the intersection of `f = 0` and `g = 0`. Three forms occur, according to how the
points are given.

* `CCDN.IsBoxAuxiliary f g B`: `g` vanishes at every integral zero of `f` in the box of
  radius `B`.
* `CCDN.IsPointAuxiliary f g M z`: `g` is a form of degree `M` vanishing at the finitely many
  points `z i`.
* `CCDN.IsProjectiveAuxiliary f g M B`: `g` is a form of degree `M` vanishing at every rational
  projective zero of `f` of multiplicative height at most `B`.

The degree bound on `g`, which differs from statement to statement, is kept separate.
-/

@[expose] public section

namespace CCDN

open MvPolynomial

/-- `g` is an auxiliary polynomial for the integral affine equation `f` on the box of
radius `B`: it is nonzero, it is not a multiple of `f`, and it vanishes at every integral zero
of `f` all of whose coordinates are at most `B` in absolute value. -/
structure IsBoxAuxiliary {n : ℕ} (f g : MvPolynomial (Fin n) ℤ) (B : ℝ) : Prop where
  /-- The auxiliary polynomial is nonzero. -/
  ne_zero : g ≠ 0
  /-- The auxiliary polynomial is not a multiple of `f`. -/
  not_dvd : ¬ f ∣ g
  /-- The auxiliary polynomial vanishes at every integral zero of `f` in the box of radius
  `B`. -/
  vanishes : ∀ x : IntPoint n, InBox x B → eval x f = 0 → eval x g = 0

/-- Unbundled form of an auxiliary polynomial on a box satisfying a further condition `P`,
typically a degree bound, in the order in which the auxiliary theorems are stated. -/
theorem exists_isBoxAuxiliary_and_iff {n : ℕ} {f : MvPolynomial (Fin n) ℤ} {B : ℝ}
    {P : MvPolynomial (Fin n) ℤ → Prop} :
    (∃ g, IsBoxAuxiliary f g B ∧ P g) ↔ ∃ g, g ≠ 0 ∧ ¬ f ∣ g ∧ P g ∧
      ∀ x : IntPoint n, InBox x B → eval x f = 0 → eval x g = 0 :=
  ⟨fun ⟨g, hg, hP⟩ => ⟨g, hg.1, hg.2, hP, hg.3⟩,
    fun ⟨g, h0, hnd, hP, hz⟩ => ⟨g, ⟨h0, hnd, hz⟩, hP⟩⟩

/-- `g` is a homogeneous auxiliary polynomial of degree `M` for `f` through the points `z`: a
nonzero form of degree `M` that vanishes at every point `z i` but is not a multiple of `f`. -/
structure IsPointAuxiliary {σ R ι : Type*} [CommRing R] (f g : MvPolynomial σ R) (M : ℕ)
    (z : ι → σ → R) : Prop where
  /-- The auxiliary form is nonzero. -/
  ne_zero : g ≠ 0
  /-- The auxiliary form is homogeneous of degree `M`. -/
  isHomogeneous : g.IsHomogeneous M
  /-- The auxiliary form vanishes at every point `z i`. -/
  eval_eq_zero : ∀ i, eval (z i) g = 0
  /-- The auxiliary form is not a multiple of `f`. -/
  not_dvd : ¬ f ∣ g

/-- Unbundled form of `CCDN.IsPointAuxiliary`. -/
theorem isPointAuxiliary_iff {σ R ι : Type*} [CommRing R] {f g : MvPolynomial σ R} {M : ℕ}
    {z : ι → σ → R} : IsPointAuxiliary f g M z ↔
      g ≠ 0 ∧ g.IsHomogeneous M ∧ (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- If there is no auxiliary form of degree `M` through the points `z`, then every form of
degree `M` vanishing at all of them is a multiple of `f`. This is the hypothesis under which the
determinant method bounds the number of points. -/
theorem dvd_of_not_exists_isPointAuxiliary {σ R ι : Type*} [CommRing R]
    {f : MvPolynomial σ R} {M : ℕ} {z : ι → σ → R} (h : ¬ ∃ g, IsPointAuxiliary f g M z)
    (g : MvPolynomial σ R) (hg : g.IsHomogeneous M) (hz : ∀ i, eval (z i) g = 0) : f ∣ g := by
  by_cases hg0 : g = 0
  · simp [hg0]
  · by_contra hnd
    exact h ⟨g, hg0, hg, hz, hnd⟩

/-- `g` is a projective auxiliary form of degree `M` for the integral form `f` at height `B`:
a nonzero form of degree `M`, not a multiple of `f`, whose rational projective zero locus
contains every rational projective zero of `f` of multiplicative height at most `B`. -/
structure IsProjectiveAuxiliary {n : ℕ} (f g : MvPolynomial (Fin (n + 1)) ℤ) (M : ℕ) (B : ℝ) :
    Prop where
  /-- The auxiliary form is nonzero. -/
  ne_zero : g ≠ 0
  /-- The auxiliary form is homogeneous of degree `M`. -/
  isHomogeneous : g.IsHomogeneous M
  /-- The auxiliary form vanishes at every rational projective zero of `f` of multiplicative
  height at most `B`. -/
  vanishes : ∀ x : ProjectivePoint n, x.mulHeight ≤ B →
    x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
    x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)
  /-- The auxiliary form is not a multiple of `f`. -/
  not_dvd : ¬ f ∣ g

end CCDN
