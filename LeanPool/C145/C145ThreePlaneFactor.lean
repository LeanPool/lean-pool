/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Concrete ordinary three-plane factor interface for C145.

The indexing is z = X 0, x = X 1, y = X 2. The factors have the exact
DRE4/DRE6 signs. This module starts from a polynomial plane identity;
it does not yet construct a response numerator or prove a tensor kernel.
-/

@[expose] public section

noncomputable section

namespace C145.ThreePlane

open MvPolynomial
open scoped BigOperators

/-- The real polynomial ring in the three variables of the plane-factor argument. -/
abbrev P3 := MvPolynomial (Fin 3) ℝ
/-- The real polynomial ring in the two variables remaining on a plane. -/
abbrev P2 := MvPolynomial (Fin 2) ℝ

/-- The variable in coordinate zero of the three-variable polynomial ring. -/
def z : P3 := X 0
/-- The variable in coordinate one of the three-variable polynomial ring. -/
def x : P3 := X 1
/-- The variable in coordinate two of the three-variable polynomial ring. -/
def y : P3 := X 2

/-- The linear form vanishing on the plane where the first two named variables sum to the third. -/
def Lz : P3 := x + y - z
/-- The linear form whose zero plane is given by the equation `x + z = y`. -/
def Ly : P3 := x + z - y
/-- The linear form whose zero plane is given by the equation `y + z = x`. -/
def Lx : P3 := y + z - x
/-- The product of the three defining linear forms. -/
def Xi : P3 := Lz * Ly * Lx

/-- Full coordinate symmetry, including the output coordinate. -/
def SymPoly (F : P3) : Prop :=
  ∀ e : Equiv.Perm (Fin 3), rename e F = F

/-- The variable in coordinate zero of the two-variable polynomial ring. -/
def u : P2 := X 0
/-- The variable in coordinate one of the two-variable polynomial ring. -/
def v : P2 := X 1
/-- The sum of the two retained plane variables. -/
def q : P2 := u + v

/-- z = x+y, with the surviving variables x=u, y=v. -/
def rhoZ : P3 →+* P2 := eval₂Hom C ![q, u, v]
/-- y = x+z, with the surviving variables x=u, z=v. -/
def rhoY : P3 →+* P2 := eval₂Hom C ![v, u, q]
/-- x = y+z, with the surviving variables z=u, y=v. -/
def rhoX : P3 →+* P2 := eval₂Hom C ![u, q, v]

/-- The equivalence viewing a three-variable polynomial as a polynomial in one distinguished
variable. -/
def phi : P3 ≃ₐ[ℝ] Polynomial P2 := finSuccEquiv ℝ 2
private def sy : Equiv.Perm (Fin 3) := Equiv.swap 0 2
private def sx : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private theorem phi_z : phi z = Polynomial.X :=
  finSuccEquiv_X_zero

private theorem phi_x : phi x = Polynomial.C u := by
  simpa only [phi, x, u, Fin.succ_zero_eq_one] using
    (finSuccEquiv_X_succ (R := ℝ) (n := 2) (j := 0))

private theorem phi_y : phi y = Polynomial.C v := by
  simpa only [phi, y, v, Fin.succ_one_eq_two] using
    (finSuccEquiv_X_succ (R := ℝ) (n := 2) (j := 1))

/-- Explicit generator bridge; the coefficient ring here is P2, not ℝ. -/
theorem rhoZ_eq_eval_finSucc (F : P3) :
    rhoZ F = Polynomial.eval q (phi F) := by
  have hh : rhoZ = (Polynomial.evalRingHom q).comp
      (phi : P3 →+* Polynomial P2) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rhoZ, phi, finSuccEquiv_apply]
    · intro i
      fin_cases i
      · change rhoZ z = Polynomial.eval q (phi z)
        rw [phi_z]
        simp [rhoZ, z]
      · change rhoZ x = Polynomial.eval q (phi x)
        rw [phi_x]
        simp [rhoZ, x]
      · change rhoZ y = Polynomial.eval q (phi y)
        rw [phi_y]
        simp [rhoZ, y]
  exact congrArg (fun h : P3 →+* P2 => h F) hh

private theorem phi_Lz : phi Lz = -(Polynomial.X - Polynomial.C q) := by
  rw [Lz, map_sub, map_add, phi_x, phi_y, phi_z]
  simp only [q, map_add]
  ring

theorem rhoZ_Lz : rhoZ Lz = 0 := by
  simp [rhoZ, Lz, x, y, z, q, u, v]

theorem rhoY_Ly : rhoY Ly = 0 := by
  simp [rhoY, Ly, x, y, z, q, u, v]

theorem rhoX_Lx : rhoX Lx = 0 := by
  simp [rhoX, Lx, x, y, z, q, u, v]; ring

/-- The installed univariate root theorem supplies the first actual divisor. -/
theorem plane_factor_z (F : P3) : rhoZ F = 0 ↔ Lz ∣ F := by
  constructor
  · intro h
    have hr : Polynomial.IsRoot (phi F) q := by
      change Polynomial.eval q (phi F) = 0
      rw [← rhoZ_eq_eval_finSucc]
      exact h
    obtain ⟨A, hA⟩ := Polynomial.dvd_iff_isRoot.mpr hr
    refine ⟨phi.symm (-A), ?_⟩
    apply phi.injective
    rw [map_mul, phi.apply_symm_apply, phi_Lz, hA]
    ring
  · rintro ⟨A, rfl⟩
    rw [map_mul, rhoZ_Lz, zero_mul]

private theorem renameY_twice (F : P3) : rename sy (rename sy F) = F := by
  rw [rename_rename]
  have hh : (sy : Fin 3 → Fin 3) ∘ sy = id := by
    funext i
    exact Equiv.swap_apply_self 0 2 i
  rw [hh, rename_id_apply]

private theorem renameX_twice (F : P3) : rename sx (rename sx F) = F := by
  rw [rename_rename]
  have hh : (sx : Fin 3 → Fin 3) ∘ sx = id := by
    funext i
    exact Equiv.swap_apply_self 0 1 i
  rw [hh, rename_id_apply]

private theorem renameY_Lz : rename sy Lz = Ly := by
  norm_num [sy, Lz, Ly, x, y, z, Equiv.swap_apply_def]

private theorem renameX_Lz : rename sx Lz = Lx := by
  norm_num [sx, Lz, Lx, x, y, z, Equiv.swap_apply_def]; ring

private theorem rhoY_via_swap (F : P3) : rhoY F = rhoZ (rename sy F) := by
  rw [rhoZ, eval₂Hom_rename]
  have hh : (![q, u, v] : Fin 3 → P2) ∘ sy = ![v, u, q] := by
    funext i
    fin_cases i <;> norm_num [sy, Equiv.swap_apply_def]
  rw [hh]
  rfl

private theorem rhoX_via_swap (F : P3) : rhoX F = rhoZ (rename sx F) := by
  rw [rhoZ, eval₂Hom_rename]
  have hh : (![q, u, v] : Fin 3 → P2) ∘ sx = ![u, q, v] := by
    funext i
    fin_cases i <;> norm_num [sx, Equiv.swap_apply_def]
  rw [hh]
  rfl

theorem plane_factor_y (F : P3) : rhoY F = 0 ↔ Ly ∣ F := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := (plane_factor_z (rename sy F)).mp
      ((rhoY_via_swap F) ▸ h)
    refine ⟨rename sy A, ?_⟩
    have hh := congrArg (fun G : P3 => rename sy G) hA
    simpa only [map_mul, renameY_twice, renameY_Lz] using hh
  · rintro ⟨A, rfl⟩
    rw [map_mul, rhoY_Ly, zero_mul]

theorem plane_factor_x (F : P3) : rhoX F = 0 ↔ Lx ∣ F := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := (plane_factor_z (rename sx F)).mp
      ((rhoX_via_swap F) ▸ h)
    refine ⟨rename sx A, ?_⟩
    have hh := congrArg (fun G : P3 => rename sx G) hA
    simpa only [map_mul, renameX_twice, renameX_Lz] using hh
  · rintro ⟨A, rfl⟩
    rw [map_mul, rhoX_Lx, zero_mul]

/-- Full symmetry derives both unobserved plane identities. -/
theorem all_plane_identities {F : P3} (hs : SymPoly F) (hz : rhoZ F = 0) :
    rhoY F = 0 ∧ rhoX F = 0 := by
  constructor
  · rw [rhoY_via_swap, hs sy]
    exact hz
  · rw [rhoX_via_swap, hs sx]
    exact hz

theorem all_oriented_divisors {F : P3} (hs : SymPoly F) (hz : rhoZ F = 0) :
    Lz ∣ F ∧ Ly ∣ F ∧ Lx ∣ F := by
  obtain ⟨hy, hx⟩ := all_plane_identities hs hz
  exact ⟨(plane_factor_z F).mp hz, (plane_factor_y F).mp hy,
    (plane_factor_x F).mp hx⟩

/-- Exact off-plane images; these are the nonzero cancellation factors. -/
theorem off_plane_images :
    rhoY Lz = 2 * u ∧ rhoX Lz = 2 * v ∧ rhoX Ly = 2 * u := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [rhoY, rhoX, Lz, Ly, x, y, z, q, u, v] <;> ring

private theorem two_u_ne : (2 : P2) * u ≠ 0 := by
  intro h
  have hh := congrArg (fun G : P2 => MvPolynomial.eval (fun _ => (1 : ℝ)) G) h
  norm_num [u] at hh

private theorem two_v_ne : (2 : P2) * v ≠ 0 := by
  intro h
  have hh := congrArg (fun G : P2 => MvPolynomial.eval (fun _ => (1 : ℝ)) G) h
  norm_num [v] at hh

/-- Two domain cancellations extract the product; no Bezout premise is used. -/
theorem xi_dvd {F : P3} (hs : SymPoly F) (hz : rhoZ F = 0) : Xi ∣ F := by
  obtain ⟨hy, hx⟩ := all_plane_identities hs hz
  obtain ⟨A, hA⟩ := (plane_factor_z F).mp hz
  obtain ⟨hyz, hxz, hxy⟩ := off_plane_images
  have hAy : rhoY A = 0 := by
    rw [hA, map_mul, hyz] at hy
    exact (mul_eq_zero.mp hy).resolve_left two_u_ne
  obtain ⟨B, hB⟩ := (plane_factor_y A).mp hAy
  have hBx : rhoX B = 0 := by
    rw [hA, hB, map_mul, map_mul, hxz, hxy, ← mul_assoc] at hx
    exact (mul_eq_zero.mp hx).resolve_left (mul_ne_zero two_v_ne two_u_ne)
  obtain ⟨R, hR⟩ := (plane_factor_x B).mp hBx
  refine ⟨R, ?_⟩
  rw [hA, hB, hR, Xi]
  ring

private theorem linear_degree_le (a b c i : Fin 3) :
    degreeOf i (X a + X b - X c : P3) ≤ 1 := by
  have hX (j : Fin 3) : degreeOf i (X j : P3) ≤ 1 := by
    by_cases h : i = j <;> simp [degreeOf_X, h]
  exact (degreeOf_sub_le i _ _).trans
    (max_le ((degreeOf_add_le i _ _).trans (max_le (hX a) (hX b))) (hX c))

private theorem one_le_degree_of_coeff {F : P3} (i : Fin 3)
    (h : F.coeff (Finsupp.single i 1) ≠ 0) : 1 ≤ degreeOf i F := by
  simpa using monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr h)

theorem degree_Lz (i : Fin 3) : degreeOf i Lz = 1 := by
  apply Nat.le_antisymm (linear_degree_le 1 2 0 i)
  apply one_le_degree_of_coeff
  fin_cases i <;>
    norm_num [Lz, x, y, z, AddMonoidAlgebra.coeff_add, MvPolynomial.coeff_sub, coeff_X,
      Finsupp.single_eq_single_iff]

theorem degree_Ly (i : Fin 3) : degreeOf i Ly = 1 := by
  apply Nat.le_antisymm (linear_degree_le 1 0 2 i)
  apply one_le_degree_of_coeff
  fin_cases i <;>
    norm_num [Ly, x, y, z, AddMonoidAlgebra.coeff_add, MvPolynomial.coeff_sub, coeff_X,
      Finsupp.single_eq_single_iff]

theorem degree_Lx (i : Fin 3) : degreeOf i Lx = 1 := by
  apply Nat.le_antisymm (linear_degree_le 2 0 1 i)
  apply one_le_degree_of_coeff
  fin_cases i <;>
    norm_num [Lx, x, y, z, AddMonoidAlgebra.coeff_add, MvPolynomial.coeff_sub, coeff_X,
      Finsupp.single_eq_single_iff]

theorem Lz_ne : Lz ≠ 0 := ne_zero_of_degreeOf_ne_zero (by rw [degree_Lz 0]; decide)
theorem Ly_ne : Ly ≠ 0 := ne_zero_of_degreeOf_ne_zero (by rw [degree_Ly 0]; decide)
theorem Lx_ne : Lx ≠ 0 := ne_zero_of_degreeOf_ne_zero (by rw [degree_Lx 0]; decide)

theorem xi_ne : Xi ≠ 0 := mul_ne_zero (mul_ne_zero Lz_ne Ly_ne) Lx_ne

/-- Coordinate degree three is proved separately for every coordinate. -/
theorem xi_degree (i : Fin 3) : degreeOf i Xi = 3 := by
  rw [Xi, degreeOf_mul_eq (mul_ne_zero Lz_ne Ly_ne) Lx_ne,
    degreeOf_mul_eq Lz_ne Ly_ne, degree_Lz, degree_Ly, degree_Lx]

/-- A three-element indexed form is used only to reindex these exact factors. -/
private def linear (r : Fin 3) : P3 := (∑ j : Fin 3, X j) - 2 * X r

private theorem xi_as_prod : Xi = ∏ r : Fin 3, linear r := by
  simp [Xi, Lz, Ly, Lx, x, y, z, linear, Fin.prod_univ_succ,
    Fin.sum_univ_succ]; ring

private theorem rename_linear (e : Equiv.Perm (Fin 3)) (r : Fin 3) :
    rename e (linear r) = linear (e r) := by
  have hh : (∑ j : Fin 3, (X (e j) : P3)) = ∑ j : Fin 3, X j :=
    _root_.Equiv.sum_comp e (fun j => (X j : P3))
  have ht : rename e (2 : P3) = 2 := by
    calc
      rename e (2 : P3) = rename e ((1 : P3) + 1) := congrArg (fun G : P3 => rename e G) (by
        norm_num)
      _ = (1 : P3) + 1 := by rw [map_add, map_one]
      _ = 2 := by norm_num
  simp [linear, hh, ht]

theorem xi_symmetric : SymPoly Xi := by
  intro e
  calc
    rename e Xi = rename e (∏ r : Fin 3, linear r) :=
      congrArg (fun G : P3 => rename e G) xi_as_prod
    _ = ∏ r : Fin 3, linear (e r) := by simp only [map_prod, rename_linear]
    _ = ∏ r : Fin 3, linear r := _root_.Equiv.prod_comp e linear
    _ = Xi := xi_as_prod.symm

theorem quotient_symmetric {F R : P3} (hs : SymPoly F) (h : F = Xi * R) :
    SymPoly R := by
  intro e
  apply mul_left_cancel₀ xi_ne
  calc
    Xi * rename e R = rename e (Xi * R) := by rw [map_mul, xi_symmetric e]
    _ = rename e F := congrArg (fun G : P3 => rename e G) h.symm
    _ = F := hs e
    _ = Xi * R := h

theorem quotient_unique {F R S : P3} (hR : F = Xi * R) (hS : F = Xi * S) :
    R = S :=
  mul_left_cancel₀ xi_ne (hR.symm.trans hS)

theorem factor_degree {F R : P3} (h : F = Xi * R) (hF : F ≠ 0)
    (i : Fin 3) : degreeOf i F = 3 + degreeOf i R := by
  have hR : R ≠ 0 := by
    intro hR
    apply hF
    rw [h, hR, mul_zero]
  rw [h, degreeOf_mul_eq xi_ne hR, xi_degree]

/-- No divisibility or quotient-symmetry assumption: both are conclusions. -/
theorem symmetric_three_plane_factor {F : P3} (hs : SymPoly F)
    (hz : rhoZ F = 0) :
    ∃! R : P3, F = Xi * R ∧ SymPoly R ∧
      (F ≠ 0 → ∀ i : Fin 3, degreeOf i F = 3 + degreeOf i R) := by
  obtain ⟨R, hR⟩ := xi_dvd hs hz
  refine ⟨R, ⟨hR, quotient_symmetric hs hR, fun hF i => factor_degree hR hF i⟩, ?_⟩
  intro S hS
  exact quotient_unique hS.1 hR


end C145.ThreePlane

end
