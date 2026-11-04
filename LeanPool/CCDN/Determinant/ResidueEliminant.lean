/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import LeanPool.CCDN.ForMathlib.Polynomial

/-! The eliminant for a ratio g(beta)/f'(beta).
For f,g in F[t][z], coefficients are lifted into F[u][t], and z is
eliminated from f and u*f'-g. The resulting polynomial has outer t-degree
at most (2*deg_z(f)-1) times the coefficient t-degree bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The embedding `F[t] → F[u][t]` of polynomials in `t` as polynomials with constant coefficients
in the new parameter `u`. -/
def residueParameterLift {F : Type*} [CommRing F] : F[X] →+* F[X][X] :=
  mapRingHom (C : F →+* F[X])

/-- The specialization `F[u][t] → F[t]` at `u = 0`. -/
def residueParameterZero {F : Type*} [CommRing F] : F[X][X] →+* F[X] :=
  mapRingHom (evalRingHom (0 : F))

/-- Specializing `u = 0` after lifting a polynomial in `t` to `F[u][t]` recovers it. -/
@[simp] lemma residueParameterZero_lift {F : Type*} [CommRing F] (a : F[X]) :
    residueParameterZero (residueParameterLift a) = a := by
  ext i
  simp [residueParameterZero, residueParameterLift]

/-- Applying `residueParameterLift` and then `residueParameterZero` to the coefficients of a
polynomial over `F[t]` recovers it. -/
@[simp] lemma residueParameterZero_map_lift {F : Type*} [CommRing F] (f : F[X][X]) :
    (f.map residueParameterLift).map residueParameterZero = f := by
  ext i
  simp

/-- The polynomial `u · ∂f/∂z - g` in `z`, with coefficients in `F[u][t]`, whose common roots with
`f` are the values `u = g(β) / f'(β)`. -/
def residueEliminationEquation {F : Type*} [CommRing F] (f g : F[X][X]) : F[X][X][X] :=
  C (C X) * (f.map residueParameterLift).derivative - g.map residueParameterLift

/-- The resultant in `z` of `f` and `u · ∂f/∂z - g`, a polynomial in `t` with coefficients in `F[u]`
that vanishes at every ratio `u = g(β) / f'(β)` at a simple root `β` of `f`. -/
def residueEliminant {F : Type*} [CommRing F] (f g : F[X][X]) : F[X][X] :=
  (f.map residueParameterLift).resultant (residueEliminationEquation f g)
    f.natDegree (f.natDegree - 1)

/-- At `u = 0`, `residueEliminationEquation f g` specializes to `-g`. -/
@[simp] lemma residueEliminationEquation_zero {F : Type*} [CommRing F] (f g : F[X][X]) :
    (residueEliminationEquation f g).map residueParameterZero = -g := by
  simp only [residueEliminationEquation, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C]
  rw [show residueParameterZero (C X : F[X][X]) = 0 by simp [residueParameterZero],
    C_0, zero_mul, zero_sub, residueParameterZero_map_lift]

private lemma residueEliminant_zero {F : Type*} [CommRing F] (f g : F[X][X]) :
    residueParameterZero (residueEliminant f g) =
      f.resultant (-g) f.natDegree (f.natDegree - 1) := by
  rw [residueEliminant, ← resultant_map_map]
  rw [residueParameterZero_map_lift, residueEliminationEquation_zero]

/-- If `g` has smaller `z`-degree than `f`, then `residueEliminationEquation f g` has `z`-degree at
most `deg_z f - 1`. -/
lemma residueEliminationEquation_natDegree_le {F : Type*} [CommRing F]
    (f g : F[X][X]) (hg : g.natDegree < f.natDegree) :
    (residueEliminationEquation f g).natDegree ≤ f.natDegree - 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_C_mul_le _ _).trans
      ((natDegree_derivative_le _).trans (Nat.sub_le_sub_right natDegree_map_le 1))
  · exact natDegree_map_le.trans (by omega)

private lemma coefficient_derivative_natDegree_le {R : Type*} [CommRing R]
    (f : R[X][X]) (D : ℕ) (hf : ∀ i, (f.coeff i).natDegree ≤ D) (i : ℕ) :
    (f.derivative.coeff i).natDegree ≤ D := by
  have he : f.derivative.coeff i = (i + 1) • f.coeff (i + 1) := by
    rw [coeff_derivative]
    simp [nsmul_eq_mul, mul_comm]
  rw [he]
  exact (natDegree_smul_le _ _).trans (hf _)

/-- If all coefficients of `f` and `g` have `t`-degree at most `D`, then the residue eliminant has
`t`-degree at most `(2 deg_z f - 1) · D`. -/
theorem residueEliminant_natDegree_le {F : Type*} [CommRing F]
    (f g : F[X][X]) (D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (residueEliminant f g).natDegree ≤ (f.natDegree + (f.natDegree - 1)) * D := by
  have hfl : ∀ i, ((f.map residueParameterLift).coeff i).natDegree ≤ D := by
    intro i
    simp only [coeff_map, residueParameterLift, coe_mapRingHom]
    exact natDegree_map_le.trans (hf i)
  apply Polynomial.natDegree_resultant_le
  · exact hfl
  · intro i
    simp only [residueEliminationEquation, coeff_sub, coeff_C_mul]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (coefficient_derivative_natDegree_le _ D hfl i)
    · simp only [coeff_map, residueParameterLift, coe_mapRingHom]
      exact natDegree_map_le.trans (hg i)

/-- The eliminant is nonzero: specializing u=0 gives the nonzero resultant
of f and -g over F(t). -/
theorem residueEliminant_ne_zero {F : Type*} [Field F]
    (f g : F[X][X]) (hf : Irreducible (f.map (algebraMap F[X] (RatFunc F))))
    (hg : g ≠ 0) (hdeg : g.natDegree < f.natDegree) :
    residueEliminant f g ≠ 0 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  have hg0 : (-g).map φ ≠ 0 := by
    intro h
    exact (neg_ne_zero.mpr hg)
      ((Polynomial.map_injective φ hinj) (h.trans (Polynomial.map_zero φ).symm))
  have hdegrees : ((-g).map φ).natDegree < (f.map φ).natDegree := by
    simpa only [natDegree_map_eq_of_injective hinj, natDegree_neg] using hdeg
  have hn : ((-g).map φ).natDegree ≤ f.natDegree - 1 := by
    rw [natDegree_map_eq_of_injective hinj, natDegree_neg]
    omega
  have hres := Polynomial.resultant_ne_zero_of_irreducible_of_natDegree_lt
    (f.map φ) ((-g).map φ) hf hg0 hdegrees (f.natDegree - 1) hn
  intro h
  have hz := congrArg φ (congrArg residueParameterZero h)
  rw [map_zero, map_zero, residueEliminant_zero, ← resultant_map_map] at hz
  apply hres
  simpa only [natDegree_map_eq_of_injective hinj] using hz

end
end CCDN
