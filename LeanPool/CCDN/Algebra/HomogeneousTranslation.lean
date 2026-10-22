/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Integral translations of the affine chart, lifted to homogeneous linear
coordinate changes, preserve primitive equations and homogeneous degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The homogeneous linear substitution fixing `X 0` and sending `X (j + 1)` to
`X (j + 1) + a j * X 0`; on the affine chart `X 0 = 1` it is the translation by `a`. -/
def homogeneousTranslationHom (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0))

/-- Composing the homogeneous translations by `a` and by `b` gives the homogeneous translation
by `a + b`. -/
lemma homogeneousTranslationHom_comp {R : Type*} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (homogeneousTranslationHom R a).comp (homogeneousTranslationHom R b) =
      homogeneousTranslationHom R (a + b) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [homogeneousTranslationHom]
  · simp only [homogeneousTranslationHom, AlgHom.comp_apply, aeval_X, Fin.cons_succ,
      map_add, map_mul, aeval_C, Fin.cons_zero, Pi.add_apply, algebraMap_eq]
    ring

/-- The homogeneous translation by zero is the identity. -/
@[simp] lemma homogeneousTranslationHom_zero (R : Type*) [CommRing R] (n : ℕ) :
    homogeneousTranslationHom R (0 : Fin n → R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [homogeneousTranslationHom]

/-- The homogeneous translation by `a` (fixing `X 0` and sending `X (j + 1)` to
`X (j + 1) + a j * X 0`) as an algebra automorphism, with inverse the homogeneous translation
by `-a`. -/
def homogeneousTranslation (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (homogeneousTranslationHom R a) (homogeneousTranslationHom R (-a))
    (by rw [homogeneousTranslationHom_comp, add_neg_cancel, homogeneousTranslationHom_zero])
    (by rw [homogeneousTranslationHom_comp, neg_add_cancel, homogeneousTranslationHom_zero])

/-- The homogeneous translation of a homogeneous polynomial of degree `d` is homogeneous of
degree `d`. -/
lemma homogeneousTranslation_homogeneous {R : Type*} [CommRing R] {n d : ℕ}
    (a : Fin n → R) {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsHomogeneous d) :
    (homogeneousTranslation R a f).IsHomogeneous d := by
  change (aeval (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)) f).IsHomogeneous d
  let v : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
    Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)
  have hv : ∀ i, (v i).IsHomogeneous 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [v, Fin.cons_zero] using isHomogeneous_X R (0 : Fin (n + 1))
    · simpa only [v, Fin.cons_succ] using
        (isHomogeneous_X R j.succ).add ((isHomogeneous_X R (0 : Fin (n + 1))).C_mul (a j))
  simpa only [one_mul] using hf.aeval v hv

/-- The homogeneous translation by an integer vector of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.translate_homogeneous {n : ℕ} (a : Fin n → ℤ)
    {f : MvPolynomial (Fin (n + 1)) ℤ} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (homogeneousTranslation ℤ a f) := by
  intro c hc
  have hd := (C_dvd_iff_dvd_coeff c _).mpr hc
  have he := map_dvd (homogeneousTranslation ℤ a).symm.toRingHom hd
  have hC : (homogeneousTranslation ℤ a).symm (C c) = C c :=
    (homogeneousTranslation ℤ a).symm.commutes c
  change (homogeneousTranslation ℤ a).symm (C c) ∣
    (homogeneousTranslation ℤ a).symm (homogeneousTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp he)

/-- The homogeneous translation of `f` by `a` evaluates at `x` to the value of `f` at the point
with coordinates `x 0` and `x (j + 1) + a j * x 0`. -/
lemma homogeneousTranslation_eval {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) (x : Fin (n + 1) → R) :
    eval x (homogeneousTranslation R a f) =
      eval (Fin.cons (x 0) (fun j => x j.succ + a j * x 0)) f := by
  change eval x (eval₂ C (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)) f) = _
  rw [← eval_assoc]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- On the affine chart `X 0 = 1`, the homogeneous translation of `f` by `a` evaluates at the
point `(1, z)` to the value of `f` at `(1, z + a)`. -/
lemma homogeneousTranslation_eval_chart {R : Type*} [CommRing R] {n : ℕ}
    (a z : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons 1 z) (homogeneousTranslation R a f) = eval (Fin.cons 1 (z + a)) f := by
  rw [homogeneousTranslation_eval]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_one]
  rfl

/-- If `z` lies in the box of radius `B ≥ 1` and every coordinate of `a` lies in `[0, d]`, then
every coordinate of `z - a` has absolute value at most `(d + 1) * B`. -/
lemma homogeneousTranslation_integer_point_box {n : ℕ} {B : ℝ} {d : ℕ}
    (hB : 1 ≤ B) (a z : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (hz : InBox z B) (j : Fin n) :
    |((z j - a j : ℤ) : ℝ)| ≤ ((d : ℝ) + 1) * B := by
  rw [Int.cast_sub]
  have ha0 : (0 : ℝ) ≤ a j := by exact_mod_cast (ha j).1
  have had : (a j : ℝ) ≤ d := by exact_mod_cast (ha j).2
  have h := abs_sub_le (z j : ℝ) 0 (a j : ℝ)
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ha0] at h
  nlinarith [hz j, show (0 : ℝ) ≤ d by positivity]

end
end CCDN
