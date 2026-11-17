/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ScaledHomogenization
import LeanPool.CCDN.ForMathlib.MvPolynomial

/-! Restriction to a nonzero constant homogenizing coordinate. Proper affine
sections follow from homogeneous nonmultiples also on x₀=h, not just x₀=1. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The `R`-algebra endomorphism of `MvPolynomial (Fin (n + 1)) R` that substitutes `C h * X 0` for
the first variable and fixes the other variables. -/
def firstCoordinateScaleHom (R : Type*) [CommRing R] {n : ℕ} (h : R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval (Fin.cons (C h * X 0) (fun j => X j.succ))

/-- Composing the scalings of the first variable by `h` and by `k` gives the scaling by `k * h`. -/
lemma firstCoordinateScaleHom_comp {R : Type*} [CommRing R] {n : ℕ} (h k : R) :
    (firstCoordinateScaleHom R (n := n) h).comp (firstCoordinateScaleHom R k) =
      firstCoordinateScaleHom R (k * h) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [firstCoordinateScaleHom, mul_assoc]
  · simp [firstCoordinateScaleHom]

/-- Scaling the first variable by `1` is the identity. -/
@[simp] lemma firstCoordinateScaleHom_one (R : Type*) [CommRing R] (n : ℕ) :
    firstCoordinateScaleHom R (n := n) 1 = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [firstCoordinateScaleHom]

/-- For nonzero `h` in a field `K`, the `K`-algebra automorphism of `MvPolynomial (Fin (n + 1)) K`
substituting `C h * X 0` for the first variable; its inverse scales by `h⁻¹`. -/
def firstCoordinateScale (K : Type*) [Field K] {n : ℕ} (h : K) (hh : h ≠ 0) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (firstCoordinateScaleHom K h) (firstCoordinateScaleHom K h⁻¹)
    (by rw [firstCoordinateScaleHom_comp, inv_mul_cancel₀ hh, firstCoordinateScaleHom_one])
    (by rw [firstCoordinateScaleHom_comp, mul_inv_cancel₀ hh, firstCoordinateScaleHom_one])

/-- Scaling the first variable preserves homogeneity of degree `d`. -/
lemma firstCoordinateScaleHom_homogeneous {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsHomogeneous d) :
    (firstCoordinateScaleHom R h f).IsHomogeneous d := by
  let v : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
    Fin.cons (C h * X 0) (fun j => X j.succ)
  have hv : ∀ i, (v i).IsHomogeneous 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (isHomogeneous_X R (0 : Fin (n + 1))).C_mul h
    · exact isHomogeneous_X R j.succ
  change (aeval v f).IsHomogeneous d
  simpa only [one_mul] using hf.aeval v hv

/-- Restriction of a polynomial in `n + 1` variables to the slice `x₀ = h`: the ring homomorphism
sending `X 0` to `C h` and `X i.succ` to `X i`. -/
def homogeneousSlice {R : Type*} [CommRing R] (n : ℕ) (h : R) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  eval₂Hom C (Fin.cons (C h) X)

/-- The restriction of `f` to the slice `x₀ = h` is the affine chart `x₀ = 1` of `f` with its first
variable scaled by `h`. -/
lemma homogeneousSlice_eq_chart_scale {R : Type*} [CommRing R] {n : ℕ}
    (h : R) (f : MvPolynomial (Fin (n + 1)) R) :
    homogeneousSlice n h f = affineChart n (firstCoordinateScaleHom R h f) := by
  have he : homogeneousSlice n h =
      (affineChart n).comp (firstCoordinateScaleHom R h).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [homogeneousSlice, affineChart, firstCoordinateScaleHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [homogeneousSlice, affineChart, firstCoordinateScaleHom]
  exact RingHom.congr_fun he f

/-- Evaluating the restriction of `f` to the slice `x₀ = h` at `x` is evaluating `f` at the point
`Fin.cons h x`. -/
lemma homogeneousSlice_eval {R : Type*} [CommRing R] {n : ℕ}
    (h : R) (f : MvPolynomial (Fin (n + 1)) R) (x : Fin n → R) :
    eval x (homogeneousSlice n h f) = eval (Fin.cons h x) f := by
  change eval x (eval₂ C (Fin.cons (C h) X) f) = _
  rw [← eval_assoc]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The restriction of a homogeneous polynomial of degree `d` to the slice `x₀ = h` has total degree
at most `d`. -/
lemma homogeneousSlice_degree_le {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsHomogeneous d) :
    (homogeneousSlice n h f).totalDegree ≤ d := by
  rw [homogeneousSlice_eq_chart_scale]
  exact (affineChart_totalDegree_le _).trans
    (firstCoordinateScaleHom_homogeneous h hf).totalDegree_le

/-- The restriction of the monomial `monomial m c` to the slice `x₀ = h` is the monomial with
exponent `chartExponent m` and coefficient `c * h ^ m 0`. -/
lemma homogeneousSlice_monomial {R : Type*} [CommRing R] {n : ℕ}
    (h : R) (m : Fin (n + 1) →₀ ℕ) (c : R) :
    homogeneousSlice n h (monomial m c) = monomial (chartExponent m) (c * h ^ m 0) := by
  change eval₂ C (Fin.cons (C h) X) (monomial m c) = _
  rw [eval₂_monomial, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, map_mul, map_pow, chartExponent_apply]
  ring

/-- If `f` has total degree at most `d`, then restricting the scaled homogenization
`scaledHomogenize d h f` to the slice `x₀ = h` gives `C (h ^ d) * f`. -/
lemma homogeneousSlice_scaledHomogenize {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) :
    homogeneousSlice n h (scaledHomogenize d h f) = C (h ^ d) * f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [homogeneousSlice_monomial, chartExponent_homogenizedExponent, C_mul_monomial]
  congr 1
  change (h ^ m.sum (fun _ e => e) * f.coeff m) * h ^ (d - m.sum (fun _ e => e)) = h ^ d * f.coeff m
  calc
    _ = (h ^ m.sum (fun _ e => e) * h ^ (d - m.sum (fun _ e => e))) * f.coeff m := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le ((le_totalDegree hm).trans hf)]

/-- Nonzero constant slices reflect divisibility when the equation's degree
is preserved. This is the proper-section transfer for the scaled models. -/
private theorem homogeneous_dvd_of_slice_dvd {K : Type*} [Field K] {n d M : ℕ}
    {f g : MvPolynomial (Fin (n + 1)) K} {h : K} (hh : h ≠ 0)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g.IsHomogeneous M)
    (hd : (homogeneousSlice n h f).totalDegree = d)
    (hdiv : homogeneousSlice n h f ∣ homogeneousSlice n h g) : f ∣ g := by
  rw [homogeneousSlice_eq_chart_scale, homogeneousSlice_eq_chart_scale] at hdiv
  rw [homogeneousSlice_eq_chart_scale] at hd
  have hf0' : firstCoordinateScaleHom K h f ≠ 0 := by
    exact (map_ne_zero_iff _ (firstCoordinateScale K h hh).injective).mpr hf0
  have hdiv' := homogeneous_dvd_of_affineChart_dvd (firstCoordinateScaleHom_homogeneous h hf) hf0'
    (firstCoordinateScaleHom_homogeneous h hg) hd hdiv
  have he := map_dvd (firstCoordinateScale K h hh).symm.toRingHom hdiv'
  change (firstCoordinateScale K h hh).symm (firstCoordinateScale K h hh f) ∣
    (firstCoordinateScale K h hh).symm (firstCoordinateScale K h hh g) at he
  simpa only [AlgEquiv.symm_apply_apply] using he

private lemma homogeneousSlice_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (h : R) (f : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.map φ (homogeneousSlice n h f) =
      homogeneousSlice n (φ h) (MvPolynomial.map φ f) := by
  have he : (MvPolynomial.map φ).comp (homogeneousSlice n h) =
      (homogeneousSlice n (φ h)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [homogeneousSlice]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [homogeneousSlice]
  exact RingHom.congr_fun he f

/-- Integer nonmultiples of a primitive homogeneous equation stay proper on
a nonzero rational slice preserving the degree. -/
theorem rational_homogeneousSlice_not_dvd {n d M : ℕ}
    {f g : MvPolynomial (Fin (n + 1)) ℤ} {h : ℤ} (hh : h ≠ 0)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g.IsHomogeneous M)
    (hprim : PrimitiveIntegerPolynomial f) (hd : (homogeneousSlice n h f).totalDegree = d)
    (hnd : ¬ f ∣ g) :
    ¬ MvPolynomial.map (Int.castRingHom ℚ) (homogeneousSlice n h f) ∣
      MvPolynomial.map (Int.castRingHom ℚ) (homogeneousSlice n h g) := by
  intro hdiv
  rw [homogeneousSlice_map, homogeneousSlice_map] at hdiv
  apply hnd
  apply hprim.rational_map_dvd_iff.mp
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  apply homogeneous_dvd_of_slice_dvd hhQ (hf.map _) ?_ (hg.map _) ?_ hdiv
  · exact fun he => hf0 ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using he))
  · change (homogeneousSlice n ((Int.castRingHom ℚ) h)
      (MvPolynomial.map (Int.castRingHom ℚ) f)).totalDegree = d
    rw [← homogeneousSlice_map]
    have he : (MvPolynomial.map (Int.castRingHom ℚ) (homogeneousSlice n h f)).totalDegree =
        (homogeneousSlice n h f).totalDegree := totalDegree_map_of_injective Int.cast_injective _
    exact he.trans hd

end
end CCDN
