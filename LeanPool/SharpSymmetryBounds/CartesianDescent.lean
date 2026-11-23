/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.CartesianReal

/-!
# Descent to real Cartesian equations

Descent to a real Cartesian equation preserves the curve, the degree and geometric
irreducibility; sharpness by real Cartesian polynomials in every degree.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma cartesianize_conjugateSwap (P : BPoly) :
    map (starRingEnd ℂ) (cartesianize P) = cartesianize (conjugateSwap P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [conjugateSwap]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      congr 1
      fin_cases i <;> simp [conjugateSwap, sub_eq_add_neg]

/-- The real parts of the coefficients of a plane polynomial, as a real polynomial. -/
noncomputable def realCoefficients (P : BPoly) : RPoly :=
  .ofCoeff (Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff P))

lemma realCoefficients_map {P : BPoly} (hP : map (starRingEnd ℂ) P = P) :
    map Complex.ofRealHom (realCoefficients P) = P := by
  apply (map_mapRange_eq_iff Complex.ofRealHom Complex.re (by simp) P).mpr
  intro s
  have h := congrArg (fun p : BPoly => p.coeff s) hP
  rw [coeff_map] at h
  exact Complex.conj_eq_iff_re.mp h

lemma conjugateSwap_eq_of_coeff {P : BPoly}
    (hP : ∀ a b : ℕ, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    conjugateSwap P = P := by
  ext s
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  rw [he, coeff_conjugateSwap, ← hP]

/-- Descent to a real Cartesian equation preserves the curve, degree, and geometric
irreducibility. No reality of the original equation's coefficient phase is assumed. -/
theorem exists_cartesian_equation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = P.totalDegree ∧
      cartesianLocus f = realLocus P := by
  obtain ⟨s, hs, hreal⟩ := exists_real_equation hP hd hinf
  let Q := C s * P
  have hQ : Irreducible Q := C_mul_irreducible hs hP
  have hfix : conjugateSwap Q = Q := conjugateSwap_eq_of_coeff hreal
  have hmap := realCoefficients_map (by rw [cartesianize_conjugateSwap, hfix])
  let f := realCoefficients (cartesianize Q)
  have he : complexifyReal f = Q := by
    change complexify (map Complex.ofRealHom (realCoefficients (cartesianize Q))) = Q
    rw [hmap, complexify_cartesianize]
  have hf : GeometricallyIrreducible f := by
    change Irreducible (map Complex.ofRealHom (realCoefficients (cartesianize Q)))
    rw [hmap]
    exact hQ.map complexifyEquiv.symm.toMulEquiv
  refine ⟨f, hf, ?_, ?_⟩
  · rw [← complexifyReal_degree, he]
    change (C s * P).totalDegree = P.totalDegree
    rw [totalDegree_mul_of_isDomain (C_ne_zero.mpr hs) hP.ne_zero, totalDegree_C, zero_add]
  · rw [← complexifyReal_locus, he]
    exact realLocus_C_mul hs P

/-- Sharpness is attained by real Cartesian polynomials in every degree. -/
theorem cartesian_rotation_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (CartesianDirectSymmetries f) = max d (2 * d - 4) := by
  obtain ⟨P, hP, hdeg, hinf, hnc, hc⟩ := rotation_bound_sharp d hd
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  refine ⟨f, hf, hfd.trans hdeg, hfl ▸ hinf, ?_, ?_⟩
  · simpa only [NotCircle, hfl] using hnc
  · simpa only [CartesianDirectSymmetries, hfl] using hc

theorem cartesian_full_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) = 2 * d := by
  obtain ⟨P, hP, hdeg, hinf, hnc, hc⟩ := isometry_bound_sharp d hd
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  refine ⟨f, hf, hfd.trans hdeg, hfl ▸ hinf, ?_, ?_⟩
  · simpa only [NotCircle, hfl] using hnc
  · simpa only [hfl] using hc

end CurveSymmetry
