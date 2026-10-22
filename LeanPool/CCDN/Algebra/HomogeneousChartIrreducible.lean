/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
import LeanPool.CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Dehomogenization preserves degree and irreducibility when the
homogenizing coordinate does not divide the homogeneous equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A full-degree affine chart detects irreducibility of the original
equation; a factor lost on the chart would force a degree drop. -/
theorem irreducible_of_affineChart_irreducible {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K)
    (hdeg : (affineChart n f).totalDegree = f.totalDegree)
    (hir : Irreducible (affineChart n f)) : Irreducible f := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hunit (a : MvPolynomial (Fin (n + 1)) K) (ha : a ≠ 0)
      (hda : a.totalDegree = (affineChart n a).totalDegree)
      (hu : IsUnit (affineChart n a)) : IsUnit a := by
    have ha0 : a.totalDegree = 0 := hda.trans (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have he := totalDegree_eq_zero_iff_eq_C.mp ha0
    rw [he]
    apply (isUnit_iff_ne_zero.mpr ?_).map C
    intro hc
    exact ha (by rw [he, hc, map_zero])
  refine ⟨fun h => hir.not_isUnit (h.map (affineChart n)), ?_⟩
  intro a b hab
  have ha : a ≠ 0 := by intro h; exact hf0 (by rw [hab, h, zero_mul])
  have hb : b ≠ 0 := by intro h; exact hf0 (by rw [hab, h, mul_zero])
  have hc : affineChart n f = affineChart n a * affineChart n b := by rw [hab, map_mul]
  have hac : affineChart n a ≠ 0 := by
    intro h
    exact hir.ne_zero (by rw [hc, h, zero_mul])
  have hbc : affineChart n b ≠ 0 := by
    intro h
    exact hir.ne_zero (by rw [hc, h, mul_zero])
  have hsum := totalDegree_mul_of_isDomain ha hb
  have hsumc := totalDegree_mul_of_isDomain hac hbc
  rw [← hab] at hsum
  rw [← hc, hdeg, hsum] at hsumc
  have hla := affineChart_totalDegree_le a
  have hlb := affineChart_totalDegree_le b
  obtain hau | hbu := hir.isUnit_or_isUnit hc
  · exact Or.inl (hunit a ha (by omega) hau)
  · exact Or.inr (hunit b hb (by omega) hbu)

/-- No variable `X j` divides an irreducible homogeneous polynomial of degree at least `2`. -/
theorem variable_not_dvd_irreducible_homogeneous {K : Type*} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
    (hir : Irreducible f) (hd : 2 ≤ d) (j : Fin (n + 1)) : ¬ X j ∣ f := by
  rintro ⟨g, hg⟩
  have hx : ¬ IsUnit (X j : MvPolynomial (Fin (n + 1)) K) := by
    intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    simp at h
  have hu := (hir.isUnit_or_isUnit hg).resolve_left hx
  have h := totalDegree_mul (X j) g
  rw [← hg, hf.totalDegree hir.ne_zero, totalDegree_X,
    (isUnit_iff_totalDegree_of_isReduced.mp hu).2] at h
  omega

/-- An irreducible homogeneous polynomial of degree at least `2` divides no variable `X j`. -/
theorem irreducible_homogeneous_not_dvd_variable {K : Type*} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
    (hir : Irreducible f) (hd : 2 ≤ d) (j : Fin (n + 1)) : ¬ f ∣ X j := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact X_ne_zero j (by simpa only [h, mul_zero] using hg)
  have hh := congrArg totalDegree hg
  rw [totalDegree_X, totalDegree_mul_of_isDomain hir.ne_zero hg0,
    hf.totalDegree hir.ne_zero] at hh
  omega

/-- If `X 0` does not divide the homogeneous polynomial `f` of degree `d`, then the affine chart
`x₀ = 1` of `f` has total degree exactly `d`. -/
theorem affineChart_degree_of_not_variable_dvd {K : Type*} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
    (hX : ¬ X 0 ∣ f) : (affineChart n f).totalDegree = d := by
  have hle := (affineChart_totalDegree_le f).trans hf.totalDegree_le
  by_contra hne
  have hd : 0 < d := by omega
  have hsmall : (affineChart n f).totalDegree ≤ d - 1 := by omega
  let g := scaledHomogenize (d - 1) 1 (affineChart n f)
  have hg : g.IsHomogeneous (d - 1) := scaledHomogenize_homogeneous 1 _ hsmall
  have hxg : (X 0 * g).IsHomogeneous d := by
    convert (isHomogeneous_X K (0 : Fin (n + 1))).mul hg using 1
    omega
  have he : f = X 0 * g := by
    apply affineChart_injective_on_homogeneous hf hxg
    rw [map_mul, show affineChart n (X 0) = 1 by simp [affineChart],
      one_mul, affineChart_scaledHomogenize_one]
  exact hX ⟨g, he⟩

/-- If `X 0` does not divide the irreducible homogeneous polynomial `f`, then the affine chart
`x₀ = 1` of `f` is irreducible. -/
theorem affineChart_irreducible_of_not_variable_dvd {K : Type*} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
    (hir : Irreducible f) (hX : ¬ X 0 ∣ f) :
    Irreducible (affineChart n f) := by
  have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
  have hd : 0 < d := by
    rw [← hf.totalDegree hir.ne_zero]
    exact MvPolynomial.totalDegree_pos_of_irreducible hir
  have hc0 : affineChart n f ≠ 0 := by
    intro he
    have hh := hdeg
    rw [he, totalDegree_zero] at hh
    omega
  refine ⟨?_, ?_⟩
  · intro hu
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hdeg] at hh
    omega
  · intro a b hab
    have ha0 : a ≠ 0 := by
      intro ha
      exact hc0 (by simpa only [ha, zero_mul] using hab)
    have hb0 : b ≠ 0 := by
      intro hb
      exact hc0 (by simpa only [hb, mul_zero] using hab)
    have hsum : a.totalDegree + b.totalDegree = d := by
      rw [← totalDegree_mul_of_isDomain ha0 hb0, ← hab, hdeg]
    have hh : (scaledHomogenize a.totalDegree 1 a *
        scaledHomogenize b.totalDegree 1 b).IsHomogeneous d := by
      simpa only [hsum] using (scaledHomogenize_homogeneous 1 a le_rfl).mul
        (scaledHomogenize_homogeneous 1 b le_rfl)
    have he : f = scaledHomogenize a.totalDegree 1 a * scaledHomogenize b.totalDegree 1 b := by
      apply affineChart_injective_on_homogeneous hf hh
      rw [map_mul, affineChart_scaledHomogenize_one, affineChart_scaledHomogenize_one]
      exact hab
    obtain ha | hb := hir.isUnit_or_isUnit he
    · left
      simpa only [affineChart_scaledHomogenize_one] using ha.map (affineChart n)
    · right
      simpa only [affineChart_scaledHomogenize_one] using hb.map (affineChart n)

end
end CCDN
