/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreComplexProjectionGeometry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreLiteralProjectionGeometry

/-! # Complex-input holomorphic projection geometry

Orthogonal projection identities on the actual ambient Ginibre L² space.
The closed polynomial subspace/entire-representative bridge is separate.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConstantL2_star (n : ℕ) (hn : 0 < n) (a : ℂ) :
    star (ginibreConstantL2 n hn a) = ginibreConstantL2 n hn (star a) := by
  let := ginibreProbabilityInstance hn
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (ginibreConstantL2 n hn a),
    Lp.coeFn_const (2 : ℝ≥0∞) (ginibreMeasure n) a,
    Lp.coeFn_const (2 : ℝ≥0∞) (ginibreMeasure n) (star a)] with z hs ha hsa
  rw [hs]
  change star ((Lp.const 2 (ginibreMeasure n) a : Configuration n → ℂ) z) =
    (Lp.const 2 (ginibreMeasure n) (star a) : Configuration n → ℂ) z
  rw [ha, hsa]
  rfl

theorem ginibreConstantClosedSubspace_star_mem {n : ℕ} (hn : 0 < n)
    {a : Lp ℂ 2 (ginibreMeasure n)} (ha : a ∈ ginibreConstantClosedSubspace n hn) :
    star a ∈ ginibreConstantClosedSubspace n hn := by
  obtain ⟨c, rfl⟩ := ha
  change star (ginibreConstantL2 n hn c) ∈ ginibreConstantClosedSubspace n hn
  rw [ginibreConstantL2_star]
  exact ⟨star c, rfl⟩

theorem ginibreConstants_le_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreConstantClosedSubspace n hn ≤ ginibreHolomorphicAmbientClosedSpan n hn := by
  rw [← ginibreFiniteQuotientDegreeZero_eq_constants,
    ginibreHolomorphicAmbientClosedSpan_eq_graded]
  exact le_iSup (fun r => ginibreFiniteQuotientDegreeClosedSpan n r hn) 0

theorem ginibrePositive_le_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibrePositiveQuotientGradedClosedSpan n hn ≤ ginibreHolomorphicAmbientClosedSpan n hn := by
  rw [ginibreHolomorphicAmbientClosedSpan_eq_graded]
  exact ginibrePositiveQuotientGradedClosedSpan_le_graded n hn

theorem ginibreConstants_positive_orthogonal {n : ℕ} (hn : 0 < n)
    {a b : Lp ℂ 2 (ginibreMeasure n)}
    (ha : a ∈ ginibreConstantClosedSubspace n hn)
    (hb : b ∈ ginibrePositiveQuotientGradedClosedSpan n hn) : inner ℂ a b = 0 := by
  apply degreeZero_orthogonal_positiveGraded hn _ hb
  rwa [ginibreFiniteQuotientDegreeZero_eq_constants]

private theorem projection_inner_of_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (H : ClosedSubmodule ℂ E)
    (x y : E) (hy : y ∈ H) : inner ℂ (H.starProjection x) y = inner ℂ x y := by
  have h := Submodule.starProjection_inner_eq_zero x y hy
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm

/-- The holomorphic projection splits into the constant and positive-degree projections. -/
theorem ginibreHolomorphicProjection_split (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) :
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection f =
      (ginibreConstantClosedSubspace n hn).starProjection f +
        (ginibrePositiveQuotientGradedClosedSpan n hn).starProjection f := by
  let H := ginibreHolomorphicAmbientClosedSpan n hn
  let C := ginibreConstantClosedSubspace n hn
  let P := ginibrePositiveQuotientGradedClosedSpan n hn
  let h := H.starProjection f
  let a := C.starProjection f
  let b := P.starProjection f
  have hh : h ∈ H := Submodule.starProjection_apply_mem _ f
  have ha : a ∈ C := Submodule.starProjection_apply_mem _ f
  have hb : b ∈ P := Submodule.starProjection_apply_mem _ f
  have hdH : h - a - b ∈ H :=
    H.sub_mem (H.sub_mem hh (ginibreConstants_le_holomorphic n hn ha))
      (ginibrePositive_le_holomorphic n hn hb)
  have hdC : ∀ c ∈ ginibreFiniteQuotientDegreeClosedSpan n 0 hn,
      inner ℂ (h - a - b) c = 0 := by
    intro c hc
    have hcC : c ∈ C := by simpa [C, ginibreFiniteQuotientDegreeZero_eq_constants] using hc
    have hbc : inner ℂ b c = 0 := by
      rw [← inner_conj_symm b c, ginibreConstants_positive_orthogonal hn hcC hb, map_zero]
    rw [inner_sub_left, inner_sub_left,
      projection_inner_of_mem H f c (ginibreConstants_le_holomorphic n hn hcC),
      projection_inner_of_mem C f c hcC, hbc]
    simp
  have hdP : ∀ p ∈ P, inner ℂ (h - a - b) p = 0 := by
    intro p hp
    rw [inner_sub_left, inner_sub_left,
      projection_inner_of_mem H f p (ginibrePositive_le_holomorphic n hn hp),
      ginibreConstants_positive_orthogonal hn ha hp,
      projection_inner_of_mem P f p hp]
    simp
  have he := eq_zero_of_mem_holomorphic_of_orthogonal_degreeZero_positive hn hdH hdC hdP
  change h = a + b
  simpa [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)

/-- Conjugation commutes with the genuine constant projection. -/
theorem ginibreConstantProjection_star (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) :
    (ginibreConstantClosedSubspace n hn).starProjection (star f) =
      star ((ginibreConstantClosedSubspace n hn).starProjection f) := by
  let C := ginibreConstantClosedSubspace n hn
  have ha := ginibreConstantClosedSubspace_star_mem hn
    (Submodule.starProjection_apply_mem C.toSubmodule f)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ha
  intro y hy
  have hsy := ginibreConstantClosedSubspace_star_mem hn hy
  have h := Submodule.starProjection_inner_eq_zero f (star y) hsy
  have hc := congrArg star h
  rw [← Lp_inner_star_star, Lp_star_star, Lp_star_sub] at hc
  simpa using hc

/-- The antiholomorphic orthogonal projection is obtained by conjugating the
holomorphic orthogonal projection by the genuine antiunitary involution. -/
def ginibreAntiholomorphicProjection (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) : Lp ℂ 2 (ginibreMeasure n) :=
  star ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection (star f))

/-- The genuine closed conjugate-holomorphic subspace. -/
def ginibreAntiholomorphicAmbientClosedSpan (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) where
  toSubmodule := {
    carrier := {f | star f ∈ ginibreHolomorphicAmbientClosedSpan n hn}
    zero_mem' := by
      change star (0 : Lp ℂ 2 (ginibreMeasure n)) ∈ ginibreHolomorphicAmbientClosedSpan n hn
      rw [Lp_star_zero]; exact Submodule.zero_mem _
    add_mem' := by
      intro x y hx hy
      change star (x+y) ∈ ginibreHolomorphicAmbientClosedSpan n hn
      rw [Lp_star_add]
      exact (ginibreHolomorphicAmbientClosedSpan n hn).add_mem hx hy
    smul_mem' := by
      intro a x hx
      change star (a • x) ∈ ginibreHolomorphicAmbientClosedSpan n hn
      rw [Lp_star_complex_smul]
      exact (ginibreHolomorphicAmbientClosedSpan n hn).smul_mem (star a) hx }
  isClosed' := (ginibreHolomorphicAmbientClosedSpan n hn).isClosed.preimage
    (LpConjugationIsometry (ginibreMeasure n)).continuous

/-- The conjugated operator is literally the orthogonal projection onto the
closed conjugate-holomorphic subspace, rather than only a norm comparison. -/
theorem ginibreAntiholomorphicProjection_eq_starProjection (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) :
    ginibreAntiholomorphicProjection n hn f =
      (ginibreAntiholomorphicAmbientClosedSpan n hn).starProjection f := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change star (star ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection (star f))) ∈
      ginibreHolomorphicAmbientClosedSpan n hn
    rw [Lp_star_star]
    exact Submodule.starProjection_apply_mem _ (star f)
  · intro y hy
    change star y ∈ ginibreHolomorphicAmbientClosedSpan n hn at hy
    have h := congrArg star (Submodule.starProjection_inner_eq_zero (star f) (star y) hy)
    rw [← Lp_inner_star_star, Lp_star_sub, Lp_star_star,
      Lp_star_star] at h
    simpa [ginibreAntiholomorphicProjection] using h

/-- Lemma 2.7(2)'s full complex-input two-projection bound for the closed
holomorphic polynomial subspace, with no regularity or reality assumption. -/
theorem ginibre_complex_two_projection_bound (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) :
    ‖(ginibreHolomorphicAmbientClosedSpan n hn).starProjection f‖ ^ 2 +
      ‖ginibreAntiholomorphicProjection n hn f‖ ^ 2 ≤
    ‖f‖ ^ 2 + ‖(ginibreConstantClosedSubspace n hn).starProjection f‖ ^ 2 := by
  let C := ginibreConstantClosedSubspace n hn
  let P := ginibrePositiveQuotientGradedClosedSpan n hn
  let a := C.starProjection f
  let b := P.starProjection f
  let d := P.starProjection (star f)
  let c := star d
  have ha : a ∈ C := Submodule.starProjection_apply_mem _ f
  have hb : b ∈ P := Submodule.starProjection_apply_mem _ f
  have hd : d ∈ P := Submodule.starProjection_apply_mem _ (star f)
  have hab : inner ℂ a b = 0 := ginibreConstants_positive_orthogonal hn ha hb
  have hbc : inner ℂ b c = 0 :=
    inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan hn hb hd
  have hac : inner ℂ a c = 0 := by
    have h := congrArg star (ginibreConstants_positive_orthogonal hn
      (ginibreConstantClosedSubspace_star_mem hn ha) hd)
    rw [← Lp_inner_star_star, Lp_star_star] at h
    simpa [c] using h
  have hba : inner ℂ b a = 0 := by rw [← inner_conj_symm b a, hab, map_zero]
  have hca : inner ℂ c a = 0 := by rw [← inner_conj_symm c a, hac, map_zero]
  have hcb : inner ℂ c b = 0 := by rw [← inner_conj_symm c b, hbc, map_zero]
  have haf : inner ℂ a (f - a) = 0 := by
    rw [← inner_conj_symm a (f-a), Submodule.starProjection_inner_eq_zero f a ha, map_zero]
  have hbf : inner ℂ b f = inner ℂ b b := by
    have h : inner ℂ b (f-b) = 0 := by
      rw [← inner_conj_symm b (f-b), Submodule.starProjection_inner_eq_zero f b hb, map_zero]
    rw [inner_sub_right] at h
    exact sub_eq_zero.mp h
  have hcf : inner ℂ c f = inner ℂ c c := by
    have h := congrArg star (Submodule.starProjection_inner_eq_zero (star f) d hd)
    rw [← Lp_inner_star_star, Lp_star_sub, Lp_star_star] at h
    have h' : inner ℂ (f-c) c = 0 := by simpa [c, d] using h
    have h'' : inner ℂ c (f-c) = 0 := by rw [← inner_conj_symm c (f-c), h', map_zero]
    rw [inner_sub_right] at h''
    exact sub_eq_zero.mp h''
  have hrest : inner ℂ (b+c) ((f-a)-(b+c)) = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, inner_add_right,
      inner_sub_right, inner_sub_right, inner_add_right, hbf, hcf, hba, hca, hbc, hcb]
    ring
  have hnormA := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a (f-a) haf
  have hnormBC := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero b c hbc
  have hnormRest := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b+c)
    ((f-a)-(b+c)) hrest
  rw [add_sub_cancel] at hnormA
  rw [add_sub_cancel] at hnormRest
  have hnormP : ‖(ginibreHolomorphicAmbientClosedSpan n hn).starProjection f‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [ginibreHolomorphicProjection_split]
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b hab
  have hQ : ginibreAntiholomorphicProjection n hn f = a+c := by
    rw [ginibreAntiholomorphicProjection, ginibreHolomorphicProjection_split,
      Lp_star_add, ginibreConstantProjection_star, Lp_star_star]
  have hnormQ : ‖ginibreAntiholomorphicProjection n hn f‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    rw [hQ]
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a c hac
  rw [hnormP, hnormQ]
  change ‖a‖ ^ 2 + ‖b‖ ^ 2 + (‖a‖ ^ 2 + ‖c‖ ^ 2) ≤ ‖f‖ ^ 2 + ‖a‖ ^ 2
  nlinarith [sq_nonneg ‖(f-a)-(b+c)‖]

/-- Lemma 2.7(3)'s projection geometry for every real centered L² input.
There is no smoothness, weak-gradient or generator-domain requirement. -/
theorem ginibre_real_centered_projection_geometry (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) (hreal : star f = f)
    (hcenter : (ginibreConstantClosedSubspace n hn).starProjection f = 0) :
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection f
    let r := f-h-star h
    inner ℂ h (star h) = 0 ∧ inner ℂ h r = 0 ∧ inner ℂ (star h) r = 0 ∧
      ‖f‖ ^ 2 = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 ∧
      ‖f-h‖ ^ 2 = ‖f‖ ^ 2 / 2 + ‖r‖ ^ 2 / 2 ∧
      ‖f‖ ^ 2 / 2 ≤ ‖f-h‖ ^ 2 := by
  dsimp
  let H := ginibreHolomorphicAmbientClosedSpan n hn
  let h := H.starProjection f
  let r := f-h-star h
  have hh : h ∈ ginibrePositiveQuotientGradedClosedSpan n hn := by
    dsimp [h, H]
    rw [ginibreHolomorphicProjection_split, hcenter, zero_add]
    exact Submodule.starProjection_apply_mem _ f
  have hhs : inner ℂ h (star h) = 0 :=
    inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan hn hh hh
  have hres : inner ℂ h (f-h) = 0 := by
    rw [← inner_conj_symm h (f-h), Submodule.starProjection_inner_eq_zero f h
      (Submodule.starProjection_apply_mem H.toSubmodule f), map_zero]
  have hhr : inner ℂ h r = 0 := by
    change inner ℂ h ((f-h)-star h) = 0
    rw [inner_sub_right, hres, hhs, sub_zero]
  have hsres : inner ℂ (star h) (f-star h) = 0 := by
    have h' := congrArg star hres
    rw [← Lp_inner_star_star, Lp_star_sub, hreal] at h'
    simpa using h'
  have hsr : inner ℂ (star h) r = 0 := by
    have hsH : inner ℂ (star h) h = 0 := by
      rw [← inner_conj_symm (star h) h, hhs, map_zero]
    have hr : r = (f-star h)-h := by dsimp [r]; abel
    rw [hr, inner_sub_right, hsres, hsH, sub_zero]
  have hnorm : ‖f‖ ^ 2 = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
    have h' := norm_sq_eq_two_mul_norm_sq_add_of_h_star_remainder_orthogonal
      h r hhs hhr hsr
    have he : h + star h + r = f := by dsimp [r]; abel
    rwa [he] at h'
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero h (f-h) hres
  rw [add_sub_cancel] at hpy
  have hdist : ‖f-h‖ ^ 2 = ‖f‖ ^ 2 / 2 + ‖r‖ ^ 2 / 2 := by nlinarith
  exact ⟨hhs, hhr, hsr, hnorm, hdist, by
    rw [hdist]
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by norm_num))⟩

end
end GinibrePoincare

