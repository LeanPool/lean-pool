/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Reflection

/-!
# Orientation-reversing symmetries

Opposite Euclidean symmetries in complex affine form; they form a torsor for the direct part when
they exist.
-/

@[expose] public section

namespace CurveSymmetry

/-- An orientation-reversing Euclidean symmetry in complex affine coordinates. -/
def OppositeSymmetry (S : Set ℂ) (a b : ℂ) : Prop :=
  ‖a‖ = 1 ∧ ∀ z : ℂ, a * star z + b ∈ S ↔ z ∈ S

/-- Affine parameters `(a, b)` of the opposite symmetries `z ↦ a conj z + b` of the locus. -/
abbrev OppositeSymmetries (P : BPoly) :=
  {ab : ℂ × ℂ // OppositeSymmetry (realLocus P) ab.1 ab.2}

/-- The two possible orientations, with their unique affine parameters. -/
abbrev EuclideanSymmetries (P : BPoly) := DirectSymmetries P ⊕ OppositeSymmetries P

lemma opposite_comp_opposite {S : Set ℂ} {a b c d : ℂ}
    (h1 : OppositeSymmetry S a b) (h2 : OppositeSymmetry S c d) :
    DirectSymmetry S (a * star c) (a * star d + b) := by
  refine ⟨by simp [h1.1, h2.1], ?_⟩
  intro z
  have he : a * star c * z + (a * star d + b) = a * star (c * star z + d) + b := by
    simp only [star_add, star_mul, star_star]
    ring
  rw [he]
  exact (h1.2 (c * star z + d)).trans (h2.2 z)

lemma opposite_comp_direct {S : Set ℂ} {a b c d : ℂ}
    (h1 : OppositeSymmetry S a b) (h2 : DirectSymmetry S c d) :
    OppositeSymmetry S (a * star c) (a * star d + b) := by
  refine ⟨by simp [h1.1, h2.1], ?_⟩
  intro z
  have he : a * star c * star z + (a * star d + b) = a * star (c * z + d) + b := by
    simp only [star_add, star_mul]
    ring
  rw [he]
  exact (h1.2 (c * z + d)).trans (h2.2 z)

lemma opposite_inverse {S : Set ℂ} {a b : ℂ} (h : OppositeSymmetry S a b) :
    OppositeSymmetry S a (-a * star b) := by
  have hc := mul_star_eq_one_of_norm h.1
  refine ⟨h.1, ?_⟩
  intro z
  have he : a * star (a * star z + -a * star b) + b = z := by
    simp only [star_add, star_mul, star_star, star_neg]
    linear_combination (z - b) * hc
  exact (he ▸ h.2 (a * star z + -a * star b)).symm

/-- The opposite-orientation part is a torsor for the direct part, if nonempty. -/
noncomputable def oppositeDirectEquiv (P : BPoly) (g : OppositeSymmetries P) :
    OppositeSymmetries P ≃ DirectSymmetries P where
  toFun u := ⟨(g.val.1 * star u.val.1, g.val.1 * star u.val.2 + g.val.2),
    opposite_comp_opposite g.prop u.prop⟩
  invFun u := ⟨(g.val.1 * star u.val.1, g.val.1 * star u.val.2 + -g.val.1 * star g.val.2),
    opposite_comp_direct (opposite_inverse g.prop) u.prop⟩
  left_inv u := by
    have hc := mul_star_eq_one_of_norm g.prop.1
    apply Subtype.ext
    apply Prod.ext
    · change g.val.1 * star (g.val.1 * star u.val.1) = u.val.1
      simp only [star_mul, star_star]
      linear_combination u.val.1 * hc
    · change g.val.1 * star (g.val.1 * star u.val.2 + g.val.2) +
        -g.val.1 * star g.val.2 = u.val.2
      simp only [star_add, star_mul, star_star]
      linear_combination u.val.2 * hc
  right_inv u := by
    have hc := mul_star_eq_one_of_norm g.prop.1
    apply Subtype.ext
    apply Prod.ext
    · change g.val.1 * star (g.val.1 * star u.val.1) = u.val.1
      simp only [star_mul, star_star]
      linear_combination u.val.1 * hc
    · change g.val.1 * star (g.val.1 * star u.val.2 + -g.val.1 * star g.val.2) +
        g.val.2 = u.val.2
      simp only [star_add, star_mul, star_star, star_neg]
      linear_combination (u.val.2 - g.val.2) * hc

lemma opposite_shift {P : BPoly} {a b c : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) :
    OppositeSymmetry (realLocus (shift c P)) a (a * star c + b - c) := by
  refine ⟨h.1, ?_⟩
  intro z
  rw [mem_realLocus_shift, mem_realLocus_shift]
  have he : a * star z + (a * star c + b - c) + c = a * star (z + c) + b := by
    simp only [star_add]
    ring
  rw [he]
  exact h.2 (z + c)

/-- If a nonidentity direct rotation is centered at zero, every opposite symmetry
is centered there too. -/
lemma opposite_centered {P : BPoly}
    (hcenter : ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = 0)
    {r : ℂ} (hr : r ≠ 1) (hrot : DirectSymmetry (realLocus P) r 0)
    {a b : ℂ} (hg : OppositeSymmetry (realLocus P) a b) : b = 0 := by
  have ha := mul_star_eq_one_of_norm hg.1
  have hconj := opposite_comp_opposite
    (opposite_comp_direct hg hrot) (opposite_inverse hg)
  have he := hcenter _ _ hconj
  simp only [star_neg, star_mul, star_star, star_zero, mul_zero, zero_add] at he
  have he' : (1 - star r) * b = 0 := by
    linear_combination he + star r * b * ha
  have hn : 1 - star r ≠ 0 := by
    intro h
    apply hr
    have hs : star r = 1 := (sub_eq_zero.mp h).symm
    simpa using congrArg star hs
  exact (mul_eq_zero.mp he').resolve_left hn

end CurveSymmetry
