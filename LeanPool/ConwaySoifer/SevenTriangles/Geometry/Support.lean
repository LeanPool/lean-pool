/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Algebra of support forms

A single normal proves a bound only at its own triangle orientation. A global
bound needs an additional support-edge theorem plus ALL candidate directions.
This file does not silently replace that quantifier with one normal.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

noncomputable section

namespace ConwaySoifer.SevenTriangles

/-- Coordinate coefficients of a real linear functional in oblique coordinates. -/
abbrev Form := ℝ × ℝ

/-- Apply a coordinate linear functional to a point. -/
def formEval (l : Form) (p : Point) : ℝ := l.1 * p.1 + l.2 * p.2

/-- Rotate a linear functional through 120 degrees in the dual metric. -/
def formRotate120 (l : Form) : Form :=
  (-l.1 / 2 - l.2, 3 * l.1 / 4 - l.2 / 2)

/-- Squared dual norm of a coordinate linear functional. -/
def formNormSq (l : Form) : ℝ := (3 / 4 : ℝ) * l.1 ^ 2 + l.2 ^ 2

/-- The nonnegative dual norm of a coordinate linear functional. -/
def formNorm (l : Form) : ℝ := Real.sqrt (formNormSq l)

/-- The dual metric inner product of two coordinate linear functionals. -/
def formInner (l m : Form) : ℝ := (3 / 4 : ℝ) * l.1 * m.1 + l.2 * m.2

/-- The coordinate determinant of two linear-functional coefficient vectors. -/
def formDet (l m : Form) : ℝ := l.1 * m.2 - l.2 * m.1

/-- Negate a coordinate linear functional. -/
def formNeg (l : Form) : Form := (-l.1, -l.2)

/-- The determinant functional associated with a planar direction. -/
def vectorNormal (p : Point) : Form := (-p.2, p.1)

/-- The determinant normal associated with an oriented edge. -/
def edgeNormal (p q : Point) : Form := vectorNormal (q - p)

/-- The Euclidean inner product expressed in oblique coordinates. -/
def metricInner (p q : Point) : ℝ := p.1 * q.1 + (3 / 4 : ℝ) * p.2 * q.2

/-- The coordinate determinant used for affine area calculations. -/
def coordDet (p q : Point) : ℝ := p.1 * q.2 - p.2 * q.1

/-- Rotation through negative 60 degrees in oblique coordinates. -/
def rotateNeg60 (p : Point) : Point :=
  (p.1 / 2 + 3 * p.2 / 4, -p.1 + p.2 / 2)

theorem rotated_form_sum (l : Form) (p : Point) :
    formEval l p + formEval (formRotate120 l) p +
      formEval (formRotate120 (formRotate120 l)) p = 0 := by
  dsimp [formEval, formRotate120]
  ring

theorem formNormSq_rotate (l : Form) :
    formNormSq (formRotate120 l) = formNormSq l := by
  dsimp [formNormSq, formRotate120]
  ring

theorem formNormSq_neg (l : Form) : formNormSq (formNeg l) = formNormSq l := by
  rcases l with ⟨x, z⟩
  dsimp [formNormSq, formNeg]
  ring

theorem formNormSq_nonneg (l : Form) : 0 ≤ formNormSq l := by
  rcases l with ⟨x, z⟩
  dsimp [formNormSq]
  positivity

theorem formNormSq_pos_left_of_det_pos {l m : Form} (h : 0 < formDet l m) :
    0 < formNormSq l := by
  rcases l with ⟨lx, lz⟩
  rcases m with ⟨mx, mz⟩
  dsimp [formDet, formNormSq] at h ⊢
  by_contra hn
  have hz : (3 / 4 : ℝ) * lx ^ 2 + lz ^ 2 = 0 :=
    le_antisymm (le_of_not_gt hn) (by positivity)
  have hlx : lx = 0 := by
    nlinarith [sq_nonneg lx, sq_nonneg lz]
  have hlz : lz = 0 := by
    nlinarith [sq_nonneg lx, sq_nonneg lz]
  subst lx
  subst lz
  norm_num at h

theorem formNormSq_pos_right_of_det_pos {l m : Form} (h : 0 < formDet l m) :
    0 < formNormSq m := by
  rcases l with ⟨lx, lz⟩
  rcases m with ⟨mx, mz⟩
  dsimp [formDet, formNormSq] at h ⊢
  by_contra hn
  have hz : (3 / 4 : ℝ) * mx ^ 2 + mz ^ 2 = 0 :=
    le_antisymm (le_of_not_gt hn) (by positivity)
  have hmx : mx = 0 := by
    nlinarith [sq_nonneg mx, sq_nonneg mz]
  have hmz : mz = 0 := by
    nlinarith [sq_nonneg mx, sq_nonneg mz]
  subst mx
  subst mz
  norm_num at h

theorem formNorm_nonneg (l : Form) : 0 ≤ formNorm l := Real.sqrt_nonneg _

theorem formNorm_sq (l : Form) : formNorm l ^ 2 = formNormSq l := by
  exact Real.sq_sqrt (formNormSq_nonneg l)

theorem form_inner_lagrange (l m : Form) :
    formNormSq l * formNormSq m - formInner l m ^ 2 =
      (3 / 4 : ℝ) * (l.1 * m.2 - l.2 * m.1) ^ 2 := by
  rcases l with ⟨lx, lz⟩
  rcases m with ⟨mx, mz⟩
  dsimp [formNormSq, formInner]
  ring

theorem formInner_le_norm_mul_norm (l m : Form) :
    formInner l m ≤ formNorm l * formNorm m := by
  have hlag := form_inner_lagrange l m
  have hsq : formInner l m ^ 2 ≤ formNormSq l * formNormSq m := by
    nlinarith [sq_nonneg (l.1 * m.2 - l.2 * m.1)]
  have hprod : 0 ≤ formNorm l * formNorm m :=
    mul_nonneg (formNorm_nonneg l) (formNorm_nonneg m)
  have hprodSq :
      (formNorm l * formNorm m) ^ 2 = formNormSq l * formNormSq m := by
    rw [mul_pow, formNorm_sq, formNorm_sq]
  by_cases h : formInner l m ≤ 0
  · exact le_trans h hprod
  · have hpos : 0 < formInner l m := lt_of_not_ge h
    nlinarith

theorem formNorm_add_le (l m : Form) :
    formNorm (l + m) ≤ formNorm l + formNorm m := by
  have hadd :
      formNormSq (l + m) =
        formNormSq l + formNormSq m + 2 * formInner l m := by
    rcases l with ⟨lx, lz⟩
    rcases m with ⟨mx, mz⟩
    dsimp [formNormSq, formInner]
    ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact add_nonneg (formNorm_nonneg l) (formNorm_nonneg m)
  rw [hadd]
  have hi := formInner_le_norm_mul_norm l m
  rw [add_sq, formNorm_sq, formNorm_sq]
  linarith

theorem formNorm_nonneg_smul (a : ℝ) (ha : 0 ≤ a) (l : Form) :
    formNorm (a • l) = a * formNorm l := by
  have hs : formNormSq (a • l) = a ^ 2 * formNormSq l := by
    rcases l with ⟨x, z⟩
    dsimp [formNormSq]
    ring
  dsimp [formNorm]
  rw [hs, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]

/-- Determinant signs give the explicit nonnegative coordinates of a vector
inside a two-dimensional cone. -/
theorem exists_nonneg_combo_of_det {u v l : Form} (huv : 0 < formDet u v)
    (hul : 0 ≤ formDet u l) (hlv : 0 ≤ formDet l v) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ l = a • u + b • v := by
  let δ := formDet u v
  let a := formDet l v / δ
  let b := formDet u l / δ
  have hδ : 0 < δ := huv
  have ha : 0 ≤ a := div_nonneg hlv hδ.le
  have hb : 0 ≤ b := div_nonneg hul hδ.le
  refine ⟨a, b, ha, hb, ?_⟩
  rcases u with ⟨ux, uz⟩
  rcases v with ⟨vx, vz⟩
  rcases l with ⟨lx, lz⟩
  have hne : ux * vz - uz * vx ≠ 0 := by
    dsimp [δ, formDet] at hδ
    exact ne_of_gt hδ
  have hne' : vz * ux - vx * uz ≠ 0 := by
    convert hne using 1; ring
  apply Prod.ext
  · dsimp [a, b, δ, formDet]
    field_simp [hne, hne']
    ring
  · dsimp [a, b, δ, formDet]
    field_simp [hne, hne']
    ring

/-- The sum of support values at three successive equilateral-triangle normals. -/
def supportNumerator (l : Form) (p₀ p₁ p₂ : Point) : ℝ :=
  -(formEval l p₀ + formEval (formRotate120 l) p₁ +
    formEval (formRotate120 (formRotate120 l)) p₂)

theorem supportNumerator_add (l m : Form) (p₀ p₁ p₂ : Point) :
    supportNumerator (l + m) p₀ p₁ p₂ =
      supportNumerator l p₀ p₁ p₂ + supportNumerator m p₀ p₁ p₂ := by
  rcases l with ⟨lx, lz⟩
  rcases m with ⟨mx, mz⟩
  rcases p₀ with ⟨x₀, z₀⟩
  rcases p₁ with ⟨x₁, z₁⟩
  rcases p₂ with ⟨x₂, z₂⟩
  dsimp [supportNumerator, formEval, formRotate120]
  ring

theorem supportNumerator_smul (a : ℝ) (l : Form) (p₀ p₁ p₂ : Point) :
    supportNumerator (a • l) p₀ p₁ p₂ =
      a * supportNumerator l p₀ p₁ p₂ := by
  rcases l with ⟨lx, lz⟩
  rcases p₀ with ⟨x₀, z₀⟩
  rcases p₁ with ⟨x₁, z₁⟩
  rcases p₂ with ⟨x₂, z₂⟩
  dsimp [supportNumerator, formEval, formRotate120]
  ring

/-- Endpoint support certificates propagate to every direction in their cone.
This is the algebraic completeness step used by the finite orientation fan. -/
theorem support_bound_on_cone {u v l : Form} {p₀ p₁ p₂ : Point}
    (hu : formNorm u ≤ supportNumerator u p₀ p₁ p₂)
    (hv : formNorm v ≤ supportNumerator v p₀ p₁ p₂)
    (huv : 0 < formDet u v) (hul : 0 ≤ formDet u l) (hlv : 0 ≤ formDet l v) :
    formNorm l ≤ supportNumerator l p₀ p₁ p₂ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_nonneg_combo_of_det huv hul hlv
  calc
    formNorm (a • u + b • v) ≤ formNorm (a • u) + formNorm (b • v) :=
      formNorm_add_le _ _
    _ = a * formNorm u + b * formNorm v := by
      rw [formNorm_nonneg_smul a ha, formNorm_nonneg_smul b hb]
    _ ≤ a * supportNumerator u p₀ p₁ p₂ +
        b * supportNumerator v p₀ p₁ p₂ :=
      add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
    _ = supportNumerator (a • u + b • v) p₀ p₁ p₂ := by
      rw [supportNumerator_add, supportNumerator_smul, supportNumerator_smul]

theorem formEval_neg (l : Form) (p : Point) :
    formEval (formNeg l) p = -formEval l p := by
  rcases l with ⟨lx, lz⟩
  rcases p with ⟨px, pz⟩
  dsimp [formEval, formNeg]
  ring

theorem formRotate120_neg (l : Form) :
    formRotate120 (formNeg l) = formNeg (formRotate120 l) := by
  rcases l with ⟨x, z⟩
  apply Prod.ext <;> dsimp [formRotate120, formNeg] <;> ring

theorem edgeNormal_reverse (p q : Point) :
    edgeNormal q p = formNeg (edgeNormal p q) := by
  rcases p with ⟨px, pz⟩
  rcases q with ⟨qx, qz⟩
  apply Prod.ext <;> dsimp [edgeNormal, vectorNormal, formNeg] <;> ring

theorem formNormSq_edgeNormal (p q : Point) :
    formNormSq (edgeNormal p q) = sqDist p q := by
  rcases p with ⟨px, pz⟩
  rcases q with ⟨qx, qz⟩
  dsimp [formNormSq, edgeNormal, vectorNormal, sqDist]
  ring

theorem edgeNormal_equal_on_endpoints (p q : Point) :
    formEval (edgeNormal p q) p = formEval (edgeNormal p q) q := by
  rcases p with ⟨px, pz⟩
  rcases q with ⟨qx, qz⟩
  dsimp [formEval, edgeNormal, vectorNormal]
  ring

theorem edgeNormal_eval_gap (p q r : Point) :
    formEval (edgeNormal p q) r - formEval (edgeNormal p q) p =
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) := by
  rcases p with ⟨px, pz⟩
  rcases q with ⟨qx, qz⟩
  rcases r with ⟨rx, rz⟩
  dsimp [formEval, edgeNormal, vectorNormal]
  ring

theorem formRotate120_vectorNormal (p : Point) :
    formRotate120 (vectorNormal p) = vectorNormal (rotate60 p - p) := by
  rcases p with ⟨x, z⟩
  apply Prod.ext <;> dsimp [formRotate120, vectorNormal, rotate60] <;> ring

theorem formRotate120_twice_vectorNormal (p : Point) :
    formRotate120 (formRotate120 (vectorNormal p)) =
      vectorNormal (-rotate60 p) := by
  rcases p with ⟨x, z⟩
  apply Prod.ext <;> dsimp [formRotate120, vectorNormal, rotate60] <;> ring

theorem formRotate120_vectorNormal_clockwise (p : Point) :
    formRotate120 (vectorNormal p) = vectorNormal (-rotateNeg60 p) := by
  rcases p with ⟨x, z⟩
  apply Prod.ext <;> dsimp [formRotate120, vectorNormal, rotateNeg60] <;> ring

theorem formRotate120_twice_vectorNormal_clockwise (p : Point) :
    formRotate120 (formRotate120 (vectorNormal p)) =
      vectorNormal (rotateNeg60 p - p) := by
  rcases p with ⟨x, z⟩
  apply Prod.ext <;> dsimp [formRotate120, vectorNormal, rotateNeg60] <;> ring

theorem metric_lagrange (p q : Point) :
    sqDist p (0, 0) * sqDist q (0, 0) - metricInner p q ^ 2 =
      (3 / 4 : ℝ) * coordDet p q ^ 2 := by
  rcases p with ⟨px, pz⟩
  rcases q with ⟨qx, qz⟩
  dsimp [sqDist, metricInner, coordDet]
  ring

theorem metricInner_rotate60 (p : Point) :
    metricInner p (rotate60 p) = sqDist p (0, 0) / 2 := by
  rcases p with ⟨x, z⟩
  dsimp [metricInner, rotate60, sqDist]
  ring

theorem coordDet_rotate60 (p : Point) :
    coordDet p (rotate60 p) = sqDist p (0, 0) := by
  rcases p with ⟨x, z⟩
  dsimp [coordDet, rotate60, sqDist]
  ring

theorem metricInner_rotateNeg60 (p : Point) :
    metricInner p (rotateNeg60 p) = sqDist p (0, 0) / 2 := by
  rcases p with ⟨x, z⟩
  dsimp [metricInner, rotateNeg60, sqDist]
  ring

theorem coordDet_rotateNeg60 (p : Point) :
    coordDet p (rotateNeg60 p) = -sqDist p (0, 0) := by
  rcases p with ⟨x, z⟩
  dsimp [coordDet, rotateNeg60, sqDist]
  ring

theorem point_eq_of_inner_det_eq {e p q : Point} (he : 0 < sqDist e (0, 0))
    (hinner : metricInner e p = metricInner e q)
    (hdet : coordDet e p = coordDet e q) :
    p = q := by
  let w : Point := p - q
  have hiw : metricInner e w = 0 := by
    rcases e with ⟨ex, ez⟩
    rcases p with ⟨px, pz⟩
    rcases q with ⟨qx, qz⟩
    dsimp [w, metricInner] at hinner ⊢
    linarith
  have hdw : coordDet e w = 0 := by
    rcases e with ⟨ex, ez⟩
    rcases p with ⟨px, pz⟩
    rcases q with ⟨qx, qz⟩
    dsimp [w, coordDet] at hdet ⊢
    linarith
  have hlag := metric_lagrange e w
  rw [hiw, hdw] at hlag
  have hw : sqDist w (0, 0) = 0 := by
    nlinarith
  rcases p with ⟨px, pz⟩
  rcases q with ⟨qx, qz⟩
  dsimp [w, sqDist] at hw
  apply Prod.ext <;> dsimp
  · nlinarith [sq_nonneg (px - qx), sq_nonneg (pz - qz)]
  · nlinarith [sq_nonneg (px - qx), sq_nonneg (pz - qz)]

/-- For an equilateral triangle, the support gap normal to one edge has
absolute value `side²`.  This algebraic identity is the normalization used by
the finite orientation certificates. -/
theorem EquilateralTriangle.edge_support_gap_sq (T : EquilateralTriangle) :
    (formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 2) -
      formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 0)) ^ 2 =
      T.side ^ 4 := by
  let e : Point := T.vertices 1 - T.vertices 0
  let d : Point := T.vertices 2 - T.vertices 0
  have he : sqDist e (0, 0) = T.side ^ 2 := by
    simpa [e, sqDist] using T.equilateral 1 0 (by decide)
  have hd : sqDist d (0, 0) = T.side ^ 2 := by
    simpa [d, sqDist] using T.equilateral 2 0 (by decide)
  have hde : sqDist d e = T.side ^ 2 := by
    simpa [d, e, sqDist] using T.equilateral 2 1 (by decide)
  have hinner : metricInner e d = T.side ^ 2 / 2 := by
    rcases e with ⟨ex, ez⟩
    rcases d with ⟨dx, dz⟩
    dsimp [sqDist, metricInner] at he hd hde ⊢
    nlinarith
  have hlag := metric_lagrange e d
  have hdet :
      (e.1 * d.2 - e.2 * d.1) ^ 2 = T.side ^ 4 := by
    rw [he, hd, hinner] at hlag
    dsimp [coordDet] at hlag
    ring_nf at hlag
    nlinarith
  have hgap :
      formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 2) -
        formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 0) =
        e.1 * d.2 - e.2 * d.1 := by
    rw [edgeNormal_eval_gap]
    rfl
  rw [hgap, hdet]

theorem EquilateralTriangle.edge_support_gap_cases (T : EquilateralTriangle) :
    let gap :=
      formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 2) -
        formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 0)
    gap = T.side ^ 2 ∨ gap = -(T.side ^ 2) := by
  dsimp
  have h := T.edge_support_gap_sq
  have h' :
      (formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 2) -
        formEval (edgeNormal (T.vertices 0) (T.vertices 1)) (T.vertices 0)) ^ 2 =
        (T.side ^ 2) ^ 2 := by
    calc
      _ = T.side ^ 4 := h
      _ = (T.side ^ 2) ^ 2 := by
        ring
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp h'

/-- The equilateral equations classify the third vertex into the two genuine
orientations.  No alignment or orientation is assumed. -/
theorem EquilateralTriangle.thirdVertex_orientation (T : EquilateralTriangle) :
    T.vertices 2 - T.vertices 0 = rotate60 (T.vertices 1 - T.vertices 0) ∨
      T.vertices 2 - T.vertices 0 = rotateNeg60 (T.vertices 1 - T.vertices 0) := by
  let e : Point := T.vertices 1 - T.vertices 0
  let d : Point := T.vertices 2 - T.vertices 0
  have he : sqDist e (0, 0) = T.side ^ 2 := by
    simpa [e, sqDist] using T.equilateral 1 0 (by decide)
  have hd : sqDist d (0, 0) = T.side ^ 2 := by
    simpa [d, sqDist] using T.equilateral 2 0 (by decide)
  have hde : sqDist d e = T.side ^ 2 := by
    simpa [d, e, sqDist] using T.equilateral 2 1 (by decide)
  have hinner : metricInner e d = T.side ^ 2 / 2 := by
    rcases e with ⟨ex, ez⟩
    rcases d with ⟨dx, dz⟩
    dsimp [sqDist, metricInner] at he hd hde ⊢
    nlinarith
  have hepos : 0 < sqDist e (0, 0) := by
    rw [he]
    exact sq_pos_of_pos T.side_pos
  have hgap := T.edge_support_gap_cases
  have hdet :
      coordDet e d = T.side ^ 2 ∨ coordDet e d = -(T.side ^ 2) := by
    simpa [e, d, edgeNormal_eval_gap, coordDet] using hgap
  rcases hdet with hdet | hdet
  · left
    apply point_eq_of_inner_det_eq hepos
    · rw [metricInner_rotate60, he]
      exact hinner
    · rw [coordDet_rotate60, he]
      exact hdet
  · right
    apply point_eq_of_inner_det_eq hepos
    · rw [metricInner_rotateNeg60, he]
      exact hinner
    · rw [coordDet_rotateNeg60, he]
      exact hdet

/-- A lower support half-plane is convex in the rational coordinate model. -/
theorem convex_formEval_superlevel (l : Form) (c : ℝ) :
    Convex ℝ {p : Point | c ≤ formEval l p} := by
  intro p hp q hq a b ha hb hab
  calc
    c = a * c + b * c := by
      rw [← add_mul, hab, one_mul]
    _ ≤ a * formEval l p + b * formEval l q :=
      add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
    _ = formEval l (a • p + b • q) := by
      rcases p with ⟨px, pz⟩
      rcases q with ⟨qx, qz⟩
      rcases l with ⟨lx, lz⟩
      dsimp [formEval]
      ring

/-- A linear support inequality checked at all three vertices holds on the
entire filled triangle.  This is the trusted bridge from support calculations
to the carrier, rather than an assumption that a witness lies at a vertex. -/
theorem EquilateralTriangle.formEval_lower_bound (T : EquilateralTriangle)
    (l : Form) (c : ℝ) (hvertices : ∀ i, c ≤ formEval l (T.vertices i))
    {p : Point} (hp : p ∈ T.carrier) :
    c ≤ formEval l p := by
  apply convexHull_min ?_ (convex_formEval_superlevel l c) hp
  rintro _ ⟨i, rfl⟩
  exact hvertices i

/-- The analogous upper support inequality on a filled triangle. -/
theorem EquilateralTriangle.formEval_upper_bound (T : EquilateralTriangle)
    (l : Form) (c : ℝ) (hvertices : ∀ i, formEval l (T.vertices i) ≤ c)
    {p : Point} (hp : p ∈ T.carrier) :
    formEval l p ≤ c := by
  have h := T.formEval_lower_bound (-l.1, -l.2) (-c) (fun i => by
    simpa [formEval, add_comm] using neg_le_neg (hvertices i)) hp
  simpa [formEval, add_comm] using h

theorem ccw_edge_gaps (a e : Point) :
    let b := a + e
    let c := a + rotate60 e
    formEval (edgeNormal a b) c - formEval (edgeNormal a b) a = sqDist e (0, 0) ∧
    formEval (edgeNormal b c) a - formEval (edgeNormal b c) b = sqDist e (0, 0) ∧
    formEval (edgeNormal c a) b - formEval (edgeNormal c a) c = sqDist e (0, 0) := by
  rcases a with ⟨ax, az⟩
  rcases e with ⟨ex, ez⟩
  dsimp [edgeNormal, vectorNormal, formEval, rotate60, sqDist]
  constructor
  · ring
  constructor <;> ring

theorem cw_edge_gaps (a e : Point) :
    let b := a + e
    let c := a + rotateNeg60 e
    formEval (edgeNormal b a) c - formEval (edgeNormal b a) b = sqDist e (0, 0) ∧
    formEval (edgeNormal a c) b - formEval (edgeNormal a c) a = sqDist e (0, 0) ∧
    formEval (edgeNormal c b) a - formEval (edgeNormal c b) c = sqDist e (0, 0) := by
  rcases a with ⟨ax, az⟩
  rcases e with ⟨ex, ez⟩
  dsimp [edgeNormal, vectorNormal, formEval, rotateNeg60, sqDist]
  constructor
  · ring
  constructor <;> ring

theorem ccw_support_min_sum (a e : Point) :
    let b := a + e
    let c := a + rotate60 e
    let l := vectorNormal e
    formEval l a + formEval (formRotate120 l) b +
      formEval (formRotate120 (formRotate120 l)) c = -sqDist e (0, 0) := by
  rcases a with ⟨ax, az⟩
  rcases e with ⟨ex, ez⟩
  dsimp [vectorNormal, formEval, formRotate120, rotate60, sqDist]
  ring

theorem cw_support_min_sum (a e : Point) :
    let b := a + e
    let c := a + rotateNeg60 e
    let l := vectorNormal e
    formEval (formNeg l) b + formEval (formRotate120 (formNeg l)) a +
      formEval (formRotate120 (formRotate120 (formNeg l))) c = -sqDist e (0, 0) := by
  rcases a with ⟨ax, az⟩
  rcases e with ⟨ex, ez⟩
  dsimp [vectorNormal, formNeg, formEval, formRotate120, rotateNeg60, sqDist]
  ring

/-- Every equilateral triangle has one inward support orientation, independent
of the three contained points subsequently tested.  Both chiralities are
derived from the equilateral equations. -/
theorem EquilateralTriangle.exists_own_orientation_support_bound
    (T : EquilateralTriangle) :
    ∃ l : Form, 0 < formNorm l ∧
      ∀ {p₀ p₁ p₂ : Point},
        p₀ ∈ T.carrier → p₁ ∈ T.carrier → p₂ ∈ T.carrier →
        supportNumerator l p₀ p₁ p₂ ≤ T.side * formNorm l := by
  let a := T.vertices 0
  let b := T.vertices 1
  let c := T.vertices 2
  let e : Point := b - a
  let d : Point := c - a
  let l := vectorNormal e
  have hlab : edgeNormal a b = l := by
    rfl
  have he : sqDist e (0, 0) = T.side ^ 2 := by
    simpa [e, a, b, sqDist] using T.equilateral 1 0 (by decide)
  have hspos : 0 < T.side ^ 2 := sq_pos_of_pos T.side_pos
  have hb : b = a + e := by
    simp [e]
  have hsqrt : Real.sqrt (formNormSq l) = T.side := by
    have hn : formNormSq l = T.side ^ 2 := by
      rw [← he]
      rcases e with ⟨ex, ez⟩
      dsimp [l, vectorNormal, formNormSq, sqDist]
      ring
    rw [hn, Real.sqrt_sq_eq_abs, abs_of_pos T.side_pos]
  rcases T.thirdVertex_orientation with hccw | hcw
  · refine ⟨l, ?_, ?_⟩
    · dsimp [formNorm]
      rw [hsqrt]
      exact T.side_pos
    intro p₀ p₁ p₂ hp₀ hp₁ hp₂
    dsimp [supportNumerator, formNorm]
    rw [hsqrt]
    have hccw' : d = rotate60 e := by
      simpa [d, e, a, b, c] using hccw
    have hc : c = a + rotate60 e := by
      rw [show c = a + d by simp [d], hccw']
    have hl₁ : formRotate120 l = edgeNormal b c := by
      rw [show l = vectorNormal e by rfl, formRotate120_vectorNormal, ← hccw']
      congr 1
      simp [d, e, a, b, c]
    have hl₂ : formRotate120 (formRotate120 l) = edgeNormal c a := by
      rw [show l = vectorNormal e by rfl, formRotate120_twice_vectorNormal, ← hccw']
      congr 1
      simp [d, a, c]
    have hgaps := ccw_edge_gaps a e
    rw [← hb, ← hc, he] at hgaps
    obtain ⟨hgap₀, hgap₁, hgap₂⟩ := hgaps
    have h₀ := T.formEval_lower_bound (edgeNormal a b) (formEval (edgeNormal a b) a)
      (fun i => by
        fin_cases i
        · simp [a]
        · simpa [b] using (edgeNormal_equal_on_endpoints a b).le
        · simpa [c] using (show formEval (edgeNormal a b) a ≤
            formEval (edgeNormal a b) c by linarith)) hp₀
    have h₁ := T.formEval_lower_bound (edgeNormal b c) (formEval (edgeNormal b c) b)
      (fun i => by
        fin_cases i
        · simpa [a] using (show formEval (edgeNormal b c) b ≤
            formEval (edgeNormal b c) a by linarith)
        · simp [b]
        · simpa [c] using (edgeNormal_equal_on_endpoints b c).le) hp₁
    have h₂ := T.formEval_lower_bound (edgeNormal c a) (formEval (edgeNormal c a) c)
      (fun i => by
        fin_cases i
        · simpa [a] using (edgeNormal_equal_on_endpoints c a).le
        · simpa [b] using (show formEval (edgeNormal c a) c ≤
            formEval (edgeNormal c a) b by linarith)
        · simp [c]) hp₂
    rw [hlab] at h₀
    rw [← hl₁] at h₁
    rw [← hl₂] at h₂
    have hsum :
        formEval l a + formEval (formRotate120 l) b +
          formEval (formRotate120 (formRotate120 l)) c = -(T.side ^ 2) := by
      have hs := ccw_support_min_sum a e
      rw [← hb, ← hc, he] at hs
      exact hs
    calc
      -(formEval l p₀ + formEval (formRotate120 l) p₁ +
          formEval (formRotate120 (formRotate120 l)) p₂) ≤ T.side ^ 2 := by
        linarith
      _ = T.side * T.side := by
        ring
  · refine ⟨formNeg l, ?_, ?_⟩
    · dsimp [formNorm]
      rw [formNormSq_neg, hsqrt]
      exact T.side_pos
    intro p₀ p₁ p₂ hp₀ hp₁ hp₂
    dsimp [supportNumerator, formNorm]
    rw [formNormSq_neg, hsqrt]
    have hcw' : d = rotateNeg60 e := by
      simpa [d, e, a, b, c] using hcw
    have hc : c = a + rotateNeg60 e := by
      rw [show c = a + d by simp [d], hcw']
    have hl₁old : formRotate120 l = edgeNormal c a := by
      rw [show l = vectorNormal e by rfl, formRotate120_vectorNormal_clockwise, ← hcw']
      congr 1
      simp [d, a, c]
    have hl₂old : formRotate120 (formRotate120 l) = edgeNormal b c := by
      rw [show l = vectorNormal e by rfl, formRotate120_twice_vectorNormal_clockwise, ← hcw']
      congr 1
      simp [d, e, a, b, c]
    have hl₀ : formNeg l = edgeNormal b a := by
      rw [edgeNormal_reverse a b]
      rfl
    have hl₁ : formRotate120 (formNeg l) = edgeNormal a c := by
      rw [formRotate120_neg, hl₁old, ← edgeNormal_reverse c a]
    have hl₂ : formRotate120 (formRotate120 (formNeg l)) = edgeNormal c b := by
      rw [formRotate120_neg, formRotate120_neg, hl₂old, ← edgeNormal_reverse b c]
    have hgaps := cw_edge_gaps a e
    rw [← hb, ← hc, he] at hgaps
    obtain ⟨hgap₀, hgap₁, hgap₂⟩ := hgaps
    have h₀ := T.formEval_lower_bound (edgeNormal b a) (formEval (edgeNormal b a) b)
      (fun i => by
        fin_cases i
        · simpa [a] using (edgeNormal_equal_on_endpoints b a).le
        · simp [b]
        · simpa [c] using (show formEval (edgeNormal b a) b ≤
            formEval (edgeNormal b a) c by linarith)) hp₀
    have h₁ := T.formEval_lower_bound (edgeNormal a c) (formEval (edgeNormal a c) a)
      (fun i => by
        fin_cases i
        · simp [a]
        · simpa [b] using (show formEval (edgeNormal a c) a ≤
            formEval (edgeNormal a c) b by linarith)
        · simpa [c] using (edgeNormal_equal_on_endpoints a c).le) hp₁
    have h₂ := T.formEval_lower_bound (edgeNormal c b) (formEval (edgeNormal c b) c)
      (fun i => by
        fin_cases i
        · simpa [a] using (show formEval (edgeNormal c b) c ≤
            formEval (edgeNormal c b) a by linarith)
        · simpa [b] using (edgeNormal_equal_on_endpoints c b).le
        · simp [c]) hp₂
    rw [← hl₀] at h₀
    rw [← hl₁] at h₁
    rw [← hl₂] at h₂
    have hsum :
        formEval (formNeg l) b + formEval (formRotate120 (formNeg l)) a +
          formEval (formRotate120 (formRotate120 (formNeg l))) c = -(T.side ^ 2) := by
      have hs := cw_support_min_sum a e
      rw [← hb, ← hc, he] at hs
      exact hs
    calc
      -(formEval (formNeg l) p₀ + formEval (formRotate120 (formNeg l)) p₁ +
          formEval (formRotate120 (formRotate120 (formNeg l))) p₂) ≤ T.side ^ 2 := by
        linarith
      _ = T.side * T.side := by
        ring

/-- Exact algebra behind the certificate test `N >= 0`, `N*N >= D`. -/
theorem candidate_bound {N D : ℝ} (hN : 0 ≤ N) (hD : 0 < D) (hgap : D ≤ N ^ 2) :
    1 ≤ N / Real.sqrt D := by
  have hs₀ := Real.sqrt_nonneg D
  have hs₂ := Real.sq_sqrt (le_of_lt hD)
  have hs : Real.sqrt D ≤ N := by
    nlinarith
  apply (le_div_iff₀ (Real.sqrt_pos.2 hD)).2
  simpa using hs

/-- Sum three chosen support inequalities. No minimizer-selection assumption is needed. -/
theorem support_sum_bound (l : Form) (p₀ p₁ p₂ c : Point) (s₀ s₁ s₂ r D : ℝ)
    (h₀ : 0 ≤ formEval l p₀ - formEval l c + s₀)
    (h₁ : 0 ≤ formEval (formRotate120 l) p₁ - formEval (formRotate120 l) c + s₁)
    (h₂ : 0 ≤ formEval (formRotate120 (formRotate120 l)) p₂ -
      formEval (formRotate120 (formRotate120 l)) c + s₂)
    (hs : s₀ + s₁ + s₂ = r * Real.sqrt D) :
    -(formEval l p₀ + formEval (formRotate120 l) p₁ +
      formEval (formRotate120 (formRotate120 l)) p₂) ≤ r * Real.sqrt D := by
  have hsum := rotated_form_sum l c
  linarith

end ConwaySoifer.SevenTriangles
