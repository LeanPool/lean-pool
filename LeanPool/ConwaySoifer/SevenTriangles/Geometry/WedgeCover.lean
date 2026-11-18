/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Area
public import Mathlib.Data.Fin.VecNotation
public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.WedgeInequalities
import Mathlib.Tactic.NormNum.RealSqrt

/-! Triangle containment and polygon area bounds in ray coordinates. -/

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

open MeasureTheory

namespace ConwaySoifer.SevenTriangles

/-- The six unit-hexagon facet functionals, each normalized to level one. -/
def sideForm : Fin 6 → Form :=
  ![(1, 1 / 2), (0, 1), (-1, 1 / 2), (-1, -1 / 2), (0, -1), (1, -1 / 2)]

/-! ### Toolkit: membership in a filled triangle -/

/-- A convex combination of three points lies in their hull. -/
theorem mem_convexHull_triangle_of_weights (a b c p : Point) {w₁ w₂ w₃ : ℝ}
    (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (h₃ : 0 ≤ w₃) (hsum : w₁ + w₂ + w₃ = 1)
    (hp : p = w₁ • a + w₂ • b + w₃ • c) : p ∈ convexHull ℝ {a, b, c} := by
  have hconv := convex_convexHull ℝ ({a, b, c} : Set Point)
  have hmem : ∀ i : Fin 3, (![a, b, c] i) ∈ convexHull ℝ ({a, b, c} : Set Point) := by
    intro i
    apply subset_convexHull
    fin_cases i <;> simp
  have := hconv.sum_mem (t := Finset.univ) (w := ![w₁, w₂, w₃]) (z := ![a, b, c])
    (fun i _ => by fin_cases i <;> simpa) (by simp [Fin.sum_univ_three, hsum])
    (fun i _ => hmem i)
  simpa [Fin.sum_univ_three, hp] using this

theorem coordDet_barycentric_sum (a b c p : Point) :
    coordDet (c - b) (p - b) + coordDet (a - c) (p - c) + coordDet (b - a) (p - a) =
      coordDet (b - a) (c - a) := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  rcases c with ⟨c1, c2⟩
  rcases p with ⟨p1, p2⟩
  simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
  ring

theorem coordDet_barycentric_point (a b c p : Point) :
    coordDet (b - a) (c - a) • p =
      coordDet (c - b) (p - b) • a + coordDet (a - c) (p - c) • b + coordDet (b - a) (p - a) • c :=
          by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  rcases c with ⟨c1, c2⟩
  rcases p with ⟨p1, p2⟩
  simp only [coordDet, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
    Prod.mk.injEq]
  constructor <;> ring

/-- Half-plane description of a positively oriented triangle: the three edge inequalities put a
point into the filled triangle. -/
theorem mem_convexHull_triangle (a b c p : Point) (hdet : 0 < coordDet (b - a) (c - a))
    (h₁ : 0 ≤ coordDet (b - a) (p - a)) (h₂ : 0 ≤ coordDet (c - b) (p - b))
    (h₃ : 0 ≤ coordDet (a - c) (p - c)) : p ∈ convexHull ℝ {a, b, c} := by
  set D := coordDet (b - a) (c - a) with hD
  have hsum := coordDet_barycentric_sum a b c p
  have hpt := coordDet_barycentric_point a b c p
  apply mem_convexHull_triangle_of_weights a b c p (w₁ := coordDet (c - b) (p - b) / D)
    (w₂ := coordDet (a - c) (p - c) / D) (w₃ := coordDet (b - a) (p - a) / D)
    (div_nonneg h₂ hdet.le) (div_nonneg h₃ hdet.le) (div_nonneg h₁ hdet.le)
  · rw [← add_div, ← add_div, hsum, ← hD, div_self hdet.ne']
  · have hDne : D ≠ 0 := hdet.ne'
    calc
      p = D⁻¹ • (D • p) := by
        rw [smul_smul, inv_mul_cancel₀ hDne, one_smul]
      _ = _ := by
        rw [← hD] at hpt
        rw [hpt, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
        simp only [div_eq_inv_mul]

/-! ### The polygon in ray coordinates

Write points of the wedge at `vertex i` as `vertex i + α • u + β • w` with `u, w` the unit
directions
of the two rays.  The three edge functionals of an equilateral triangle become
`σₖ + cₖ α + c_{k+1} β` (the coefficient along the second ray is the cyclic shift of the first),
with `σ₀ + σ₁ + σ₂ = s²`, `c₀ + c₁ + c₂ = 0`, `c₀² + c₁² + c₂² = 2 s²`.  Everything below is pure
algebra in these coordinates; `Point = ℝ × ℝ` is reused for ray coordinates, `coordDet` for areas.
-/

/-- Membership in `T ∩ W` in ray coordinates. -/
def InPoly (σ₀ σ₁ σ₂ c₀ c₁ c₂ : ℝ) (q : Point) : Prop :=
  0 ≤ q.1 ∧ 0 ≤ q.2 ∧ 0 ≤ σ₀ + c₀ * q.1 + c₁ * q.2 ∧ 0 ≤ σ₁ + c₁ * q.1 + c₂ * q.2 ∧
    0 ≤ σ₂ + c₂ * q.1 + c₀ * q.2

theorem inPoly_shift (σ₀ σ₁ σ₂ c₀ c₁ c₂ : ℝ) (q : Point) :
    InPoly σ₁ σ₂ σ₀ c₁ c₂ c₀ q ↔ InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ q := by
  unfold InPoly
  tauto

/-- Area of a triangle in ray coordinates. -/
def triArea (q₁ q₂ q₃ : Point) : ℝ := |coordDet (q₂ - q₁) (q₃ - q₁)| / 2

theorem triArea_nonneg (q₁ q₂ q₃ : Point) : 0 ≤ triArea q₁ q₂ q₃ := by
  unfold triArea
  positivity

theorem triArea_self (q : Point) : triArea q q q = 0 := by
  simp [triArea, coordDet]

theorem triArea_of_nonneg {q₁ q₂ q₃ : Point} (h : 0 ≤ coordDet (q₂ - q₁) (q₃ - q₁)) :
    triArea q₁ q₂ q₃ = coordDet (q₂ - q₁) (q₃ - q₁) / 2 := by
  rw [triArea, abs_of_nonneg h]

/-- The polygon is covered by three (possibly degenerate) triangles of total area at most `A`. -/
def CoverBound (σ₀ σ₁ σ₂ c₀ c₁ c₂ A : ℝ) : Prop :=
  ∃ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ q₉ : Point,
    (∀ q, InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ q →
      q ∈ convexHull ℝ {q₁, q₂, q₃} ∨ q ∈ convexHull ℝ {q₄, q₅, q₆} ∨
        q ∈ convexHull ℝ {q₇, q₈, q₉}) ∧
    triArea q₁ q₂ q₃ + triArea q₄ q₅ q₆ + triArea q₇ q₈ q₉ ≤ A

theorem CoverBound.mono {σ₀ σ₁ σ₂ c₀ c₁ c₂ A B : ℝ} (h : CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ A)
    (hAB : A ≤ B) : CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ B := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉, hcov, harea⟩ := h
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉, hcov, harea.trans hAB⟩

theorem CoverBound.shift {σ₀ σ₁ σ₂ c₀ c₁ c₂ A : ℝ} (h : CoverBound σ₁ σ₂ σ₀ c₁ c₂ c₀ A) :
    CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ A := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉, hcov, harea⟩ := h
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉,
    fun q hq => hcov q ((inPoly_shift _ _ _ _ _ _ q).2 hq), harea⟩

/-- Both rays exit through the same side `σ + c α + d β = 0`: the polygon is the triangle
`O, A, B`. -/
theorem coverBound_same_side (σ₀ σ₁ σ₂ c₀ c₁ c₂ a b σ c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hσ : 0 < σ) (hca : σ + c * a = 0) (hdb : σ + d * b = 0)
    (hL : ∀ q, InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ q → 0 ≤ σ + c * q.1 + d * q.2) :
    CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (a * b / 2) := by
  refine ⟨(0, 0), (a, 0), (0, b), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), ?_, ?_⟩
  · intro q hq
    left
    have hLq := hL q hq
    obtain ⟨h1, h2, -⟩ := hq
    apply mem_convexHull_triangle
    · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
      nlinarith
    · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
      nlinarith
    · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
      have key : σ * ((0 - a) * (q.2 - 0) - (b - 0) * (q.1 - a)) =
          a * b * (σ + c * q.1 + d * q.2) := by
        linear_combination (-(a * q.2)) * hdb + (-(b * q.1)) * hca
      have h0 : 0 ≤ σ * ((0 - a) * (q.2 - 0) - (b - 0) * (q.1 - a)) := by
        rw [key]
        positivity
      exact nonneg_of_mul_nonneg_right h0 hσ
    · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
      nlinarith
  · rw [triArea_self]
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith

/-- Quadrilateral case: the first ray exits through side `0`, the second through side `2`, and the
common vertex `V₀` of these sides lies strictly inside the wedge.  Two triangles `O A V₀`, `O V₀ B`.
-/
theorem coverBound_quad (c₀ c₁ σ₁ a b : ℝ) (hc₀ : c₀ < 0) (ha : 0 < a) (hb : 0 < b)
    (hL₀B : 0 < -c₀ * a + c₁ * b) (hL₂A : 0 < -c₀ * b + (-c₀ - c₁) * a) :
    CoverBound (-c₀ * a) σ₁ (-c₀ * b) c₀ c₁ (-c₀ - c₁)
      (c₀ * (2 * c₀ * a * b + (c₀ + c₁) * a ^ 2 - c₁ * b ^ 2) /
        (2 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2))) := by
  have hD : 0 < c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 := quadDet_pos hc₀.ne
  have hDne : c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 ≠ 0 := hD.ne'
  obtain ⟨α₀, hα₀⟩ : ∃ x : ℝ, x * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) = c₀ * (c₀ * a - c₁ * b) :=
    ⟨_, div_mul_cancel₀ _ hDne⟩
  obtain ⟨β₀, hβ₀⟩ : ∃ x : ℝ, x * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) = c₀ * (c₀ * b + (c₀ + c₁) * a) :=
    ⟨_, div_mul_cancel₀ _ hDne⟩
  have hα₀pos : 0 < α₀ := by
    have h : 0 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) < α₀ * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) := by
      rw [zero_mul, hα₀]
      exact mul_pos_of_neg_of_neg hc₀ (by linarith)
    exact lt_of_mul_lt_mul_right h hD.le
  have hβ₀pos : 0 < β₀ := by
    have h : 0 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) < β₀ * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) := by
      rw [zero_mul, hβ₀]
      exact mul_pos_of_neg_of_neg hc₀ (by linarith)
    exact lt_of_mul_lt_mul_right h hD.le
  -- the two half-plane identities
  have idA : ∀ q : Point, (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) * ((α₀ - a) * (q.2 - 0) - (β₀ - 0) * (q.1 -
      a)) =
      (-c₀ * b + (-c₀ - c₁) * a) * (-c₀ * a + c₀ * q.1 + c₁ * q.2) := by
    intro q
    linear_combination (q.2) * hα₀ + (a - q.1) * hβ₀
  have idB : ∀ q : Point, (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) *
      ((0 - α₀) * (q.2 - β₀) - (b - β₀) * (q.1 - α₀)) =
      (-c₀ * a + c₁ * b) * (-c₀ * b + (-c₀ - c₁) * q.1 + c₀ * q.2) := by
    intro q
    linear_combination (b - q.2) * hα₀ + (q.1) * hβ₀
  refine ⟨(0, 0), (a, 0), (α₀, β₀), (0, 0), (α₀, β₀), (0, b), (0, 0), (0, 0), (0, 0), ?_, ?_⟩
  · intro q hq
    obtain ⟨h1, h2, hL0, -, hL2⟩ := hq
    rcases le_or_gt (α₀ * q.2 - β₀ * q.1) 0 with hcase | hcase
    · left
      apply mem_convexHull_triangle
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith only [mul_pos ha hβ₀pos]
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith only [mul_nonneg ha.le h2]
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        have h0 : 0 ≤ (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) *
            ((α₀ - a) * (q.2 - 0) - (β₀ - 0) * (q.1 - a)) := by
          rw [idA q]
          exact mul_nonneg hL₂A.le hL0
        exact nonneg_of_mul_nonneg_right h0 hD
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith only [hcase]
    · right; left
      apply mem_convexHull_triangle
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith only [mul_pos hα₀pos hb]
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith only [hcase]
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        have h0 : 0 ≤ (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) *
            ((0 - α₀) * (q.2 - β₀) - (b - β₀) * (q.1 - α₀)) := by
          rw [idB q]
          exact mul_nonneg hL₀B.le hL2
        exact nonneg_of_mul_nonneg_right h0 hD
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith only [mul_nonneg hb.le h1]
  · rw [triArea_self]
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [abs_of_nonneg (by nlinarith only [mul_nonneg ha.le hβ₀pos.le]),
      abs_of_nonneg (by nlinarith only [mul_nonneg hα₀pos.le hb.le])]
    have key : (a * β₀ + α₀ * b) * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) =
        c₀ * (2 * c₀ * a * b + (c₀ + c₁) * a ^ 2 - c₁ * b ^ 2) := by
      linear_combination a * hβ₀ + b * hα₀
    rw [← key, le_div_iff₀ (by positivity)]
    exact le_of_eq (by ring)

/-- Pentagonal case: the first ray exits through side `0`, the second through side `1`, and the
common vertex `V₁` of these sides is outside the wedge; the other two vertices `V₀, V₂` are inside.
Three triangles `O A V₀`, `O V₀ B`, `V₀ V₂ B`.  Here `c₁ = -c₀ - c₂` and `σ₂ = D + c₀ a + c₂ b`. -/
theorem coverBound_pent (c₀ c₂ σ₂ a b : ℝ) (hc₀ : c₀ < 0) (hc₂ : c₂ < 0) (ha : 0 < a) (hb : 0 < b)
    (hσ₂ : σ₂ = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 + c₀ * a + c₂ * b)
    (hL₂A : 0 ≤ σ₂ + c₂ * a) (hL₂B : 0 < σ₂ + c₀ * b) :
    CoverBound (-c₀ * a) (-c₂ * b) σ₂ c₀ (-c₀ - c₂) c₂
      (((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 -
        (-c₀ * (-c₀ - c₂) * a ^ 2 + 2 * c₀ * c₂ * a * b - c₂ * (-c₀ - c₂) * b ^ 2)) /
        (2 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2))) := by
  have hD : 0 < c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 := quadDet_pos hc₀.ne
  have hDne : c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 ≠ 0 := hD.ne'
  have hc0sq : 0 < c₀ ^ 2 := by
    rw [sq]; exact mul_pos_of_neg_of_neg hc₀ hc₀
  obtain ⟨α₀, hα₀⟩ : ∃ x : ℝ, x * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) = c₀ ^ 2 * a + (-c₀ - c₂) * σ₂ := ⟨_,
      div_mul_cancel₀ _ hDne⟩
  obtain ⟨β₀, hβ₀⟩ : ∃ x : ℝ, x * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) = -c₀ * (σ₂ + c₂ * a) := ⟨_,
      div_mul_cancel₀ _ hDne⟩
  obtain ⟨α₂, hα₂⟩ : ∃ x : ℝ, x * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) = -c₂ * (σ₂ + c₀ * b) := ⟨_,
      div_mul_cancel₀ _ hDne⟩
  obtain ⟨β₂, hβ₂⟩ : ∃ x : ℝ, x * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) = (-c₀ - c₂) * σ₂ + c₂ ^ 2 * b := ⟨_,
      div_mul_cancel₀ _ hDne⟩
  have hσ₂pos : 0 < σ₂ := by
    have := mul_neg_of_neg_of_pos hc₀ hb
    linarith
  have hα₀pos : 0 < α₀ := by
    have h : 0 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) < α₀ * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) := by
      rw [zero_mul, hα₀]
      have h1 : 0 < c₀ ^ 2 * a := mul_pos hc0sq ha
      have h2 : 0 < (-c₀ - c₂) * σ₂ := mul_pos (by linarith) hσ₂pos
      linarith
    exact lt_of_mul_lt_mul_right h hD.le
  have hβ₀nn : 0 ≤ β₀ := by
    have h : 0 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ≤ β₀ * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) := by
      rw [zero_mul, hβ₀]
      exact mul_nonneg (by linarith) hL₂A
    exact le_of_mul_le_mul_right h hD
  have hα₂pos : 0 < α₂ := by
    have h : 0 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) < α₂ * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) := by
      rw [zero_mul, hα₂]
      exact mul_pos (by linarith) hL₂B
    exact lt_of_mul_lt_mul_right h hD.le
  -- differences, cleared of denominators
  have E1 : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * (α₂ - α₀) = -c₂ * (σ₂ + c₀ * b) - (c₀ ^ 2 * a + (-c₀ - c₂)
      * σ₂) := by
    linear_combination hα₂ - hα₀
  have E2 : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * (β₂ - β₀) = ((-c₀ - c₂) * σ₂ + c₂ ^ 2 * b) - (-c₀ * (σ₂ +
      c₂ * a)) := by
    linear_combination hβ₂ - hβ₀
  have E3 : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * α₀ = c₀ ^ 2 * a + (-c₀ - c₂) * σ₂ := by
    linear_combination hα₀
  have E4 : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * β₀ = -c₀ * (σ₂ + c₂ * a) := by
    linear_combination hβ₀
  -- orientation of the third triangle
  have hdet3 : (α₂ - α₀) * (b - β₀) - (β₂ - β₀) * (0 - α₀) = σ₂ + c₀ * b := by
    have e : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 * ((α₂ - α₀) * (b - β₀) - (β₂ - β₀) * (0 - α₀)) =
        ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * (α₂ - α₀)) * ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * b - (c₀ ^ 2 + c₀
            * c₂ + c₂ ^ 2) * β₀) - ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * (β₂ - β₀)) * (0 - (c₀ ^ 2 + c₀ *
            c₂ + c₂ ^ 2) * α₀) := by
          ring
    rw [E1, E2, E3, E4] at e
    have e' : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 * ((α₂ - α₀) * (b - β₀) - (β₂ - β₀) * (0 - α₀)) = (c₀
        ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 * (σ₂ + c₀ * b) := by
      rw [e, hσ₂]
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hDne) e'
  -- half-plane identities
  have idA : ∀ q : Point, (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * ((α₀ - a) * (q.2 - 0) - (β₀ - 0) * (q.1 -
      a)) =
      (σ₂ + c₂ * a) * (-c₀ * a + c₀ * q.1 + (-c₀ - c₂) * q.2) := by
    intro q
    linear_combination (q.2) * hα₀ + (a - q.1) * hβ₀
  have idC1 : ∀ q : Point, (α₂ - α₀) * (q.2 - β₀) - (β₂ - β₀) * (q.1 - α₀) =
      σ₂ + c₂ * q.1 + c₀ * q.2 := by
    intro q
    have e : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 * ((α₂ - α₀) * (q.2 - β₀) - (β₂ - β₀) * (q.1 - α₀)) =
        ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * (α₂ - α₀)) * ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * q.2 - (c₀ ^ 2 +
            c₀ * c₂ + c₂ ^ 2) * β₀) - ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * (β₂ - β₀)) * ((c₀ ^ 2 + c₀ * c₂
            + c₂ ^ 2) * q.1 - (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * α₀) := by
          ring
    rw [E1, E2, E3, E4] at e
    have e' : (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 * ((α₂ - α₀) * (q.2 - β₀) - (β₂ - β₀) * (q.1 - α₀)) =
        (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 * (σ₂ + c₂ * q.1 + c₀ * q.2) := by
      rw [e, hσ₂]
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hDne) e'
  have idC2 : ∀ q : Point, (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * ((0 - α₂) * (q.2 - β₂) - (b - β₂) * (q.1 -
      α₂)) =
      (σ₂ + c₀ * b) * (-c₂ * b + (-c₀ - c₂) * q.1 + c₂ * q.2) := by
    intro q
    linear_combination (b - q.2) * hα₂ + (q.1) * hβ₂
  -- areas of the three triangles
  have hA1 : triArea (0, 0) (a, 0) (α₀, β₀) = a * β₀ / 2 := by
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [abs_of_nonneg (by nlinarith only [mul_nonneg ha.le hβ₀nn])]
    ring
  have hA2 : triArea (0, 0) (α₀, β₀) (0, b) = α₀ * b / 2 := by
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [abs_of_nonneg (by nlinarith only [mul_pos hα₀pos hb])]
    ring
  have hA3 : triArea (α₀, β₀) (α₂, β₂) (0, b) = (σ₂ + c₀ * b) / 2 := by
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [hdet3, abs_of_nonneg hL₂B.le]
  have key : (a * β₀ + α₀ * b + (σ₂ + c₀ * b)) * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) =
      (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 - (-c₀ * (-c₀ - c₂) * a ^ 2 + 2 * c₀ * c₂ * a * b - c₂ * (-c₀
          - c₂) * b ^ 2) := by
    simp only [hσ₂] at hα₀ hβ₀ ⊢
    linear_combination a * hβ₀ + b * hα₀
  clear E1 E2 E3 E4
  refine ⟨(0, 0), (a, 0), (α₀, β₀), (0, 0), (α₀, β₀), (0, b), (α₀, β₀), (α₂, β₂), (0, b), ?_, ?_⟩
  · intro q hq
    obtain ⟨h1, h2, hL0, hL1, hL2⟩ := hq
    have hb1 := mul_nonneg hb.le h1
    have ha2 := mul_nonneg ha.le h2
    rcases lt_or_ge (α₀ * q.2 - β₀ * q.1) 0 with hcase | hcase
    · left
      have hβ₀pos : 0 < β₀ := by
        by_contra hneg
        push Not at hneg
        have e1 := mul_nonneg hα₀pos.le h2
        have e2 := mul_nonneg (neg_nonneg.2 hneg) h1
        linarith
      have hab := mul_pos ha hβ₀pos
      apply mem_convexHull_triangle
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        linarith
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        linarith
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        have h0 : 0 ≤ (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) * ((α₀ - a) * (q.2 - 0) - (β₀ - 0) * (q.1 - a)) :=
            by
          rw [idA q]
          exact mul_nonneg hL₂A hL0
        exact nonneg_of_mul_nonneg_right h0 hD
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        linarith
    · rcases le_or_gt 0 ((0 - α₀) * (q.2 - β₀) - (b - β₀) * (q.1 - α₀)) with hcase2 | hcase2
      · right; left
        have hab := mul_pos hα₀pos hb
        apply mem_convexHull_triangle
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          linarith
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          linarith
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          exact hcase2
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          linarith
      · right; right
        apply mem_convexHull_triangle
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          rw [hdet3]
          exact hL₂B
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          rw [idC1 q]
          exact hL2
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          have h0 : 0 ≤ (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) *
              ((0 - α₂) * (q.2 - β₂) - (b - β₂) * (q.1 - α₂)) := by
            rw [idC2 q]
            exact mul_nonneg hL₂B.le hL1
          exact nonneg_of_mul_nonneg_right h0 hD
        · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
          linarith
  · rw [hA1, hA2, hA3, le_div_iff₀ (by positivity)]
    exact le_of_eq (by linear_combination key)

/-- The case tree when the first ray exits through side `0`. -/
theorem coverBound_zero (s σ₀ σ₁ σ₂ c₀ c₁ c₂ a b : ℝ) (hs : 0 < s) (hσ₀ : 0 ≤ σ₀) (hσ₁ : 0 ≤ σ₁)
    (hσ₂ : 0 ≤ σ₂) (hsum : σ₀ + σ₁ + σ₂ = s ^ 2) (hc : c₀ + c₁ + c₂ = 0)
    (hc2 : c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 = 2 * s ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hA : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (a, 0)) (hB : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (0, b))
    (hc₀ : c₀ < 0) (hexA : σ₀ + c₀ * a = 0)
    (hexB : (σ₀ + c₁ * b = 0 ∧ c₁ < 0) ∨ (σ₁ + c₂ * b = 0 ∧ c₂ < 0) ∨ (σ₂ + c₀ * b = 0 ∧ c₀ < 0))
    (hdiam : a ^ 2 + a * b + b ^ 2 ≤ s ^ 2) :
    CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2) ∧
      (s < a + b → CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2)) := by
  obtain ⟨-, -, -, hL₁A, hL₂A⟩ := hA
  obtain ⟨-, -, hL₀B, hL₁B, hL₂B⟩ := hB
  simp only [mul_zero, add_zero] at hL₁A hL₂A hL₀B hL₁B hL₂B
  have hσ₀e : σ₀ = -c₀ * a := by
    linarith
  subst hσ₀e
  have hc₂e : c₂ = -c₀ - c₁ := by
    linarith
  have hD : s ^ 2 = c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 := by
    rw [hc₂e] at hc2
    linear_combination (-1 / 2 : ℝ) * hc2
  rcases lt_or_ge c₁ 0 with hc₁ | hc₁
  · -- type 2a: `c₁ < 0`, `c₂ > 0`
    subst hc₂e
    have hc₂pos : 0 < -c₀ - c₁ := by
      linarith
    rcases lt_or_eq_of_le hL₀B with hstrict | heq
    · -- the second ray exits through side 2: quadrilateral
      have hσ₂e : σ₂ = -c₀ * b := by
        rcases hexB with h | h | h
        · linarith [h.1]
        · linarith [h.2]
        · linarith [h.1]
      subst hσ₂e
      have hσ₁e : σ₁ = c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b) := by
        linarith
      subst hσ₁e
      have hL₂A' : 0 < -c₀ * b + (-c₀ - c₁) * a := by
        have := mul_pos hc₂pos ha
        nlinarith
      have hcov := coverBound_quad c₀ c₁ (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b)) a b hc₀ ha hb
        hstrict hL₂A'
      have hbd := quad_bound s c₀ c₁ a b hs hc₀ ha hb hD (by linarith) (by linarith) (by linarith)
        hstrict hL₂A'
      exact ⟨hcov.mono hbd.1, fun hab => hcov.mono (hbd.2 hab)⟩
    · -- both rays exit through side 0: triangle
      have hcov := coverBound_same_side (-c₀ * a) σ₁ σ₂ c₀ c₁ (-c₀ - c₁) a b (-c₀ * a) c₀ c₁ ha hb
        (by nlinarith) (by ring) (by linarith) (fun q hq => hq.2.2.1)
      have hbd := same_side_bound s a b hdiam
      exact ⟨hcov.mono hbd.1, fun _ => hcov.mono hbd.2⟩
  · rcases lt_or_ge c₂ 0 with hc₂ | hc₂
    · -- type 2b: `c₂ < 0`, `c₁ > 0`
      have hc₁e : c₁ = -c₀ - c₂ := by
        linarith
      subst hc₁e
      have hD' : s ^ 2 = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 := by
        rw [hD]; ring
      rcases lt_or_eq_of_le hL₂B with hstrict | heq
      · -- the second ray exits through side 1: pentagon
        have hσ₁e : σ₁ = -c₂ * b := by
          rcases hexB with h | h | h
          · linarith [h.2]
          · linarith [h.1]
          · linarith [h.1]
        subst hσ₁e
        have hσ₂e : σ₂ = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 + c₀ * a + c₂ * b := by
          linarith
        have hcov := coverBound_pent c₀ c₂ σ₂ a b hc₀ hc₂ ha hb hσ₂e hL₂A hstrict
        have hbd := pent_bound s c₀ c₂ σ₂ a b hs hc₀ hc₂ ha hb hD' hσ₂e hL₂A hstrict
        exact ⟨hcov.mono hbd.1, fun hab => hcov.mono (hbd.2 hab)⟩
      · -- the second ray exits through side 2
        have hσ₂e : σ₂ = -c₀ * b := by
          linarith
        subst hσ₂e
        rcases lt_or_eq_of_le hL₂A with hstrictA | heqA
        · -- quadrilateral with `V₀` strictly inside
          have hσ₁e : σ₁ = c₀ ^ 2 + c₀ * (-c₀ - c₂) + (-c₀ - c₂) ^ 2 + c₀ * (a + b) := by
            linarith
          subst hσ₁e
          have hL₀B' : 0 < -c₀ * a + (-c₀ - c₂) * b := by
            have := mul_pos (neg_pos.2 hc₀) ha
            have := mul_nonneg (by linarith : (0 : ℝ) ≤ -c₀ - c₂) hb.le
            linarith
          have hL₂A' : 0 < -c₀ * b + (-c₀ - (-c₀ - c₂)) * a := by
            have e : -c₀ - (-c₀ - c₂) = c₂ := by
              ring
            rw [e]
            exact hstrictA
          have hcov := coverBound_quad c₀ (-c₀ - c₂)
            (c₀ ^ 2 + c₀ * (-c₀ - c₂) + (-c₀ - c₂) ^ 2 + c₀ * (a + b)) a b hc₀ ha hb hL₀B' hL₂A'
          have hbd := quad_bound s c₀ (-c₀ - c₂) a b hs hc₀ ha hb hD (by linarith) (by linarith)
            (by linarith) hL₀B' hL₂A'
          have e : -c₀ - (-c₀ - c₂) = c₂ := by
            ring
          rw [e] at hcov
          exact ⟨hcov.mono hbd.1, fun hab => hcov.mono (hbd.2 hab)⟩
        · -- both rays exit through side 2: triangle
          have hcov := coverBound_same_side (-c₀ * a) σ₁ (-c₀ * b) c₀ (-c₀ - c₂) c₂ a b (-c₀ * b)
            c₂ c₀ ha hb (by nlinarith) (by linarith) (by ring) (fun q hq => hq.2.2.2.2)
          have hbd := same_side_bound s a b hdiam
          exact ⟨hcov.mono hbd.1, fun _ => hcov.mono hbd.2⟩
    · -- type 1: `c₁ ≥ 0`, `c₂ ≥ 0`: the second ray exits through side 2
      subst hc₂e
      have hσ₂e : σ₂ = -c₀ * b := by
        rcases hexB with h | h | h
        · linarith [h.2]
        · linarith [h.2]
        · linarith [h.1]
      subst hσ₂e
      have hσ₁e : σ₁ = c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b) := by
        linarith
      subst hσ₁e
      have hL₀B' : 0 < -c₀ * a + c₁ * b := by
        have := mul_pos (neg_pos.2 hc₀) ha
        have := mul_nonneg hc₁ hb.le
        linarith
      have hL₂A' : 0 < -c₀ * b + (-c₀ - c₁) * a := by
        have := mul_pos (neg_pos.2 hc₀) hb
        have := mul_nonneg hc₂ ha.le
        linarith
      have hcov := coverBound_quad c₀ c₁ (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b)) a b hc₀ ha hb
        hL₀B' hL₂A'
      have hbd := quad_bound s c₀ c₁ a b hs hc₀ ha hb hD (by linarith) (by linarith) (by linarith)
        hL₀B' hL₂A'
      exact ⟨hcov.mono hbd.1, fun hab => hcov.mono (hbd.2 hab)⟩

/-- The case tree for an arbitrary exit side of the first ray, by cyclic relabelling. -/
theorem coverBound_full (s σ₀ σ₁ σ₂ c₀ c₁ c₂ a b : ℝ) (hs : 0 < s) (hσ₀ : 0 ≤ σ₀) (hσ₁ : 0 ≤ σ₁)
    (hσ₂ : 0 ≤ σ₂) (hsum : σ₀ + σ₁ + σ₂ = s ^ 2) (hc : c₀ + c₁ + c₂ = 0)
    (hc2 : c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 = 2 * s ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hA : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (a, 0)) (hB : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (0, b))
    (hexA : (σ₀ + c₀ * a = 0 ∧ c₀ < 0) ∨ (σ₁ + c₁ * a = 0 ∧ c₁ < 0) ∨ (σ₂ + c₂ * a = 0 ∧ c₂ < 0))
    (hexB : (σ₀ + c₁ * b = 0 ∧ c₁ < 0) ∨ (σ₁ + c₂ * b = 0 ∧ c₂ < 0) ∨ (σ₂ + c₀ * b = 0 ∧ c₀ < 0))
    (hdiam : a ^ 2 + a * b + b ^ 2 ≤ s ^ 2) :
    CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2) ∧
      (s < a + b → CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2)) := by
  rcases hexA with ⟨h, hc₀⟩ | ⟨h, hc₁⟩ | ⟨h, hc₂⟩
  · exact coverBound_zero s σ₀ σ₁ σ₂ c₀ c₁ c₂ a b hs hσ₀ hσ₁ hσ₂ hsum hc hc2 ha hb hA hB hc₀ h
      hexB hdiam
  · have := coverBound_zero s σ₁ σ₂ σ₀ c₁ c₂ c₀ a b hs hσ₁ hσ₂ hσ₀ (by linarith) (by linarith)
      (by linarith) ha hb ((inPoly_shift _ _ _ _ _ _ _).2 hA) ((inPoly_shift _ _ _ _ _ _ _).2 hB)
      hc₁ h (by tauto) hdiam
    exact ⟨this.1.shift, fun hab => (this.2 hab).shift⟩
  · have := coverBound_zero s σ₂ σ₀ σ₁ c₂ c₀ c₁ a b hs hσ₂ hσ₀ hσ₁ (by linarith) (by linarith)
      (by linarith) ha hb ((inPoly_shift _ _ _ _ _ _ _).2 ((inPoly_shift _ _ _ _ _ _ _).2 hA))
      ((inPoly_shift _ _ _ _ _ _ _).2 ((inPoly_shift _ _ _ _ _ _ _).2 hB)) hc₂ h (by tauto) hdiam
    exact ⟨this.1.shift.shift, fun hab => (this.2 hab).shift.shift⟩

/-- Extension of a contained length to the full length: the first side hit along the ray. -/
theorem exists_full_length (σ₀ σ₁ σ₂ c₀ c₁ c₂ a : ℝ) (hσ₀ : 0 ≤ σ₀) (hσ₁ : 0 ≤ σ₁) (hσ₂ : 0 ≤ σ₂)
    (hneg : c₀ < 0 ∨ c₁ < 0 ∨ c₂ < 0) (ha : 0 ≤ a)
    (h0 : 0 ≤ σ₀ + c₀ * a) (h1 : 0 ≤ σ₁ + c₁ * a) (h2 : 0 ≤ σ₂ + c₂ * a) :
    ∃ a', a ≤ a' ∧ 0 ≤ σ₀ + c₀ * a' ∧ 0 ≤ σ₁ + c₁ * a' ∧ 0 ≤ σ₂ + c₂ * a' ∧
      ((σ₀ + c₀ * a' = 0 ∧ c₀ < 0) ∨ (σ₁ + c₁ * a' = 0 ∧ c₁ < 0) ∨
        (σ₂ + c₂ * a' = 0 ∧ c₂ < 0)) := by
  set σ : Fin 3 → ℝ := ![σ₀, σ₁, σ₂] with hσdef
  set c : Fin 3 → ℝ := ![c₀, c₁, c₂] with hcdef
  have hσ : ∀ k, 0 ≤ σ k := by
    intro k
    fin_cases k
    · exact hσ₀
    · exact hσ₁
    · exact hσ₂
  have hAk : ∀ k, 0 ≤ σ k + c k * a := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  set S : Finset ℝ :=
    (Finset.univ.filter (fun k : Fin 3 => c k < 0)).image (fun k => σ k / (-c k)) with hSdef
  have hS : S.Nonempty := by
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, c k < 0 := by
      rcases hneg with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    exact ⟨_, Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩, rfl⟩⟩
  have hmem : S.min' hS ∈ S := Finset.min'_mem S hS
  have hle : ∀ k, c k < 0 → S.min' hS ≤ σ k / (-c k) := fun k hk =>
    Finset.min'_le S _ (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩, rfl⟩)
  have hge : a ≤ S.min' hS := by
    apply Finset.le_min'
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    have hk' := (Finset.mem_filter.1 hk).2
    rw [le_div_iff₀ (by linarith)]
    have := hAk k
    linarith
  have hin : ∀ k, 0 ≤ σ k + c k * S.min' hS := by
    intro k
    rcases lt_or_ge (c k) 0 with hk | hk
    · have := hle k hk
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · have := mul_nonneg hk (ha.trans hge)
      linarith [hσ k]
  obtain ⟨k, hk, hka⟩ := Finset.mem_image.1 hmem
  have hk' := (Finset.mem_filter.1 hk).2
  have hexit : σ k + c k * S.min' hS = 0 := by
    rw [← hka]
    have hne : c k ≠ 0 := hk'.ne
    field_simp
    ring
  refine ⟨S.min' hS, hge, hin 0, hin 1, hin 2, ?_⟩
  fin_cases k
  · exact Or.inl ⟨hexit, hk'⟩
  · exact Or.inr (Or.inl ⟨hexit, hk'⟩)
  · exact Or.inr (Or.inr ⟨hexit, hk'⟩)

end ConwaySoifer.SevenTriangles

end
