/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Area
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The 120-degree wedge and the area-loss lemma

`sideForm i` is the linear form whose level set `= 1` is the hexagon side `[vertex i, vertex (next
i)]`.
`wedge i` is the closed 120-degree wedge at `vertex i` bounded by the two sides through it; it
contains
the hexagon.  The area-loss lemma bounds the part of an equilateral triangle outside the wedge in
terms of the lengths of its intersections with the two rays.

Human proof: `notes/waste_cycle_reduction.md` §1 (geometric) and
`notes/one_rise_area_reduction_2026_09_06.md` §2 (normalised linear forms).  In skew units the
physical statement `|T \ W| ≥ (√3/4)·min(a², b²)` reads `volume ≥ min(a², b²)/2`.
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

open MeasureTheory

namespace ConwaySoifer.SevenTriangles

/-- The six unit-hexagon facet functionals, each normalized to level one. -/
def sideForm : Fin 6 → Form :=
  ![(1, 1 / 2), (0, 1), (-1, 1 / 2), (-1, -1 / 2), (0, -1), (1, -1 / 2)]

theorem sideForm_vertex (i : Fin 6) : formEval (sideForm i) (vertex i) = 1 := by
  fin_cases i <;> norm_num [sideForm, vertex, formEval]

theorem sideForm_vertex_next (i : Fin 6) : formEval (sideForm i) (vertex (next i)) = 1 := by
  fin_cases i <;> simp [next, sideForm, vertex, formEval] <;> norm_num

theorem mem_unitHexagon_iff (p : Point) :
    p ∈ unitHexagon ↔ ∀ i : Fin 6, formEval (sideForm i) p ≤ 1 := by
  simp only [unitHexagon, Set.mem_ofPred_eq, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ i
    fin_cases i <;> simp [sideForm, formEval] <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    simp [sideForm, formEval] at h0 h1 h2 h3 h4 h5
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- The closed 120-degree wedge at `vertex i` bounded by the two incident sides. -/
def wedge (i : Fin 6) : Set Point :=
  {p | formEval (sideForm i) p ≤ 1 ∧ formEval (sideForm (previous i)) p ≤ 1}

theorem unitHexagon_subset_wedge (i : Fin 6) : unitHexagon ⊆ wedge i := by
  intro p hp
  rw [mem_unitHexagon_iff] at hp
  exact ⟨hp i, hp (previous i)⟩

theorem continuous_formEval (l : Form) : Continuous fun p : Point => formEval l p := by
  unfold formEval
  fun_prop

theorem isClosed_wedge (i : Fin 6) : IsClosed (wedge i) := by
  unfold wedge
  rw [Set.ofPred_and]
  exact (isClosed_le (continuous_formEval _) continuous_const).inter
    (isClosed_le (continuous_formEval _) continuous_const)

theorem measurableSet_wedge (i : Fin 6) : MeasurableSet (wedge i) :=
  (isClosed_wedge i).measurableSet

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

/-- Positivity of the determinant `c₀² + c₀ c₁ + c₁²` of two adjacent edge normals. -/
theorem quadDet_pos {c₀ c₁ : ℝ} (h : c₀ ≠ 0) : 0 < c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 := by
  have h1 : 0 < c₀ ^ 2 := by
    positivity
  nlinarith [sq_nonneg (c₁ + c₀ / 2)]

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
        nlinarith
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        have h0 : 0 ≤ (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) *
            ((α₀ - a) * (q.2 - 0) - (β₀ - 0) * (q.1 - a)) := by
          rw [idA q]
          exact mul_nonneg hL₂A.le hL0
        exact nonneg_of_mul_nonneg_right h0 hD
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith
    · right; left
      apply mem_convexHull_triangle
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        have h0 : 0 ≤ (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2) *
            ((0 - α₀) * (q.2 - β₀) - (b - β₀) * (q.1 - α₀)) := by
          rw [idB q]
          exact mul_nonneg hL₀B.le hL2
        exact nonneg_of_mul_nonneg_right h0 hD
      · simp only [coordDet, Prod.fst_sub, Prod.snd_sub]
        nlinarith
  · rw [triArea_self]
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
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
    rw [abs_of_nonneg (by nlinarith [mul_nonneg ha.le hβ₀nn])]
    ring
  have hA2 : triArea (0, 0) (α₀, β₀) (0, b) = α₀ * b / 2 := by
    simp only [triArea, coordDet, Prod.fst_sub, Prod.snd_sub]
    rw [abs_of_nonneg (by nlinarith [mul_pos hα₀pos hb])]
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

/-- Algebraic core of the strengthened bound: with `s² = X² + X Z + Z²` and
`(X + Z) a + X b < s (a + b)`, the quadratic form `(X+Z) b² + 2 Z a b - X a²` is nonnegative. -/
theorem strong_core (s X Z a b : ℝ) (hs : 0 < s) (hX : 0 < X) (hZ : 0 ≤ Z) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hD : s ^ 2 = X ^ 2 + X * Z + Z ^ 2) (h : (X + Z) * a + X * b < s * (a + b)) :
    0 ≤ (X + Z) * b ^ 2 + 2 * Z * a * b - X * a ^ 2 := by
  have hC : s ≤ X + Z := by
    by_contra hne
    push Not at hne
    nlinarith [mul_pos (sub_pos.2 hne) (by positivity : 0 < s + (X + Z))]
  have hXs : X ≤ s := by
    by_contra hne
    push Not at hne
    nlinarith [mul_pos (sub_pos.2 hne) (by positivity : 0 < s + X)]
  have hXs' : X < s := by
    rcases lt_or_eq_of_le hXs with h' | h'
    · exact h'
    · exfalso
      have hZ0 : Z = 0 := by
        nlinarith
      subst hZ0
      rw [h'] at h
      nlinarith
  -- (X + Z - s) a < (s - X) b
  have h1 : (X + Z - s) * a < (s - X) * b := by
    linarith
  have hid : (X + Z - s) * (s + Z) = X * (s - X) := by
    linear_combination -hD
  have h2 : (s - X) * (X * a) < (s - X) * ((s + Z) * b) := by
    have := mul_lt_mul_of_pos_right h1 (by positivity : 0 < s + Z)
    nlinarith
  have h3 : X * a < (s + Z) * b := lt_of_mul_lt_mul_left h2 (by linarith)
  have hid2 : (s + Z) * ((X + Z) * b - (s - Z) * a) = (X + Z) * ((s + Z) * b - X * a) := by
    linear_combination (-a) * hD
  have h4 : 0 < (X + Z) * b - (s - Z) * a := by
    have : 0 < (s + Z) * ((X + Z) * b - (s - Z) * a) := by
      rw [hid2]
      exact mul_pos (by linarith) (by linarith)
    exact pos_of_mul_pos_right this (by linarith)
  have hid3 : (X + Z) * ((X + Z) * b ^ 2 + 2 * Z * a * b - X * a ^ 2) =
      ((X + Z) * b - (s - Z) * a) * ((X + Z) * b + (s + Z) * a) := by
    linear_combination (a ^ 2) * hD
  have h5 : 0 ≤ (X + Z) * ((X + Z) * b ^ 2 + 2 * Z * a * b - X * a ^ 2) := by
    rw [hid3]
    exact mul_nonneg h4.le (by positivity)
  exact nonneg_of_mul_nonneg_right h5 (by linarith)

/-! ### The polynomial inequalities behind the two bounds -/

/-- Quadrilateral, weak bound: `D · min(a², b²) ≤ D² - X (2 X a b + (X - c₁) a² + c₁ b²)` with
`D = X² - X c₁ + c₁²`. -/
theorem quad_core_weak (X c₁ a b : ℝ) (hX : 0 < X) (ha : 0 < a) (hb : 0 < b)
    (hσ₁ : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b))
    (h1 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + c₁ * a)
    (h2 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + (X - c₁) * b) :
    (X ^ 2 - X * c₁ + c₁ ^ 2) * min (a ^ 2) (b ^ 2) ≤
      (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 - X * (2 * X * a * b + (X - c₁) * a ^ 2 + c₁ * b ^ 2) := by
  have hab : 0 ≤ a * b := by
    positivity
  rcases le_or_gt 0 c₁ with hc₁ | hc₁
  · rcases le_or_gt c₁ X with hc₁X | hc₁X
    · -- type 1: `0 ≤ c₁ ≤ X`
      have hsq : (X * (a + b)) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hX2 : 0 ≤ c₁ * (X - c₁) := mul_nonneg hc₁ (by linarith)
      rcases le_total (a ^ 2) (b ^ 2) with hm | hm
      · rw [min_eq_left hm]
        nlinarith [mul_nonneg (mul_nonneg hX.le (sub_nonneg.2 hc₁X)) (sub_nonneg.2 hm),
          mul_nonneg hX2 (sq_nonneg a)]
      · rw [min_eq_right hm]
        nlinarith [mul_nonneg (mul_nonneg hX.le hc₁) (sub_nonneg.2 hm),
          mul_nonneg hX2 (sq_nonneg b)]
    · -- type 2b: `c₁ > X`, i.e. `c₂ < 0`
      have hZ : 0 < c₁ - X := by
        linarith
      have hsq : (X * a + c₁ * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hXZ : 0 ≤ X * (c₁ - X) := mul_nonneg hX.le hZ.le
      rcases le_total (a ^ 2) (b ^ 2) with hm | hm
      · rw [min_eq_left hm]
        nlinarith [mul_nonneg (mul_nonneg hc₁ hZ.le) (sub_nonneg.2 hm),
          mul_nonneg hXZ (sq_nonneg a), mul_nonneg (mul_nonneg hX.le hZ.le) hab]
      · rw [min_eq_right hm]
        nlinarith [mul_nonneg (mul_nonneg hX.le hc₁) (sub_nonneg.2 hm),
          mul_nonneg hXZ (sq_nonneg b), mul_nonneg (mul_nonneg hX.le hZ.le) hab]
  · -- type 2a: `c₁ < 0`
    have hZ : 0 < -c₁ := by
      linarith
    have hsq : ((X - c₁) * a + X * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) (by linarith) 2
    have hXZ : 0 ≤ X * (-c₁) := mul_nonneg hX.le hZ.le
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [min_eq_left hm]
      nlinarith [mul_nonneg (mul_nonneg hX.le (by linarith : (0 : ℝ) ≤ X - c₁)) (sub_nonneg.2 hm),
        mul_nonneg hXZ (sq_nonneg a), mul_nonneg hXZ hab]
    · rw [min_eq_right hm]
      nlinarith [mul_nonneg (mul_nonneg hZ.le (by linarith : (0 : ℝ) ≤ X - c₁)) (sub_nonneg.2 hm),
        mul_nonneg hXZ (sq_nonneg b), mul_nonneg hXZ hab]

/-- Quadrilateral, strong bound (`s < a + b`). -/
theorem quad_core_strong (s X c₁ a b : ℝ) (hs : 0 < s) (hX : 0 < X) (ha : 0 < a) (hb : 0 < b)
    (hD : s ^ 2 = X ^ 2 - X * c₁ + c₁ ^ 2)
    (hσ₁ : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b))
    (h1 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + c₁ * a)
    (h2 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + (X - c₁) * b)
    (hL₀B : 0 < X * a + c₁ * b) (hL₂A : 0 < X * b + (X - c₁) * a) (hab : s < a + b) :
    (X ^ 2 - X * c₁ + c₁ ^ 2) * max (a ^ 2) (b ^ 2) ≤
      (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 - X * (2 * X * a * b + (X - c₁) * a ^ 2 + c₁ * b ^ 2) := by
  have hab0 : 0 ≤ a * b := by
    positivity
  rcases le_or_gt 0 c₁ with hc₁ | hc₁
  · rcases le_or_gt c₁ X with hc₁X | hc₁X
    · -- type 1 is incompatible with `s < a + b`
      exfalso
      have hX2 : s ^ 2 ≤ X ^ 2 := by
        nlinarith [mul_nonneg hc₁ (sub_nonneg.2 hc₁X)]
      have hXs : s ≤ X := by
        by_contra h
        push Not at h
        nlinarith [mul_pos (sub_pos.2 h) (add_pos hs hX)]
      nlinarith [mul_lt_mul_of_pos_left hab hX, mul_le_mul_of_nonneg_right hXs hs.le]
    · -- type 2b: `Z' = c₁ - X > 0`
      have hZ : 0 < c₁ - X := by
        linarith
      have hsq : (X * a + c₁ * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      -- `Q'' ≥ D a²` from `X b > Z' a`
      have hQa : 0 ≤ (c₁ - X) * (-(c₁ - X) * a ^ 2 + 2 * X * a * b + c₁ * b ^ 2) := by
        apply mul_nonneg hZ.le
        nlinarith [mul_pos hL₂A ha, mul_nonneg hc₁ (sq_nonneg b)]
      -- `Q'' ≥ D b²` from the strengthened hypothesis
      have hcore := strong_core s X (c₁ - X) b a hs hX hZ.le hb.le ha.le
        (by rw [hD]; ring) (by nlinarith [mul_lt_mul_of_pos_left hab hs])
      have hQb : 0 ≤ X * (c₁ * a ^ 2 + 2 * (c₁ - X) * a * b - X * b ^ 2) := by
        apply mul_nonneg hX.le
        nlinarith [hcore]
      rcases le_total (a ^ 2) (b ^ 2) with hm | hm
      · rw [max_eq_right hm]
        nlinarith only [hsq, hQb]
      · rw [max_eq_left hm]
        nlinarith only [hsq, hQa]
  · -- type 2a: `Z = -c₁ > 0`
    have hZ : 0 < -c₁ := by
      linarith
    have hsq : ((X - c₁) * a + X * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) (by linarith) 2
    -- `Q ≥ D b²` from `X a > Z b`
    have hQb : 0 ≤ (-c₁) * ((X - c₁) * a ^ 2 + 2 * X * a * b - (-c₁) * b ^ 2) := by
      apply mul_nonneg hZ.le
      nlinarith [mul_pos hL₀B hb, mul_nonneg (by linarith : (0 : ℝ) ≤ X - c₁) (sq_nonneg a)]
    have hcore := strong_core s X (-c₁) a b hs hX hZ.le ha.le hb.le
      (by rw [hD]; ring) (by nlinarith [mul_lt_mul_of_pos_left hab hs])
    have hQa : 0 ≤ X * ((X - c₁) * b ^ 2 + 2 * (-c₁) * a * b - X * a ^ 2) := by
      apply mul_nonneg hX.le
      nlinarith [hcore]
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [max_eq_right hm]
      nlinarith only [hsq, hQb]
    · rw [max_eq_left hm]
      nlinarith only [hsq, hQa]

/-- Pentagon, weak bound: `D · min ≤ Q'` with `Q' = X C a² + 2 X Z a b + Z C b²`, `C = X + Z`. -/
theorem pent_core_weak (X Z a b : ℝ) (hX : 0 < X) (hZ : 0 < Z) (ha : 0 < a) (hb : 0 < b) :
    (X ^ 2 + X * Z + Z ^ 2) * min (a ^ 2) (b ^ 2) ≤
      X * (X + Z) * a ^ 2 + 2 * X * Z * a * b + Z * (X + Z) * b ^ 2 := by
  have hab : 0 ≤ a * b := by
    positivity
  have hXZ : 0 ≤ X * Z := by
    positivity
  rcases le_total (a ^ 2) (b ^ 2) with hm | hm
  · rw [min_eq_left hm]
    nlinarith [mul_nonneg (mul_nonneg hZ.le (by linarith : (0 : ℝ) ≤ X + Z)) (sub_nonneg.2 hm),
      mul_nonneg hXZ (sq_nonneg a), mul_nonneg hXZ hab]
  · rw [min_eq_right hm]
    nlinarith [mul_nonneg (mul_nonneg hX.le (by linarith : (0 : ℝ) ≤ X + Z)) (sub_nonneg.2 hm),
      mul_nonneg hXZ (sq_nonneg b), mul_nonneg hXZ hab]

/-- Pentagon, strong bound (`s < a + b`), with `D ≥ C a + Z b` and `D > X a + C b`. -/
theorem pent_core_strong (s X Z a b : ℝ) (hs : 0 < s) (hX : 0 < X) (hZ : 0 < Z) (ha : 0 < a)
    (hb : 0 < b) (hD : s ^ 2 = X ^ 2 + X * Z + Z ^ 2)
    (h1 : (X + Z) * a + Z * b ≤ X ^ 2 + X * Z + Z ^ 2)
    (h2 : X * a + (X + Z) * b < X ^ 2 + X * Z + Z ^ 2) (hab : s < a + b) :
    (X ^ 2 + X * Z + Z ^ 2) * max (a ^ 2) (b ^ 2) ≤
      X * (X + Z) * a ^ 2 + 2 * X * Z * a * b + Z * (X + Z) * b ^ 2 := by
  have hab0 : 0 ≤ a * b := by
    positivity
  have hsab : s * s < s * (a + b) := mul_lt_mul_of_pos_left hab hs
  rcases le_total (Z * a) (X * b) with hZX | hZX
  · -- `Z a ≤ X b`
    have hQa : 0 ≤ Z * (-Z * a ^ 2 + 2 * X * a * b + (X + Z) * b ^ 2) := by
      apply mul_nonneg hZ.le
      nlinarith [mul_le_mul_of_nonneg_left hZX ha.le, mul_nonneg (by linarith : (0 : ℝ) ≤ X + Z)
          (sq_nonneg b)]
    have hcore := strong_core s X Z b a hs hX hZ.le hb.le ha.le hD (by nlinarith)
    have hQb : 0 ≤ X * ((X + Z) * a ^ 2 + 2 * Z * a * b - X * b ^ 2) := by
      apply mul_nonneg hX.le
      nlinarith [hcore]
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [max_eq_right hm]
      nlinarith
    · rw [max_eq_left hm]
      nlinarith
  · -- `X b ≤ Z a`
    have hQb : 0 ≤ X * ((X + Z) * a ^ 2 + 2 * Z * a * b - X * b ^ 2) := by
      apply mul_nonneg hX.le
      nlinarith [mul_le_mul_of_nonneg_left hZX hb.le, mul_nonneg (by linarith : (0 : ℝ) ≤ X + Z)
          (sq_nonneg a)]
    have hcore := strong_core s Z X a b hs hZ hX.le ha.le hb.le (by rw [hD]; ring) (by nlinarith)
    have hQa : 0 ≤ Z * ((Z + X) * b ^ 2 + 2 * X * a * b - Z * a ^ 2) := by
      apply mul_nonneg hZ.le
      nlinarith [hcore]
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [max_eq_right hm]
      nlinarith
    · rw [max_eq_left hm]
      nlinarith

/-- The quadrilateral area bound in the form produced by `coverBound_quad`. -/
theorem quad_bound (s c₀ c₁ a b : ℝ) (hs : 0 < s) (hc₀ : c₀ < 0) (ha : 0 < a) (hb : 0 < b)
    (hD : s ^ 2 = c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2)
    (hσ₁ : 0 ≤ c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b))
    (hL₁A : 0 ≤ c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b) + c₁ * a)
    (hL₁B : 0 ≤ c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b) + (-c₀ - c₁) * b)
    (hL₀B : 0 < -c₀ * a + c₁ * b) (hL₂A : 0 < -c₀ * b + (-c₀ - c₁) * a) :
    c₀ * (2 * c₀ * a * b + (c₀ + c₁) * a ^ 2 - c₁ * b ^ 2) /
        (2 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2)) ≤ s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2 ∧
      (s < a + b → c₀ * (2 * c₀ * a * b + (c₀ + c₁) * a ^ 2 - c₁ * b ^ 2) /
        (2 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2)) ≤ s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2) := by
  have hDpos : 0 < c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 := quadDet_pos hc₀.ne
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -c₀ := ⟨_, rfl⟩
  have hc₀' : c₀ = -X := by
    linarith
  subst hc₀'
  have hXpos : 0 < X := by
    linarith
  have hD' : s ^ 2 = X ^ 2 - X * c₁ + c₁ ^ 2 := by
    rw [hD]; ring
  have hw := quad_core_weak X c₁ a b hXpos ha hb (by linarith) (by linarith) (by linarith)
  constructor
  · rw [div_le_iff₀ (by positivity), hD]
    linarith
  · intro hab
    have hst := quad_core_strong s X c₁ a b hs hXpos ha hb hD' (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hab
    rw [div_le_iff₀ (by positivity), hD]
    linarith

/-- The pentagon area bound in the form produced by `coverBound_pent`. -/
theorem pent_bound (s c₀ c₂ σ₂ a b : ℝ) (hs : 0 < s) (hc₀ : c₀ < 0) (hc₂ : c₂ < 0) (ha : 0 < a)
    (hb : 0 < b) (hD : s ^ 2 = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2)
    (hσ₂ : σ₂ = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 + c₀ * a + c₂ * b)
    (hL₂A : 0 ≤ σ₂ + c₂ * a) (hL₂B : 0 < σ₂ + c₀ * b) :
    ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 -
        (-c₀ * (-c₀ - c₂) * a ^ 2 + 2 * c₀ * c₂ * a * b - c₂ * (-c₀ - c₂) * b ^ 2)) /
        (2 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2)) ≤ s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2 ∧
      (s < a + b → ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 -
        (-c₀ * (-c₀ - c₂) * a ^ 2 + 2 * c₀ * c₂ * a * b - c₂ * (-c₀ - c₂) * b ^ 2)) /
        (2 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2)) ≤ s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2) := by
  have hDpos : 0 < c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 := quadDet_pos hc₀.ne
  subst hσ₂
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -c₀ := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = -c₂ := ⟨_, rfl⟩
  have hc₀' : c₀ = -X := by
    linarith
  have hc₂' : c₂ = -Z := by
    linarith
  subst hc₀' hc₂'
  have hXpos : 0 < X := by
    linarith
  have hZpos : 0 < Z := by
    linarith
  have hD' : s ^ 2 = X ^ 2 + X * Z + Z ^ 2 := by
    rw [hD]; ring
  have hw := pent_core_weak X Z a b hXpos hZpos ha hb
  constructor
  · rw [div_le_iff₀ (by positivity), hD]
    linarith
  · intro hab
    have hst := pent_core_strong s X Z a b hs hXpos hZpos ha hb hD' (by linarith) (by linarith) hab
    rw [div_le_iff₀ (by positivity), hD]
    linarith

/-- Same-side bound from the diameter. -/
theorem same_side_bound (s a b : ℝ) (hdiam : a ^ 2 + a * b + b ^ 2 ≤ s ^ 2) :
    a * b / 2 ≤ s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2 ∧
      a * b / 2 ≤ s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2 := by
  constructor
  · nlinarith [min_le_left (a ^ 2) (b ^ 2), sq_nonneg b]
  · have := max_le (le_add_of_nonneg_right (sq_nonneg b) : a ^ 2 ≤ a ^ 2 + b ^ 2)
      (le_add_of_nonneg_left (sq_nonneg a) : b ^ 2 ≤ a ^ 2 + b ^ 2)
    nlinarith

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

/-- The abstract wedge lemma: from contained lengths `a, b > 0` to a cover of the polygon by
three triangles with the required total area. -/
theorem abstract_bound (s σ₀ σ₁ σ₂ c₀ c₁ c₂ a b : ℝ) (hs : 0 < s) (hσ₀ : 0 ≤ σ₀) (hσ₁ : 0 ≤ σ₁)
    (hσ₂ : 0 ≤ σ₂) (hsum : σ₀ + σ₁ + σ₂ = s ^ 2) (hc : c₀ + c₁ + c₂ = 0)
    (hc2 : c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 = 2 * s ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hA : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (a, 0)) (hB : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (0, b))
    (hdiam : ∀ a' b', 0 ≤ a' → 0 ≤ b' → InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (a', 0) →
      InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (0, b') → a' ^ 2 + a' * b' + b' ^ 2 ≤ s ^ 2) :
    CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2) ∧
      (s < a + b → CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ (s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2)) := by
  have hneg : c₀ < 0 ∨ c₁ < 0 ∨ c₂ < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    have e0 : c₀ = 0 := by
      linarith
    have e1 : c₁ = 0 := by
      linarith
    have e2 : c₂ = 0 := by
      linarith
    subst e0 e1 e2
    nlinarith
  obtain ⟨-, -, hA0, hA1, hA2⟩ := hA
  obtain ⟨-, -, hB0, hB1, hB2⟩ := hB
  simp only [mul_zero, add_zero] at hA0 hA1 hA2 hB0 hB1 hB2
  obtain ⟨a', haa', h0', h1', h2', hexA⟩ :=
    exists_full_length σ₀ σ₁ σ₂ c₀ c₁ c₂ a hσ₀ hσ₁ hσ₂ hneg ha.le hA0 hA1 hA2
  obtain ⟨b', hbb', k0', k1', k2', hexB⟩ :=
    exists_full_length σ₀ σ₁ σ₂ c₁ c₂ c₀ b hσ₀ hσ₁ hσ₂ (by tauto) hb.le hB0 hB1 hB2
  have hA' : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (a', 0) := by
    refine ⟨by linarith, le_rfl, ?_, ?_, ?_⟩ <;> simpa
  have hB' : InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (0, b') := by
    refine ⟨le_rfl, by linarith, ?_, ?_, ?_⟩ <;> simpa
  have hres := coverBound_full s σ₀ σ₁ σ₂ c₀ c₁ c₂ a' b' hs hσ₀ hσ₁ hσ₂ hsum hc hc2
    (ha.trans_le haa') (hb.trans_le hbb') hA' hB' hexA hexB
    (hdiam a' b' (by linarith) (by linarith) hA' hB')
  have hmin : min (a ^ 2) (b ^ 2) ≤ min (a' ^ 2) (b' ^ 2) :=
    min_le_min (pow_le_pow_left₀ ha.le haa' 2) (pow_le_pow_left₀ hb.le hbb' 2)
  have hmax : max (a ^ 2) (b ^ 2) ≤ max (a' ^ 2) (b' ^ 2) :=
    max_le_max (pow_le_pow_left₀ ha.le haa' 2) (pow_le_pow_left₀ hb.le hbb' 2)
  refine ⟨hres.1.mono (by linarith), fun hab => (hres.2 (by linarith)).mono (by linarith)⟩

/-! ### Concrete filled triangles: half-plane description -/

theorem convex_coordDet_left (g P : Point) : Convex ℝ {p : Point | 0 ≤ coordDet g (p - P)} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have hb' : b = 1 - a := by
    linarith
  subst hb'
  have : coordDet g (a • p + (1 - a) • q - P) =
      a * coordDet g (p - P) + (1 - a) * coordDet g (q - P) := by
    rcases g with ⟨g1, g2⟩
    rcases P with ⟨P1, P2⟩
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    simp only [coordDet, Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul]
    ring
  rw [this]
  exact add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hq)

theorem convex_coordDet_right (g P : Point) : Convex ℝ {p : Point | 0 ≤ coordDet (p - P) g} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have hb' : b = 1 - a := by
    linarith
  subst hb'
  have : coordDet (a • p + (1 - a) • q - P) g =
      a * coordDet (p - P) g + (1 - a) * coordDet (q - P) g := by
    rcases g with ⟨g1, g2⟩
    rcases P with ⟨P1, P2⟩
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    simp only [coordDet, Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul]
    ring
  rw [this]
  exact add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hq)

theorem rotate60_rotateNeg60 (p : Point) : rotate60 (rotateNeg60 p) = p := by
  rcases p with ⟨x, z⟩
  simp only [rotate60, rotateNeg60, Prod.mk.injEq]
  constructor <;> ring

/-- Half-plane description of the positively oriented filled triangle `A, A + e, A + rotate60 e`. -/
theorem mem_tri_iff (A e p : Point) (he : 0 < sqDist e (0, 0)) :
    p ∈ convexHull ℝ {A, A + e, A + rotate60 e} ↔
      0 ≤ coordDet e (p - A) ∧ 0 ≤ coordDet (rotate60 e - e) (p - (A + e)) ∧
        0 ≤ coordDet (p - A) (rotate60 e) := by
  have hdet : coordDet e (rotate60 e) = sqDist e (0, 0) := coordDet_rotate60 e
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_⟩
    · refine convexHull_min ?_ (convex_coordDet_left e A) hp
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_ofPred_eq]
      rcases e with ⟨e1, e2⟩
      rcases A with ⟨A1, A2⟩
      simp only [coordDet, rotate60, sqDist, Prod.mk_add_mk, Prod.mk_sub_mk] at he ⊢
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg e1, sq_nonneg e2]
    · refine convexHull_min ?_ (convex_coordDet_left (rotate60 e - e) (A + e)) hp
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_ofPred_eq]
      rcases e with ⟨e1, e2⟩
      rcases A with ⟨A1, A2⟩
      simp only [coordDet, rotate60, sqDist, Prod.mk_add_mk, Prod.mk_sub_mk] at he ⊢
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg e1, sq_nonneg e2]
    · refine convexHull_min ?_ (convex_coordDet_right (rotate60 e) A) hp
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_ofPred_eq]
      rcases e with ⟨e1, e2⟩
      rcases A with ⟨A1, A2⟩
      simp only [coordDet, rotate60, sqDist, Prod.mk_add_mk, Prod.mk_sub_mk] at he ⊢
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg e1, sq_nonneg e2]
  · rintro ⟨h₁, h₂, h₃⟩
    apply mem_convexHull_triangle
    · rw [add_sub_cancel_left, add_sub_cancel_left, hdet]
      exact he
    · rwa [add_sub_cancel_left]
    · rwa [add_sub_add_left_eq_sub]
    · have : coordDet (A - (A + rotate60 e)) (p - (A + rotate60 e)) =
          coordDet (p - A) (rotate60 e) := by
        rcases e with ⟨e1, e2⟩
        rcases A with ⟨A1, A2⟩
        rcases p with ⟨p1, p2⟩
        simp only [coordDet, rotate60, Prod.mk_add_mk, Prod.mk_sub_mk]
        ring
      rw [this]
      exact h₃

/-- Every filled equilateral triangle is a positively oriented `A, A + e, A + rotate60 e`. -/
theorem EquilateralTriangle.exists_normal_form (T : EquilateralTriangle) :
    ∃ A e : Point, sqDist e (0, 0) = T.side ^ 2 ∧
      T.carrier = convexHull ℝ {A, A + e, A + rotate60 e} := by
  have hr : Set.range T.vertices = {T.vertices 0, T.vertices 1, T.vertices 2} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hsq : ∀ j, sqDist (T.vertices j - T.vertices 0) (0, 0) = sqDist (T.vertices j) (T.vertices 0)
      := by
    intro j
    simp [sqDist]
  rcases T.thirdVertex_orientation with h | h
  · refine ⟨T.vertices 0, T.vertices 1 - T.vertices 0, ?_, ?_⟩
    · rw [hsq]
      exact T.equilateral 1 0 (by decide)
    · rw [EquilateralTriangle.carrier, hr, ← h, add_sub_cancel, add_sub_cancel]
  · refine ⟨T.vertices 0, T.vertices 2 - T.vertices 0, ?_, ?_⟩
    · rw [hsq]
      exact T.equilateral 2 0 (by decide)
    · rw [EquilateralTriangle.carrier, hr, add_sub_cancel, h, rotate60_rotateNeg60, add_sub_cancel,
        Set.pair_comm]

/-! ### Ray coordinates at a hexagon vertex -/

/-- Unit direction of the ray from `vertex i` towards `vertex (previous i)`. -/
def rayU (i : Fin 6) : Point := vertex (previous i) - vertex i

/-- Unit direction of the ray from `vertex i` towards `vertex (next i)`. -/
def rayW (i : Fin 6) : Point := vertex (next i) - vertex i

/-- Coordinate along `rayU i` (vanishes on the side `[vertex i, vertex (next i)]`). -/
def alphaCoord (i : Fin 6) (p : Point) : ℝ := 1 - formEval (sideForm i) p

/-- Coordinate along `rayW i` (vanishes on the side `[vertex (previous i), vertex i]`). -/
def betaCoord (i : Fin 6) (p : Point) : ℝ := 1 - formEval (sideForm (previous i)) p

theorem mem_wedge_iff (i : Fin 6) (p : Point) :
    p ∈ wedge i ↔ 0 ≤ alphaCoord i p ∧ 0 ≤ betaCoord i p := by
  simp [wedge, alphaCoord, betaCoord, sub_nonneg]

theorem ray_decomp (i : Fin 6) (p : Point) :
    p = vertex i + (alphaCoord i p • rayU i + betaCoord i p • rayW i) := by
  rcases p with ⟨x, z⟩
  fin_cases i <;> simp only [vertex, Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Fin.zero_eta,
      Fin.isValue, Matrix.cons_val_zero, alphaCoord, formEval, sideForm, one_mul, rayU, previous,
      zero_add, Matrix.cons_val, Prod.mk_sub_mk, sub_zero, Prod.smul_mk, smul_eq_mul, mul_neg,
      mul_one, neg_sub, betaCoord, rayW, next, Matrix.cons_val_one, Prod.mk_add_mk,
      sub_add_sub_cancel, add_sub_add_left_eq_sub, Prod.ext_iff, Fin.mk_one, zero_mul,
      Fin.reduceAdd, zero_sub, sub_self, mul_zero, add_zero, add_sub_cancel, and_true,
      Fin.reduceFinMk, neg_mul, sub_neg_eq_add, sub_add_sub_cancel', neg_add_cancel_left] <;> (try
      constructor) <;> (first | exact trivial | ring)

theorem alphaCoord_rayU (i : Fin 6) (a : ℝ) : alphaCoord i (vertex i + a • rayU i) = a := by
  fin_cases i <;> simp [alphaCoord, rayU, vertex, previous, sideForm, formEval] <;> ring

theorem betaCoord_rayU (i : Fin 6) (a : ℝ) : betaCoord i (vertex i + a • rayU i) = 0 := by
  fin_cases i <;> simp [betaCoord, rayU, vertex, previous, sideForm, formEval] <;> ring

theorem alphaCoord_rayW (i : Fin 6) (b : ℝ) : alphaCoord i (vertex i + b • rayW i) = 0 := by
  fin_cases i <;> simp [alphaCoord, rayW, vertex, next, sideForm, formEval] <;> ring

theorem betaCoord_rayW (i : Fin 6) (b : ℝ) : betaCoord i (vertex i + b • rayW i) = b := by
  fin_cases i <;> simp [betaCoord, rayW, vertex, previous, next, sideForm, formEval] <;> ring

theorem coordDet_rayU_rayW (i : Fin 6) : coordDet (rayU i) (rayW i) = -1 := by
  fin_cases i <;> simp [rayU, rayW, vertex, previous, next, coordDet] <;> norm_num

theorem sqDist_rays (i : Fin 6) (a b : ℝ) :
    sqDist (vertex i + a • rayU i) (vertex i + b • rayW i) = a ^ 2 + a * b + b ^ 2 := by
  fin_cases i <;> simp [rayU, rayW, vertex, previous, next, sqDist] <;> ring

/-- The three edge functionals of the triangle `A, A+e, A+rotate60 e` in ray coordinates at
`vertex i`: the coefficient along the second ray is the cyclic shift of the one along the first. -/
theorem edge_decomp (i : Fin 6) (A e p : Point) :
    coordDet e (p - A) = coordDet e (vertex i - A) + coordDet e (rayU i) * alphaCoord i p +
        coordDet (rotate60 e - e) (rayU i) * betaCoord i p ∧
      coordDet (rotate60 e - e) (p - (A + e)) = coordDet (rotate60 e - e) (vertex i - (A + e)) +
        coordDet (rotate60 e - e) (rayU i) * alphaCoord i p +
        coordDet (-(rotate60 e)) (rayU i) * betaCoord i p ∧
      coordDet (p - A) (rotate60 e) = coordDet (vertex i - A) (rotate60 e) +
        coordDet (-(rotate60 e)) (rayU i) * alphaCoord i p + coordDet e (rayU i) * betaCoord i p :=
            by
  rcases p with ⟨x, z⟩
  rcases A with ⟨A1, A2⟩
  rcases e with ⟨e1, e2⟩
  fin_cases i <;> simp only [coordDet, Prod.mk_sub_mk, vertex, Nat.succ_eq_add_one, Nat.reduceAdd,
      one_div, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, zero_sub, mul_neg, rayU, previous,
      zero_add, Matrix.cons_val, sub_zero, mul_one, alphaCoord, formEval, sideForm, one_mul,
      rotate60, neg_sub, betaCoord, Prod.mk_add_mk, neg_add_rev, Prod.neg_mk, neg_mul,
      sub_neg_eq_add, Fin.mk_one, Matrix.cons_val_one, Fin.reduceAdd, zero_mul, Fin.reduceFinMk,
      sub_self, mul_zero] <;> refine ⟨?_, ?_, ?_⟩ <;> ring

theorem edge_sum (A e p : Point) :
    coordDet e (p - A) + coordDet (rotate60 e - e) (p - (A + e)) + coordDet (p - A) (rotate60 e) =
      sqDist e (0, 0) := by
  rcases p with ⟨x, z⟩
  rcases A with ⟨A1, A2⟩
  rcases e with ⟨e1, e2⟩
  simp only [coordDet, rotate60, sqDist, Prod.mk_add_mk, Prod.mk_sub_mk]
  ring

theorem coef_sum (i : Fin 6) (e : Point) :
    coordDet e (rayU i) + coordDet (rotate60 e - e) (rayU i) + coordDet (-(rotate60 e)) (rayU i) = 0
        := by
  rcases e with ⟨e1, e2⟩
  fin_cases i <;> simp [rayU, vertex, previous, coordDet, rotate60] <;> ring

theorem coef_sq (i : Fin 6) (e : Point) :
    coordDet e (rayU i) ^ 2 + coordDet (rotate60 e - e) (rayU i) ^ 2 +
      coordDet (-(rotate60 e)) (rayU i) ^ 2 = 2 * sqDist e (0, 0) := by
  rcases e with ⟨e1, e2⟩
  fin_cases i <;> simp [rayU, vertex, previous, coordDet, rotate60, sqDist] <;> ring

/-! ### The affine ray map and areas -/

/-- `q ↦ vertex i + q.1 • rayU i + q.2 • rayW i` as an affine map. -/
def rayMap (i : Fin 6) : (ℝ × ℝ) →ᵃ[ℝ] Point :=
  AffineMap.const ℝ (ℝ × ℝ) (vertex i) +
    ((LinearMap.fst ℝ ℝ ℝ).smulRight (rayU i) + (LinearMap.snd ℝ ℝ ℝ).smulRight (rayW
        i)).toAffineMap

theorem rayMap_apply (i : Fin 6) (q : ℝ × ℝ) :
    rayMap i q = vertex i + (q.1 • rayU i + q.2 • rayW i) := by
  simp [rayMap]

theorem rayMap_image_hull (i : Fin 6) (q₁ q₂ q₃ : ℝ × ℝ) :
    rayMap i '' convexHull ℝ {q₁, q₂, q₃} = convexHull ℝ {rayMap i q₁, rayMap i q₂, rayMap i q₃} :=
        by
  rw [AffineMap.image_convexHull, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

theorem coordDet_rayMap (i : Fin 6) (q₁ q₂ q₃ : ℝ × ℝ) :
    coordDet (rayMap i q₂ - rayMap i q₁) (rayMap i q₃ - rayMap i q₁) =
      -coordDet (q₂ - q₁) (q₃ - q₁) := by
  have h := coordDet_rayU_rayW i
  simp only [rayMap_apply]
  obtain ⟨u, hu⟩ : ∃ u, u = rayU i := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = rayW i := ⟨_, rfl⟩
  rw [← hu, ← hw] at h ⊢
  rcases u with ⟨u1, u2⟩
  rcases w with ⟨w1, w2⟩
  rcases q₁ with ⟨x1, y1⟩
  rcases q₂ with ⟨x2, y2⟩
  rcases q₃ with ⟨x3, y3⟩
  simp only [coordDet, Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.fst_add,
    Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h ⊢
  linear_combination ((x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1)) * h

theorem volume_rayMap_hull (i : Fin 6) (q₁ q₂ q₃ : ℝ × ℝ) :
    volume (rayMap i '' convexHull ℝ {q₁, q₂, q₃}) = ENNReal.ofReal (triArea q₁ q₂ q₃) := by
  rw [rayMap_image_hull, volume_triangle, triArea, coordDet_rayMap, abs_neg]

/-- Subadditivity: a cover of `T ∩ W` by three images of ray-coordinate triangles. -/
theorem volume_inter_wedge_le (i : Fin 6) (T : EquilateralTriangle) {X : ℝ}
    (q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ q₉ : ℝ × ℝ)
    (hcov : ∀ p ∈ T.carrier ∩ wedge i, p ∈ rayMap i '' convexHull ℝ {q₁, q₂, q₃} ∨
      p ∈ rayMap i '' convexHull ℝ {q₄, q₅, q₆} ∨ p ∈ rayMap i '' convexHull ℝ {q₇, q₈, q₉})
    (harea : triArea q₁ q₂ q₃ + triArea q₄ q₅ q₆ + triArea q₇ q₈ q₉ ≤ X) :
    volume (T.carrier ∩ wedge i) ≤ ENNReal.ofReal X := by
  calc volume (T.carrier ∩ wedge i)
      ≤ volume (rayMap i '' convexHull ℝ {q₁, q₂, q₃} ∪ rayMap i '' convexHull ℝ {q₄, q₅, q₆} ∪
          rayMap i '' convexHull ℝ {q₇, q₈, q₉}) := by
        apply measure_mono
        intro p hp
        rcases hcov p hp with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    _ ≤ volume (rayMap i '' convexHull ℝ {q₁, q₂, q₃}) + volume (rayMap i '' convexHull ℝ {q₄, q₅,
        q₆}) +
          volume (rayMap i '' convexHull ℝ {q₇, q₈, q₉}) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = ENNReal.ofReal (triArea q₁ q₂ q₃ + triArea q₄ q₅ q₆ + triArea q₇ q₈ q₉) := by
        rw [volume_rayMap_hull, volume_rayMap_hull, volume_rayMap_hull,
          ENNReal.ofReal_add (add_nonneg (triArea_nonneg _ _ _) (triArea_nonneg _ _ _))
            (triArea_nonneg _ _ _),
          ENNReal.ofReal_add (triArea_nonneg _ _ _) (triArea_nonneg _ _ _)]
    _ ≤ ENNReal.ofReal X := ENNReal.ofReal_le_ofReal harea

/-- From an upper bound on `T ∩ W` to a lower bound on `T \ W`. -/
theorem volume_diff_ge (i : Fin 6) (T : EquilateralTriangle) {X : ℝ} (hX : 0 ≤ X)
    (h : volume (T.carrier ∩ wedge i) ≤ ENNReal.ofReal X) :
    T.side ^ 2 / 2 - X ≤ (volume (T.carrier \ wedge i)).toReal := by
  have hsum := measure_inter_add_sdiff (μ := volume) T.carrier (measurableSet_wedge i)
  rw [T.volume_carrier] at hsum
  have hfin₁ : volume (T.carrier ∩ wedge i) ≠ ⊤ :=
    ne_top_of_le_ne_top T.volume_carrier_lt_top.ne (measure_mono Set.inter_subset_left)
  have hfin₂ : volume (T.carrier \ wedge i) ≠ ⊤ :=
    ne_top_of_le_ne_top T.volume_carrier_lt_top.ne (measure_mono Set.sdiff_subset)
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfin₁ hfin₂, ENNReal.toReal_ofReal (by positivity)] at hreal
  have h' : (volume (T.carrier ∩ wedge i)).toReal ≤ X := ENNReal.toReal_le_of_le_ofReal hX h
  linarith

/-- A cover bound in ray coordinates yields the area-loss bound. -/
theorem volume_diff_ge_of_coverBound (i : Fin 6) (T : EquilateralTriangle)
    (σ₀ σ₁ σ₂ c₀ c₁ c₂ X : ℝ)
    (hmem : ∀ p, p ∈ T.carrier ∩ wedge i →
      InPoly σ₀ σ₁ σ₂ c₀ c₁ c₂ (alphaCoord i p, betaCoord i p))
    (hcb : CoverBound σ₀ σ₁ σ₂ c₀ c₁ c₂ X) :
    T.side ^ 2 / 2 - X ≤ (volume (T.carrier \ wedge i)).toReal := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉, hq, harea⟩ := hcb
  have hX : 0 ≤ X := le_trans (add_nonneg (add_nonneg (triArea_nonneg _ _ _)
    (triArea_nonneg _ _ _)) (triArea_nonneg _ _ _)) harea
  refine volume_diff_ge i T hX (volume_inter_wedge_le i T q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ q₉ ?_ harea)
  intro p hp
  have hpq : rayMap i (alphaCoord i p, betaCoord i p) = p := by
    rw [rayMap_apply]
    exact (ray_decomp i p).symm
  rcases hq _ (hmem p hp) with h | h | h
  · exact Or.inl ⟨_, h, hpq⟩
  · exact Or.inr (Or.inl ⟨_, h, hpq⟩)
  · exact Or.inr (Or.inr ⟨_, h, hpq⟩)

/-- Both area-loss bounds for positive contained lengths. -/
theorem wedge_area_both (i : Fin 6) (T : EquilateralTriangle) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : vertex i ∈ T.carrier)
    (hpa : vertex i + a • rayU i ∈ T.carrier) (hpb : vertex i + b • rayW i ∈ T.carrier) :
    min (a ^ 2) (b ^ 2) / 2 ≤ (volume (T.carrier \ wedge i)).toReal ∧
      (T.side < a + b → max (a ^ 2) (b ^ 2) / 2 ≤ (volume (T.carrier \ wedge i)).toReal) := by
  obtain ⟨A, e, he, hT⟩ := T.exists_normal_form
  have hs := T.side_pos
  have hepos : 0 < sqDist e (0, 0) := by
    rw [he]; positivity
  have hmem : ∀ p, p ∈ T.carrier ∩ wedge i ↔
      InPoly (coordDet e (vertex i - A)) (coordDet (rotate60 e - e) (vertex i - (A + e)))
        (coordDet (vertex i - A) (rotate60 e)) (coordDet e (rayU i))
        (coordDet (rotate60 e - e) (rayU i)) (coordDet (-(rotate60 e)) (rayU i))
        (alphaCoord i p, betaCoord i p) := by
    intro p
    rw [Set.mem_inter_iff, hT, mem_tri_iff A e p hepos, mem_wedge_iff]
    obtain ⟨e0, e1, e2⟩ := edge_decomp i A e p
    rw [e0, e1, e2]
    unfold InPoly
    simp only
    tauto
  have hAin := (hmem (vertex i + a • rayU i)).1
    ⟨hpa, by rw [mem_wedge_iff, alphaCoord_rayU, betaCoord_rayU]; exact ⟨ha.le, le_rfl⟩⟩
  rw [alphaCoord_rayU, betaCoord_rayU] at hAin
  have hBin := (hmem (vertex i + b • rayW i)).1
    ⟨hpb, by rw [mem_wedge_iff, alphaCoord_rayW, betaCoord_rayW]; exact ⟨le_rfl, hb.le⟩⟩
  rw [alphaCoord_rayW, betaCoord_rayW] at hBin
  have hv' := (mem_tri_iff A e (vertex i) hepos).1 (hT ▸ hv)
  have hsum := edge_sum A e (vertex i)
  rw [he] at hsum
  have hc := coef_sum i e
  have hc2 := coef_sq i e
  rw [he] at hc2
  have hdiam : ∀ a' b', 0 ≤ a' → 0 ≤ b' →
      InPoly (coordDet e (vertex i - A)) (coordDet (rotate60 e - e) (vertex i - (A + e)))
        (coordDet (vertex i - A) (rotate60 e)) (coordDet e (rayU i))
        (coordDet (rotate60 e - e) (rayU i)) (coordDet (-(rotate60 e)) (rayU i)) (a', 0) →
      InPoly (coordDet e (vertex i - A)) (coordDet (rotate60 e - e) (vertex i - (A + e)))
        (coordDet (vertex i - A) (rotate60 e)) (coordDet e (rayU i))
        (coordDet (rotate60 e - e) (rayU i)) (coordDet (-(rotate60 e)) (rayU i)) (0, b') →
      a' ^ 2 + a' * b' + b' ^ 2 ≤ T.side ^ 2 := by
    intro a' b' _ _ hA' hB'
    have h1 : vertex i + a' • rayU i ∈ T.carrier :=
      ((hmem _).2 (by rwa [alphaCoord_rayU, betaCoord_rayU])).1
    have h2 : vertex i + b' • rayW i ∈ T.carrier :=
      ((hmem _).2 (by rwa [alphaCoord_rayW, betaCoord_rayW])).1
    have := T.sqDist_le h1 h2
    rwa [sqDist_rays] at this
  obtain ⟨hw, hst⟩ := abstract_bound T.side _ _ _ _ _ _ a b hs hv'.1 hv'.2.1 hv'.2.2 hsum hc hc2
    ha hb hAin hBin hdiam
  constructor
  · have := volume_diff_ge_of_coverBound i T _ _ _ _ _ _ _ (fun p hp => (hmem p).1 hp) hw
    linarith
  · intro hab
    have := volume_diff_ge_of_coverBound i T _ _ _ _ _ _ _ (fun p hp => (hmem p).1 hp) (hst hab)
    linarith

/-- A contained length along a unit ray is at most the side. -/
theorem ray_length_le_side (i : Fin 6) (T : EquilateralTriangle) {b : ℝ}
    (hv : vertex i ∈ T.carrier) (hpb : vertex i + b • rayW i ∈ T.carrier) : b ≤ T.side := by
  have h := T.sqDist_le hv hpb
  have e : sqDist (vertex i) (vertex i + b • rayW i) = b ^ 2 := by
    have := sqDist_rays i 0 b
    simpa using this
  rw [e] at h
  nlinarith [T.side_pos]

theorem ray_length_le_side' (i : Fin 6) (T : EquilateralTriangle) {a : ℝ}
    (hv : vertex i ∈ T.carrier) (hpa : vertex i + a • rayU i ∈ T.carrier) : a ≤ T.side := by
  have h := T.sqDist_le hpa hv
  have e : sqDist (vertex i + a • rayU i) (vertex i) = a ^ 2 := by
    have := sqDist_rays i a 0
    simpa using this
  rw [e] at h
  nlinarith [T.side_pos]

/-- Weak area-loss bound.  `a` is a length along the ray towards `vertex (previous i)`, `b` along
the
ray towards `vertex (next i)`; both rays are unit length in `sqDist`.  Any contained lengths may be
used (the bound is monotone), not only the full intersection lengths. -/
theorem wedge_area_weak (i : Fin 6) (T : EquilateralTriangle) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : vertex i ∈ T.carrier)
    (hpa : vertex i + a • (vertex (previous i) - vertex i) ∈ T.carrier)
    (hpb : vertex i + b • (vertex (next i) - vertex i) ∈ T.carrier) :
    min (a ^ 2) (b ^ 2) / 2 ≤ (volume (T.carrier \ wedge i)).toReal := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have e : min ((0 : ℝ) ^ 2) (b ^ 2) = 0 := by
      rw [zero_pow two_ne_zero]
      exact min_eq_left (sq_nonneg b)
    rw [e, zero_div]
    exact ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have e : min (a ^ 2) ((0 : ℝ) ^ 2) = 0 := by
      rw [zero_pow two_ne_zero]
      exact min_eq_right (sq_nonneg a)
    rw [e, zero_div]
    exact ENNReal.toReal_nonneg
  exact (wedge_area_both i T ha' hb' hv hpa hpb).1

/-- Strong area-loss bound, valid when the two contained lengths exceed the side. -/
theorem wedge_area_strong (i : Fin 6) (T : EquilateralTriangle) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : vertex i ∈ T.carrier)
    (hpa : vertex i + a • (vertex (previous i) - vertex i) ∈ T.carrier)
    (hpb : vertex i + b • (vertex (next i) - vertex i) ∈ T.carrier)
    (hab : T.side < a + b) :
    max (a ^ 2) (b ^ 2) / 2 ≤ (volume (T.carrier \ wedge i)).toReal := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exfalso
    have := ray_length_le_side i T hv hpb
    linarith
  rcases eq_or_lt_of_le hb with rfl | hb'
  · exfalso
    have := ray_length_le_side' i T hv hpa
    linarith
  exact (wedge_area_both i T ha' hb' hv hpa hpb).2 hab

/-- Loss outside the hexagon dominates loss outside the wedge. -/
theorem volume_diff_wedge_le (i : Fin 6) (T : EquilateralTriangle) :
    (volume (T.carrier \ wedge i)).toReal ≤ (volume (T.carrier \ unitHexagon)).toReal := by
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top T.volume_carrier_lt_top.ne
      (measure_mono Set.sdiff_subset)
  · exact measure_mono (Set.sdiff_subset_sdiff_right (unitHexagon_subset_wedge i))

end ConwaySoifer.SevenTriangles
