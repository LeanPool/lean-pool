/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Area
public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.WedgeCover
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum.RealSqrt

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
      constructor) <;> ring

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
