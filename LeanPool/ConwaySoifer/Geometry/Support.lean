/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.TriangleHalfspaces
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Support forms and orientations of equilateral triangles in triangular coordinates

The support value of a direction `e` at a point `q` is the determinant `cross e q`; the three
edge directions of an equilateral triangle are `e, rot e, rot (rot e)` where `rot` is the
rotation by 120 degrees, `rot (a, b) = (-a-b, a)`.  The `Orientation` structure records an exact
description of a nondegenerate filled triangle as the intersection of three halfspaces with
these normals; the sum of the three offsets equals `side · |e|`.  This is the geometric fact
behind the certificate checker: three chosen mandatory points give a lower bound for the side
of any triangle of this orientation containing them, and the endpoint/forbidden-point contact
conditions are inherited from `Halfspaces.lean`.

The algebra of the cone lemma (`support_bound_on_cone`) is adapted from
`SevenTriangles/Geometry/Support.lean` (commit `b17ca52a`) to the metric `a² + ab + b²`.
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
namespace ConwaySoifer

/-- Rotation by 120 degrees. -/
def rot (p : Point) : Point := (-p.1 - p.2, p.1)
/-- Rotation by 60 degrees. -/
def rot60 (p : Point) : Point := (-p.2, p.1 + p.2)
/-- Rotation by -60 degrees. -/
def rotNeg60 (p : Point) : Point := (p.1 + p.2, -p.1)

/-- `rotPow j` is `rot` iterated `j` times. -/
def rotPow : Fin 3 → Point → Point := ![id, rot, rot ∘ rot]

@[simp] theorem rotPow_zero (p : Point) : rotPow 0 p = p := rfl
@[simp] theorem rotPow_one (p : Point) : rotPow 1 p = rot p := rfl
@[simp] theorem rotPow_two (p : Point) : rotPow 2 p = rot (rot p) := rfl

theorem rot_rot_rot (p : Point) : rot (rot (rot p)) = p := by
  rcases p with ⟨a, b⟩; apply Prod.ext <;> simp [rot]; ring

theorem rot_add (p q : Point) : rot (p + q) = rot p + rot q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  apply Prod.ext <;> simp [rot]; ring

theorem rot_sub (p q : Point) : rot (p - q) = rot p - rot q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  apply Prod.ext <;> simp [rot]; ring

theorem rot_smul (t : ℝ) (p : Point) : rot (t • p) = t • rot p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot]; ring

theorem rot_neg (p : Point) : rot (-p) = -rot p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot]; ring

theorem rot_sum (p : Point) : p + rot p + rot (rot p) = 0 := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot] <;> ring

theorem rotPow_add (j : Fin 3) (p q : Point) : rotPow j (p + q) = rotPow j p + rotPow j q := by
  fin_cases j <;> simp [rot_add]

theorem rotPow_smul (j : Fin 3) (t : ℝ) (p : Point) : rotPow j (t • p) = t • rotPow j p := by
  fin_cases j <;> simp [rot_smul]

theorem rot60_rot60 (p : Point) : rot60 (rot60 p) = rot p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot60, rot]; ring

theorem rot_rot60 (p : Point) : rot (rot60 p) = -p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot60, rot]

theorem rot_rotNeg60 (p : Point) : rot (rotNeg60 p) = rot60 p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot60, rotNeg60, rot]

theorem rotNeg60_eq (p : Point) : rotNeg60 p = p - rot60 p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [rot60, rotNeg60]

/-! ### Bilinearity of `cross` and the metric -/

theorem cross_add_left (u v w : Point) : cross (u + v) w = cross u w + cross v w := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩; rcases w with ⟨e, f⟩
  simp [cross]; ring

theorem cross_add_right (u v w : Point) : cross u (v + w) = cross u v + cross u w := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩; rcases w with ⟨e, f⟩
  simp [cross]; ring

theorem cross_sub_right (u v w : Point) : cross u (v - w) = cross u v - cross u w := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩; rcases w with ⟨e, f⟩
  simp [cross]; ring

theorem cross_sub_left (u v w : Point) : cross (u - v) w = cross u w - cross v w := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩; rcases w with ⟨e, f⟩
  simp [cross]; ring

theorem cross_smul_left (t : ℝ) (u v : Point) : cross (t • u) v = t * cross u v := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [cross]; ring

theorem cross_smul_right (t : ℝ) (u v : Point) : cross u (t • v) = t * cross u v := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [cross]; ring

theorem cross_neg_left (u v : Point) : cross (-u) v = -cross u v := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [cross]; ring

theorem cross_anticomm (u v : Point) : cross u v = -cross v u := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [cross]; ring

theorem cross_rot (u v : Point) : cross (rot u) (rot v) = cross u v := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [cross, rot]; ring

theorem cross_rotPow (j : Fin 3) (u v : Point) : cross (rotPow j u) (rotPow j v) = cross u v := by
  fin_cases j <;> simp [cross_rot]

/-- Squared length of a vector. -/
def normSq (u : Point) : ℝ := u.1 ^ 2 + u.1 * u.2 + u.2 ^ 2

theorem normSq_eq_sqDist (u : Point) : normSq u = sqDist u (0, 0) := by
  rcases u with ⟨a, b⟩; simp [normSq, sqDist]

theorem normSq_nonneg (u : Point) : 0 ≤ normSq u := by
  rw [normSq_eq_sqDist]; exact sqDist_nonneg _ _

theorem normSq_rot (u : Point) : normSq (rot u) = normSq u := by
  rcases u with ⟨a, b⟩; dsimp [normSq, rot]; ring

theorem normSq_rotPow (j : Fin 3) (u : Point) : normSq (rotPow j u) = normSq u := by
  fin_cases j <;> simp [normSq_rot]

theorem normSq_smul (t : ℝ) (u : Point) : normSq (t • u) = t ^ 2 * normSq u := by
  rcases u with ⟨a, b⟩; simp [normSq]; ring

theorem normSq_neg (u : Point) : normSq (-u) = normSq u := by
  rcases u with ⟨a, b⟩; dsimp [normSq]; ring

theorem normSq_eq_zero_iff (u : Point) : normSq u = 0 ↔ u = 0 := by
  rw [normSq_eq_sqDist, sqDist_eq_zero_iff]; rfl

theorem normSq_pos_iff (u : Point) : 0 < normSq u ↔ u ≠ 0 := by
  constructor
  · intro h hu; rw [hu] at h; simp [normSq] at h
  · intro h; exact lt_of_le_of_ne (normSq_nonneg u) (fun h' => h ((normSq_eq_zero_iff u).mp
      h'.symm))

/-- The metric inner product. -/
def metricInner (u v : Point) : ℝ := u.1 * v.1 + (u.1 * v.2 + u.2 * v.1) / 2 + u.2 * v.2

theorem metricInner_self (u : Point) : metricInner u u = normSq u := by
  rcases u with ⟨a, b⟩; simp [metricInner, normSq]; ring

theorem lagrange (u v : Point) :
    normSq u * normSq v - metricInner u v ^ 2 = (3 / 4 : ℝ) * cross u v ^ 2 := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [normSq, metricInner, cross]; ring

theorem normSq_add (u v : Point) :
    normSq (u + v) = normSq u + normSq v + 2 * metricInner u v := by
  rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩
  simp [normSq, metricInner]; ring

/-- Euclidean length. -/
def len (u : Point) : ℝ := Real.sqrt (normSq u)

theorem len_nonneg (u : Point) : 0 ≤ len u := Real.sqrt_nonneg _

theorem len_sq (u : Point) : len u ^ 2 = normSq u := Real.sq_sqrt (normSq_nonneg u)

theorem len_pos_iff (u : Point) : 0 < len u ↔ u ≠ 0 := by
  rw [len, Real.sqrt_pos, normSq_pos_iff]

theorem metricInner_le_len_mul_len (u v : Point) : metricInner u v ≤ len u * len v := by
  have hlag := lagrange u v
  have hsq : metricInner u v ^ 2 ≤ normSq u * normSq v := by
    nlinarith [sq_nonneg (cross u v)]
  have hprod : 0 ≤ len u * len v := mul_nonneg (len_nonneg u) (len_nonneg v)
  have hprodSq : (len u * len v) ^ 2 = normSq u * normSq v := by
    rw [mul_pow, len_sq, len_sq]
  by_cases h : metricInner u v ≤ 0
  · exact le_trans h hprod
  · have hpos : 0 < metricInner u v := lt_of_not_ge h
    nlinarith

theorem len_add_le (u v : Point) : len (u + v) ≤ len u + len v := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact add_nonneg (len_nonneg u) (len_nonneg v)
  rw [normSq_add, add_sq, len_sq, len_sq]
  have := metricInner_le_len_mul_len u v
  linarith

theorem len_smul_nonneg {t : ℝ} (ht : 0 ≤ t) (u : Point) : len (t • u) = t * len u := by
  rw [len, normSq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_nonneg ht]
  rfl

theorem len_rotPow (j : Fin 3) (u : Point) : len (rotPow j u) = len u := by
  rw [len, len, normSq_rotPow]

/-! ### Cones -/

/-- Nonnegative coordinates of a vector inside a two-dimensional cone. -/
theorem exists_nonneg_combo_of_cross {u v l : Point} (huv : 0 < cross u v)
    (hul : 0 ≤ cross u l) (hlv : 0 ≤ cross l v) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ l = a • u + b • v := by
  refine ⟨cross l v / cross u v, cross u l / cross u v, div_nonneg hlv huv.le,
    div_nonneg hul huv.le, ?_⟩
  rcases u with ⟨ux, uz⟩; rcases v with ⟨vx, vz⟩; rcases l with ⟨lx, lz⟩
  have hne : ux * vz - uz * vx ≠ 0 := by
    simpa [cross] using huv.ne'
  have hne' : vz * ux - vx * uz ≠ 0 := by
    convert hne using 1; ring
  apply Prod.ext
  · dsimp [cross]; field_simp [hne, hne']; ring
  · dsimp [cross]; field_simp [hne, hne']; ring

/-- The support numerator of a direction for three chosen points. -/
def supportNum (e p₀ p₁ p₂ : Point) : ℝ :=
  cross e p₀ + cross (rot e) p₁ + cross (rot (rot e)) p₂

theorem supportNum_add (e f p₀ p₁ p₂ : Point) :
    supportNum (e + f) p₀ p₁ p₂ = supportNum e p₀ p₁ p₂ + supportNum f p₀ p₁ p₂ := by
  simp only [supportNum, rot_add, cross_add_left]; ring

theorem supportNum_smul (t : ℝ) (e p₀ p₁ p₂ : Point) :
    supportNum (t • e) p₀ p₁ p₂ = t * supportNum e p₀ p₁ p₂ := by
  simp only [supportNum, rot_smul, cross_smul_left]; ring

/-- Endpoint support certificates propagate to every direction of their cone. -/
theorem support_bound_on_cone {u v l p₀ p₁ p₂ : Point}
    (hu : len u ≤ supportNum u p₀ p₁ p₂) (hv : len v ≤ supportNum v p₀ p₁ p₂)
    (huv : 0 < cross u v) (hul : 0 ≤ cross u l) (hlv : 0 ≤ cross l v) :
    len l ≤ supportNum l p₀ p₁ p₂ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_nonneg_combo_of_cross huv hul hlv
  calc
    len (a • u + b • v) ≤ len (a • u) + len (b • v) := len_add_le _ _
    _ = a * len u + b * len v := by
      rw [len_smul_nonneg ha, len_smul_nonneg hb]
    _ ≤ a * supportNum u p₀ p₁ p₂ + b * supportNum v p₀ p₁ p₂ :=
      add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
    _ = supportNum (a • u + b • v) p₀ p₁ p₂ := by
      rw [supportNum_add, supportNum_smul, supportNum_smul]

/-! ### The two chiralities of an equilateral triangle -/

theorem metricInner_rot60 (u : Point) : metricInner u (rot60 u) = normSq u / 2 := by
  rcases u with ⟨a, b⟩; simp [metricInner, rot60, normSq]; ring

theorem cross_rot60 (u : Point) : cross u (rot60 u) = normSq u := by
  rcases u with ⟨a, b⟩; simp [cross, rot60, normSq]; ring

theorem metricInner_rotNeg60 (u : Point) : metricInner u (rotNeg60 u) = normSq u / 2 := by
  rcases u with ⟨a, b⟩; simp [metricInner, rotNeg60, normSq]; ring

theorem cross_rotNeg60 (u : Point) : cross u (rotNeg60 u) = -normSq u := by
  rcases u with ⟨a, b⟩; simp [cross, rotNeg60, normSq]; ring

theorem point_eq_of_inner_cross_eq {e p q : Point} (he : 0 < normSq e)
    (hinner : metricInner e p = metricInner e q) (hcross : cross e p = cross e q) : p = q := by
  have hiw : metricInner e (p - q) = 0 := by
    rcases e with ⟨a, b⟩; rcases p with ⟨c, d⟩; rcases q with ⟨x, y⟩
    simp [metricInner] at hinner ⊢; linarith
  have hcw : cross e (p - q) = 0 := by
    rw [cross_sub_right, hcross, sub_self]
  have hlag := lagrange e (p - q)
  rw [hiw, hcw] at hlag
  have hw : normSq (p - q) = 0 := by
    nlinarith [normSq_nonneg (p - q)]
  rw [normSq_eq_zero_iff] at hw
  exact sub_eq_zero.mp hw

theorem sqDist_eq_normSq_sub (p q : Point) : sqDist p q = normSq (p - q) := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩; simp [sqDist, normSq]

/-- The third vertex of an equilateral triangle is obtained from the first edge by a rotation of
`±60` degrees. -/
theorem EquilateralTriangle.thirdVertex_orientation (T : EquilateralTriangle) :
    T.vertices 2 - T.vertices 0 = rot60 (T.vertices 1 - T.vertices 0) ∨
      T.vertices 2 - T.vertices 0 = rotNeg60 (T.vertices 1 - T.vertices 0) := by
  set u := T.vertices 1 - T.vertices 0 with hu
  set v := T.vertices 2 - T.vertices 0 with hv
  have h10 : normSq u = T.side ^ 2 := by
    rw [hu, ← sqDist_eq_normSq_sub]; exact T.equilateral 1 0 (by decide)
  have h20 : normSq v = T.side ^ 2 := by
    rw [hv, ← sqDist_eq_normSq_sub]; exact T.equilateral 2 0 (by decide)
  have h21 : normSq (v - u) = T.side ^ 2 := by
    have : v - u = T.vertices 2 - T.vertices 1 := by
      rw [hu, hv]; abel
    rw [this, ← sqDist_eq_normSq_sub]; exact T.equilateral 2 1 (by decide)
  have hinner : metricInner u v = T.side ^ 2 / 2 := by
    have hsub : normSq (v - u) = normSq v + normSq u - 2 * metricInner u v := by
      rcases u with ⟨a, b⟩; rcases v with ⟨c, d⟩; simp [normSq, metricInner]; ring
    rw [h21, h20, h10] at hsub; linarith
  have hlag := lagrange u v
  rw [h10, h20, hinner] at hlag
  have hcross : cross u v = T.side ^ 2 ∨ cross u v = -(T.side ^ 2) := by
    have : cross u v ^ 2 = (T.side ^ 2) ^ 2 := by
      nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  by_cases hs : T.side = 0
  · have hu0 : u = 0 := (normSq_eq_zero_iff u).mp (by rw [h10, hs]; ring)
    have hv0 : v = 0 := (normSq_eq_zero_iff v).mp (by rw [h20, hs]; ring)
    left; rw [hu0, hv0]; apply Prod.ext <;> simp [rot60]
  have hpos : 0 < normSq u := by
    rw [h10]; positivity
  rcases hcross with hc | hc
  · left
    apply point_eq_of_inner_cross_eq hpos
    · rw [metricInner_rot60, h10, hinner]
    · rw [cross_rot60, h10, hc]
  · right
    apply point_eq_of_inner_cross_eq hpos
    · rw [metricInner_rotNeg60, h10, hinner]
    · rw [cross_rotNeg60, h10, hc]

/-! ### Orientations -/

theorem forall_fin3 {P : Fin 3 → Prop} : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ j => by fin_cases j <;> assumption⟩

theorem vec3_zero (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 0 = a := rfl
theorem vec3_one (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 1 = b := rfl
theorem vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

theorem neg_rot_eq (p : Point) : -rot p = p - rot60 p := by
  rcases p with ⟨a, b⟩; apply Prod.ext <;> simp [rot, rot60]; ring

theorem rot_rotNeg60_sub (p : Point) : rot (rotNeg60 p - p) = p := by
  rcases p with ⟨a, b⟩; apply Prod.ext <;> simp [rot, rotNeg60]; ring

theorem rot_eq_neg_rotNeg60 (p : Point) : rot p = -rotNeg60 p := by
  rcases p with ⟨a, b⟩; apply Prod.ext <;> simp [rot, rotNeg60]; ring

/-- An exact halfspace description of a filled triangle whose outward edge directions are the
three successive 120-degree rotations of `dir`, together with the side identity. -/
structure Orientation (T : EquilateralTriangle) where
  /-- An outward edge direction in triangular coordinates. -/
  dir : Point
  /-- The three bounds for the successive rotated edge directions. -/
  offset : Fin 3 → ℝ
  dir_pos : 0 < normSq dir
  mem_iff : ∀ q, q ∈ T.carrier ↔ ∀ j : Fin 3, cross (rotPow j dir) q ≤ offset j
  sum_offset : offset 0 + offset 1 + offset 2 = T.side * len dir

theorem EquilateralTriangle.exists_orientation (T : EquilateralTriangle) (hs : 0 < T.side) :
    Nonempty (Orientation T) := by
  obtain ⟨a, ha⟩ : ∃ a, a = T.vertices 0 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = T.vertices 1 - T.vertices 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = T.vertices 2 - T.vertices 0 := ⟨_, rfl⟩
  have hmem : ∀ q, q ∈ T.carrier ↔
      0 ≤ cross (q - a) v / cross u v ∧ 0 ≤ cross u (q - a) / cross u v ∧
        cross (q - a) v / cross u v + cross u (q - a) / cross u v ≤ 1 := by
    intro q
    rw [T.carrier_eq_halfspaces hs, EquilateralTriangle.halfspaces, triangleHalfspaces_iff]
    simp only [baryFirst, barySecond, triangleDet]
    rw [← hu, ← hv, ← ha]
  have hnu : normSq u = T.side ^ 2 := by
    rw [hu, ← sqDist_eq_normSq_sub]; exact T.equilateral 1 0 (by decide)
  have hnv : normSq v = T.side ^ 2 := by
    rw [hv, ← sqDist_eq_normSq_sub]; exact T.equilateral 2 0 (by decide)
  have hnvu : normSq (v - u) = T.side ^ 2 := by
    have : v - u = T.vertices 2 - T.vertices 1 := by
      rw [hu, hv]; abel
    rw [this, ← sqDist_eq_normSq_sub]; exact T.equilateral 2 1 (by decide)
  have hlen : ∀ w, normSq w = T.side ^ 2 → len w = T.side := by
    intro w hw; rw [len, hw, Real.sqrt_sq hs.le]
  have horient := T.thirdVertex_orientation
  rw [← hu, ← hv] at horient
  -- the five atoms
  have hX : ∀ q, cross (q - a) v = -cross v q + cross v a := by
    intro q; rw [cross_sub_left, cross_anticomm q v, cross_anticomm a v]; ring
  have hZ : ∀ q, cross u (q - a) = cross u q - cross u a := fun q => cross_sub_right _ _ _
  rcases horient with hccw | hcw
  · -- counterclockwise: `v = rot60 u`, normals `v, -u, u - v`
    have hcuv : cross u v = normSq u := by
      rw [hccw, cross_rot60]
    have hpos : 0 < cross u v := by
      rw [hcuv, hnu]; positivity
    have e1 : rot v = -u := by
      rw [hccw, rot_rot60]
    have e2 : rot (-u) = u - v := by
      rw [rot_neg, neg_rot_eq, hccw]
    refine ⟨⟨v, ![cross v a, cross (-u) a, cross (u - v) a + cross u v], ?_, ?_, ?_⟩⟩
    · rw [hnv]; positivity
    · intro q
      rw [hmem q, forall_fin3, vec3_zero, vec3_one, vec3_two, rotPow_zero, rotPow_one,
        rotPow_two, e1, e2, hX, hZ, cross_neg_left, cross_neg_left, cross_sub_left,
        cross_sub_left, ← add_div, div_le_one hpos, div_nonneg_iff, div_nonneg_iff]
      constructor
      · rintro ⟨h0, h1, h2⟩
        have h0' : 0 ≤ -cross v q + cross v a := by
          rcases h0 with h | h
          · exact h.1
          · exact absurd h.2 (not_le.mpr hpos)
        have h1' : 0 ≤ cross u q - cross u a := by
          rcases h1 with h | h
          · exact h.1
          · exact absurd h.2 (not_le.mpr hpos)
        refine ⟨by linarith, by linarith, by linarith⟩
      · rintro ⟨h0, h1, h2⟩
        refine ⟨Or.inl ⟨by linarith, hpos.le⟩, Or.inl ⟨by linarith, hpos.le⟩, by linarith⟩
    · rw [vec3_zero, vec3_one, vec3_two, cross_neg_left, cross_sub_left, hlen v hnv, hcuv, hnu]
      ring
  · -- clockwise: `v = rotNeg60 u`, normals `v - u, u, -v`
    have hcuv : cross u v = -normSq u := by
      rw [hcw, cross_rotNeg60]
    have hneg : cross u v < 0 := by
      rw [hcuv, hnu]; nlinarith
    have e1 : rot (v - u) = u := by
      rw [hcw, rot_rotNeg60_sub]
    have e2 : rot u = -v := by
      rw [hcw, rot_eq_neg_rotNeg60]
    refine ⟨⟨v - u, ![cross (v - u) a - cross u v, cross u a, cross (-v) a], ?_, ?_, ?_⟩⟩
    · rw [hnvu]; positivity
    · intro q
      rw [hmem q, forall_fin3, vec3_zero, vec3_one, vec3_two, rotPow_zero, rotPow_one,
        rotPow_two, e1, e2, hX, hZ, cross_neg_left, cross_neg_left, cross_sub_left,
        cross_sub_left, ← add_div, div_le_one_of_neg hneg, div_nonneg_iff, div_nonneg_iff]
      constructor
      · rintro ⟨h0, h1, h2⟩
        have h0' : -cross v q + cross v a ≤ 0 := by
          rcases h0 with h | h
          · exact absurd h.2 (not_le.mpr hneg)
          · exact h.1
        have h1' : cross u q - cross u a ≤ 0 := by
          rcases h1 with h | h
          · exact absurd h.2 (not_le.mpr hneg)
          · exact h.1
        refine ⟨by linarith, by linarith, by linarith⟩
      · rintro ⟨h0, h1, h2⟩
        refine ⟨Or.inr ⟨by linarith, hneg.le⟩, Or.inr ⟨by linarith, hneg.le⟩, by linarith⟩
    · rw [vec3_zero, vec3_one, vec3_two, cross_neg_left, cross_sub_left, hlen (v - u) hnvu, hcuv,
        hnu]
      ring

/-! ### Consequences used by the checker -/

namespace Orientation
variable {T : EquilateralTriangle} (O : Orientation T)

theorem cross_le (j : Fin 3) {q : Point} (hq : q ∈ T.carrier) :
    cross (rotPow j O.dir) q ≤ O.offset j := (O.mem_iff q).mp hq j

/-- Three contained points bound the side from below. -/
theorem supportNum_le {p₀ p₁ p₂ : Point} (h₀ : p₀ ∈ T.carrier) (h₁ : p₁ ∈ T.carrier)
    (h₂ : p₂ ∈ T.carrier) : supportNum O.dir p₀ p₁ p₂ ≤ T.side * len O.dir := by
  have e0 := O.cross_le 0 h₀
  have e1 := O.cross_le 1 h₁
  have e2 := O.cross_le 2 h₂
  simp only [rotPow_zero, rotPow_one, rotPow_two] at e0 e1 e2
  rw [← O.sum_offset]; unfold supportNum; linarith

theorem len_dir_pos : 0 < len O.dir := by
  rw [len, Real.sqrt_pos]; exact O.dir_pos

/-- Any direction-form certificate `len l ≤ supportNum l …` for three contained points forces
`1 ≤ side`, provided `l` is a positive multiple of the orientation direction. -/
theorem one_le_side_of_bound {p₀ p₁ p₂ : Point} (h₀ : p₀ ∈ T.carrier) (h₁ : p₁ ∈ T.carrier)
    (h₂ : p₂ ∈ T.carrier) (hb : len O.dir ≤ supportNum O.dir p₀ p₁ p₂) : 1 ≤ T.side := by
  have h := O.supportNum_le h₀ h₁ h₂
  have hl := O.len_dir_pos
  nlinarith

/-- The halfspace system of an orientation. -/
def system : HalfspaceSystem (Fin 3) where
  normal j := linearForm (-(rotPow j O.dir).2, (rotPow j O.dir).1)
  offset := O.offset

theorem system_normal_apply (j : Fin 3) (q : Point) :
    O.system.normal j q = cross (rotPow j O.dir) q := by
  simp [system, linearForm_apply, cross]; ring

theorem carrier_eq_system : T.carrier = O.system.carrier := by
  ext q
  rw [O.mem_iff q]
  simp only [HalfspaceSystem.carrier, Set.mem_ofPred_eq, system_normal_apply]
  rfl

/-- A full ray endpoint has an outward edge direction with positive exit derivative that is
supported at the endpoint. -/
theorem full_endpoint {v d : Point} (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) :
    ∃ j : Fin 3, 0 < cross (rotPow j O.dir) d ∧
      ∀ q ∈ T.carrier, cross (rotPow j O.dir) q ≤
        cross (rotPow j O.dir) (linePoint v d (rayLen T v d)) := by
  obtain ⟨j, hj, -, hq⟩ := rayLen_has_supporting_normal T O.system O.carrier_eq_system hv hd
  refine ⟨j, ?_, ?_⟩
  · rwa [system_normal_apply] at hj
  · intro q hq'
    have := hq q hq'
    rwa [system_normal_apply, system_normal_apply] at this

/-- A forbidden point on a positive ray from a contained point has a strictly separating outward
edge direction with positive exit derivative. -/
theorem forbidden {v d : Point} (hv : v ∈ T.carrier) {t : ℝ} (ht : 0 < t)
    (hout : linePoint v d t ∉ T.carrier) :
    ∃ j : Fin 3, 0 < cross (rotPow j O.dir) d ∧
      ∀ q ∈ T.carrier, cross (rotPow j O.dir) q < cross (rotPow j O.dir) (linePoint v d t) := by
  obtain ⟨j, hj, hq⟩ := forbidden_ray_has_strict_support T O.system O.carrier_eq_system hv ht hout
  refine ⟨j, ?_, ?_⟩
  · rwa [system_normal_apply] at hj
  · intro q hq'
    have := hq q hq'
    rwa [system_normal_apply, system_normal_apply] at this

end Orientation

/-! ### The three 120-degree cones cover the plane -/

/-- The constant east vector in triangular coordinates. -/
def eastDir : Point := (1, 0)

theorem rot_eastDir : rot eastDir = (-1, 1) := by
  simp [rot, eastDir]

theorem cone_cover_of_rot (e : Point) :
    (0 ≤ cross eastDir e ∧ 0 ≤ cross e (rot eastDir)) ∨
      (0 ≤ cross eastDir (rot e) ∧ 0 ≤ cross (rot e) (rot eastDir)) ∨
      (0 ≤ cross eastDir (rot (rot e)) ∧ 0 ≤ cross (rot (rot e)) (rot eastDir)) := by
  rcases e with ⟨x, y⟩
  simp only [cross, eastDir, rot]
  by_cases hy : 0 ≤ y
  · by_cases hxy : 0 ≤ x + y
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · by_cases hx : 0 ≤ x
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

/-! ### Relabelling the faces and choosing a representative in the first cone -/

theorem rotPow_succ (j : Fin 3) (p : Point) : rotPow j (rot p) = rotPow (j + 1) p := by
  fin_cases j <;> simp [rot_rot_rot]

/-- The same triangle with the faces relabelled cyclically: `dir ↦ rot dir`. -/
def Orientation.rotate {T : EquilateralTriangle} (O : Orientation T) : Orientation T where
  dir := rot O.dir
  offset := fun j => O.offset (j + 1)
  dir_pos := by
    rw [normSq_rot]; exact O.dir_pos
  mem_iff := by
    intro q
    rw [O.mem_iff q]
    constructor
    · intro h j; rw [rotPow_succ]; exact h (j + 1)
    · intro h j
      have := h (j - 1)
      rw [rotPow_succ, sub_add_cancel] at this
      exact this
  sum_offset := by
    have : O.offset (0 + 1) + O.offset (1 + 1) + O.offset (2 + 1) =
        O.offset 0 + O.offset 1 + O.offset 2 := by
      simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
        show (2 : Fin 3) + 1 = 0 from rfl]
      ring
    change O.offset (0 + 1) + O.offset (1 + 1) + O.offset (2 + 1) = T.side * len (rot O.dir)
    rw [this, O.sum_offset, len, len, normSq_rot]

/-- Every nondegenerate triangle has an orientation whose direction lies in the closed cone from
`eastDir` to `rot eastDir`. -/
theorem EquilateralTriangle.exists_orientation_in_arc (T : EquilateralTriangle)
    (hs : 0 < T.side) :
    ∃ O : Orientation T, 0 ≤ cross eastDir O.dir ∧ 0 ≤ cross O.dir (rot eastDir) := by
  obtain ⟨O⟩ := T.exists_orientation hs
  rcases cone_cover_of_rot O.dir with h | h | h
  · exact ⟨O, h⟩
  · exact ⟨O.rotate, h⟩
  · exact ⟨O.rotate.rotate, h⟩

/-! ### Parallel vectors inside the first cone -/

theorem exists_parallel_of_cross_eq_zero {u l : Point} (hu : u ≠ 0) (h : cross u l = 0) :
    ∃ t : ℝ, l = t • u := by
  rcases u with ⟨a, b⟩; rcases l with ⟨c, d⟩
  simp only [cross] at h
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl; exact hu rfl
    have hc : c = 0 := by
      have : -(b * c) = 0 := by
        linarith
      simpa [hb] using this
    refine ⟨d / b, ?_⟩
    apply Prod.ext <;> simp [hc]; field_simp
  · refine ⟨c / a, ?_⟩
    apply Prod.ext
    · simp; field_simp
    · simp; field_simp; linarith

/-- In the closed cone from `eastDir` to `rot eastDir`, a nonzero vector parallel to another
nonzero vector of the cone is a positive multiple of it. -/
theorem pos_of_parallel_in_arc {u l : Point} (hu : u ≠ 0) (hl : l ≠ 0)
    (hu₁ : 0 ≤ cross eastDir u) (hu₂ : 0 ≤ cross u (rot eastDir))
    (hl₁ : 0 ≤ cross eastDir l) (hl₂ : 0 ≤ cross l (rot eastDir)) (h : cross u l = 0) :
    ∃ t : ℝ, 0 < t ∧ l = t • u := by
  obtain ⟨t, rfl⟩ := exists_parallel_of_cross_eq_zero hu h
  refine ⟨t, ?_, rfl⟩
  have ht0 : t ≠ 0 := by
    rintro rfl; simp at hl
  rw [cross_smul_right] at hl₁
  rw [cross_smul_left] at hl₂
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · exfalso
    -- `cross eastDir u ≥ 0` and `t < 0` force `cross eastDir u = 0`, then `u ∥ eastDir`
    have h1 : cross eastDir u = 0 := by
      nlinarith
    have h2 : cross u (rot eastDir) = 0 := by
      nlinarith
    rcases u with ⟨a, b⟩
    simp only [cross, eastDir, rot] at h1 h2
    have hb : b = 0 := by
      linarith
    have ha : a = 0 := by
      rw [hb] at h2; linarith
    exact hu (by simp [ha, hb])
  · exact ht

end ConwaySoifer
