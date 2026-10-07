/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Support
public import LeanPool.ConwaySoifer.Geometry.Area
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Caps of a triangle cut by a line

For a triangle `conv {a, b, c}` and a linear level function `g = cross u ·`, the part above
level `ℓ` when `a, b` lie at or below `ℓ` and `c` strictly above is contained in the triangle
`conv {c, X, Y}` with `X, Y` the level-`ℓ` points of the edges `ca`, `cb`; conversely that
triangle is contained in the part at or above `ℓ` when `a, b ≤ ℓ ≤ c`.  Its volume is the
product of the two edge fractions times the volume of the whole triangle.  A level line has
measure zero.  These are the tools for the two area lemmas of the research proof (§2.1 and
§4.1), proved in `CornerCap.lean`.
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
namespace ConwaySoifer

/-- The level-`ℓ` point of the segment from `c` towards `a`. -/
def capPoint (u : Point) (ℓ : ℝ) (c a : Point) : Point :=
  c + ((cross u c - ℓ) / (cross u c - cross u a)) • (a - c)

theorem cross_capPoint (u : Point) (ℓ : ℝ) (c a : Point) (h : cross u a < cross u c) :
    cross u (capPoint u ℓ c a) = ℓ := by
  unfold capPoint
  rw [cross_add_right, cross_smul_right, cross_sub_right]
  have hne : cross u c - cross u a ≠ 0 := by
    linarith
  field_simp
  ring

theorem range_vec3 (a b c : Point) : Set.range (![a, b, c] : Fin 3 → Point) = {a, b, c} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem mem_hull3_iff {a b c : Point} (hdet : triangleDet a b c ≠ 0) (p : Point) :
    p ∈ convexHull ℝ {a, b, c} ↔
      0 ≤ baryFirst a b c p ∧ 0 ≤ barySecond a b c p ∧
        baryFirst a b c p + barySecond a b c p ≤ 1 := by
  rw [← range_vec3, ← triangleHalfspaces_eq_convexHull a b c hdet]
  exact triangleHalfspaces_iff a b c p

theorem mem_hull3_of_coeffs {a b c : Point} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t ≤ 1) : (1 - s - t) • a + s • b + t • c ∈ convexHull ℝ {a, b, c} :=
  convex_three_mem (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp))
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hs ht hst

theorem hull3_comm (a b c : Point) : convexHull ℝ {a, b, c} = convexHull ℝ {b, a, c} := by
  rw [Set.insert_comm]

theorem hull3_rotate (a b c : Point) : convexHull ℝ {a, b, c} = convexHull ℝ {b, c, a} := by
  rw [Set.insert_comm, Set.pair_comm]

theorem cross_convex_combo (u a b c : Point) (s t : ℝ) :
    cross u ((1 - s - t) • a + s • b + t • c) =
      (1 - s - t) * cross u a + s * cross u b + t * cross u c := by
  simp only [cross_add_right, cross_smul_right]

theorem triangleDet_eq_cross (a b c : Point) : triangleDet a b c = cross (b - a) (c - a) := rfl

theorem triangleDet_rotate (a b c : Point) : triangleDet b c a = triangleDet a b c := by
  rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
  simp [triangleDet, cross]; ring

theorem triangleDet_swap (a b c : Point) : triangleDet b a c = -triangleDet a b c := by
  rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
  simp [triangleDet, cross]; ring

/-- The cap above level `ℓ` is contained in the triangle `c, X, Y`. -/
theorem cap_subset (u : Point) (ℓ : ℝ) {a b c : Point} (hdet : triangleDet a b c ≠ 0)
    (ha : cross u a ≤ ℓ) (hb : cross u b ≤ ℓ) (hc : ℓ < cross u c) :
    convexHull ℝ {a, b, c} ∩ {p | ℓ ≤ cross u p} ⊆
      convexHull ℝ {c, capPoint u ℓ c a, capPoint u ℓ c b} := by
  rintro p ⟨hp, hℓ⟩
  simp only [Set.mem_ofPred_eq] at hℓ
  obtain ⟨hs, ht, hst⟩ := (mem_hull3_iff hdet p).mp hp
  have hpe := bary_expansion a b c p hdet
  set s := baryFirst a b c p with hs_def
  set t := barySecond a b c p with ht_def
  have hga : cross u c - cross u a ≠ 0 := by
    linarith
  have hgb : cross u c - cross u b ≠ 0 := by
    linarith
  have hgℓ : cross u c - ℓ ≠ 0 := by
    linarith
  set α := (cross u c - ℓ) / (cross u c - cross u a) with hα
  set β := (cross u c - ℓ) / (cross u c - cross u b) with hβ
  have hαpos : 0 < α := div_pos (by linarith) (by linarith)
  have hβpos : 0 < β := div_pos (by linarith) (by linarith)
  -- coefficients of `p` in the cap triangle
  have hgp : cross u p = (1 - s - t) * cross u a + s * cross u b + t * cross u c := by
    rw [hpe, cross_convex_combo]
  have hsum : (1 - s - t) / α + s / β ≤ 1 := by
    rw [hα, hβ, div_div_eq_mul_div, div_div_eq_mul_div, ← add_div, div_le_one (by linarith)]
    nlinarith
  have hmem := mem_hull3_of_coeffs (a := c) (b := capPoint u ℓ c a) (c := capPoint u ℓ c b)
    (div_nonneg (by linarith) hαpos.le) (div_nonneg hs hβpos.le) hsum
  convert hmem using 1
  rw [hpe]
  simp only [capPoint, ← hα, ← hβ]
  rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
  apply Prod.ext <;> simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul] <;>
    field_simp <;> ring

/-- The triangle `c, X, Y` lies in the part at or above level `ℓ`. -/
theorem cap_supset (u : Point) (ℓ : ℝ) {a b c : Point}
    (ha : cross u a ≤ ℓ) (hb : cross u b ≤ ℓ) (hc : ℓ < cross u c) :
    convexHull ℝ {c, capPoint u ℓ c a, capPoint u ℓ c b} ⊆
      convexHull ℝ {a, b, c} ∩ {p | ℓ ≤ cross u p} := by
  have hX : capPoint u ℓ c a ∈ convexHull ℝ {a, b, c} := by
    have hα0 : 0 ≤ (cross u c - ℓ) / (cross u c - cross u a) := div_nonneg (by linarith) (by
        linarith)
    have hα1 : (cross u c - ℓ) / (cross u c - cross u a) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    unfold capPoint
    exact (convex_convexHull ℝ _).add_smul_sub_mem (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) ⟨hα0, hα1⟩
  have hY : capPoint u ℓ c b ∈ convexHull ℝ {a, b, c} := by
    have hβ0 : 0 ≤ (cross u c - ℓ) / (cross u c - cross u b) := div_nonneg (by linarith) (by
        linarith)
    have hβ1 : (cross u c - ℓ) / (cross u c - cross u b) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    unfold capPoint
    exact (convex_convexHull ℝ _).add_smul_sub_mem (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) ⟨hβ0, hβ1⟩
  have hconv : Convex ℝ (convexHull ℝ {a, b, c} ∩ {p | ℓ ≤ cross u p}) := by
    refine (convex_convexHull ℝ _).inter ?_
    intro p hp q hq x y hx hy hxy
    simp only [Set.mem_ofPred_eq] at hp hq ⊢
    rw [cross_add_right, cross_smul_right, cross_smul_right]
    have hxy' : x * ℓ + y * ℓ = ℓ := by
      rw [← add_mul, hxy, one_mul]
    nlinarith [mul_nonneg hx (sub_nonneg.2 hp), mul_nonneg hy (sub_nonneg.2 hq)]
  apply convexHull_min _ hconv
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨subset_convexHull ℝ _ (by simp), hc.le⟩
  · exact ⟨hX, by simp only [Set.mem_ofPred_eq]; rw [cross_capPoint u ℓ c a (by linarith)]⟩
  · exact ⟨hY, by simp only [Set.mem_ofPred_eq]; rw [cross_capPoint u ℓ c b (by linarith)]⟩

/-- The volume of the cap triangle. -/
theorem volume_capTriangle (u : Point) (ℓ : ℝ) (a b c : Point) :
    volume (convexHull ℝ {c, capPoint u ℓ c a, capPoint u ℓ c b}) =
      ENNReal.ofReal (|(cross u c - ℓ) / (cross u c - cross u a)| *
        |(cross u c - ℓ) / (cross u c - cross u b)| * (|triangleDet a b c| / 2)) := by
  rw [volume_triangle]
  congr 1
  simp only [capPoint, add_sub_cancel_left, cross_smul_left, cross_smul_right, abs_mul]
  rw [triangleDet_eq_cross]
  have : cross (a - c) (b - c) = cross (b - a) (c - a) := by
    rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
    simp [cross]; ring
  rw [this]; ring

/-! ### A level line is a null set -/

theorem volume_level_line (u : Point) (hu : u ≠ 0) (ℓ : ℝ) :
    volume {p : Point | cross u p = ℓ} = 0 := by
  -- the line is a proper affine subspace
  set f : Point →ₗ[ℝ] ℝ := linearForm (-u.2, u.1) with hf
  have hfe : ∀ p, f p = cross u p := by
    intro p; simp [hf, linearForm_apply, cross]; ring
  have hnormSq : 0 < normSq u := (normSq_pos_iff u).mpr hu
  -- a point with `f = 1`
  set v : Point := (normSq u)⁻¹ • rot60 u with hv
  have hfv : f v = 1 := by
    rw [hfe, hv, cross_smul_right, cross_rot60, inv_mul_cancel₀ hnormSq.ne']
  set p0 : Point := ℓ • v with hp0
  have hp0f : f p0 = ℓ := by
    rw [hp0, map_smul, hfv, smul_eq_mul, mul_one]
  have hp0c : cross u p0 = ℓ := by
    rw [← hfe]; exact hp0f
  let S : AffineSubspace ℝ Point := AffineSubspace.mk' p0 (LinearMap.ker f)
  have hS : (S : Set Point) = {p | cross u p = ℓ} := by
    ext p
    simp only [S, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, hfe, cross_sub_right,
      hp0c, Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hStop : S ≠ ⊤ := by
    intro htop
    have : p0 + v ∈ S := by
      rw [htop]; exact AffineSubspace.mem_top _ _ _
    rw [← SetLike.mem_coe, hS] at this
    simp only [Set.mem_ofPred_eq, cross_add_right] at this
    rw [← hfe, ← hfe, hp0f, hfv] at this
    linarith
  rw [← hS]
  exact Measure.addHaar_affineSubspace volume S hStop

theorem volume_inter_level_line (Q : Set Point) (u : Point) (hu : u ≠ 0) (ℓ : ℝ) :
    volume (Q ∩ {p : Point | cross u p = ℓ}) = 0 :=
  measure_mono_null Set.inter_subset_right (volume_level_line u hu ℓ)

/-! ### Level values on an equilateral triangle -/

/-- The two chiralities, for arbitrary vectors of equal length forming an equilateral triangle
with their difference. -/
theorem orientation_of_lengths {e d : Point} {σ : ℝ} (hσ : 0 < σ) (he : normSq e = σ ^ 2)
    (hd : normSq d = σ ^ 2) (hed : normSq (d - e) = σ ^ 2) :
    d = rot60 e ∨ d = rotNeg60 e := by
  have hinner : metricInner e d = σ ^ 2 / 2 := by
    have hsub : normSq (d - e) = normSq d + normSq e - 2 * metricInner e d := by
      rcases e with ⟨a, b⟩; rcases d with ⟨c, d⟩; simp [normSq, metricInner]; ring
    rw [hed, hd, he] at hsub; linarith
  have hlag := lagrange e d
  rw [he, hd, hinner] at hlag
  have hcross : cross e d = σ ^ 2 ∨ cross e d = -(σ ^ 2) := by
    have : cross e d ^ 2 = (σ ^ 2) ^ 2 := by
      nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  have hpos : 0 < normSq e := by
    rw [he]; positivity
  rcases hcross with hc | hc
  · left
    apply point_eq_of_inner_cross_eq hpos
    · rw [metricInner_rot60, he, hinner]
    · rw [cross_rot60, he, hc]
  · right
    apply point_eq_of_inner_cross_eq hpos
    · rw [metricInner_rotNeg60, he, hinner]
    · rw [cross_rotNeg60, he, hc]

theorem cross_rot60_identity (u e : Point) :
    cross u e ^ 2 - cross u e * cross u (rot60 e) + cross u (rot60 e) ^ 2 =
      normSq u * normSq e := by
  rcases u with ⟨a, b⟩; rcases e with ⟨c, d⟩; simp [cross, rot60, normSq]; ring

theorem cross_rotNeg60_identity (u e : Point) :
    cross u e ^ 2 - cross u e * cross u (rotNeg60 e) + cross u (rotNeg60 e) ^ 2 =
      normSq u * normSq e := by
  rcases u with ⟨a, b⟩; rcases e with ⟨c, d⟩; simp [cross, rotNeg60, normSq]; ring

/-- For an equilateral triangle of side `σ` and a level form of unit length, the differences of
the level values of the vertices satisfy `x² - x y + y² = σ²`. -/
theorem level_identity (Q : EquilateralTriangle) (hσ : 0 < Q.side) (u : Point)
    (hu : normSq u = 1) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (cross u (Q.vertices j) - cross u (Q.vertices i)) ^ 2 -
      (cross u (Q.vertices j) - cross u (Q.vertices i)) *
        (cross u (Q.vertices k) - cross u (Q.vertices i)) +
      (cross u (Q.vertices k) - cross u (Q.vertices i)) ^ 2 = Q.side ^ 2 := by
  set e := Q.vertices j - Q.vertices i with he
  set d := Q.vertices k - Q.vertices i with hd
  have hne : normSq e = Q.side ^ 2 := by
    rw [he, ← sqDist_eq_normSq_sub]; exact Q.equilateral j i hij.symm
  have hnd : normSq d = Q.side ^ 2 := by
    rw [hd, ← sqDist_eq_normSq_sub]; exact Q.equilateral k i hik.symm
  have hned : normSq (d - e) = Q.side ^ 2 := by
    have : d - e = Q.vertices k - Q.vertices j := by
      rw [hd, he]; abel
    rw [this, ← sqDist_eq_normSq_sub]; exact Q.equilateral k j hjk.symm
  have h1 : cross u (Q.vertices j) - cross u (Q.vertices i) = cross u e := by
    rw [he, cross_sub_right]
  have h2 : cross u (Q.vertices k) - cross u (Q.vertices i) = cross u d := by
    rw [hd, cross_sub_right]
  rw [h1, h2]
  rcases orientation_of_lengths hσ hne hnd hned with hcw | hccw
  · rw [hcw, cross_rot60_identity, hu, hne, one_mul]
  · rw [hccw, cross_rotNeg60_identity, hu, hne, one_mul]

/-- Every point of the carrier has level at most the maximal vertex level. -/
theorem cross_le_max_vertex (Q : EquilateralTriangle) (u : Point) {p : Point}
    (hp : p ∈ Q.carrier) :
    ∃ i, (∀ j, cross u (Q.vertices j) ≤ cross u (Q.vertices i)) ∧
      cross u p ≤ cross u (Q.vertices i) := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i : Fin 3 => cross u (Q.vertices i))
  refine ⟨i, hi, ?_⟩
  have hsub : Q.carrier ⊆ {q | cross u q ≤ cross u (Q.vertices i)} := by
    apply convexHull_min
    · rintro _ ⟨j, rfl⟩; exact hi j
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [cross_add_right, cross_smul_right, cross_smul_right]
      have hab' : a * cross u (Q.vertices i) + b * cross u (Q.vertices i) = cross u (Q.vertices i)
          := by
        rw [← add_mul, hab, one_mul]
      nlinarith [mul_nonneg ha (sub_nonneg.2 hx), mul_nonneg hb (sub_nonneg.2 hy)]
  exact hsub hp

end ConwaySoifer
