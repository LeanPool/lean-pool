/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Thm73
public import LeanPool.RupertMinimality.Minimality.Planes

/-! # Bad Views -/

@[expose] public section

namespace RupertMinimality

/-!
# Lemma 7.4: horizontal double normals occur on finitely many great circles

If the silhouette cycle `x` at the view of `R` has a horizontal double normal,
then `(R l) 2 = 0` for some `l` in a finite set `badDirs V` of nonzero vectors
depending on `V` only.  Each endpoint of the double normal is either a point of
`V` or lies inside a segment `[a, b]` of `V`-points perpendicular to the double
normal; writing both endpoints as `a + s (b - a)` and `c + t (d - c)`, the
double normal `h` is perpendicular to `b - a`, `d - c` and to the view row of
`R`, so either `cross (b - a) (d - c)` lies on the view circle, or `b - a` and
`d - c` are parallel and `h` is the fixed vector `perpTo (c - a) (·)`.
No genericity is needed.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- The component of `w` perpendicular to `e` (`w` itself when `e = 0`). -/
noncomputable def perpTo (w e : ℝ³) : ℝ³ := w - (⟪w, e⟫ / ⟪e, e⟫) • e

theorem perpTo_eq {w e h : ℝ³} (μ : ℝ) (hh : h = w + μ • e) (he : ⟪h, e⟫ = 0) :
    h = perpTo w e := by
  by_cases he0 : e = 0
  · subst he0; simp [perpTo, hh]
  · have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr he0
    have hμ : μ = -(⟪w, e⟫ / ⟪e, e⟫) := by
      rw [hh, inner_add_left, real_inner_smul_left] at he
      field_simp; linarith
    rw [hh, hμ, perpTo, neg_smul, sub_eq_add_neg]

open Classical in
/-- Directions whose view circles contain all horizontal double normals. -/
noncomputable def badDirs (V : Finset ℝ³) : Finset ℝ³ :=
  ((V ×ˢ V ×ˢ V ×ˢ V).biUnion fun q =>
    {cross (q.2.1 - q.1) (q.2.2.2 - q.2.2.1), perpTo (q.2.2.1 - q.1) (q.2.2.2 - q.2.1)}).filter
    (· ≠ 0)

open Classical in
theorem ne_zero_of_mem_badDirs {V : Finset ℝ³} {l : ℝ³} (h : l ∈ badDirs V) : l ≠ 0 :=
  (mem_filter.mp h).2

open Classical in
theorem cross_mem_badDirs {V : Finset ℝ³} {a b c d : ℝ³} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (hd : d ∈ V) (h0 : cross (b - a) (d - c) ≠ 0) : cross (b - a) (d - c) ∈ badDirs V :=
  mem_filter.mpr ⟨mem_biUnion.mpr ⟨(a, b, c, d), by simp [ha, hb, hc, hd], by simp⟩, h0⟩

open Classical in
theorem perpTo_mem_badDirs {V : Finset ℝ³} {a b c d : ℝ³} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (hd : d ∈ V) (h0 : perpTo (c - a) (d - b) ≠ 0) : perpTo (c - a) (d - b) ∈ badDirs V :=
  mem_filter.mpr ⟨mem_biUnion.mpr ⟨(a, b, c, d), by simp [ha, hb, hc, hd], by simp⟩, h0⟩

theorem toEuclideanLin_two (R : Matrix (Fin 3) (Fin 3) ℝ) (l : ℝ³) :
    (R.toEuclideanLin l) 2 = R 2 0 * l 0 + R 2 1 * l 1 + R 2 2 * l 2 := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Cramer: a nonzero vector perpendicular to `e`, `e'`, `r` forces
`det (e, e', r) = 0`. -/
theorem inner_cross_eq_zero_of_perp {h e e' r : ℝ³} (hh : h ≠ 0) (h1 : ⟪h, e⟫ = 0)
    (h2 : ⟪h, e'⟫ = 0) (h3 : ⟪h, r⟫ = 0) : ⟪cross e e', r⟫ = 0 := by
  by_contra hd
  apply hh
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at h1 h2 h3
  have hcomp : ⟪cross e e', r⟫ = r 0 * (e 1 * e' 2 - e 2 * e' 1) +
      r 1 * (e 2 * e' 0 - e 0 * e' 2) + r 2 * (e 0 * e' 1 - e 1 * e' 0) := by
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    simp
  rw [hcomp] at hd
  have key : ∀ m : Fin 3, (r 0 * (e 1 * e' 2 - e 2 * e' 1) +
      r 1 * (e 2 * e' 0 - e 0 * e' 2) + r 2 * (e 0 * e' 1 - e 1 * e' 0)) * h m = 0 := by
    intro m
    fin_cases m
    · change _ * h 0 = 0
      linear_combination (e' 1 * r 2 - e' 2 * r 1) * h1 + (r 1 * e 2 - r 2 * e 1) * h2 +
        (e 1 * e' 2 - e 2 * e' 1) * h3
    · change _ * h 1 = 0
      linear_combination (e' 2 * r 0 - e' 0 * r 2) * h1 + (r 2 * e 0 - r 0 * e 2) * h2 +
        (e 2 * e' 0 - e 0 * e' 2) * h3
    · change _ * h 2 = 0
      linear_combination (e' 0 * r 1 - e' 1 * r 0) * h1 + (r 0 * e 1 - r 1 * e 0) * h2 +
        (e 0 * e' 1 - e 1 * e' 0) * h3
  ext m
  exact (mul_eq_zero.mp (key m)).resolve_left hd

/-- `cross e e' = 0` with `e ≠ 0` makes `e'` a multiple of `e`. -/
theorem eq_smul_of_cross_eq_zero {e e' : ℝ³} (he : e ≠ 0) (h : cross e e' = 0) :
    e' = (⟪e', e⟫ / ⟪e, e⟫) • e := by
  have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr he
  have h0 : e 1 * e' 2 - e 2 * e' 1 = 0 := by simpa [cross] using congrArg (· 0) h
  have h1 : e 2 * e' 0 - e 0 * e' 2 = 0 := by simpa [cross] using congrArg (· 1) h
  have h2 : e 0 * e' 1 - e 1 * e' 0 = 0 := by simpa [cross] using congrArg (· 2) h
  have hee' : ⟪e, e⟫ = e 0 * e 0 + e 1 * e 1 + e 2 * e 2 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  have he'e : ⟪e', e⟫ = e 0 * e' 0 + e 1 * e' 1 + e 2 * e' 2 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ext m
  rw [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hee, he'e, hee']
  fin_cases m <;> simp
  · linear_combination e 2 * h1 - e 1 * h2
  · linear_combination e 0 * h2 - e 2 * h0
  · linear_combination e 1 * h0 - e 0 * h1

theorem liftPt_proj_xy (w : ℝ³) : liftPt (projXy w) (w 2) = w := by
  ext m; fin_cases m <;> simp [liftPt, projXy]

/-- An endpoint of a double normal on a segment `[x, x']`: either a point of
the segment's ends, or a point inside it with the double normal perpendicular
to the segment.  Uniformly: `Y = a + s (b - a)` with `a, b` ends and
`⟪Y' - Y, b - a⟫ = 0`. -/
theorem endpoint_cases {X X' Y Y' : ℝ³} (hY : Y ∈ segment ℝ X X')
    (hX : ⟪Y - Y', X - Y⟫ ≤ 0) (hX' : ⟪Y - Y', X' - Y⟫ ≤ 0) :
    ∃ a b : ℝ³, (a = X ∨ a = X') ∧ (b = X ∨ b = X') ∧ ∃ s : ℝ, Y = a + s • (b - a) ∧
      ⟪Y' - Y, b - a⟫ = 0 := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hY
  rcases hα.eq_or_lt with hα0 | hα0
  · refine ⟨X', X', Or.inr rfl, Or.inr rfl, 0, ?_, by simp⟩
    rw [← hα0, show β = 1 by linarith]; simp
  rcases hβ.eq_or_lt with hβ0 | hβ0
  · refine ⟨X, X, Or.inl rfl, Or.inl rfl, 0, ?_, by simp⟩
    rw [← hβ0, show α = 1 by linarith]; simp
  refine ⟨X, X', Or.inl rfl, Or.inr rfl, β, ?_, ?_⟩
  · rw [show α = 1 - β by linarith]; module
  · rw [show X - (α • X + β • X') = -β • (X' - X) by rw [show α = 1 - β by linarith]; module,
      real_inner_smul_right] at hX
    rw [show X' - (α • X + β • X') = α • (X' - X) by rw [show β = 1 - α by linarith]; module,
      real_inner_smul_right] at hX'
    have e1 : 0 ≤ ⟪α • X + β • X' - Y', X' - X⟫ := by
      by_contra hc; push Not at hc; nlinarith
    have e2 : ⟪α • X + β • X' - Y', X' - X⟫ ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    rw [← neg_sub, inner_neg_left]; linarith

/-- **Lemma 7.4, core.**  A horizontal double normal of the silhouette cycle
`x` (points of `V`) at the view of `R` puts the view on one of the finitely many
great circles `(R l) 2 = 0`, `l ∈ badDirs V`. -/
theorem exists_badDir_of_hdn (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    {k : ℕ} (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (h : HasHorizontalDoubleNormal (fun i => projXy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ l ∈ badDirs V, (R.toEuclideanLin l) 2 = 0 := by
  set L := R.toEuclideanLin with hL
  obtain ⟨y, y', ⟨i, hy⟩, ⟨j, hy'⟩, hz, hne, hn1, hn2⟩ := h
  simp only [liftPt_proj_xy] at hy hy'
  have hseg : ∀ {a b w : ℝ³}, w ∈ segment ℝ (L a) (L b) → ∃ W ∈ segment ℝ a b, w = L W := by
    intro a b w hw
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
    exact ⟨α • a + β • b, ⟨α, β, hα, hβ, hαβ, rfl⟩, by simp [L, map_add, map_smul]⟩
  obtain ⟨Y, hY, rfl⟩ := hseg hy
  obtain ⟨Y', hY', rfl⟩ := hseg hy'
  have hhor : (L (Y' - Y)) 2 = 0 := by
    rw [map_sub, PiLp.sub_apply]; linarith
  have hmem : ∀ m, projXy (L (x m)) ∈
      convexHull ℝ (Set.range fun i => projXy (R.toEuclideanLin (x i))) :=
    fun m => subset_convexHull ℝ _ ⟨m, rfl⟩
  have G : ∀ {A B : ℝ³}, (L (A - B)) 2 = 0 →
      projXy (L A) - projXy (L B) ∈ normalConeAt
        (convexHull ℝ (Set.range fun i => projXy (R.toEuclideanLin (x i)))) (projXy (L A)) →
      ∀ m, ⟪A - B, x m - A⟫ ≤ 0 := by
    intro A B hAB hn m
    have := hn _ (hmem m)
    rwa [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal (by rw [← map_sub]; exact hAB),
      ← map_sub, ← map_sub, hL, inner_toEuclideanLin_SO3 hR] at this
  have hhor' : (L (Y - Y')) 2 = 0 := by rw [← neg_sub, map_neg, PiLp.neg_apply, hhor, neg_zero]
  have GY := G hhor' hn2
  have GY' := G hhor hn1
  obtain ⟨a, b, ha, hb, s, rfl, hs⟩ := endpoint_cases hY (GY i) (GY (i + 1))
  obtain ⟨c, d, hc, hd, t, rfl, ht⟩ := endpoint_cases hY' (GY' j) (GY' (j + 1))
  have haV : a ∈ V := by rcases ha with rfl | rfl <;> exact hxV _
  have hbV : b ∈ V := by rcases hb with rfl | rfl <;> exact hxV _
  have hcV : c ∈ V := by rcases hc with rfl | rfl <;> exact hxV _
  have hdV : d ∈ V := by rcases hd with rfl | rfl <;> exact hxV _
  set h := c + t • (d - c) - (a + s • (b - a)) with hhdef
  have hh0 : h ≠ 0 := by
    intro h0; apply hne; rw [sub_eq_zero.mp h0]
  have ht' : ⟪h, d - c⟫ = 0 := by
    rw [hhdef, ← neg_sub, inner_neg_left, ht, neg_zero]
  have hrow : ∀ l : ℝ³, (L l) 2 = ⟪l, !₂[R 2 0, R 2 1, R 2 2]⟫ := fun l => by
    rw [hL, toEuclideanLin_two]; simp [PiLp.inner_apply, Fin.sum_univ_three]
  by_cases hn : cross (b - a) (d - c) = 0
  · by_cases hba : b - a = 0
    · refine ⟨h, ?_, hhor⟩
      have hp : h = perpTo (c - a) (d - c) :=
        perpTo_eq t (by rw [hhdef, hba, smul_zero, add_zero]; abel) ht'
      rw [hp] at hh0 ⊢
      exact perpTo_mem_badDirs haV hcV hcV hdV hh0
    · obtain ⟨κ, hk⟩ : ∃ κ : ℝ, d - c = κ • (b - a) := ⟨_, eq_smul_of_cross_eq_zero hba hn⟩
      refine ⟨h, ?_, hhor⟩
      have hp : h = perpTo (c - a) (b - a) := perpTo_eq (t * κ - s)
        (by rw [hhdef, hk]; module) hs
      rw [hp] at hh0 ⊢
      exact perpTo_mem_badDirs haV haV hcV hbV hh0
  · refine ⟨cross (b - a) (d - c), cross_mem_badDirs haV hbV hcV hdV hn, ?_⟩
    rw [hrow]
    exact inner_cross_eq_zero_of_perp hh0 hs ht' (by rw [← hrow]; exact hhor)

end Minimality

end RupertMinimality
