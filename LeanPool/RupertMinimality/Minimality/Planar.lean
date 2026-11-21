/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Planes
public import LeanPool.RupertMinimality.Minimality.Pyramid

/-! # Planar -/

@[expose] public section

namespace RupertMinimality

/-!
# Flat point sets: the sharp statements

* `isRupert_of_coplanar_of_not_collinear`: points in a plane, not all on one
  line, are Rupert (any number of points).  The outer copy is seen face-on, so
  its shadow is the polygon `P` itself; the inner copy is seen edge-on, along a
  direction lying in the plane, so its shadow is a segment whose length is the
  width `w` of `P` in the perpendicular direction.  For all but finitely many
  directions `w` is strictly less than the diameter `D` of `P`
  (`exists_short_shadow`), and a diameter chord of `P`, shrunk by the factor
  `w / D < 1` towards an interior point, is a segment of length `w` inside
  the interior of `P`.
* `not_isRupert_of_collinear`: a nonempty set of points on a line is not
  Rupert (every shadow lies on a line, and has empty interior).
* `isRupert_empty`: the empty set is (vacuously) Rupert.
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix
open Module

/-- Affine images of collinear sets are collinear. -/
theorem collinear_image_affine {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (f : E →ᵃ[ℝ] F) {s : Set E} (h : Collinear ℝ s) : Collinear ℝ (f '' s) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p₀, v, hv⟩ := h
  refine ⟨f p₀, f.linear v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := hv p hp
  exact ⟨r, by rw [AffineMap.map_vadd, LinearMap.map_smul]⟩

/-- A set of points of the plane, not all on one line, has a convex hull with
nonempty interior. -/
theorem interior_convexHull_nonempty_of_not_collinear {S : Set ℝ²} (h : ¬ Collinear ℝ S) :
    (interior (convexHull ℝ S)).Nonempty := by
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact absurd (collinear_empty ℝ ℝ²) h
    · exact hne
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne]
  rw [collinear_iff_finrank_le_one, not_le] at h
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le (vectorSpan ℝ S)
  rw [finrank_euclideanSpace_fin] at this ⊢
  omega

/-- The convex hull of a set of points of the plane lying on one line has empty
interior. -/
theorem interior_convexHull_eq_empty_of_collinear {S : Set ℝ²} (h : Collinear ℝ S) :
    interior (convexHull ℝ S) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have htop := interior_convexHull_nonempty_iff_affineSpan_eq_top.mp ⟨x, hx⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp at hx
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne] at htop
  rw [collinear_iff_finrank_le_one, htop, finrank_top, finrank_euclideanSpace_fin] at h
  omega

/-- **Short shadows.**  For a polygon `P = conv W` (`W` not collinear) there is
a unit direction `(c, s)` and a unit vector `u` such that the segment
`{o + ⟪(c, s), q⟫ u | q ∈ P}`, for a suitable offset `o`, lies in the interior
of `P`: the width of `P` in direction `(c, s)` is less than the diameter of
`P`, so a shrunk copy of a diameter chord fits inside. -/
theorem exists_short_shadow (W : Finset ℝ²) (hW : ¬ Collinear ℝ (W : Set ℝ²)) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ ∃ u : ℝ², u 0 ^ 2 + u 1 ^ 2 = 1 ∧ ∃ o : ℝ²,
      ∀ q ∈ convexHull ℝ (W : Set ℝ²),
        o + (c * q 0 + s * q 1) • u ∈ interior (convexHull ℝ (W : Set ℝ²)) := by
  classical
  obtain ⟨x0, hx0⟩ := interior_convexHull_nonempty_of_not_collinear hW
  -- two distinct points
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ : ∃ w₁ ∈ W, ∃ w₂ ∈ W, w₁ ≠ w₂ := by
    by_contra hcon
    push Not at hcon
    apply hW
    rcases W.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · simp [collinear_empty]
    · exact (collinear_singleton ℝ w).subset fun p hp => by
        rw [Set.mem_singleton_iff]; exact hcon p hp w hw
  -- a diameter `[a, b]`, of length `D`
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := (W ×ˢ W).exists_max_image (fun p : ℝ² × ℝ² => ‖p.2 - p.1‖)
    ⟨(w₁, w₂), Finset.mem_product.mpr ⟨hw₁, hw₂⟩⟩
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨D, hD⟩ : ∃ D, D = ‖b - a‖ := ⟨_, rfl⟩
  have hdiam : ∀ w ∈ W, ∀ w' ∈ W, ‖w - w'‖ ≤ D := fun w hw w' hw' => by
    rw [hD]; exact hmax (w', w) (Finset.mem_product.mpr ⟨hw', hw⟩)
  have hDpos : 0 < D := lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
    (hdiam w₂ hw₂ w₁ hw₁)
  have hnormsq : ∀ z : ℝ², ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := fun z => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [sq_abs]
  -- a direction `(1, r)` not parallel to any difference of two points of `W`
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset
    ((W ×ˢ W).image fun p : ℝ² × ℝ² => (p.1 - p.2) 1 / (p.1 - p.2) 0)
  obtain ⟨n, hn⟩ : ∃ n, n = √(1 + r ^ 2) := ⟨_, rfl⟩
  have hn2 : n ^ 2 = 1 + r ^ 2 := by rw [hn, Real.sq_sqrt (by positivity)]
  have hnpos : 0 < n := by rw [hn]; positivity
  set c := 1 / n with hc
  set s := r / n with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, div_pow, div_pow, ← add_div, hn2]; field_simp
  -- the width in direction `(c, s)` is less than `D`
  have hwidth : ∀ w ∈ W, ∀ w' ∈ W, c * (w 0 - w' 0) + s * (w 1 - w' 1) < D := by
    intro w hw w' hw'
    obtain ⟨x, hx⟩ : ∃ x, x = w 0 - w' 0 := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = w 1 - w' 1 := ⟨_, rfl⟩
    rw [← hx, ← hy]
    have hnorm : x ^ 2 + y ^ 2 ≤ D ^ 2 := by
      have h1 := hnormsq (w - w')
      simp only [PiLp.sub_apply] at h1
      rw [hx, hy, ← h1]
      exact pow_le_pow_left₀ (norm_nonneg _) (hdiam w hw w' hw') 2
    have key : x + r * y < D * n := by
      by_cases hxy : r * x = y
      · by_cases hx0 : x = 0
        · have : y = 0 := by rw [← hxy, hx0, mul_zero]
          rw [hx0, this]; simp only [mul_zero, add_zero]; positivity
        · refine absurd (Finset.mem_image.mpr ⟨(w, w'), Finset.mem_product.mpr ⟨hw, hw'⟩, ?_⟩) hr
          simp only [PiLp.sub_apply]
          rw [← hx, ← hy, ← hxy]
          field_simp
      · have hpos : 0 < (r * x - y) ^ 2 := by
          have : r * x - y ≠ 0 := sub_ne_zero.mpr hxy
          positivity
        by_contra hcon
        push Not at hcon
        have h1 : (D * n) ^ 2 ≤ (x + r * y) ^ 2 := pow_le_pow_left₀ (by positivity) hcon 2
        have h2 : (x + r * y) ^ 2 + (r * x - y) ^ 2 = (1 + r ^ 2) * (x ^ 2 + y ^ 2) := by ring
        have h3 : (1 + r ^ 2) * (x ^ 2 + y ^ 2) ≤ (1 + r ^ 2) * D ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
        have h4 : (D * n) ^ 2 = D ^ 2 * (1 + r ^ 2) := by rw [mul_pow, hn2]
        nlinarith
    have : c * x + s * y = (x + r * y) / n := by rw [hc, hs]; field_simp
    rw [this, div_lt_iff₀ hnpos]
    exact key
  -- the extreme values `m ≤ M` of `⟪(c, s), ·⟫` on `W`, and on `P`
  obtain ⟨wM, hwM, hM⟩ := W.exists_max_image (fun q : ℝ² => c * q 0 + s * q 1) ⟨w₁, hw₁⟩
  obtain ⟨wm, hwm, hm⟩ := W.exists_min_image (fun q : ℝ² => c * q 0 + s * q 1) ⟨w₁, hw₁⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = c * wM 0 + s * wM 1 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = c * wm 0 + s * wm 1 := ⟨_, rfl⟩
  have hMm : M - m < D := by
    have := hwidth wM hwM wm hwm
    rw [hMdef, hmdef]; linarith
  have hmM : m ≤ M := by rw [hmdef, hMdef]; exact hm wM hwM
  have hbound : ∀ q ∈ convexHull ℝ (W : Set ℝ²),
      m ≤ c * q 0 + s * q 1 ∧ c * q 0 + s * q 1 ≤ M := by
    have hconv : Convex ℝ {q : ℝ² | m ≤ c * q 0 + s * q 1 ∧ c * q 0 + s * q 1 ≤ M} := by
      intro x hx y hy α β hα hβ hαβ
      simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
      have e : c * (α * x 0 + β * y 0) + s * (α * x 1 + β * y 1) =
          α * (c * x 0 + s * x 1) + β * (c * y 0 + s * y 1) := by ring
      have em : α * m + β * m = m := by rw [← add_mul, hαβ, one_mul]
      have eM : α * M + β * M = M := by rw [← add_mul, hαβ, one_mul]
      rw [e]
      constructor <;> linarith [mul_le_mul_of_nonneg_left hx.1 hα,
        mul_le_mul_of_nonneg_left hx.2 hα, mul_le_mul_of_nonneg_left hy.1 hβ,
        mul_le_mul_of_nonneg_left hy.2 hβ]
    intro q hq
    refine convexHull_min (fun w hw => ?_) hconv hq
    exact ⟨hmdef ▸ hm w hw, hMdef ▸ hM w hw⟩
  -- the segment
  set lam := (M - m) / D with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hDpos.le
  have hlam1 : lam < 1 := by rw [hlam, div_lt_one hDpos]; exact hMm
  set u : ℝ² := (1 / D) • (b - a) with hu
  have hu1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    rw [← hnormsq, hu, norm_smul, ← hD, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  refine ⟨c, s, hcs, u, hu1, (1 - lam) • x0 + lam • a - m • u, fun q hq => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = c * q 0 + s * q 1 := ⟨_, rfl⟩
  rw [← ht]
  have htb := hbound q hq
  rw [← ht] at htb
  set α := (t - m) / D with hα
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hDpos.le
  have hαl : α ≤ lam := by rw [hα, hlam]; gcongr; linarith
  set μ := α / lam with hμ
  have hμ0 : 0 ≤ μ := div_nonneg hα0 hlam0
  have hμ1 : μ ≤ 1 := div_le_one_of_le₀ hαl hlam0
  have hlamμ : lam * μ = α := by
    rcases hlam0.lt_or_eq with hpos | hzero
    · rw [hμ]; field_simp
    · rw [← hzero, zero_mul]; linarith
  have hy : a + μ • (b - a) ∈ convexHull ℝ (W : Set ℝ²) :=
    (convex_convexHull ℝ _).add_smul_sub_mem (subset_convexHull ℝ _ ha)
      (subset_convexHull ℝ _ hb) ⟨hμ0, hμ1⟩
  have hmem := (convex_convexHull ℝ (W : Set ℝ²)).combo_interior_self_mem_interior hx0 hy
    (by linarith : (0 : ℝ) < 1 - lam) hlam0 (by ring)
  convert hmem using 1
  rw [smul_add, show lam • μ • (b - a) = α • (b - a) by rw [smul_smul, hlamμ], hα, hu]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Points in the plane `z = 0`, whose shadow is not collinear, are Rupert. -/
theorem isRupert_of_flat (V : Finset ℝ³) (hz : ∀ v ∈ V, v 2 = 0)
    (hW : ¬ Collinear ℝ ((V.image projXy : Finset ℝ²) : Set ℝ²)) : IsRupert V := by
  classical
  obtain ⟨c, s, hcs, u, hu, o, hshadow⟩ := exists_short_shadow _ hW
  set E3 : Matrix (Fin 3) (Fin 3) ℝ := !![c, s, 0; 0, 0, 1; s, -c, 0] with hE3def
  have hE3 : E3 ∈ SO3 := by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [E3, Matrix.mul_apply, Fin.sum_univ_three] <;>
        ring_nf <;> linear_combination hcs
    · simp [E3, Matrix.det_fin_three]; linear_combination hcs
  have hhullz : ∀ p ∈ convexHull ℝ (V : Set ℝ³), p 2 = 0 := by
    intro p hp
    refine convexHull_min (fun v hv => hz v hv) (t := {p : ℝ³ | p 2 = 0}) ?_ hp
    intro x hx y hy α β _ _ _
    simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    rw [hx, hy]; ring
  have hP : projXy '' convexHull ℝ (V : Set ℝ³) =
      convexHull ℝ ((V.image projXy : Finset ℝ²) : Set ℝ²) := by
    rw [Finset.coe_image]; exact projL.image_convexHull _
  rw [isRupert_iff_shadows]
  refine ⟨rotZ (u 0) (u 1) * E3, Submonoid.mul_mem _ (rotZ_mem_SO3 hu) hE3, o, 1,
    Submonoid.one_mem _, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [outerShadow_one, hP]
  have hp2 := hhullz p hp
  have key : projXy ((rotZ (u 0) (u 1) * E3).toEuclideanLin p) =
      (c * (projXy p) 0 + s * (projXy p) 1) • u := by
    ext i
    fin_cases i <;>
      simp [rotZ, E3, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail, projXy,
        hp2] <;> ring
  rw [key]
  exact hshadow _ (hP ▸ ⟨p, hp, rfl⟩)

/-- **Planar sets.**  Points in a plane, not all on one line, are Rupert —
whatever their number. -/
theorem isRupert_of_coplanar_of_not_collinear (V : Finset ℝ³) (hpl : Coplanar ℝ (V : Set ℝ³))
    (hcol : ¬ Collinear ℝ (V : Set ℝ³)) : IsRupert V := by
  classical
  obtain ⟨N, hN, h, hNV⟩ := exists_plane_of_coplanar hpl
  obtain ⟨Q, hQ, r, hr, hQN⟩ := exists_rotation_to_ez N hN
  have hz : ∀ v ∈ V, (Q.toEuclideanLin v) 2 = h / r := by
    intro v hv
    have := inner_toEuclideanLin_SO3 hQ N v
    rw [hQN, hNV v hv, real_inner_smul_left, real_inner_comm, inner_ez] at this
    field_simp
    linarith
  set c : ℝ³ := (-(h / r)) • ez with hc
  apply isRupert_of_isRupert_image_rotation Q hQ
  apply isRupert_of_isRupert_image_add c
  have hz' : ∀ v ∈ (V.image Q.toEuclideanLin).image (fun x => c + x), v 2 = 0 := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
    simp [hc, ez, hz w hw]
  refine isRupert_of_flat _ hz' fun hW => hcol ?_
  -- transport collinearity back along `q ↦ Qᵀ (lift q - c)`
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ.1
  let G : ℝ² →ᵃ[ℝ] ℝ³ := (Qᵀ.toEuclideanLin ∘ₗ liftL).toAffineMap +
    AffineMap.const ℝ ℝ² (-(Qᵀ.toEuclideanLin c))
  refine (collinear_image_affine G hW).subset fun v hv => ?_
  have hmem : c + Q.toEuclideanLin v ∈ (V.image Q.toEuclideanLin).image (fun x => c + x) :=
    Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨projXy (c + Q.toEuclideanLin v), ?_, ?_⟩
  · rw [Finset.coe_image]; exact ⟨_, hmem, rfl⟩
  · simp only [G, FunLike.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
      LinearMap.coe_comp, Function.comp_apply, AffineMap.const_apply]
    rw [liftL_proj_xy (hz' _ hmem), map_add, add_comm (_ + _), neg_add_cancel_left]
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hQtQ]

/-- **Collinear sets.**  A nonempty set of points on one line is not Rupert:
every shadow of it lies on a line, so has no interior. -/
theorem not_isRupert_of_collinear (V : Finset ℝ³) (h : Collinear ℝ (V : Set ℝ³))
    (hne : V.Nonempty) : ¬ IsRupert V := by
  intro hR
  obtain ⟨R₁, -, o, R₂, -, hsub⟩ := (isRupert_iff_shadows V).mp hR
  obtain ⟨v, hv⟩ := hne
  have hin := hsub ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv), rfl⟩
  let f : ℝ³ →ₗ[ℝ] ℝ² := projL ∘ₗ R₂.toEuclideanLin
  have hout : outerShadow R₂ (convexHull ℝ (V : Set ℝ³)) = convexHull ℝ (f '' V) := by
    rw [← f.image_convexHull]; rfl
  have hcol : Collinear ℝ (f '' V) := by
    simpa using collinear_image_affine f.toAffineMap h
  rw [hout, interior_convexHull_eq_empty_of_collinear hcol] at hin
  exact hin

/-- The empty set is (vacuously) Rupert: its shadows are empty. -/
theorem isRupert_empty : IsRupert ∅ := by
  rw [isRupert_iff_shadows]
  refine ⟨1, Submonoid.one_mem _, 0, 1, Submonoid.one_mem _, ?_⟩
  rintro _ ⟨p, hp, -⟩
  simp at hp

end Minimality

end RupertMinimality
