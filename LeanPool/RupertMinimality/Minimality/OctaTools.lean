/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.L8Shapes

/-! # Octa Tools -/

@[expose] public section

namespace RupertMinimality

/-!
# Tools for Theorem 9.9

* `det3_mul_inner_eq`: an affine function vanishing on an edge and constant
  along the view `u` is proportional to the edge's orientation determinant.
* `det3_pos_of_combo`: hence the sign of every determinant test of Lemma 8.0
  at a silhouette edge follows from facet signs and one reference value.
* `four_point_parallel`: the affine dependency of four points modulo `u`
  (the diagonals of a convex quadrilateral cross).
* symmetries of `IsOctahedron`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem cross_apply_zero (a b : ℝ³) : (cross a b) 0 = a 1 * b 2 - a 2 * b 1 := by simp [cross]
theorem cross_apply_one (a b : ℝ³) : (cross a b) 1 = a 2 * b 0 - a 0 * b 2 := by simp [cross]
theorem cross_apply_two (a b : ℝ³) : (cross a b) 2 = a 0 * b 1 - a 1 * b 0 := by simp [cross]

theorem det3_expand (a b c : ℝ³) : det3 a b c =
    (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
      (a 0 * b 1 - a 1 * b 0) * c 2 := by
  simp only [det3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

theorem det3_mul_inner_sub (e u w w' N : ℝ³) :
    det3 e w u * ⟪N, w'⟫ - det3 e w' u * ⟪N, w⟫ =
      ⟪cross w w', e⟫ * ⟪u, N⟫ - ⟪cross w w', u⟫ * ⟪e, N⟫ := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]
  simp; ring

theorem det3_mul_inner_eq {e u w w' N : ℝ³} (h1 : ⟪N, e⟫ = 0) (h2 : ⟪N, u⟫ = 0) :
    det3 e w u * ⟪N, w'⟫ = det3 e w' u * ⟪N, w⟫ := by
  have := det3_mul_inner_sub e u w w' N
  rw [real_inner_comm N u, real_inner_comm N e, h1, h2] at this
  linarith

theorem det3_cyc (A B C u : ℝ³) : det3 (C - B) (A - B) u = det3 (B - A) (C - A) u := by
  simp only [det3_expand, PiLp.sub_apply]
  ring

theorem det3_shift (A B C u : ℝ³) (s : ℝ) :
    det3 (B - A) (C - (A + s • u)) u = det3 (B - A) (C - A) u := by
  simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Determinant tests from facet combinations.**  `f₁`, `f₂` are affine
(with linear parts `N₁`, `N₂`) and vanish at `P`, `Q`; the combination
`g = α f₁ + β f₂` is constant along `u`.  Then the tests
`det3 (Q - P) (w - P) u` have the sign of `-g w`, normalized by a reference. -/
theorem det3_pos_of_combo_σ {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³} {σ : ℝ}
    (hr : 0 < σ * det3 (Q - P) (r - P) u) (hgr : α * f₁ r + β * f₂ r < 0)
    (hgw : α * f₁ w + β * f₂ w < 0) : 0 < σ * det3 (Q - P) (w - P) u := by
  set N := α • N₁ + β • N₂
  have hg : ∀ z, ⟪N, z - P⟫ = α * f₁ z + β * f₂ z := by
    intro z
    simp only [N, inner_add_left, real_inner_smul_left, ← h₁, ← h₂, h1P, h2P, sub_zero]
  have hNe : ⟪N, Q - P⟫ = 0 := by rw [hg, h1Q, h2Q]; ring
  have hNu : ⟪N, u⟫ = 0 := by
    simpa only [N, inner_add_left, real_inner_smul_left] using hαβ
  have key := det3_mul_inner_eq (w := w - P) (w' := r - P) hNe hNu
  rw [hg, hg] at key
  have key' : (σ * det3 (Q - P) (w - P) u) * (α * f₁ r + β * f₂ r) =
      (σ * det3 (Q - P) (r - P) u) * (α * f₁ w + β * f₂ w) := by
    rw [mul_assoc, key]; ring
  have hproduct := mul_neg_of_pos_of_neg hr hgw
  rw [← key'] at hproduct
  exact pos_of_mul_neg_left hproduct hgr.le

/-- The determinant sign test for the positive orientation. -/
theorem det3_pos_of_combo {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³}
    (hr : 0 < det3 (Q - P) (r - P) u) (hgr : α * f₁ r + β * f₂ r < 0)
    (hgw : α * f₁ w + β * f₂ w < 0) : 0 < det3 (Q - P) (w - P) u := by
  simpa only [one_mul] using
    (det3_pos_of_combo_σ h₁ h₂ h1P h1Q h2P h2Q hαβ (σ := 1)
      (by simpa only [one_mul] using hr) hgr hgw)

theorem det3_zero_of_combo {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³}
    (hgr : α * f₁ r + β * f₂ r ≠ 0) (hgw : α * f₁ w + β * f₂ w = 0) :
    det3 (Q - P) (w - P) u = 0 := by
  set N := α • N₁ + β • N₂
  have hg : ∀ z, ⟪N, z - P⟫ = α * f₁ z + β * f₂ z := by
    intro z
    simp only [N, inner_add_left, real_inner_smul_left, ← h₁, ← h₂, h1P, h2P, sub_zero]
  have hNe : ⟪N, Q - P⟫ = 0 := by rw [hg, h1Q, h2Q]; ring
  have hNu : ⟪N, u⟫ = 0 := by
    simp only [N, inner_add_left, real_inner_smul_left]; linarith
  have key := det3_mul_inner_eq (w := w - P) (w' := r - P) hNe hNu
  rw [hg, hg, hgw, mul_zero] at key
  exact (mul_eq_zero.mp key).resolve_right hgr

/-- **Four points modulo a direction.**  `S_BCD A - S_ACD B + S_ABD C - S_ABC D`
is parallel to `u` (`S_XYZ := det3 (Y - X) (Z - X) u`); its coefficients sum to
zero. -/
theorem four_point_parallel (A B C D u : ℝ³) (hu : u ≠ 0) :
    det3 (C - B) (D - B) u • A - det3 (C - A) (D - A) u • B + det3 (B - A) (D - A) u • C -
        det3 (B - A) (C - A) u • D =
      (⟪det3 (C - B) (D - B) u • A - det3 (C - A) (D - A) u • B +
        det3 (B - A) (D - A) u • C - det3 (B - A) (C - A) u • D, u⟫ / ⟪u, u⟫) • u := by
  apply eq_smul_of_cross_eq_zero hu
  ext i; fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
      cross_apply_two, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, PiLp.zero_apply] <;> ring

theorem four_point_sum (A B C D u : ℝ³) :
    det3 (C - B) (D - B) u - det3 (C - A) (D - A) u + det3 (B - A) (D - A) u -
      det3 (B - A) (C - A) u = 0 := by
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-! ### Silhouette edges between two facets -/

/-- The signs of the determinant tests at an edge `PQ` of two facets, one
through `t` and one through `t'`, for views along `t' - t`. -/
theorem axis_edge_pos {V : Finset ℝ³} {t t' P Q : ℝ³} (h₁ : IsFacetTriangle V t P Q)
    (h₂ : IsFacetTriangle V t' P Q) (ht : t ∈ V) (ht' : t' ∈ V) (htt : t ≠ t') (htP : t ≠ P)
    (htQ : t ≠ Q) (ht'P : t' ≠ P) (ht'Q : t' ≠ Q) {r w : ℝ³} (hr : r ∈ V) (hrP : r ≠ P)
    (hrQ : r ≠ Q) (hw : w ∈ V) (hwP : w ≠ P) (hwQ : w ≠ Q)
    (href : 0 < det3 (Q - P) (r - P) (t' - t)) : 0 < det3 (Q - P) (w - P) (t' - t) := by
  obtain ⟨f₁, f₁t, f₁P, f₁Q, hf₁⟩ := h₁
  obtain ⟨f₂, f₂t', f₂P, f₂Q, hf₂⟩ := h₂
  obtain ⟨N₁, hN₁⟩ := exists_normal_of_affine f₁
  obtain ⟨N₂, hN₂⟩ := exists_normal_of_affine f₂
  have f₁t' := hf₁ t' ht' (Ne.symm htt) ht'P ht'Q
  have f₂t := hf₂ t ht htt htP htQ
  have key : ∀ z ∈ V, z ≠ P → z ≠ Q → (-f₂ t) * f₁ z + (-f₁ t') * f₂ z < 0 := by
    intro z hz hzP hzQ
    by_cases hzt : z = t
    · subst hzt; rw [f₁t]; nlinarith [hf₂ z hz htt hzP hzQ]
    by_cases hzt' : z = t'
    · subst hzt'; rw [f₂t']; nlinarith
    have := hf₁ z hz hzt hzP hzQ
    have := hf₂ z hz hzt' hzP hzQ
    nlinarith
  refine det3_pos_of_combo (fun y z => hN₁ y z) (fun y z => hN₂ y z) f₁P f₁Q f₂P f₂Q
    (α := -f₂ t) (β := -f₁ t') ?_ href (key r hr hrP hrQ) (key w hw hwP hwQ)
  rw [← hN₁, ← hN₂, f₁t, f₂t']; ring

theorem det3_zero_of_combo_ref {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³}
    (hr : det3 (Q - P) (r - P) u = 0) (hgr : α * f₁ r + β * f₂ r ≠ 0) :
    det3 (Q - P) (w - P) u = 0 := by
  set N := α • N₁ + β • N₂
  have hg : ∀ z, ⟪N, z - P⟫ = α * f₁ z + β * f₂ z := by
    intro z
    simp only [N, inner_add_left, real_inner_smul_left, ← h₁, ← h₂, h1P, h2P, sub_zero]
  have hNe : ⟪N, Q - P⟫ = 0 := by rw [hg, h1Q, h2Q]; ring
  have hNu : ⟪N, u⟫ = 0 := by
    simp only [N, inner_add_left, real_inner_smul_left]; linarith
  have key := det3_mul_inner_eq (w := w - P) (w' := r - P) hNe hNu
  rw [hg, hg, hr, zero_mul] at key
  exact (mul_eq_zero.mp key).resolve_right hgr

/-- An affine function vanishing at three non-collinear points vanishes on
their plane. -/
theorem affine_zero_of_coplanar {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {P Q R w : ℝ³} (hP : f P = 0) (hQ : f Q = 0) (hR : f R = 0)
    (hc : cross (Q - P) (R - P) ≠ 0) (hw : det3 (Q - P) (R - P) (w - P) = 0) : f w = 0 := by
  have h1 : ⟪N, Q - P⟫ = 0 := by rw [← hf, hP, hQ, sub_zero]
  have h2 : ⟪N, R - P⟫ = 0 := by rw [← hf, hP, hR, sub_zero]
  have hcN : cross (cross (Q - P) (R - P)) N = 0 := by
    have e : ∀ a b n : ℝ³, cross (cross a b) n = ⟪a, n⟫ • b - ⟪b, n⟫ • a := by
      intro a b n; ext i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
          cross_apply_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
          Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;> ring
    rw [e, real_inner_comm, h1, real_inner_comm, h2, zero_smul, zero_smul, sub_zero]
  have hN := eq_smul_of_cross_eq_zero hc hcN
  have : f w = ⟪N, w - P⟫ := by rw [← hf, hP, sub_zero]
  rw [this, hN, real_inner_smul_left]
  have : ⟪cross (Q - P) (R - P), w - P⟫ = 0 := hw
  rw [this, mul_zero]

/-- A facet's three vertices are not collinear when an adjacent facet (through
two of them) is strictly negative at the third. -/
theorem cross_ne_zero_of_affine {g : ℝ³ → ℝ} {N : ℝ³} (hg : ∀ y z, g y - g z = ⟪N, y - z⟫)
    {P Q R : ℝ³} (hPQ : P ≠ Q) (hP : g P = 0) (hQ : g Q = 0) (hR : g R < 0) :
    cross (Q - P) (R - P) ≠ 0 := by
  intro h0
  have hQP : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
  have := eq_smul_of_cross_eq_zero hQP h0
  have e : g R = ⟪N, R - P⟫ := by rw [← hg, hP, sub_zero]
  have e2 : ⟪N, Q - P⟫ = 0 := by rw [← hg, hP, hQ, sub_zero]
  rw [this, real_inner_smul_right, e2, mul_zero] at e
  linarith

theorem det3_sub_left_eq (e x t t' : ℝ³) :
    det3 e (t - x) (t' - t) = det3 e (t - x) (t' - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-! ### Symmetries of `IsOctahedron` -/

theorem IsFacetTriangle.perm₁₂ {V : Finset ℝ³} {P Q R : ℝ³} (h : IsFacetTriangle V P Q R) :
    IsFacetTriangle V Q P R := by
  obtain ⟨f, fP, fQ, fR, hf⟩ := h
  exact ⟨f, fQ, fP, fR, fun x hx h1 h2 h3 => hf x hx h2 h1 h3⟩

theorem IsFacetTriangle.perm₂₃ {V : Finset ℝ³} {P Q R : ℝ³} (h : IsFacetTriangle V P Q R) :
    IsFacetTriangle V P R Q := by
  obtain ⟨f, fP, fQ, fR, hf⟩ := h
  exact ⟨f, fP, fR, fQ, fun x hx h1 h2 h3 => hf x hx h1 h3 h2⟩

theorem IsFacetTriangle.congr_set {V W : Finset ℝ³} {P Q R : ℝ³} (h : IsFacetTriangle V P Q R)
    (hVW : V = W) : IsFacetTriangle W P Q R := hVW ▸ h

theorem IsOctahedron.swap₁ {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsOctahedron a' a b b' c c' := by
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a', a, b, b', c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Perm.nodup_iff ?_ |>.mpr h.nodup
    simp only [List.perm_iff_count]; intro z; simp [List.count_cons]; omega
  · exact h.facet_a'bc.congr_set e
  · exact h.facet_a'bc'.congr_set e
  · exact h.facet_a'b'c.congr_set e
  · exact h.facet_a'b'c'.congr_set e
  · exact h.facet_abc.congr_set e
  · exact h.facet_abc'.congr_set e
  · exact h.facet_ab'c.congr_set e
  · exact h.facet_ab'c'.congr_set e

theorem IsOctahedron.swap₂ {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsOctahedron a a' b' b c c' := by
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a, a', b', b, c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Perm.nodup_iff ?_ |>.mpr h.nodup
    simp only [List.perm_iff_count]; intro z; simp [List.count_cons]; omega
  · exact h.facet_ab'c.congr_set e
  · exact h.facet_ab'c'.congr_set e
  · exact h.facet_abc.congr_set e
  · exact h.facet_abc'.congr_set e
  · exact h.facet_a'b'c.congr_set e
  · exact h.facet_a'b'c'.congr_set e
  · exact h.facet_a'bc.congr_set e
  · exact h.facet_a'bc'.congr_set e

theorem IsOctahedron.swap₃ {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsOctahedron a a' b b' c' c := by
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a, a', b, b', c', c} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Perm.nodup_iff ?_ |>.mpr h.nodup
    simp only [List.perm_iff_count]; intro z; simp [List.count_cons]; omega
  · exact h.facet_abc'.congr_set e
  · exact h.facet_abc.congr_set e
  · exact h.facet_ab'c'.congr_set e
  · exact h.facet_ab'c.congr_set e
  · exact h.facet_a'bc'.congr_set e
  · exact h.facet_a'bc.congr_set e
  · exact h.facet_a'b'c'.congr_set e
  · exact h.facet_a'b'c.congr_set e

theorem IsOctahedron.perm₁₂ {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsOctahedron b b' a a' c c' := by
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {b, b', a, a', c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Perm.nodup_iff ?_ |>.mpr h.nodup
    simp only [List.perm_iff_count]; intro z; simp [List.count_cons]; omega
  · exact (h.facet_abc.perm₁₂).congr_set e
  · exact (h.facet_abc'.perm₁₂).congr_set e
  · exact (h.facet_a'bc.perm₁₂).congr_set e
  · exact (h.facet_a'bc'.perm₁₂).congr_set e
  · exact (h.facet_ab'c.perm₁₂).congr_set e
  · exact (h.facet_ab'c'.perm₁₂).congr_set e
  · exact (h.facet_a'b'c.perm₁₂).congr_set e
  · exact (h.facet_a'b'c'.perm₁₂).congr_set e

theorem IsOctahedron.perm₂₃ {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsOctahedron a a' c c' b b' := by
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a, a', c, c', b, b'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Perm.nodup_iff ?_ |>.mpr h.nodup
    simp only [List.perm_iff_count]; intro z; simp [List.count_cons]; omega
  · exact (h.facet_abc.perm₂₃).congr_set e
  · exact (h.facet_ab'c.perm₂₃).congr_set e
  · exact (h.facet_abc'.perm₂₃).congr_set e
  · exact (h.facet_ab'c'.perm₂₃).congr_set e
  · exact (h.facet_a'bc.perm₂₃).congr_set e
  · exact (h.facet_a'b'c.perm₂₃).congr_set e
  · exact (h.facet_a'bc'.perm₂₃).congr_set e
  · exact (h.facet_a'b'c'.perm₂₃).congr_set e

end Minimality

end RupertMinimality
