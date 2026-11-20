/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Oct9Weak

/-! # Oct9 Par -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 9.9, the parallel case `f = 0` (§9.6 of L9)

With normalized labels (`κ_A, κ_B, κ_C > 0`), `f = g_a + g_b + g_c = 0`
means that the opposite faces `abc` and `a'b'c'` are parallel.  Each pair `W`
gives two weak quad edges (Lemma 9.6 with `f = 0`) that are not bad (same
argument as §9.5).  By Lemma 9.11 (`isRupert_weak_edge`) each gives a passage
unless it is touching or its lateral edge is parallel to the common normal;
two touching edges give a passage by Lemma 9.4; and at most one edge of the
octahedron is parallel to the normal.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem cross_cross_eq (a b n : ℝ³) : cross (cross a b) n = ⟪a, n⟫ • b - ⟪b, n⟫ • a := by
  ext i; fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
      cross_apply_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
      Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;> ring

/-- A vector orthogonal to two independent vectors is a multiple of their cross
product. -/
theorem eq_smul_cross_of_perp {e₁ e₂ d : ℝ³} (hc : cross e₁ e₂ ≠ 0) (h1 : ⟪d, e₁⟫ = 0)
    (h2 : ⟪d, e₂⟫ = 0) : ∃ s : ℝ, d = s • cross e₁ e₂ := by
  refine ⟨_, eq_smul_of_cross_eq_zero hc ?_⟩
  rw [cross_cross_eq, real_inner_comm, h1, real_inner_comm, h2, zero_smul, zero_smul, sub_zero]

/-- Orthogonality to a plane, transferred through a parallel plane. -/
theorem perp_transfer {e₁ e₂ N d w : ℝ³} (hc : cross e₁ e₂ ≠ 0) (hN : N ≠ 0)
    (hN1 : ⟪N, e₁⟫ = 0) (hN2 : ⟪N, e₂⟫ = 0) (hd1 : ⟪d, e₁⟫ = 0) (hd2 : ⟪d, e₂⟫ = 0)
    (hw : ⟪N, w⟫ = 0) : ⟪d, w⟫ = 0 := by
  obtain ⟨s, hs⟩ := eq_smul_cross_of_perp hc hd1 hd2
  obtain ⟨t, ht⟩ := eq_smul_cross_of_perp hc hN1 hN2
  have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hN ht
  have : ⟪cross e₁ e₂, w⟫ = 0 := by
    rw [ht, real_inner_smul_left] at hw
    exact (mul_eq_zero.mp hw).resolve_left ht0
  rw [hs, real_inner_smul_left, this, mul_zero]

/-- Two disjoint edges parallel to one direction `n`, the first inside a facet
and the second from a vertex of that facet to a vertex beneath it: impossible. -/
theorem two_parallel_contra {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {A B Q S n : ℝ³} {s t : ℝ} (hA : f A = 0) (hB : f B = 0) (hQ : f Q = 0) (hS : f S < 0)
    (h1 : B - A = s • n) (hs : s ≠ 0) (h2 : S - Q = t • n) : False := by
  have e1 : ⟪N, n⟫ = 0 := by
    have := hf B A
    rw [hA, hB, h1, real_inner_smul_right, sub_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hs
  have := hf S Q
  rw [hQ, h2, real_inner_smul_right, e1, mul_zero, sub_zero] at this
  linarith

/-- **`f = 0` makes the faces `abc` and `a'b'c'` parallel**: every affine
function vanishing on `a', b', c'` is constant on `a, b, c`. -/
theorem facet_eq_of_f0 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (hfl : l a + l b + l c = 0) (hfm : m a + m b + m c = 0)
    (hbc : galeD l m b c ≠ 0) {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (ha' : f a' = 0) (hb' : f b' = 0) (hc' : f c' = 0) : f a = f c ∧ f b = f c := by
  have r1 := hl.apply hf
  have r2 := hm.apply hf
  rw [ha', hb', hc'] at r1 r2
  simp only [galeD] at hbc
  have k1 : (l b * m c - m b * l c) * (f b - f a) = 0 := by
    have ea : l a = -(l b + l c) := by linarith
    have eb : m a = -(m b + m c) := by linarith
    rw [ea] at r1; rw [eb] at r2
    linear_combination m c * r1 - l c * r2
  have k2 : (l b * m c - m b * l c) * (f c - f a) = 0 := by
    have ea : l a = -(l b + l c) := by linarith
    have eb : m a = -(m b + m c) := by linarith
    rw [ea] at r1; rw [eb] at r2
    linear_combination -m b * r1 + l b * r2
  have z1 := (mul_eq_zero.mp k1).resolve_left hbc
  have z2 := (mul_eq_zero.mp k2).resolve_left hbc
  constructor <;> linarith

theorem finset_perm_bac {a a' b b' c c' : ℝ³} :
    ({b, b', a, a', c, c'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem finset_perm_cba {a a' b b' c c' : ℝ³} :
    ({c, c', b, b', a, a'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **The pair `W = C` in the parallel case** (`U = A`): the weak edges
`b → a` and `a' → b'` give a passage, or one of the lateral edges `c a'`,
`b c'` is orthogonal to the bottom, resp. top, face. -/
theorem isRupert_pair_f0 {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0)
    (hU : 0 < galeD G.l G.m c a) :
    IsRupert {a, a', b, b', c, c'} ∨ (⟪c - a', a - b⟫ = 0 ∧ ⟪c - a', c - a⟫ = 0) ∨
      (⟪c' - b, b' - a'⟫ = 0 ∧ ⟪c' - b, c' - b'⟫ = 0) := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  -- pole signs at `c`, `c'`, `a`, `b'`, `b`
  obtain ⟨c1, c2, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂
    (self c) hκc.ne'
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁ (hl.galeD hm c').perm₂₃.perm₁₂.swap₁
    (self c') (by rw [anti]; linarith)
  obtain ⟨a1, a2, a3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  obtain ⟨b1, b2, b3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁
    (self b') (by rw [anti]; linarith)
  obtain ⟨-, -, e3⟩ := pole_signs F.perm₁₂ (hl.galeD hm b).perm₁₂ (self b) hκb.ne'
  have hca' : 0 < galeD G.l G.m c a' := pos_of_mul_pos_pos c1 hU
  have hcb : galeD G.l G.m c b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at c3) hU
  have hc'a : 0 < galeD G.l G.m c' a := by
    have e : galeD G.l G.m a c * galeD G.l G.m a c' = galeD G.l G.m c a * galeD G.l G.m c' a := by
      rw [anti c a, anti c' a]; ring
    exact pos_of_mul_pos_pos (e ▸ a2) hU
  have hc'b : galeD G.l G.m c' b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at d3) hc'a
  have hac : galeD G.l G.m a c < 0 := by rw [anti]; linarith
  have hab : 0 < galeD G.l G.m a b := pos_of_mul_neg_neg (by linarith) hac
  have hab' : 0 < galeD G.l G.m a b' := pos_of_mul_pos_pos a1 hab
  have hb'c : 0 < galeD G.l G.m b' c := by
    rw [anti]; linarith [neg_of_mul_pos_neg (by linarith : 0 < galeD G.l G.m c b *
      galeD G.l G.m c b') hcb]
  have hb'a : galeD G.l G.m b' a < 0 := neg_of_mul_neg_pos b3 hb'c
  have hb'a' : galeD G.l G.m b' a' < 0 := neg_of_mul_pos_neg b1 hb'a
  have hb'c' : 0 < galeD G.l G.m b' c' := pos_of_mul_pos_pos b2 hb'c
  have hbc : galeD G.l G.m b c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e3; exact lt_irrefl _ e3
  -- `f = 0`
  have hF0 : ∀ t, galeD G.l G.m t a + galeD G.l G.m t b + galeD G.l G.m t c = 0 := by
    intro t; rw [← galeF_eq]; simp only [galeF]; rw [hf.1, hf.2]; ring
  have sc := galeD_sum hl hm c
  have hF0c := hF0 c
  have hF0c' := hF0 c'
  rw [self] at sc hF0c
  have hcc' := anti c c'
  have hfl' : G.l a' + G.l b' + G.l c' = 0 := by linarith [hl.sum, hf.1]
  have hfm' : G.m a' + G.m b' + G.m c' = 0 := by linarith [hm.sum, hf.2]
  have hb'c'0 : galeD G.l G.m b' c' ≠ 0 := hb'c'.ne'
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hnab : a ≠ b := hnd.1.2.1
  have hnab' : a' ≠ b' := hnd.2.1.2.1
  -- the edge `b → a` (poles `c`, `c'`; top face `b' a' c'`)
  have hq₁ := facet_lt_of_dep (hl.galeD hm c').perm₁₂ (F.perm₁₂).a'b'c (by simp) (by simp)
    (F.perm₁₂).nodup (self c') (mul_neg_of_neg_of_pos hc'b (by linarith))
  obtain ⟨T1, T2⟩ := facet_eq_of_f0 hl hm hf.1 hf.2 hbc (F.perm₁₂).a'b'c'.hN
    (F.perm₁₂).a'b'c'.hQ (F.perm₁₂).a'b'c'.hP (F.perm₁₂).a'b'c'.hR
  have hgood₁ := not_bad_of_dep (hl.galeD hm b').perm₁₂ (Ne.symm hnab) (self b')
    (by rw [anti]; linarith) (by rw [anti b b']; linarith) hb'a'.le hb'c.le hb'c'.le
  have r₁ := isRupert_weak_edge F.perm₁₂ hq₁ (by rw [T1, T2]) (by rw [T1]) hgood₁
  -- the edge `a' → b'` (poles `c'`, `c`; top face `a b c`)
  have hq₂ := facet_lt_of_dep (hl.galeD hm c).swap₁.swap₂.swap₃ (F.swap₁.swap₂.swap₃).a'b'c
    (by simp) (by simp) (F.swap₁.swap₂.swap₃).nodup (self c)
    (mul_neg_of_pos_of_neg hca' (by linarith))
  obtain ⟨B1, B2⟩ := facet_eq_of_f0 hl.swap₁.swap₂.swap₃ hm.swap₁.swap₂.swap₃ hfl' hfm'
    hb'c'0 (F.swap₁.swap₂.swap₃).a'b'c'.hN (F.swap₁.swap₂.swap₃).a'b'c'.hP
    (F.swap₁.swap₂.swap₃).a'b'c'.hQ (F.swap₁.swap₂.swap₃).a'b'c'.hR
  have hgood₂ := not_bad_of_dep (L := fun t => galeD G.l G.m t a)
    (hl.galeD' hm a).swap₁.swap₂.swap₃ hnab' (self a) (by rw [anti]; linarith)
    (by rw [anti a a', anti a b']; linarith) (by rw [anti]; linarith) hc'a.le hU.le
  have r₂ := isRupert_weak_edge F.swap₁.swap₂.swap₃ hq₂ (by rw [B1, B2]) (by rw [B2]) hgood₂
  rcases r₁ with r₁ | t₁ | l₁
  · left
    exact isRupert_congr_set r₁ finset_perm_bac
  · rcases r₂ with r₂ | t₂ | l₂
    · left; rwa [finset_perm_a'b'] at r₂
    · left
      have := isRupert_of_touching_pair h.perm₂₃.perm₁₂.perm₂₃
        (by rw [inner_sub_left]; linarith [t₁.1]) (by rw [inner_sub_left]; linarith [t₂.1])
      exact isRupert_congr_set this finset_perm_cba
    · right; right; exact l₂
  · right; left; exact l₁


theorem finset_perm_bca {a a' b b' c c' : ℝ³} :
    ({b, b', c, c', a, a'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem finset_perm_cab {a a' b b' c c' : ℝ³} :
    ({c, c', a, a', b, b'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **§9.6 with `U = A` for the pair `C`**: all three pairs, and the count of
lateral edges parallel to the normal. -/
theorem isRupert_octahedron_parallel_core {a a' b b' c c' : ℝ³}
    (h : IsOctahedron a a' b b' c c') (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : 0 < galeD G.l G.m b b')
    (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0)
    (hU : 0 < galeD G.l G.m c a) : IsRupert {a, a', b, b', c, c'} := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨-, -, a3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  obtain ⟨-, -, e3⟩ := pole_signs F.perm₁₂ (hl.galeD hm b).perm₁₂ (self b) hκb.ne'
  have hac : galeD G.l G.m a c < 0 := by rw [anti]; linarith
  have hab : 0 < galeD G.l G.m a b := pos_of_mul_neg_neg (by linarith) hac
  have hbc : 0 < galeD G.l G.m b c := by
    have : galeD G.l G.m b a < 0 := by rw [anti]; linarith
    exact pos_of_mul_neg_neg (by linarith) this
  have hbc0 : galeD G.l G.m b c ≠ 0 := hbc.ne'
  -- the three pairs
  have PC := isRupert_pair_f0 h G hκa hκb hκc hf hU
  have PA := isRupert_pair_f0 h.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃ hκb hκc hκa
    ⟨by simp only [GaleData.perm₁₂, GaleData.perm₂₃]; linarith [hf.1],
     by simp only [GaleData.perm₁₂, GaleData.perm₂₃]; linarith [hf.2]⟩ hab
  have PB := isRupert_pair_f0 h.perm₂₃.perm₁₂ G.perm₂₃.perm₁₂ hκc hκa hκb
    ⟨by simp only [GaleData.perm₁₂, GaleData.perm₂₃]; linarith [hf.1],
     by simp only [GaleData.perm₁₂, GaleData.perm₂₃]; linarith [hf.2]⟩ hbc
  rw [finset_perm_bca] at PA
  rw [finset_perm_cab] at PB
  -- the geometry of the parallel faces
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab', hab'', hac', hac''⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc', hbc''⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set n := cross (b - a) (c - a) with hn_def
  have hn : n ≠ 0 :=
    cross_ne_zero_of_affine F.abc'.hN hab' F.abc'.hP F.abc'.hQ
      (F.abc'.neg c (by simp) (Ne.symm hac') (Ne.symm hbc') hcc')
  have hn' : cross (b' - a') (c' - a') ≠ 0 :=
    cross_ne_zero_of_affine F.a'b'c.hN ha'b' F.a'b'c.hP F.a'b'c.hQ
      (F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'))
  set T := F.a'b'c'
  obtain ⟨T1, T2⟩ := facet_eq_of_f0 hl hm hf.1 hf.2 hbc0 T.hN T.hP T.hQ T.hR
  have hTN : T.N ≠ 0 := by
    intro h0
    have := T.hN a a'
    rw [h0, inner_zero_left, T.hP] at this
    linarith [T.neg a (by simp) haa' hab'' hac'']
  have topPerp : ∀ d : ℝ³, ⟪d, b' - a'⟫ = 0 → ⟪d, c' - a'⟫ = 0 →
      ⟪d, b - a⟫ = 0 ∧ ⟪d, c - a⟫ = 0 := by
    intro d h1 h2
    have n1 : ⟪T.N, b' - a'⟫ = 0 := by rw [← T.hN, T.hP, T.hQ, sub_zero]
    have n2 : ⟪T.N, c' - a'⟫ = 0 := by rw [← T.hN, T.hP, T.hR, sub_zero]
    exact ⟨perp_transfer hn' hTN n1 n2 h1 h2 (by rw [← T.hN, T1, T2]; ring),
      perp_transfer hn' hTN n1 n2 h1 h2 (by rw [← T.hN, T1]; ring)⟩
  have toN : ∀ d : ℝ³, ⟪d, b - a⟫ = 0 ∧ ⟪d, c - a⟫ = 0 → ∃ s : ℝ, d = s • n :=
    fun d hd => eq_smul_cross_of_perp hn hd.1 hd.2
  -- the three lateral edges
  have X12 : ∀ s t : ℝ, c - a' = s • n → c' - b = t • n → False := by
    intro s t h1 h2
    have hs : s ≠ 0 := by
      rintro rfl; rw [zero_smul, sub_eq_zero] at h1; exact ha'c h1.symm
    exact two_parallel_contra F.a'bc.hN F.a'bc.hP F.a'bc.hR F.a'bc.hQ
      (F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc'') (Ne.symm hcc')) h1 hs h2
  have X23 : ∀ s t : ℝ, c' - b = s • n → a - b' = t • n → False := by
    intro s t h1 h2
    have ht : t ≠ 0 := by
      rintro rfl; rw [zero_smul, sub_eq_zero] at h2; exact hab'' h2
    have h1' : b - c' = (-s) • n := by rw [neg_smul, ← h1]; abel
    exact two_parallel_contra F.ab'c'.hN F.ab'c'.hQ F.ab'c'.hP F.ab'c'.hR
      (F.ab'c'.neg b (by simp) (Ne.symm hab') hbb' hbc'') h2 ht h1'
  have X13 : ∀ s t : ℝ, c - a' = s • n → a - b' = t • n → False := by
    intro s t h1 h2
    have hs : s ≠ 0 := by
      rintro rfl; rw [zero_smul, sub_eq_zero] at h1; exact ha'c h1.symm
    exact two_parallel_contra F.a'b'c.hN F.a'b'c.hP F.a'b'c.hR F.a'b'c.hQ
      (F.a'b'c.neg a (by simp) haa' hab'' hac') h1 hs h2
  -- each pair contributes one of them
  have hC : IsRupert {a, a', b, b', c, c'} ∨ (∃ s : ℝ, c - a' = s • n) ∨
      (∃ s : ℝ, c' - b = s • n) := by
    rcases PC with R | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl R
    · refine Or.inr (Or.inl (toN _ ⟨?_, h2⟩))
      simp only [inner_sub_left, inner_sub_right] at h1 ⊢; linarith
    · refine Or.inr (Or.inr (toN _ (topPerp _ h1 ?_)))
      simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith
  have hA : IsRupert {a, a', b, b', c, c'} ∨ (∃ s : ℝ, a - b' = s • n) ∨
      (∃ s : ℝ, c - a' = s • n) := by
    rcases PA with R | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl R
    · refine Or.inr (Or.inl (toN _ ⟨?_, ?_⟩))
      · simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith
      · simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith
    · obtain ⟨s, hs⟩ := toN (a' - c) (topPerp (a' - c) (by
        simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith) (by
        simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith))
      exact Or.inr (Or.inr ⟨-s, by rw [neg_smul, ← hs]; abel⟩)
  have hB : IsRupert {a, a', b, b', c, c'} ∨ (∃ s : ℝ, c' - b = s • n) ∨
      (∃ s : ℝ, a - b' = s • n) := by
    rcases PB with R | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl R
    · obtain ⟨s, hs⟩ := toN (b - c') ⟨by
        simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith, h1⟩
      exact Or.inr (Or.inl ⟨-s, by rw [neg_smul, ← hs]; abel⟩)
    · obtain ⟨s, hs⟩ := toN (b' - a) (topPerp (b' - a) h2 (by
        simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢; linarith))
      exact Or.inr (Or.inr ⟨-s, by rw [neg_smul, ← hs]; abel⟩)
  rcases hC with R | ⟨s1, x1⟩ | ⟨s2, x2⟩
  · exact R
  · rcases hA with R | ⟨s3, x3⟩ | -
    · exact R
    · exact (X13 s1 s3 x1 x3).elim
    · rcases hB with R | ⟨s2, x2⟩ | ⟨s3, x3⟩
      · exact R
      · exact (X12 s1 s2 x1 x2).elim
      · exact (X13 s1 s3 x1 x3).elim
  · rcases hA with R | ⟨s3, x3⟩ | ⟨s1, x1⟩
    · exact R
    · exact (X23 s2 s3 x2 x3).elim
    · exact (X12 s1 s2 x1 x2).elim

/-- **Theorem 9.9, case `f = 0`** (§9.6). -/
theorem isRupert_octahedron_parallel {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0) :
    IsRupert {a, a', b, b', c, c'} := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
    (galeD_self _ _ c) hκc.ne'
  rcases lt_or_gt_of_ne (show galeD G.l G.m c a ≠ 0 by intro h0; rw [h0, zero_mul] at c3; linarith)
    with hU | hU
  · have hb : 0 < galeD G.l G.m c b := pos_of_mul_neg_neg (by rwa [mul_comm] at c3) hU
    refine isRupert_congr_set (isRupert_octahedron_parallel_core h.perm₁₂ G.perm₁₂ hκb hκa hκc
      ⟨?_, ?_⟩ hb) finset_perm_bac
    · simp only [GaleData.perm₁₂]; linarith [hf.1]
    · simp only [GaleData.perm₁₂]; linarith [hf.2]
  · exact isRupert_octahedron_parallel_core h G hκa hκb hκc hf hU

end Minimality

end RupertMinimality
