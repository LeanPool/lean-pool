/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Oct9Quad

/-! # Oct9 Gale -/

@[expose] public section

namespace RupertMinimality

/-!
# The Gale diagram of an octahedron, as dependencies (L9 §9.4)

Two affine dependencies `l`, `m` of the six vertices play the role of the
Gale vectors `g_t = (-m t, l t)`; `galeD l m s t = det (g_s, g_t)` up to sign.
Everything the proof of Theorem 9.9 needs from the Gale diagram follows by
applying dependencies to facet functions (pole coordinates, Lemma 9.6) and from
the three-term Plücker relation (a `ring` identity).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `l` (a function on the vertices) is an affine dependency of the six points. -/
structure IsDep (a a' b b' c c' : ℝ³) (l : ℝ³ → ℝ) : Prop where
  sum : l a + l a' + l b + l b' + l c + l c' = 0
  vsum : l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c' = 0

theorem IsDep.apply {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l)
    {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫) :
    l a * f a + l a' * f a' + l b * f b + l b' * f b' + l c * f c + l c' * f c' = 0 := by
  have e : ∀ t, f t = f a + ⟪N, t - a⟫ := fun t => by rw [← hf]; ring
  have hv := congrArg (fun v => ⟪N, v⟫) h.vsum
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hv
  rw [e a', e b, e b', e c, e c']
  simp only [inner_sub_right]
  have hs := h.sum
  linear_combination hv + (f a - ⟪N, a⟫) * hs

theorem IsDep.comb {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (α β : ℝ) :
    IsDep a a' b b' c c' (fun t => α * l t + β * m t) := by
  constructor
  · linear_combination α * hl.sum + β * hm.sum
  · have h1 := hl.vsum; have h2 := hm.vsum
    calc _ = α • (l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c') +
          β • (m a • a + m a' • a' + m b • b + m b' • b' + m c • c + m c' • c') := by
            simp only [add_smul, smul_add, smul_smul]; abel
      _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]

theorem IsDep.swap₁ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a' a b b' c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.swap₂ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a a' b' b c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.swap₃ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a a' b b' c' c l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.perm₁₂ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep b b' a a' c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.perm₂₃ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a a' c c' b b' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

/-- `det (g_s, g_t)` for the Gale vectors of the dependencies `l`, `m`. -/
def galeD (l m : ℝ³ → ℝ) (s t : ℝ³) : ℝ := l s * m t - m s * l t

theorem galeD_self (l m : ℝ³ → ℝ) (s : ℝ³) : galeD l m s s = 0 := by simp [galeD]; ring

theorem galeD_anti (l m : ℝ³ → ℝ) (s t : ℝ³) : galeD l m t s = -galeD l m s t := by
  simp [galeD]; ring

theorem galeD_plucker (l m : ℝ³ → ℝ) (a b c d : ℝ³) :
    galeD l m a b * galeD l m c d - galeD l m a c * galeD l m b d +
      galeD l m a d * galeD l m b c = 0 := by
  simp only [galeD]; ring

/-- The dependency `t ↦ det (g_s, g_t)` vanishing at `s`. -/
theorem IsDep.galeD {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (s : ℝ³) : IsDep a a' b b' c c' (galeD l m s) := by
  have := hl.comb hm (-m s) (l s)
  convert this using 2 with t; simp only [Minimality.galeD]; ring

/-- Two terms of a dependency applied to a facet. -/
theorem pair_sign {L₁ L₂ f₁ f₂ : ℝ} (h : L₁ * f₁ + L₂ * f₂ = 0) (h₁ : f₁ < 0) (h₂ : f₂ < 0) :
    L₁ * L₂ ≤ 0 ∧ (L₁ = 0 ↔ L₂ = 0) := by
  constructor
  · by_contra hc; push Not at hc
    rcases lt_or_gt_of_ne (show L₁ ≠ 0 by rintro rfl; simp at hc) with hl | hl
    · have : L₂ < 0 := by nlinarith
      nlinarith [mul_pos_of_neg_of_neg hl h₁, mul_pos_of_neg_of_neg this h₂]
    · have : 0 < L₂ := by nlinarith
      nlinarith [mul_neg_of_pos_of_neg hl h₁, mul_neg_of_pos_of_neg this h₂]
  · constructor
    · rintro rfl
      simp only [zero_mul, zero_add, mul_eq_zero] at h
      exact h.resolve_right h₂.ne
    · rintro rfl
      simp only [zero_mul, add_zero, mul_eq_zero] at h
      exact h.resolve_right h₁.ne

/-- **Pole coordinates (i).**  A dependency vanishing at `t` and not at `t'`
has, on the equator of the axis `t t'`, one strict sign on each diagonal and
opposite signs on the two diagonals. -/
theorem pole_signs {t t' e e' g g' : ℝ³} (F : OctFacets t t' e e' g g') {L : ℝ³ → ℝ}
    (hL : IsDep t t' e e' g g' L) (h0 : L t = 0) (hκ : L t' ≠ 0) :
    0 < L e * L e' ∧ 0 < L g * L g' ∧ L e * L g < 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, hte, hte', htg, htg'⟩, ⟨ht'e, ht'e', ht'g, ht'g'⟩, ⟨hee', heg, heg'⟩,
    ⟨he'g, he'g'⟩, hgg', -⟩ := hnd
  have r1 := hL.apply F.a'bc.hN
  rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, h0] at r1
  have r2 := hL.apply F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, h0] at r2
  have r3 := hL.apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, h0] at r3
  have r4 := hL.apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR, h0] at r4
  have n1e' := F.a'bc.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g
  have n1g' := F.a'bc.neg g' (by simp) (Ne.symm ht'g') (Ne.symm heg') (Ne.symm hgg')
  have n2e' := F.a'bc'.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g'
  have n2g := F.a'bc'.neg g (by simp) (Ne.symm ht'g) (Ne.symm heg) hgg'
  have n3e := F.a'b'c.neg e (by simp) (Ne.symm ht'e) hee' heg
  have n3g' := F.a'b'c.neg g' (by simp) (Ne.symm ht'g') (Ne.symm he'g') (Ne.symm hgg')
  have n4e := F.a'b'c'.neg e (by simp) (Ne.symm ht'e) hee' heg'
  have n4g := F.a'b'c'.neg g (by simp) (Ne.symm ht'g) (Ne.symm he'g) hgg'
  obtain ⟨s1, z1⟩ := pair_sign (L₁ := L e') (L₂ := L g') (by linarith) n1e' n1g'
  obtain ⟨s2, z2⟩ := pair_sign (L₁ := L e') (L₂ := L g) (by linarith) n2e' n2g
  obtain ⟨s3, z3⟩ := pair_sign (L₁ := L e) (L₂ := L g') (by linarith) n3e n3g'
  obtain ⟨s4, z4⟩ := pair_sign (L₁ := L e) (L₂ := L g) (by linarith) n4e n4g
  have hs := hL.sum
  rw [h0] at hs
  have he' : L e' ≠ 0 := by
    intro h'
    have a1 := z1.mp h'; have a2 := z2.mp h'; have a4 := z4.mpr a2
    apply hκ; linarith
  have hg' : L g' ≠ 0 := fun h' => he' (z1.mpr h')
  have hg : L g ≠ 0 := fun h' => he' (z2.mpr h')
  have he : L e ≠ 0 := fun h' => hg (z4.mp h')
  have q1 : L e' * L g' < 0 := lt_of_le_of_ne s1 (mul_ne_zero he' hg')
  have q2 : L e' * L g < 0 := lt_of_le_of_ne s2 (mul_ne_zero he' hg)
  have q3 : L e * L g' < 0 := lt_of_le_of_ne s3 (mul_ne_zero he hg')
  have q4 : L e * L g < 0 := lt_of_le_of_ne s4 (mul_ne_zero he hg)
  refine ⟨?_, ?_, q4⟩
  · have := mul_pos_of_neg_of_neg q4 q2
    have hgg : 0 < L g * L g := mul_self_pos.mpr hg
    nlinarith
  · have := mul_pos_of_neg_of_neg q4 q3
    have hee : 0 < L e * L e := mul_self_pos.mpr he
    nlinarith

/-- **Not bad, from one affine dependency.**  If the
dependency vanishing at the hidden vertex `x'` is negative at the tail `x`,
nonnegative at both poles and nonpositive at `y'` and on `x + y`, then the
edge `x → y` is not bad. -/
theorem not_bad_of_dep {x x' y y' p p' : ℝ³} {L : ℝ³ → ℝ} (hL : IsDep x x' y y' p p' L)
    (hxy : x ≠ y) (h0 : L x' = 0) (hx : L x < 0) (hxy' : L x + L y ≤ 0) (hy' : L y' ≤ 0)
    (hp : 0 ≤ L p) (hp' : 0 ≤ L p') :
    ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ := by
  intro hbad
  have hφ := hL.apply (f := fun t => ⟪t, y - x⟫) (N := y - x)
    (fun a b => by simp only [← inner_sub_left, real_inner_comm])
  simp only [h0, zero_mul, add_zero] at hφ
  set M := max ⟪y, y - x⟫ ⟪y', y - x⟫
  have hyM : ⟪y, y - x⟫ ≤ M := le_max_left _ _
  have hy'M : ⟪y', y - x⟫ ≤ M := le_max_right _ _
  have hpM : M ≤ ⟪p, y - x⟫ := le_trans hbad (min_le_left _ _)
  have hp'M : M ≤ ⟪p', y - x⟫ := le_trans hbad (min_le_right _ _)
  have hn : 0 < ⟪y - x, y - x⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hxv : ⟪x, y - x⟫ = ⟪y, y - x⟫ - ⟪y - x, y - x⟫ := by rw [inner_sub_left]; ring
  have hs := hL.sum
  rw [h0] at hs
  rw [hxv] at hφ
  have hsM : (L x + L y + L y' + L p + L p') * M = 0 := by
    rw [show L x + L y + L y' + L p + L p' = 0 by linarith, zero_mul]
  linarith [mul_le_mul_of_nonneg_left hpM hp, mul_le_mul_of_nonneg_left hp'M hp',
    mul_le_mul_of_nonpos_left hy'M hy', mul_le_mul_of_nonpos_left hyM hxy',
    mul_neg_of_neg_of_pos hx hn]

/-- **Lemma 9.6 (one facet).**  A dependency `μ` vanishing at `p'`, applied to
the facet `x' y' p`, compares the two other values. -/
theorem facet_lt_of_dep {x x' y y' p p' : ℝ³} {L : ℝ³ → ℝ} (hL : IsDep x x' y y' p p' L)
    {V : Finset ℝ³} (G : FacetFn V x' y' p) (hxV : x ∈ V) (hyV : y ∈ V)
    (hnd : [x, x', y, y', p, p'].Nodup)
    (h0 : L p' = 0) (hs : L x * (L x + L y) < 0) : G.f x < G.f y := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have r := hL.apply G.hN
  rw [G.hP, G.hQ, G.hR, h0] at r
  have nx := G.neg x hxV hxx' hxy' hxp
  have ny := G.neg y hyV (Ne.symm hx'y) hyy' hyp
  have e : L x * (G.f x - G.f y) = -(L x + L y) * G.f y := by linarith
  rcases lt_or_gt_of_ne (show L x ≠ 0 by rintro h; simp [h] at hs) with h | h
  · have : 0 < L x + L y := by nlinarith
    nlinarith
  · have : L x + L y < 0 := by nlinarith
    nlinarith

/-- Cramer's rule in `det3` form. -/
theorem cramer (e₁ e₂ e₃ v : ℝ³) :
    det3 e₁ e₂ e₃ • v = det3 v e₂ e₃ • e₁ + det3 e₁ v e₃ • e₂ + det3 e₁ e₂ v • e₃ := by
  ext i; fin_cases i <;>
    simp only [det3_expand, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] <;> ring

/-- A nontrivial linear relation makes `det3` vanish. -/
theorem det3_eq_zero_of_lin {u v w : ℝ³} {α β γ : ℝ} (h : α • u + β • v + γ • w = 0)
    (hne : ¬(α = 0 ∧ β = 0 ∧ γ = 0)) : det3 u v w = 0 := by
  have h0 := congrArg (· 0) h; have h1 := congrArg (· 1) h; have h2 := congrArg (· 2) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h0 h1 h2
  have ea : α * det3 u v w = 0 := by
    rw [det3_expand]
    linear_combination (v 1 * w 2 - v 2 * w 1) * h0 - (v 0 * w 2 - v 2 * w 0) * h1 +
      (v 0 * w 1 - v 1 * w 0) * h2
  have eb : β * det3 u v w = 0 := by
    rw [det3_expand]
    linear_combination (u 2 * w 1 - u 1 * w 2) * h0 - (u 2 * w 0 - u 0 * w 2) * h1 +
      (u 1 * w 0 - u 0 * w 1) * h2
  have ec : γ * det3 u v w = 0 := by
    rw [det3_expand]
    linear_combination (u 1 * v 2 - u 2 * v 1) * h0 - (u 0 * v 2 - u 2 * v 0) * h1 +
      (u 0 * v 1 - u 1 * v 0) * h2
  by_contra hd
  exact hne ⟨(mul_eq_zero.mp ea).resolve_right hd, (mul_eq_zero.mp eb).resolve_right hd,
    (mul_eq_zero.mp ec).resolve_right hd⟩

/-- Two dependencies `l`, `m` of the six vertices that are independent on them
(the Gale vectors are `g_t = (-m t, l t)`). -/
structure GaleData (a a' b b' c c' : ℝ³) where
  /-- The first coordinate of each vertex in the Gale diagram. -/
  l : ℝ³ → ℝ
  /-- The second coordinate of each vertex in the Gale diagram. -/
  m : ℝ³ → ℝ
  hl : IsDep a a' b b' c c' l
  hm : IsDep a a' b b' c c' m
  indep : ∀ α β : ℝ, α * l a + β * m a = 0 → α * l a' + β * m a' = 0 →
    α * l b + β * m b = 0 → α * l b' + β * m b' = 0 →
    α * l c + β * m c = 0 → α * l c' + β * m c' = 0 → α = 0 ∧ β = 0

/-- Exchange the two vertices of the first opposite pair. -/
def GaleData.swap₁ {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : GaleData a' a b b' c c' :=
  ⟨G.l, G.m, G.hl.swap₁, G.hm.swap₁, fun α β h1 h2 h3 h4 h5 h6 => G.indep α β h2 h1 h3 h4 h5 h6⟩

/-- Exchange the two vertices of the second opposite pair. -/
def GaleData.swap₂ {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : GaleData a a' b' b c c' :=
  ⟨G.l, G.m, G.hl.swap₂, G.hm.swap₂, fun α β h1 h2 h3 h4 h5 h6 => G.indep α β h1 h2 h4 h3 h5 h6⟩

/-- Exchange the two vertices of the third opposite pair. -/
def GaleData.swap₃ {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : GaleData a a' b b' c' c :=
  ⟨G.l, G.m, G.hl.swap₃, G.hm.swap₃, fun α β h1 h2 h3 h4 h5 h6 => G.indep α β h1 h2 h3 h4 h6 h5⟩

/-- Exchange the first and second opposite pairs. -/
def GaleData.perm₁₂ {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : GaleData b b' a a' c c' :=
  ⟨G.l, G.m, G.hl.perm₁₂, G.hm.perm₁₂, fun α β h1 h2 h3 h4 h5 h6 => G.indep α β h3 h4 h1 h2 h5 h6⟩

/-- Exchange the second and third opposite pairs. -/
def GaleData.perm₂₃ {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : GaleData a a' c c' b b' :=
  ⟨G.l, G.m, G.hl.perm₂₃, G.hm.perm₂₃, fun α β h1 h2 h3 h4 h5 h6 => G.indep α β h1 h2 h5 h6 h3 h4⟩

/-- The dependency expressing `v` in the frame `a, b, c, a'` (Cramer). -/
noncomputable def frameDep (a b c a' v : ℝ³) (t : ℝ³) : ℝ :=
  if t = v then -det3 (b - a) (c - a) (a' - a)
  else if t = b then det3 (v - a) (c - a) (a' - a)
  else if t = c then det3 (b - a) (v - a) (a' - a)
  else if t = a' then det3 (b - a) (c - a) (v - a)
  else if t = a then det3 (b - a) (c - a) (a' - a) - det3 (v - a) (c - a) (a' - a) -
    det3 (b - a) (v - a) (a' - a) - det3 (b - a) (c - a) (v - a)
  else 0

theorem frameDep_isDep {a a' b c v w : ℝ³} (hnd : [a, a', b, v, c, w].Nodup) :
    IsDep a a' b v c w (frameDep a b c a' v) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hav, hac, haw⟩, ⟨ha'b, ha'v, ha'c, ha'w⟩, ⟨hbv, hbc, hbw⟩,
    ⟨hvc, hvw⟩, hcw, -⟩ := hnd
  have hcr := cramer (b - a) (c - a) (a' - a) (v - a)
  constructor <;> simp only [frameDep, ↓reduceIte, haa', hab, hav, hac, Ne.symm haw, ha'b, ha'v,
    ha'c, Ne.symm ha'w, hbv, Ne.symm hbc, Ne.symm hbw, Ne.symm hvc, Ne.symm hvw, Ne.symm hcw]
  · ring
  · rw [zero_smul, add_zero]
    linear_combination (norm := module) -hcr

theorem IsDep.swap₂₃' {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b c' c b' l) :
    IsDep a a' b b' c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem frame_det_ne {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    det3 (b - a) (c - a) (a' - a) ≠ 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hcr : cross (b - a) (c - a) ≠ 0 :=
    cross_ne_zero_of_affine F.abc'.hN hab F.abc'.hP F.abc'.hQ
      (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
  intro h0
  have := affine_zero_of_coplanar F.abc.hN F.abc.hP F.abc.hQ F.abc.hR hcr h0
  have := F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c
  linarith

theorem OctFacets.nonempty_galeData {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    Nonempty (GaleData a a' b b' c c') := by
  have hD := frame_det_ne F
  have hnd := F.nodup
  have hnd' : [a, a', b, c', c, b'].Nodup :=
    nodup_perm_aux (by
      have : [a, a', b, b', c, c'].Perm [a, a', b, c', c, b'] := by
        rw [List.perm_iff_count]; intro z; simp only [List.count_cons, List.count_nil]; omega
      exact this) hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  refine ⟨⟨frameDep a b c a' b', frameDep a b c a' c', frameDep_isDep F.nodup,
    (frameDep_isDep hnd').swap₂₃', fun α β _ _ _ h4 _ h6 => ?_⟩⟩
  simp only [frameDep, ↓reduceIte, Ne.symm hab', Ne.symm hac', Ne.symm ha'b', Ne.symm ha'c',
    Ne.symm hbb', Ne.symm hbc', hb'c, hb'c', Ne.symm hb'c', Ne.symm hcc'] at h4 h6
  constructor
  · have : α * det3 (b - a) (c - a) (a' - a) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hD
  · have : β * det3 (b - a) (c - a) (a' - a) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hD

theorem IsOctahedron.nonempty_galeData {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    Nonempty (GaleData a a' b b' c c') :=
  let ⟨F⟩ := h.nonempty_octFacets; F.nonempty_galeData

/-- **Planar equators.** If `κ_A = det(g_a, g_a') = 0`, the equator `b, c, b', c'` is planar. -/
theorem GaleData.planar_of_kappa {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c')
    (hκ : galeD G.l G.m a a' = 0) : det3 (c - b) (b' - b) (c' - b) = 0 := by
  simp only [galeD] at hκ
  obtain ⟨α, β, hne, h1, h2⟩ : ∃ α β : ℝ, ¬(α = 0 ∧ β = 0) ∧ α * G.l a + β * G.m a = 0 ∧
      α * G.l a' + β * G.m a' = 0 := by
    by_cases ha : G.l a = 0 ∧ G.m a = 0
    · by_cases ha' : G.l a' = 0 ∧ G.m a' = 0
      · exact ⟨1, 0, by simp, by simp [ha.1], by simp [ha'.1]⟩
      · refine ⟨G.m a', -G.l a', fun h => ha' ⟨by linarith [h.2], h.1⟩, ?_, ?_⟩
        · linear_combination hκ
        · ring
    · refine ⟨G.m a, -G.l a, fun h => ha ⟨by linarith [h.2], h.1⟩, ?_, ?_⟩
      · ring
      · linear_combination -hκ
  have hL := G.hl.comb G.hm α β
  generalize hLdef : (fun t => α * G.l t + β * G.m t) = L at hL
  have h1' : L a = 0 := by rw [← hLdef]; exact h1
  have h2' : L a' = 0 := by rw [← hLdef]; exact h2
  have hs := hL.sum; have hv := hL.vsum
  rw [h1', h2', zero_smul, zero_smul] at hv
  rw [h1', h2'] at hs
  have hrel : L c • (c - b) + L b' • (b' - b) + L c' • (c' - b) = 0 := by
    have hb : L b = -(L b' + L c + L c') := by linarith
    rw [hb] at hv; rw [← hv]; simp only [smul_sub]; module
  refine det3_eq_zero_of_lin hrel ?_
  rintro ⟨e1, e2, e3⟩
  have e0 : L b = 0 := by linarith
  rw [← hLdef] at e0 e1 e2 e3
  exact hne (G.indep α β h1 h2 e0 e2 e1 e3)

theorem isRupert_of_kappa_zero {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκ : galeD G.l G.m a a' = 0) :
    IsRupert {a, a', b, b', c, c'} :=
  isRupert_planar_equator h (G.planar_of_kappa hκ)

/-- A dependency that is `≤ 0` on the face opposite `abc` vanishes identically. -/
theorem dep_zero_of_face {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') {D : ℝ³ → ℝ}
    (hD : IsDep a a' b b' c c' D) (h1 : D a' ≤ 0) (h2 : D b' ≤ 0) (h3 : D c' ≤ 0) :
    D a = 0 ∧ D a' = 0 ∧ D b = 0 ∧ D b' = 0 ∧ D c = 0 ∧ D c' = 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have r := hD.apply F.abc.hN
  rw [F.abc.hP, F.abc.hQ, F.abc.hR] at r
  have n1 := F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c
  have n2 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
  have n3 := F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc')
  have p1 := mul_nonneg_of_nonpos_of_nonpos h1 n1.le
  have p2 := mul_nonneg_of_nonpos_of_nonpos h2 n2.le
  have p3 := mul_nonneg_of_nonpos_of_nonpos h3 n3.le
  have z1 : D a' = 0 := by
    have : D a' * F.abc.f a' = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n1.ne
  have z2 : D b' = 0 := by
    have : D b' * F.abc.f b' = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n2.ne
  have z3 : D c' = 0 := by
    have : D c' * F.abc.f c' = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n3.ne
  have hcr : cross (b - a) (c - a) ≠ 0 :=
    cross_ne_zero_of_affine F.abc'.hN hab F.abc'.hP F.abc'.hQ
      (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
  have hs := hD.sum; have hv := hD.vsum
  rw [z1, z2, z3] at hs hv
  simp only [zero_smul, add_zero] at hv
  have hrel : D b • (b - a) + D c • (c - a) + (0 : ℝ) • (0 : ℝ³) = 0 := by
    have ha : D a = -(D b + D c) := by linarith
    rw [ha] at hv; rw [← hv]; simp only [smul_sub]; module
  -- `cross (b - a) (c - a) ≠ 0` forces both coefficients to vanish
  have key : ∀ α β : ℝ, α • (b - a) + β • (c - a) = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have hb : α • cross (b - a) (c - a) = 0 := by
      have : cross (α • (b - a) + β • (c - a)) (c - a) = α • cross (b - a) (c - a) := by
        ext i; fin_cases i <;>
          simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
            cross_apply_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring
      rw [← this, h]; ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one,
        cross_apply_two]
    have hc : β • cross (b - a) (c - a) = 0 := by
      have : cross (b - a) (α • (b - a) + β • (c - a)) = β • cross (b - a) (c - a) := by
        ext i; fin_cases i <;>
          simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
            cross_apply_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring
      rw [← this, h]; ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one,
        cross_apply_two]
    exact ⟨(smul_eq_zero.mp hb).resolve_right hcr, (smul_eq_zero.mp hc).resolve_right hcr⟩
  rw [zero_smul, add_zero] at hrel
  obtain ⟨zb, zc⟩ := key _ _ hrel
  exact ⟨by linarith, z1, zb, z2, zc, z3⟩

/-- `det(g_t, f)` for `f = g_a + g_b + g_c`. -/
def galeF (l m : ℝ³ → ℝ) (a b c : ℝ³) (t : ℝ³) : ℝ :=
  l t * (m a + m b + m c) - m t * (l a + l b + l c)

theorem galeF_eq (l m : ℝ³ → ℝ) (a b c t : ℝ³) :
    galeF l m a b c t = galeD l m t a + galeD l m t b + galeD l m t c := by
  simp only [galeF, galeD]; ring

/-- **Lemma 9.8 (arc lemma)**, for `f = g_a + g_b + g_c ≠ 0`. -/
theorem arc_lemma {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκ : galeD G.l G.m a a' ≠ 0)
    (hf : ¬(G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0)) :
    (0 < galeF G.l G.m a b c a ∧ 0 < galeF G.l G.m a b c a') ∨
    (0 < galeF G.l G.m a b c b ∧ 0 < galeF G.l G.m a b c b') ∨
    (0 < galeF G.l G.m a b c c ∧ 0 < galeF G.l G.m a b c c') := by
  set D := galeF G.l G.m a b c with hDdef
  have hD : IsDep a a' b b' c c' D := by
    have := G.hl.comb G.hm (G.m a + G.m b + G.m c) (-(G.l a + G.l b + G.l c))
    convert this using 2 with t; simp only [hDdef, galeF]; ring
  by_contra hno
  simp only [not_or, not_and_or, not_lt] at hno
  obtain ⟨hA, hB, hC⟩ := hno
  have hz : D a = 0 ∧ D a' = 0 := by
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rcases hC with hC | hC
    · have := dep_zero_of_face F.swap₁.swap₂.swap₃ hD.swap₁.swap₂.swap₃ hA hB hC
      exact ⟨this.2.1, this.1⟩
    · have := dep_zero_of_face F.swap₁.swap₂ hD.swap₁.swap₂ hA hB hC
      exact ⟨this.2.1, this.1⟩
    · have := dep_zero_of_face F.swap₁.swap₃ hD.swap₁.swap₃ hA hB hC
      exact ⟨this.2.1, this.1⟩
    · have := dep_zero_of_face F.swap₁ hD.swap₁ hA hB hC
      exact ⟨this.2.1, this.1⟩
    · have := dep_zero_of_face F.swap₂.swap₃ hD.swap₂.swap₃ hA hB hC
      exact ⟨this.1, this.2.1⟩
    · have := dep_zero_of_face F.swap₂ hD.swap₂ hA hB hC
      exact ⟨this.1, this.2.1⟩
    · have := dep_zero_of_face F.swap₃ hD.swap₃ hA hB hC
      exact ⟨this.1, this.2.1⟩
    · have := dep_zero_of_face F hD hA hB hC
      exact ⟨this.1, this.2.1⟩
  obtain ⟨z1, z2⟩ := hz
  simp only [hDdef, galeF] at z1 z2
  apply hf
  have e1 : (G.l a + G.l b + G.l c) * galeD G.l G.m a a' = 0 := by
    simp only [galeD]; linear_combination -G.l a * z2 + G.l a' * z1
  have e2 : (G.m a + G.m b + G.m c) * galeD G.l G.m a a' = 0 := by
    simp only [galeD]; linear_combination G.m a' * z1 - G.m a * z2
  exact ⟨(mul_eq_zero.mp e1).resolve_right hκ, (mul_eq_zero.mp e2).resolve_right hκ⟩

theorem galeD_sum {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (s : ℝ³) :
    galeD l m s a + galeD l m s a' + galeD l m s b + galeD l m s b' + galeD l m s c +
      galeD l m s c' = 0 := by
  have h1 := hl.sum; have h2 := hm.sum
  simp only [galeD]; linear_combination l s * h2 - m s * h1

theorem IsDep.galeD' {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (s : ℝ³) :
    IsDep a a' b b' c c' (fun t => Minimality.galeD l m t s) := by
  have := hl.comb hm (m s) (-l s)
  convert this using 2 with t; simp only [Minimality.galeD]; ring

theorem finset_perm_ba {a a' b b' c c' : ℝ³} :
    ({b, b', a, a', c', c} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem finset_perm_a'b' {a a' b b' c c' : ℝ³} :
    ({a', a, b', b, c', c} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem finset_perm_c'c {a a' b b' c c' : ℝ³} :
    ({c', c, b, b', a, a'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **The generic case (§9.5)** for a normalized labeling (`κ_A, κ_B, κ_C > 0`),
the arc-lemma pair `W = C` and `U = A`: `b → a` and `a' → b'` are quad edges
(Lemma 9.6) with poles `c'`, `c`, neither is bad (`not_bad_of_dep`), so one of
them gives a passage by Lemma 9.3, or both are touching and Lemma 9.4 applies. -/
theorem isRupert_gale_core {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hfc : 0 < galeF G.l G.m a b c c) (hfc' : 0 < galeF G.l G.m a b c c')
    (hU : 0 < galeD G.l G.m c a) : IsRupert {a, a', b, b', c, c'} := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  -- pole signs at `c`, `c'`, `a`, `b'`
  obtain ⟨c1, c2, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂
    (self c) hκc.ne'
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁ (hl.galeD hm c').perm₂₃.perm₁₂.swap₁
    (self c') (by rw [anti]; linarith)
  obtain ⟨a1, a2, a3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  obtain ⟨b1, b2, b3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁
    (self b') (by rw [anti]; linarith)
  -- signs of `det(g_c, ·)` and `det(g_c', ·)`
  have hca' : 0 < galeD G.l G.m c a' := pos_of_mul_pos_pos c1 hU
  have hcb : galeD G.l G.m c b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at c3) hU
  have hcb' : galeD G.l G.m c b' < 0 := neg_of_mul_pos_neg (by linarith) hcb
  have hc'a : 0 < galeD G.l G.m c' a := by
    have e : galeD G.l G.m a c * galeD G.l G.m a c' = galeD G.l G.m c a * galeD G.l G.m c' a := by
      rw [anti c a, anti c' a]; ring
    exact pos_of_mul_pos_pos (e ▸ a2) hU
  have hc'a' : 0 < galeD G.l G.m c' a' := pos_of_mul_pos_pos d1 hc'a
  have hc'b : galeD G.l G.m c' b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at d3) hc'a
  have hc'b' : galeD G.l G.m c' b' < 0 := neg_of_mul_pos_neg (by linarith) hc'b
  -- signs of `det(g_a, ·)` and `det(g_b', ·)`
  have hac : galeD G.l G.m a c < 0 := by rw [anti]; linarith
  have hab : 0 < galeD G.l G.m a b := pos_of_mul_neg_neg (by linarith) hac
  have hab' : 0 < galeD G.l G.m a b' := pos_of_mul_pos_pos a1 hab
  have hb'c : 0 < galeD G.l G.m b' c := by rw [anti]; linarith
  have hb'a : galeD G.l G.m b' a < 0 := neg_of_mul_neg_pos b3 hb'c
  have hb'a' : galeD G.l G.m b' a' < 0 := neg_of_mul_pos_neg b1 hb'a
  have hb'c' : 0 < galeD G.l G.m b' c' := by rw [anti]; linarith
  -- sums
  have sc := galeD_sum hl hm c
  have sc' := galeD_sum hl hm c'
  rw [galeF_eq] at hfc hfc'
  rw [self] at sc hfc
  rw [self] at sc'
  have hcc' := anti c c'
  -- the crossed pair
  have hndb := (F.perm₁₂.swap₃).nodup
  have hnda := (F.swap₁.swap₂.swap₃).nodup
  have hq₁ := facet_lt_of_dep (hl.galeD hm c).perm₁₂.swap₃ (F.perm₁₂.swap₃).a'b'c (by simp)
    (by simp) hndb (self c) (by nlinarith)
  have hq₂ := facet_lt_of_dep (hl.galeD hm c').perm₁₂ (F.perm₁₂.swap₃).a'b'c' (by simp)
    (by simp) (F.perm₁₂).nodup (self c') (by nlinarith)
  have hr₁ := facet_lt_of_dep (hl.galeD hm c).swap₁.swap₂.swap₃ (F.swap₁.swap₂.swap₃).a'b'c
    (by simp) (by simp) hnda (self c) (by nlinarith)
  have hr₂ := facet_lt_of_dep (hl.galeD hm c').swap₁.swap₂ (F.swap₁.swap₂.swap₃).a'b'c'
    (by simp) (by simp) (F.swap₁.swap₂).nodup (self c') (by nlinarith)
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hnba : a ≠ b := hnd.1.2.1
  have hnab' : a' ≠ b' := hnd.2.1.2.1
  have hgood₁ := not_bad_of_dep (hl.galeD hm b').perm₁₂.swap₃ (Ne.symm hnba) (self b')
    (by rw [anti]; linarith) (by rw [anti b b']; linarith) hb'a'.le hb'c'.le hb'c.le
  have hgood₂ := not_bad_of_dep (L := fun t => galeD G.l G.m t a)
    (hl.galeD' hm a).swap₁.swap₂.swap₃ hnab' (self a) (by rw [anti]; linarith)
    (by rw [anti a a', anti a b']; linarith) (by rw [anti]; linarith) hc'a.le hU.le
  by_cases ht₁ : ⟪c', a - b⟫ = ⟪c, a - b⟫ ∧ ⟪c, a - b⟫ = ⟪a', a - b⟫ ∧ ⟪a', a - b⟫ < ⟪a, a - b⟫
  · by_cases ht₂ : ⟪c', b' - a'⟫ = ⟪c, b' - a'⟫ ∧ ⟪c, b' - a'⟫ = ⟪b, b' - a'⟫ ∧
        ⟪b, b' - a'⟫ < ⟪b', b' - a'⟫
    · have := isRupert_of_touching_pair h.perm₂₃.perm₁₂.perm₂₃.swap₁
        (by rw [inner_sub_left]; linarith [ht₁.1]) (by rw [inner_sub_left]; linarith [ht₂.1])
      rwa [finset_perm_c'c] at this
    · have := isRupert_quad_edge F.swap₁.swap₂.swap₃ hr₁ hr₂ hgood₂ ht₂
      rwa [finset_perm_a'b'] at this
  · have := isRupert_quad_edge F.perm₁₂.swap₃ hq₁ hq₂ hgood₁ ht₁
    rwa [finset_perm_ba] at this

theorem isRupert_congr_set {s t : Finset ℝ³} (h : IsRupert s) (e : s = t) : IsRupert t := e ▸ h


theorem galeF_perm₁₂ (l m : ℝ³ → ℝ) (a b c t : ℝ³) : galeF l m b a c t = galeF l m a b c t := by
  simp only [galeF]; ring

theorem galeF_perm₂₃ (l m : ℝ³ → ℝ) (a b c t : ℝ³) : galeF l m a c b t = galeF l m a b c t := by
  simp only [galeF]; ring

/-- The generic case with the arc-lemma pair `W = C` (either `U`). -/
theorem isRupert_gale_W {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hfc : 0 < galeF G.l G.m a b c c) (hfc' : 0 < galeF G.l G.m a b c c') :
    IsRupert {a, a', b, b', c, c'} := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
    (galeD_self _ _ c) hκc.ne'
  rcases lt_or_gt_of_ne (show galeD G.l G.m c a ≠ 0 by intro h0; rw [h0, zero_mul] at c3; linarith)
    with hU | hU
  · have hb : 0 < galeD G.l G.m c b := pos_of_mul_neg_neg (by rwa [mul_comm] at c3) hU
    refine isRupert_congr_set (isRupert_gale_core h.perm₁₂ G.perm₁₂ hκb hκa hκc ?_ ?_ hb) ?_
    · simpa [GaleData.perm₁₂, galeF_perm₁₂] using hfc
    · simpa [GaleData.perm₁₂, galeF_perm₁₂] using hfc'
    · ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact isRupert_gale_core h G hκa hκb hκc hfc hfc' hU

/-- **Theorem 9.9, generic case** (§9.5): normalized labels (`κ > 0` on all
three pairs) and `f = g_a + g_b + g_c ≠ 0`. -/
theorem isRupert_octahedron_generic {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : ¬(G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0)) :
    IsRupert {a, a', b, b', c, c'} := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  rcases arc_lemma F G hκa.ne' hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `W = A`: relabel `(b, c, a)`
    refine isRupert_congr_set (isRupert_gale_W h.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃ hκb hκc hκa ?_ ?_) ?_
    · simpa [GaleData.perm₁₂, GaleData.perm₂₃, galeF_perm₁₂, galeF_perm₂₃, galeF] using
        (by simp only [galeF] at h1 ⊢; linarith : 0 < galeF G.l G.m b c a a)
    · simpa [GaleData.perm₁₂, GaleData.perm₂₃, galeF_perm₁₂, galeF_perm₂₃, galeF] using
        (by simp only [galeF] at h2 ⊢; linarith : 0 < galeF G.l G.m b c a a')
    · ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · -- `W = B`: relabel `(a, c, b)`
    refine isRupert_congr_set (isRupert_gale_W h.perm₂₃ G.perm₂₃ hκa hκc hκb ?_ ?_) ?_
    · simpa [GaleData.perm₂₃, galeF_perm₂₃] using h1
    · simpa [GaleData.perm₂₃, galeF_perm₂₃] using h2
    · ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact isRupert_gale_W h G hκa hκb hκc h1 h2

end Minimality

end RupertMinimality
