/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.L8Shapes

/-! # L8 T4 -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 8.3: every T4 is Rupert
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **T4, combinatorial form**: the quadrilateral facet
`A K₁ T K₂` (`K₁`, `K₂` of degree 3) and the triangles `K₁AC`, `K₁CT`,
`K₂AB`, `K₂BT`, `ABC`, `BCT`. -/
structure IsT4 (A B C T K₁ K₂ : ℝ³) : Prop where
  nodup : [A, B, C, T, K₁, K₂].Nodup
  affineIndependent : AffineIndependent ℝ ![A, B, C, T]
  quad : IsFacet {A, B, C, T, K₁, K₂} {A, K₁, T, K₂}
  facet_K₁AC : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ A C
  facet_K₁CT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ C T
  facet_K₂AB : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ A B
  facet_K₂BT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ B T
  facet_ABC : IsFacetTriangle {A, B, C, T, K₁, K₂} A B C
  facet_BCT : IsFacetTriangle {A, B, C, T, K₁, K₂} B C T

/-- The facet conditions put a T4 in normal form (as for Cor. 5.7, with the
quadrilateral facet making `A, T, K₁, K₂` coplanar: `β₁ γ₂ = c₁ b₂`). -/
theorem IsT4.exists_normalForm {A B C T K₁ K₂ : ℝ³} (h : IsT4 A B C T K₁ K₂) :
    ∃ a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ : ℝ, 0 < a₁ ∧ 0 < β₁ ∧ 0 < c₁ ∧ 0 < t₁ ∧
      0 < a₂ ∧ 0 < b₂ ∧ 0 < γ₂ ∧ 0 < t₂ ∧
      a₁ - β₁ + c₁ + t₁ = 1 ∧ a₂ + b₂ - γ₂ + t₂ = 1 ∧ β₁ * γ₂ = c₁ * b₂ ∧
      K₁ = a₁ • A - β₁ • B + c₁ • C + t₁ • T ∧ K₂ = a₂ • A + b₂ • B - γ₂ • C + t₂ • T := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hAB, hAC, hAT, hAK₁, hAK₂⟩, ⟨hBC, hBT, hBK₁, hBK₂⟩, ⟨hCT, hCK₁, hCK₂⟩,
    ⟨hTK₁, hTK₂⟩, hK₁K₂, -⟩ := hnd
  obtain ⟨l1A, l1B, l1C, l1T, hs1, hK₁⟩ := exists_bary h.affineIndependent K₁
  obtain ⟨l2A, l2B, l2C, l2T, hs2, hK₂⟩ := exists_bary h.affineIndependent K₂
  have ev1 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK₁ ▸ affine_apply_comb4 f hs1 :
    f K₁ = l1A * f A + l1B * f B + l1C * f C + l1T * f T)
  have ev2 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK₂ ▸ affine_apply_comb4 f hs2 :
    f K₂ = l2A * f A + l2B * f B + l2C * f C + l2T * f T)
  obtain ⟨f, fB, fC, fT, hf⟩ := h.facet_BCT
  have fA := hf A (by simp) hAB hAC hAT
  have fK₁ := hf K₁ (by simp) (Ne.symm hBK₁) (Ne.symm hCK₁) (Ne.symm hTK₁)
  have fK₂ := hf K₂ (by simp) (Ne.symm hBK₂) (Ne.symm hCK₂) (Ne.symm hTK₂)
  rw [ev1, fB, fC, fT] at fK₁
  rw [ev2, fB, fC, fT] at fK₂
  simp only [mul_zero, add_zero] at fK₁ fK₂
  have h1A : 0 < l1A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fA.le]
  have h2A : 0 < l2A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fA.le]
  obtain ⟨g, gA, gB, gC, hg⟩ := h.facet_ABC
  have gT := hg T (by simp) (Ne.symm hAT) (Ne.symm hBT) (Ne.symm hCT)
  have gK₁ := hg K₁ (by simp) (Ne.symm hAK₁) (Ne.symm hBK₁) (Ne.symm hCK₁)
  have gK₂ := hg K₂ (by simp) (Ne.symm hAK₂) (Ne.symm hBK₂) (Ne.symm hCK₂)
  rw [ev1, gA, gB, gC] at gK₁
  rw [ev2, gA, gB, gC] at gK₂
  simp only [mul_zero, zero_add] at gK₁ gK₂
  have h1T : 0 < l1T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc gT.le]
  have h2T : 0 < l2T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc gT.le]
  obtain ⟨hh, hhK, hhA, hhC, hhx⟩ := h.facet_K₁AC
  have hhB := hhx B (by simp) hBK₁ (Ne.symm hAB) hBC
  have hhT := hhx T (by simp) hTK₁ (Ne.symm hAT) (Ne.symm hCT)
  have e := ev1 hh
  rw [hhK, hhA, hhC] at e
  simp only [mul_zero, zero_add, add_zero] at e
  have h1B : l1B < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc hhB.le, mul_neg_of_pos_of_neg h1T hhT]
  obtain ⟨m, mK, mA, mB, hm⟩ := h.facet_K₂AB
  have mC := hm C (by simp) hCK₂ (Ne.symm hAC) (Ne.symm hBC)
  have mT := hm T (by simp) hTK₂ (Ne.symm hAT) (Ne.symm hBT)
  have e2 := ev2 m
  rw [mK, mA, mB] at e2
  simp only [mul_zero, zero_add, add_zero] at e2
  have h2C : l2C < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc mC.le, mul_neg_of_pos_of_neg h2T mT]
  -- the quadrilateral facet `A K₁ T K₂`
  obtain ⟨q, hq0, hq⟩ := h.quad
  have qA := hq0 A (by simp)
  have qK₁ := hq0 K₁ (by simp)
  have qT := hq0 T (by simp)
  have qK₂ := hq0 K₂ (by simp)
  have qB := hq B (by simp) (by simp [Ne.symm hAB, hBK₁, hBT, hBK₂])
  have qC := hq C (by simp) (by simp [Ne.symm hAC, hCK₁, hCT, hCK₂])
  rw [ev1, qA, qT] at qK₁
  rw [ev2, qA, qT] at qK₂
  simp only [mul_zero, zero_add, add_zero] at qK₁ qK₂
  have h1C : 0 < l1C := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos_of_neg_of_neg h1B qB, mul_nonneg_of_nonpos_of_nonpos hc qC.le]
  have h2B : 0 < l2B := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos_of_neg_of_neg h2C qC, mul_nonneg_of_nonpos_of_nonpos hc qB.le]
  have hcop : l1B * l2C = l1C * l2B := by
    have h1 : l1B * q B = -(l1C * q C) := by linarith
    have h2 : l2B * q B = -(l2C * q C) := by linarith
    have hqB : q B ≠ 0 := qB.ne
    have : (l1B * l2C - l1C * l2B) * q B = 0 := by linear_combination l2C * h1 - l1C * h2
    have := (mul_eq_zero.mp this).resolve_right hqB
    linarith
  refine ⟨l1A, -l1B, l1C, l1T, l2A, l2B, -l2C, l2T, h1A, by linarith, h1C, h1T, h2A, h2B,
    by linarith, h2T, by linarith, by linarith, by linear_combination hcop, ?_, ?_⟩
  · rw [hK₁]; module
  · rw [hK₂]; module

/-- A pure depth lemma for the two T4 cycles (`K_lo` below and `K_up` above the
chord `AT`). -/
theorem t4_nws {p2 p3 s γ c l₁ l₂ : ℝ} (hs : 0 < s) (hγ : 0 < γ) (hc : 0 < c)
    (hl₁ : 0 < l₁) (hl₁' : l₁ < 1) (hl₂ : 0 < l₂) (hl₂' : l₂ < 1) (hp3 : p3 ≠ 0) :
    NWS4 (quad 0 (-(γ * s) + l₂ * p3) p3 p2) ∨ NWS4 (quad 0 (c * s + l₁ * p3) p3 p2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at h1 h2
  have hγs := mul_pos hγ hs
  have hcs := mul_pos hc hs
  rcases lt_or_gt_of_ne hp3 with hp | hp
  · have e1 : l₂ * p3 < 0 := mul_neg_of_pos_of_neg hl₂ hp
    have e2 : p3 < l₁ * p3 := by nlinarith
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith [h1.1, h1.2.1, h1.2.2.1,
      h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  · have e1 : l₂ * p3 < p3 := by nlinarith
    have e2 : 0 < l₁ * p3 := mul_pos hl₁ hp
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith [h1.1, h1.2.1, h1.2.2.1,
      h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]

/-- **T4, case `x < 1`**, in the frame `(B - A, C - A, T - A)`:
`K₁ = (-y c₁, c₁, t₁)`, `K₂ = (y γ₂, -γ₂, t₂)` with `y > 1` (coplanar quad
`A K₁ T K₂`).  The views are `X - B` for `X` in the face `ACT` such that `K₁`
and `K₂` project into the open side `AT` (an open segment of such `X`), tilted
across that side. -/
theorem isRupert_T4_core {A B C T : ℝ³} (hΔ : det3 (B - A) (C - A) (T - A) ≠ 0)
    {c₁ t₁ γ₂ t₂ y : ℝ} (hc₁ : 0 < c₁) (ht₁ : 0 < t₁) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hy : 1 < y) (ha₁ : 0 < 1 + y * c₁ - c₁ - t₁) (ha₂ : 0 < 1 - y * γ₂ + γ₂ - t₂) :
    IsRupert {A, B, C, T, A + cmb (B - A) (C - A) (T - A) (-(y * c₁)) c₁ t₁,
      A + cmb (B - A) (C - A) (T - A) (y * γ₂) (-γ₂) t₂} := by
  classical
  set f₁ := B - A
  set f₂ := C - A
  set f₃ := T - A
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => A + cmb f₁ f₂ f₃ a b c with hP
  have eA : A = P 0 0 0 := by simp [hP, cmb]
  have eB : B = P 1 0 0 := by simp [hP, cmb, f₁]
  have eC : C = P 0 1 0 := by simp [hP, cmb, f₂]
  have eT : T = P 0 0 1 := by simp [hP, cmb, f₃]
  have hf₃ : f₃ ≠ 0 := by
    intro h0; apply hΔ; simp [h0, det3, cross]
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- choose the view: `w` in the open interval, off the circle `⟪f₃, d⟫ = 0`
  set lo := max 0 ((t₁ - 1) / c₁)
  set hi := min (y - 1) (t₁ / c₁)
  have hlohi : lo < hi := by
    simp only [lo, hi, max_lt_iff, lt_min_iff]
    refine ⟨⟨by linarith, ?_⟩, div_pos ht₁ hc₁, ?_⟩
    · rw [div_lt_iff₀ hc₁]; nlinarith
    · exact div_lt_div_of_pos_right (by linarith) hc₁
  have hdw : ∀ w : ℝ, ⟪f₃, cmb f₁ f₂ f₃ (-y) 1 w⟫ = ⟪f₃, cmb f₁ f₂ f₃ (-y) 1 0⟫ + w * ⟪f₃, f₃⟫ := by
    intro w; simp only [cmb, inner_add_right, inner_smul_right]; ring
  have hf₃f₃ : 0 < ⟪f₃, f₃⟫ := real_inner_self_pos.mpr hf₃
  obtain ⟨w, hwlo, hwhi, hwp⟩ : ∃ w, lo < w ∧ w < hi ∧ ⟪f₃, cmb f₁ f₂ f₃ (-y) 1 w⟫ ≠ 0 := by
    by_cases h0 : ⟪f₃, cmb f₁ f₂ f₃ (-y) 1 ((lo + hi) / 2)⟫ = 0
    · refine ⟨(lo + 3 * hi) / 4, by linarith, by linarith, fun h1 => ?_⟩
      rw [hdw] at h0 h1
      nlinarith
    · exact ⟨(lo + hi) / 2, by linarith, by linarith, h0⟩
  have hw0 : 0 < w := lt_of_le_of_lt (le_max_left _ _) hwlo
  have hw3 : t₁ - 1 < c₁ * w := by
    have := lt_of_le_of_lt (le_max_right _ _) hwlo
    rw [div_lt_iff₀ hc₁] at this; linarith
  have hw1 : w < y - 1 := lt_of_lt_of_le hwhi (min_le_left _ _)
  have hw2 : c₁ * w < t₁ := by
    have := lt_of_lt_of_le hwhi (min_le_right _ _)
    rw [lt_div_iff₀ hc₁] at this; linarith
  have hy0 : 0 < y := by linarith
  have L1 : 0 < 1 + c₁ * w - t₁ := by linarith
  have L1' : 0 < t₁ - c₁ * w := by linarith
  have L2 : 0 < 1 - γ₂ * w - t₂ := by nlinarith
  have M : 0 < c₁ * (1 - t₂) + γ₂ * (1 - t₁) := by nlinarith
  have P1 := mul_pos hy0 L1
  have P2 := mul_pos hy0 L1'
  have P3 := mul_pos hy0 L2
  have P4 := mul_pos hy0 M
  have P5 := mul_pos hy0 hc₁
  have P6 := mul_pos hy0 hγ₂
  have P9 := mul_pos hγ₂ hw0
  have P7 := mul_pos hy0 (add_pos P9 ht₂)
  have P8 := mul_pos hy0 (add_pos (mul_pos hc₁ ht₂) (mul_pos hγ₂ ht₁))
  have hyw : 0 < y - 1 - w := by linarith
  have eK₁ : A + cmb (B - A) (C - A) (T - A) (-(y * c₁)) c₁ t₁ = P (-(y * c₁)) c₁ t₁ := rfl
  have eK₂ : A + cmb (B - A) (C - A) (T - A) (y * γ₂) (-γ₂) t₂ = P (y * γ₂) (-γ₂) t₂ := rfl
  rw [eK₁, eK₂, eA, eB, eC, eT]
  set V : Finset ℝ³ := {P 0 0 0, P 1 0 0, P 0 1 0, P 0 0 1, P (-(y * c₁)) c₁ t₁,
    P (y * γ₂) (-γ₂) t₂} with hV
  have hmemV : ∀ z ∈ V, z = P 0 0 0 ∨ z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 1 ∨
      z = P (-(y * c₁)) c₁ t₁ ∨ z = P (y * γ₂) (-γ₂) t₂ := by
    intro z hz; simpa [hV] using hz
  set d := cmb f₁ f₂ f₃ (-y) 1 w with hd
  set u₀ := σ • d with hu₀
  have hd0 : d ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ h0).2.1
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := smul_ne_zero hσ0 hd0
  have hs0 : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd0
  have hdd : ⟪d, d⟫ = -y * ⟪f₁, d⟫ + ⟪f₂, d⟫ + w * ⟪f₃, d⟫ := by
    have e : ⟪d, d⟫ = ⟪cmb f₁ f₂ f₃ (-y) 1 w, d⟫ := rfl
    rw [e]; simp only [cmb, inner_add_left, real_inner_smul_left]; ring
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪A, u₀⟫ + σ * (a * ⟪f₁, d⟫ + b * ⟪f₂, d⟫ + c * ⟪f₃, d⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, real_inner_smul_right]; ring
  have hp3 : ⟪f₃, d⟫ ≠ 0 := hwp
  rcases t4_nws (p2 := ⟪f₂, d⟫) (p3 := ⟪f₃, d⟫) (s := ⟪d, d⟫) (γ := γ₂) (c := c₁)
    (l₁ := t₁ - c₁ * w) (l₂ := t₂ + γ₂ * w) hs0 hγ₂ hc₁ L1' (by linarith) (by positivity)
    (by linarith) hp3 with hlo | hup
  · -- the cycle `(A, K₂, T, C)`
    have hQ : NWS4 fun i => ⟪quad (P 0 0 0) (P (y * γ₂) (-γ₂) t₂) (P 0 0 1) (P 0 1 0) i, u₀⟫ := by
      have := hlo.affine ⟪A, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> (try simp only [hdd]) <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ 0 (-1) (1 / 2)) hu₀0
      (quad (P 0 0 0) (P (y * γ₂) (-γ₂) t₂) (P 0 0 1) (P 0 1 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by
              simp only [detc]
              clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                P8 P9 hyw ha₁ ha₂
              linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by
              simp only [detc]
              clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                P8 P9 hyw ha₁ ha₂
              linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by
                simp only [detc]
                clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                  P8 P9 hyw ha₁ ha₂
                linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by
                simp only [detc]
                clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                  P8 P9 hyw ha₁ ha₂
                linarith)
  · -- the cycle `(A, K₁, T, C)`
    have hQ : NWS4 fun i => ⟪quad (P 0 0 0) (P (-(y * c₁)) c₁ t₁) (P 0 0 1) (P 0 1 0) i, u₀⟫ := by
      have := hup.affine ⟪A, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> (try simp only [hdd]) <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ 0 1 (-1 / 2)) hu₀0
      (quad (P 0 0 0) (P (-(y * c₁)) c₁ t₁) (P 0 0 1) (P 0 1 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by
              simp only [detc]
              clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                P8 P9 hyw ha₁ ha₂
              linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by
              simp only [detc]
              clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                P8 P9 hyw ha₁ ha₂
              linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by
                simp only [detc]
                clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                  P8 P9 hyw ha₁ ha₂
                linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by
                simp only [detc]
                clear * - hc₁ ht₁ hγ₂ ht₂ hy hy0 hw0 hw1 hw2 hw3 L1 L1' L2 M P1 P2 P3 P4 P5 P6 P7
                  P8 P9 hyw ha₁ ha₂
                linarith)

theorem t4eq_nws {p2 p3 s γ β t₁ t₂ : ℝ} (hs : 0 < s) (hγ : 0 < γ) (hβ : 0 < β)
    (ht₁ : 0 < t₁) (ht₁' : t₁ < 1) (ht₂ : 0 < t₂) (ht₂' : t₂ < 1) :
    NWS4 (quad p2 0 (-(γ * s) + t₂ * p3) p3) ∨ NWS4 (quad (p2 - s) 0 (β * s + t₁ * p3) p3) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at h1 h2
  have hγs := mul_pos hγ hs
  have hβs := mul_pos hβ hs
  rcases le_or_gt 0 p3 with hp | hp
  · have e1 : t₂ * p3 ≤ p3 := by nlinarith
    have e2 : 0 ≤ t₁ * p3 := by positivity
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith [h1.1, h1.2.1, h1.2.2.1,
      h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  · have e1 : t₂ * p3 < 0 := mul_neg_of_pos_of_neg ht₂ hp
    have e2 : p3 < t₁ * p3 := by nlinarith
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith [h1.1, h1.2.1, h1.2.2.1,
      h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]

/-- **T4, case `x = y = 1`**: the quad is parallel to `BC`; the view is `C - B`. -/
theorem isRupert_T4_eq {A B C T : ℝ³} (hΔ : det3 (B - A) (C - A) (T - A) ≠ 0)
    {β t₁ γ t₂ : ℝ} (hβ : 0 < β) (ht₁ : 0 < t₁) (ht₁' : t₁ < 1) (hγ : 0 < γ) (ht₂ : 0 < t₂)
    (ht₂' : t₂ < 1) :
    IsRupert {A, B, C, T, A + cmb (B - A) (C - A) (T - A) (-β) β t₁,
      A + cmb (B - A) (C - A) (T - A) γ (-γ) t₂} := by
  classical
  set f₁ := B - A
  set f₂ := C - A
  set f₃ := T - A
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => A + cmb f₁ f₂ f₃ a b c with hP
  have eA : A = P 0 0 0 := by simp [hP, cmb]
  have eB : B = P 1 0 0 := by simp [hP, cmb, f₁]
  have eC : C = P 0 1 0 := by simp [hP, cmb, f₂]
  have eT : T = P 0 0 1 := by simp [hP, cmb, f₃]
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have h1 : 0 < 1 - t₁ := by linarith
  have h2 : 0 < 1 - t₂ := by linarith
  have Q1 := add_pos (mul_pos hβ ht₂) (mul_pos hγ ht₁)
  have Q2 := add_pos (mul_pos hβ h2) (mul_pos hγ h1)
  have eK₁ : A + cmb (B - A) (C - A) (T - A) (-β) β t₁ = P (-β) β t₁ := rfl
  have eK₂ : A + cmb (B - A) (C - A) (T - A) γ (-γ) t₂ = P γ (-γ) t₂ := rfl
  rw [eK₁, eK₂, eA, eB, eC, eT]
  set V : Finset ℝ³ := {P 0 0 0, P 1 0 0, P 0 1 0, P 0 0 1, P (-β) β t₁, P γ (-γ) t₂} with hV
  have hmemV : ∀ z ∈ V, z = P 0 0 0 ∨ z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 1 ∨
      z = P (-β) β t₁ ∨ z = P γ (-γ) t₂ := by
    intro z hz; simpa [hV] using hz
  set d := cmb f₁ f₂ f₃ (-1) 1 0 with hd
  set u₀ := σ • d with hu₀
  have hd0 : d ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ h0).2.1
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := smul_ne_zero hσ0 hd0
  have hs0 : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd0
  have hdd : ⟪d, d⟫ = -⟪f₁, d⟫ + ⟪f₂, d⟫ := by
    have e : ⟪d, d⟫ = ⟪cmb f₁ f₂ f₃ (-1) 1 0, d⟫ := rfl
    rw [e]; simp only [cmb, inner_add_left, real_inner_smul_left]; ring
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪A, u₀⟫ + σ * (a * ⟪f₁, d⟫ + b * ⟪f₂, d⟫ + c * ⟪f₃, d⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, real_inner_smul_right]; ring
  rcases t4eq_nws (p2 := ⟪f₂, d⟫) (p3 := ⟪f₃, d⟫) hs0 hγ hβ ht₁ ht₁' ht₂ ht₂' with h₁ | h₂
  · -- the cycle `(C, A, K₂, T)`
    have hQ : NWS4 fun i => ⟪quad (P 0 1 0) (P 0 0 0) (P γ (-γ) t₂) (P 0 0 1) i, u₀⟫ := by
      have := h₁.affine ⟪A, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> (try simp only [hdd]) <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ 0 (-1) (1 / 2)) hu₀0
      (quad (P 0 1 0) (P 0 0 0) (P γ (-γ) t₂) (P 0 0 1)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
  · -- the cycle `(B, A, K₁, T)`
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 0 0) (P (-β) β t₁) (P 0 0 1) i, u₀⟫ := by
      have := h₂.affine ⟪A, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> (try simp only [hdd]) <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ 0 1 (-1 / 2)) hu₀0
      (quad (P 1 0 0) (P 0 0 0) (P (-β) β t₁) (P 0 0 1)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hβ hγ ht₁ ht₂ h1 h2 Q1 Q2; linarith)

/-- **Theorem 8.3.**  Every T4 is Rupert. -/
theorem isRupert_T4 {A B C T K₁ K₂ : ℝ³} (h : IsT4 A B C T K₁ K₂) :
    IsRupert {A, B, C, T, K₁, K₂} := by
  obtain ⟨a₁, β₁, c₁, t₁, a₂, b₂, γ₂, t₂, ha₁, hβ₁, hc₁, ht₁, ha₂, hb₂, hγ₂, ht₂, hs₁, hs₂,
    hcop, hK₁, hK₂⟩ := h.exists_normalForm
  have hΔ : det3 (B - A) (C - A) (T - A) ≠ 0 := by
    intro h0
    exact not_coplanar_of_affineIndependent h.affineIndependent (coplanar_of_det4_eq_zero h0)
  have eK₁ : K₁ = A + cmb (B - A) (C - A) (T - A) (-β₁) c₁ t₁ := by
    rw [hK₁, show a₁ = 1 + β₁ - c₁ - t₁ by linarith]; simp only [cmb]; module
  have eK₂ : K₂ = A + cmb (B - A) (C - A) (T - A) b₂ (-γ₂) t₂ := by
    rw [hK₂, show a₂ = 1 - b₂ + γ₂ - t₂ by linarith]; simp only [cmb]; module
  rcases lt_trichotomy c₁ β₁ with hx | hx | hx
  · -- `x < 1`
    set y := β₁ / c₁
    have hy : 1 < y := (one_lt_div hc₁).mpr hx
    have hβy : β₁ = y * c₁ := by simp only [y]; field_simp
    have hby : b₂ = y * γ₂ := by
      simp only [y]; field_simp; linarith
    rw [eK₁, eK₂, hβy, hby]
    exact isRupert_T4_core hΔ hc₁ ht₁ hγ₂ ht₂ hy (by nlinarith) (by nlinarith)
  · -- `x = y = 1`
    subst hx
    have hb : b₂ = γ₂ := (mul_left_cancel₀ hc₁.ne' hcop).symm
    rw [eK₁, eK₂, hb]
    exact isRupert_T4_eq hΔ hc₁ ht₁ (by linarith) hγ₂ ht₂ (by linarith)
  · -- `x > 1`: exchange `B ↔ C`, `K₁ ↔ K₂`
    have hΔ' : det3 (C - A) (B - A) (T - A) ≠ 0 := by
      intro h0; apply hΔ
      have : det3 (C - A) (B - A) (T - A) = -det3 (B - A) (C - A) (T - A) := by
        simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring
      linarith
    have hbγ : b₂ < γ₂ := by
      by_contra hc; push Not at hc
      have := mul_le_mul_of_nonneg_left hc hc₁.le
      nlinarith
    set y := γ₂ / b₂
    have hy : 1 < y := (one_lt_div hb₂).mpr hbγ
    have hγy : γ₂ = y * b₂ := by simp only [y]; field_simp
    have hcy : c₁ = y * β₁ := by
      simp only [y]; field_simp; linarith
    have e1 : K₂ = A + cmb (C - A) (B - A) (T - A) (-(y * b₂)) b₂ t₂ := by
      rw [eK₂, ← hγy]; simp only [cmb]; module
    have e2 : K₁ = A + cmb (C - A) (B - A) (T - A) (y * β₁) (-β₁) t₁ := by
      rw [eK₁, ← hcy]; simp only [cmb]; module
    have := isRupert_T4_core hΔ' hb₂ ht₂ hβ₁ ht₁ hy (by nlinarith) (by nlinarith)
    rw [← e1, ← e2] at this
    convert this using 1
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

end Minimality

end RupertMinimality
