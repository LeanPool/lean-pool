/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Tilt
public import LeanPool.RupertMinimality.Minimality.Octahedron

/-! # L8 Shapes -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 8.2 (every T5) and tools for Theorems 8.3, 8.4

Shapes are given by their facet structures and put in a normal form in an
affine frame `cmb f₁ f₂ f₃`; every determinant test of Lemma 8.0 is then a
coefficient determinant (`det3_cmb`) times the frame's orientation.  The views
are tilted off a direction parallel to an edge or face; one of two or three
predicted cycles is robustly unimodal (`NWS4` for 4-cycles), and
Corollary 8.0′ (with Theorem 7.5) gives the passage.  T4 and T3 are in
`L8T4.lean` and `L8T3.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Tools: affine frames, 4-cycles -/

/-- The combination `a f₁ + b f₂ + c f₃`. -/
def cmb (f₁ f₂ f₃ : ℝ³) (a b c : ℝ) : ℝ³ := a • f₁ + b • f₂ + c • f₃

theorem cmb_sub (f₁ f₂ f₃ : ℝ³) (a b c a' b' c' : ℝ) :
    cmb f₁ f₂ f₃ a b c - cmb f₁ f₂ f₃ a' b' c' = cmb f₁ f₂ f₃ (a - a') (b - b') (c - c') := by
  simp only [cmb]; module

theorem add_cmb_sub (E f₁ f₂ f₃ : ℝ³) (a b c a' b' c' : ℝ) :
    (E + cmb f₁ f₂ f₃ a b c) - (E + cmb f₁ f₂ f₃ a' b' c') =
      cmb f₁ f₂ f₃ (a - a') (b - b') (c - c') := by
  rw [add_sub_add_left_eq_sub, cmb_sub]

/-- The determinant of three coefficient rows. -/
def detc (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : ℝ) : ℝ :=
  a₁ * (b₂ * c₃ - b₃ * c₂) - a₂ * (b₁ * c₃ - b₃ * c₁) + a₃ * (b₁ * c₂ - b₂ * c₁)

theorem det3_cmb (f₁ f₂ f₃ : ℝ³) (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ σ : ℝ) :
    det3 (cmb f₁ f₂ f₃ a₁ a₂ a₃) (cmb f₁ f₂ f₃ b₁ b₂ b₃) (σ • cmb f₁ f₂ f₃ c₁ c₂ c₃) =
      detc a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ * (σ * det3 f₁ f₂ f₃) := by
  simp only [det3, cmb, detc, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  simp
  ring

/-- Coordinates in a frame with nonzero determinant are unique. -/
theorem cmb_eq_zero {f₁ f₂ f₃ : ℝ³} (hΔ : det3 f₁ f₂ f₃ ≠ 0) {a b c : ℝ}
    (h : cmb f₁ f₂ f₃ a b c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have z : ∀ x y : ℝ³, det3 0 x y = 0 := fun x y => by
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  have e1 := det3_cmb f₁ f₂ f₃ a b c 0 1 0 0 0 1 1
  have e2 := det3_cmb f₁ f₂ f₃ a b c 1 0 0 0 0 1 1
  have e3 := det3_cmb f₁ f₂ f₃ a b c 1 0 0 0 1 0 1
  rw [h, z] at e1 e2 e3
  simp only [detc, one_mul] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · have : a * det3 f₁ f₂ f₃ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hΔ
  · have : b * det3 f₁ f₂ f₃ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hΔ
  · have : c * det3 f₁ f₂ f₃ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hΔ

theorem tiltSign_pos {a b u v : ℝ³} {P₀ D : ℝ} (hD : 0 < D) (hu : det3 a b u = P₀ * D)
    (h : 0 < P₀) : TiltSign a b u v := Or.inl (by rw [hu]; exact mul_pos h hD)

theorem tiltSign_zero {a b u v : ℝ³} {P₀ P₁ D : ℝ} (hD : 0 < D) (hu : det3 a b u = P₀ * D)
    (hv : det3 a b v = P₁ * D) (h₀ : P₀ = 0) (h₁ : 0 < P₁) : TiltSign a b u v :=
  Or.inr ⟨by rw [hu, h₀, zero_mul], by rw [hv]; exact mul_pos h₁ hD⟩

section quad
variable {α : Type*} (p₀ p₁ p₂ p₃ : α)
theorem quad_0 : quad p₀ p₁ p₂ p₃ 0 = p₀ := rfl
theorem quad_1 : quad p₀ p₁ p₂ p₃ 1 = p₁ := rfl
theorem quad_2 : quad p₀ p₁ p₂ p₃ 2 = p₂ := rfl
theorem quad_3 : quad p₀ p₁ p₂ p₃ 3 = p₃ := rfl
end quad

theorem zmod4_add_one : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧
    (3 : ZMod 4) + 1 = 0 := by decide

theorem zmod4_pairs : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 0) ∨
    (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2) := by decide

theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

/-- The diagonals `{z₀, z₂}`, `{z₁, z₃}` of a 4-cycle are *not weakly
separated* (Corollary 8.0′). -/
def NWS4 (z : ZMod 4 → ℝ) : Prop :=
  (z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3) ∧ (z 1 < z 0 ∨ z 3 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2)

theorem isOpen_NWS4 : IsOpen {z : ZMod 4 → ℝ | NWS4 z} := by
  have hlt : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [NWS4, Set.ofPred_and, Set.ofPred_or]
  exact ((hlt 0 1).union ((hlt 0 3).union ((hlt 2 1).union (hlt 2 3)))).inter
    ((hlt 1 0).union ((hlt 3 0).union ((hlt 1 2).union (hlt 3 2))))

theorem NWS4.mul {z : ZMod 4 → ℝ} (h : NWS4 z) {t : ℝ} (ht : t ≠ 0) : NWS4 fun i => t * z i := by
  obtain ⟨h1, h2⟩ := h
  rcases lt_or_gt_of_ne ht with ht | ht
  · have key : ∀ {x y : ℝ}, x < y → t * y < t * x := fun hxy => by nlinarith
    exact ⟨by rcases h2 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))],
      by rcases h1 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))]⟩
  · have key : ∀ {x y : ℝ}, x < y → t * x < t * y := fun hxy => by nlinarith
    exact ⟨by rcases h1 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))],
      by rcases h2 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))]⟩

theorem isCyclicUnimodal_of_NWS4 {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h : NWS4 z) :
    IsCyclicUnimodal z :=
  isCyclicUnimodal_four hinj ⟨h.1, h.2, hinj.ne (by decide), hinj.ne (by decide)⟩

/-- Corollary 8.0′ for 4-cycles with the "not weakly separated" condition. -/
theorem isRupert_of_tilted_NWS4 (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0)
    (x : ZMod 4 → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (hQ : NWS4 fun i => ⟪x i, u₀⟫) : IsRupert V :=
  isRupert_of_tilted_unimodal V u₀ v hu₀ (by norm_num) x hxV hcyc hrest NWS4 isOpen_NWS4
    (fun z c hc hz => hz.mul hc.ne') hQ (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)

theorem NWS4.affine {z : ZMod 4 → ℝ} (h : NWS4 z) (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
    NWS4 fun i => c + t * z i := by
  obtain ⟨h1, h2⟩ := h.mul ht
  simp only [NWS4] at h1 h2 ⊢
  refine ⟨?_, ?_⟩ <;> [rcases h1 with h | h | h | h; rcases h2 with h | h | h | h] <;>
    simp only [add_lt_add_iff_left] <;> tauto

theorem inner_add_cmb (E f₁ f₂ f₃ d : ℝ³) (a b c : ℝ) :
    ⟪E + cmb f₁ f₂ f₃ a b c, d⟫ = ⟪E, d⟫ + (a * ⟪f₁, d⟫ + b * ⟪f₂, d⟫ + c * ⟪f₃, d⟫) := by
  simp only [cmb, inner_add_left, real_inner_smul_left]

theorem det3_pos_or_neg {Δ : ℝ} (h : Δ ≠ 0) : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * Δ := by
  rcases lt_or_gt_of_ne h with h | h
  · exact ⟨-1, Or.inr rfl, by linarith⟩
  · exact ⟨1, Or.inl rfl, by linarith⟩

/-- **T5 with `S₁S₄ ∥ S₂S₃`** (the L6 exceptions), in normal form:
`S₄ = S₁ + k (S₃ - S₂)` and `K = a₁ E - β₁ S₃ + c₁ S₂ + t₁ S₁`. -/
theorem isRupert_T5_parallel {E S₁ S₂ S₃ : ℝ³} (hΔ : det3 (S₁ - E) (S₂ - E) (S₃ - E) ≠ 0)
    {k a₁ β₁ c₁ t₁ : ℝ} (hk : 0 < k) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (_ : 0 < c₁)
    (ht₁ : 0 < t₁) (hs : a₁ - β₁ + c₁ + t₁ = 1) (hbc : β₁ < c₁) :
    IsRupert {E, S₁, S₂, S₃, S₁ + k • (S₃ - S₂), a₁ • E - β₁ • S₃ + c₁ • S₂ + t₁ • S₁} := by
  classical
  have hc₁ : 0 < c₁ := lt_trans hβ₁ hbc
  set f₁ := S₁ - E
  set f₂ := S₂ - E
  set f₃ := S₃ - E
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => E + cmb f₁ f₂ f₃ a b c with hP
  have eE : E = P 0 0 0 := by simp [hP, cmb]
  have e1 : S₁ = P 1 0 0 := by simp [hP, cmb, f₁]
  have e2 : S₂ = P 0 1 0 := by simp [hP, cmb, f₂]
  have e3 : S₃ = P 0 0 1 := by simp [hP, cmb, f₃]
  have e4 : S₁ + k • (S₃ - S₂) = P 1 (-k) k := by simp only [hP, cmb, f₁, f₂, f₃]; module
  have eK : a₁ • E - β₁ • S₃ + c₁ • S₂ + t₁ • S₁ = P t₁ c₁ (-β₁) := by
    have ha : a₁ = 1 + β₁ - c₁ - t₁ := by linarith
    simp only [hP, cmb, f₁, f₂, f₃, ha]; module
  rw [e4, eK, eE, e1, e2, e3]
  set V : Finset ℝ³ := {P 0 0 0, P 1 0 0, P 0 1 0, P 0 0 1, P 1 (-k) k, P t₁ c₁ (-β₁)} with hV
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hpos := mul_pos hk ha₁
  have hpos2 := mul_pos hk (sub_pos.2 hbc)
  have hpos3 := mul_pos hk ht₁
  have hpos4 := mul_pos hk hβ₁
  set u₀ := σ • cmb f₁ f₂ f₃ 0 (-1) 1 with hu₀
  have hu₀0 : u₀ ≠ 0 := by
    rw [hu₀]
    apply smul_ne_zero hσ0
    intro h0
    have := (cmb_eq_zero hΔ h0).2.2
    norm_num at this
  -- depths along `S₃ - S₂`
  set d := f₃ - f₂
  have hd : cmb f₁ f₂ f₃ 0 (-1) 1 = d := by simp only [cmb, d]; module
  have hs0 : 0 < ⟪d, d⟫ := by
    rw [real_inner_self_eq_norm_sq]
    have : d ≠ 0 := by
      intro h0; apply hu₀0; rw [hu₀, hd, h0, smul_zero]
    positivity
  have hz : ∀ a b c, ⟪P a b c, u₀⟫ = ⟪E, u₀⟫ + σ * (a * ⟪f₁, d⟫ + b * ⟪f₂, d⟫ + c * ⟪f₃, d⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, hd, real_inner_smul_right]; ring
  have hf3 : ⟪f₃, d⟫ = ⟪f₂, d⟫ + ⟪d, d⟫ := by
    simp only [d, inner_sub_left, inner_sub_right, real_inner_comm f₂ f₃]; ring
  have hmemV : ∀ y ∈ V, y = P 0 0 0 ∨ y = P 1 0 0 ∨ y = P 0 1 0 ∨ y = P 0 0 1 ∨
      y = P 1 (-k) k ∨ y = P t₁ c₁ (-β₁) := by
    intro y hy; simpa [hV] using hy
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ = ⟪E, u₀⟫ + σ * (a * ⟪f₁, d⟫ + b * ⟪f₂, d⟫ +
      c * (⟪f₂, d⟫ + ⟪d, d⟫)) := by
    intro a b c; rw [hz, hf3]
  have hkd := mul_pos hk hs0
  by_cases h5 : NWS4 (quad (0 : ℝ) (⟪f₁, d⟫ + k * ⟪d, d⟫) ⟪f₁, d⟫ ⟪f₂, d⟫)
  · -- the cycle `F5 = (E, S₄, S₁, S₂)`
    have hQ : NWS4 fun i => ⟪quad (P 0 0 0) (P 1 (-k) k) (P 1 0 0) (P 0 1 0) i, u₀⟫ := by
      have := h5.affine ⟪E, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (-1 / 2) 1 0) hu₀0
      (quad (P 0 0 0) (P 1 (-k) k) (P 1 0 0) (P 0 1 0)) ?_ ?_ ?_ hQ
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
              clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
              nlinarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by
              simp only [detc]
              clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
              nlinarith)
    · intro y hy hyx i
      have hx0 := hyx 0; have hx1 := hyx 1; have hx2 := hyx 2; have hx3 := hyx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV y hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
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
                clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
                nlinarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by
                simp only [detc]
                clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
                nlinarith)
  · -- otherwise `F3 = (E, S₁, S₄, S₃)` is not weakly separated
    have h3 : NWS4 (quad (0 : ℝ) ⟪f₁, d⟫ (⟪f₁, d⟫ + k * ⟪d, d⟫) (⟪f₂, d⟫ + ⟪d, d⟫)) := by
      simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at h5 ⊢
      push Not at h5
      refine ⟨?_, Or.inr (Or.inr (Or.inl (by linarith)))⟩
      have := h5 (Or.inr (Or.inr (Or.inl (by linarith))))
      exact Or.inr (Or.inl (by linarith [this.2.1]))
    have hQ : NWS4 fun i => ⟪quad (P 0 0 0) (P 1 0 0) (P 1 (-k) k) (P 0 0 1) i, u₀⟫ := by
      have := h3.affine ⟪E, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (1 / 2) (-1) 0) hu₀0
      (quad (P 0 0 0) (P 1 0 0) (P 1 (-k) k) (P 0 0 1)) ?_ ?_ ?_ hQ
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
              clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
              nlinarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by
              simp only [detc]
              clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
              nlinarith)
    · intro y hy hyx i
      have hx0 := hyx 0; have hx1 := hyx 1; have hx2 := hyx 2; have hx3 := hyx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV y hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
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
                clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
                nlinarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by
                simp only [detc]
                clear * - hk ha₁ hβ₁ hc₁ ht₁ hs hbc hpos hpos2 hpos3 hpos4
                nlinarith)

/-- **Theorem 8.2.**  Every T5 (capped square pyramid) is Rupert, including the
L6 exceptions `S₁S₄ ∥ S₂S₃`. -/
theorem isRupert_cappedSquarePyramid_all {E S₁ S₂ S₃ S₄ K : ℝ³}
    (h : IsCappedSquarePyramid E S₁ S₂ S₃ S₄ K) : IsRupert {E, S₁, S₂, S₃, S₄, K} := by
  by_cases hpar : ∀ k : ℝ, S₄ - S₁ ≠ k • (S₃ - S₂)
  · exact isRupert_cappedSquarePyramid h hpar
  push Not at hpar
  obtain ⟨k, hk⟩ := hpar
  obtain ⟨a₁, β₁, c₁, t₁, b₂, γ₂, t₂, ha₁, hβ₁, hc₁, ht₁, hb₂, hγ₂, ht₂, hs₁, hs₂, hconv,
    hK, hS⟩ := h.exists_normalForm
  have hΔ : det3 (S₁ - E) (S₂ - E) (S₃ - E) ≠ 0 := by
    intro h0
    apply not_coplanar_of_affineIndependent h.affineIndependent
    have hc := coplanar_of_det4_eq_zero (a := E) (b := S₁) (c := S₂) (d := S₃) h0
    convert hc using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  -- compare the two expressions of `S₄`
  set f₁ := S₁ - E
  set f₂ := S₂ - E
  set f₃ := S₃ - E
  have hrel : cmb f₁ f₂ f₃ (γ₂ - b₂) (k - γ₂) (b₂ - k) = 0 := by
    have ht : t₂ = 1 - b₂ + γ₂ := by linarith
    have : S₄ - S₁ - k • (S₃ - S₂) = 0 := by rw [hk, sub_self]
    rw [hS, ht] at this
    rw [← this]; simp only [cmb, f₁, f₂, f₃]; module
  obtain ⟨hγb, hkγ, -⟩ := cmb_eq_zero hΔ hrel
  have hb : b₂ = k := by linarith
  have hγ : γ₂ = k := by linarith
  have ht : t₂ = 1 := by linarith
  subst hb
  have hbc : β₁ < c₁ := by rw [hγ] at hconv; exact lt_of_mul_lt_mul_right hconv hb₂.le
  have hS' : S₄ = S₁ + b₂ • (S₃ - S₂) := by rw [← hk]; abel
  rw [hS', hK]
  exact isRupert_T5_parallel hΔ hb₂ ha₁ hβ₁ hc₁ ht₁ hs₁ hbc

end Minimality

end RupertMinimality
