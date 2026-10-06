/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Distance-weighted absorption up to the top time

A local estimate `|g(x, s)| ≤ c₁ ρ Λ + c₂ / ρ`, valid whenever `|g| ≤ Λ` on the backward window
`B̄(x, 2ρ) × [s - ρ², s]` inside an annulus, yields a bound for `g` on every smaller annulus that
is uniform up to the top time `t = 0`. The circular term carries the small factor `ρ`; it is
absorbed with the weight `d(x) = min(|x| - a, b - |x|)`. This is the device that makes the
interior estimates of the proof of `lem:aniso:annulus` uniform up to the blow-up time.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CIV



/-- The Euclidean norm is 1-Lipschitz. -/
theorem abs_sub_vec3EuclideanNorm_le (x y : Vec3) :
    |vec3EuclideanNorm y - vec3EuclideanNorm x| ≤ vec3EuclideanNorm (y - x) := by
  have h1 : vec3EuclideanNorm y ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
    have := vec3EuclideanNorm_add_le (y - x) x
    rwa [sub_add_cancel] at this
  have h2 : vec3EuclideanNorm x ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm y := by
    have := vec3EuclideanNorm_add_le (x - y) y
    rw [sub_add_cancel] at this
    have e : vec3EuclideanNorm (x - y) = vec3EuclideanNorm (y - x) := by
      rw [← vec3EuclideanNorm_neg, neg_sub]
    linarith only [this, e]
  rw [abs_le]
  constructor <;> linarith only [h1, h2]

/-- A closed Euclidean annulus times a compact time interval is compact. -/
theorem isCompact_closedAnnulus_prod_Icc (a b t t' : ℝ) :
    IsCompact ({x : Vec3 | a ≤ vec3EuclideanNorm x ∧ vec3EuclideanNorm x ≤ b} ×ˢ Icc t t') := by
  refine IsCompact.prod ?_ isCompact_Icc
  have hK : IsCompact (closure (vec3Ball 0 (|b| + 1))) :=
    isCompact_closure_vec3Ball (by positivity)
  refine hK.of_isClosed_subset ?_ (fun x hx => ?_)
  · exact (isClosed_le continuous_const continuous_vec3EuclideanNorm).inter
      (isClosed_le continuous_vec3EuclideanNorm continuous_const)
  · rw [closure_vec3Ball (by positivity)]
    show vec3EuclideanNorm (x - 0) ≤ |b| + 1
    rw [sub_zero]
    linarith only [hx.2, le_abs_self b]

/-- Distance-weighted absorption: a local circular estimate with a small factor `ρ` on backward
windows gives a bound on every smaller annulus, uniform up to the top time. -/
theorem exists_bound_of_weighted_absorption {g : ParabolicPoint → ℝ} {a b a' b' t₁ τ c₁ c₂ : ℝ}
    (hab : 0 ≤ a ∧ a < a' ∧ a' < b' ∧ b' < b ∧ b ≤ 1) (hτ : 0 < τ) (ht₁ : t₁ < 0)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcont : ContinuousOn (fun z : Vec3 × ℝ => g z)
      ({x | a ≤ vec3EuclideanNorm x ∧ vec3EuclideanNorm x ≤ b} ×ˢ Ico (t₁ - τ) 0))
    (hlocal : ∀ (x : Vec3) (s ρ Λ : ℝ), a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      t₁ ≤ s → s < 0 → 0 < ρ → ρ ≤ 1 → ρ ^ 2 ≤ τ →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ 2 * ρ →
        a < vec3EuclideanNorm y ∧ vec3EuclideanNorm y < b) →
      (∀ (y : Vec3) (s' : ℝ), vec3EuclideanNorm (y - x) ≤ 2 * ρ → s - ρ ^ 2 ≤ s' → s' ≤ s →
        |g (y, s')| ≤ Λ) →
      |g (x, s)| ≤ c₁ * ρ * Λ + c₂ / ρ) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s, t₁ ≤ s → s < 0 → |g (x, s)| ≤ K := by
  obtain ⟨ha0, haa', ha'b', hb'b, hb1⟩ := hab
  set A₀ : Set Vec3 := {x | a ≤ vec3EuclideanNorm x ∧ vec3EuclideanNorm x ≤ b} with hA₀
  -- the collar bound
  obtain ⟨E₀, hE₀⟩ := (isCompact_closedAnnulus_prod_Icc a b (t₁ - τ)
    t₁).exists_bound_of_continuousOn
    (hcont.mono (prod_mono subset_rfl (fun t ht => ⟨ht.1, by linarith only [ht.2, ht₁]⟩)))
  set E : ℝ := max E₀ 0 with hE
  have hE0 : 0 ≤ E := le_max_right _ _
  -- the weight and the scale cap
  set d : Vec3 → ℝ := fun x => min (vec3EuclideanNorm x - a) (b - vec3EuclideanNorm x) with hd
  set ρ₀ : ℝ := min 1 (min (Real.sqrt τ) (1 / (4 * c₁ + 1))) with hρ₀
  have hρ₀pos : 0 < ρ₀ := lt_min one_pos (lt_min (Real.sqrt_pos.mpr hτ) (by positivity))
  have hρ₀1 : ρ₀ ≤ 1 := min_le_left _ _
  have hρ₀τ : ρ₀ ^ 2 ≤ τ := by
    have h1 : ρ₀ ≤ Real.sqrt τ := (min_le_right _ _).trans (min_le_left _ _)
    calc ρ₀ ^ 2 ≤ Real.sqrt τ ^ 2 := pow_le_pow_left₀ hρ₀pos.le h1 2
      _ = τ := Real.sq_sqrt hτ.le
  have hρ₀c : 4 * c₁ * ρ₀ ≤ 1 := by
    have h1 : ρ₀ ≤ 1 / (4 * c₁ + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : (4 * c₁ + 1) * ρ₀ ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1
      linarith only [h1]
    nlinarith only [h2, hρ₀pos]
  set A : ℝ := c₁ * E + c₂ * (4 + 1 / ρ₀) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the main weighted bound on each truncated slab
  have hmain : ∀ T₂, t₁ ≤ T₂ → T₂ < 0 → ∀ x : Vec3, a < vec3EuclideanNorm x →
      vec3EuclideanNorm x < b → ∀ s, t₁ ≤ s → s ≤ T₂ → d x * |g (x, s)| ≤ 2 * A := by
    intro T₂ hT₁ hT₂
    obtain ⟨Λ₀', hΛ₀'⟩ := (isCompact_closedAnnulus_prod_Icc a b (t₁ - τ) T₂
      ).exists_bound_of_continuousOn
      (hcont.mono (prod_mono subset_rfl (fun t ht => ⟨ht.1, by linarith only [ht.2, hT₂]⟩)))
    set Λ₀ : ℝ := max Λ₀' 0 with hΛ₀
    -- weight facts
    have hdle : ∀ x : Vec3, d x ≤ 1 := fun x =>
      (min_le_right _ _).trans (by linarith only [hb1, vec3EuclideanNorm_nonneg x, ha0])
    have hdpos : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b → 0 < d x :=
      fun x h1 h2 => lt_min (by linarith only [h1]) (by linarith only [h2])
    have hdlip : ∀ x y : Vec3, d x - vec3EuclideanNorm (y - x) ≤ d y := by
      intro x y
      have hl := abs_le.mp (abs_sub_vec3EuclideanNorm_le x y)
      simp only [hd]
      refine le_min ?_ ?_
      · linarith only [min_le_left (vec3EuclideanNorm x - a) (b - vec3EuclideanNorm x), hl.1]
      · linarith only [min_le_right (vec3EuclideanNorm x - a) (b - vec3EuclideanNorm x), hl.2]
    -- one absorption step
    have hstep : ∀ Λ : ℝ, 0 ≤ Λ → (∀ x : Vec3, a < vec3EuclideanNorm x →
        vec3EuclideanNorm x < b → ∀ s, t₁ ≤ s → s ≤ T₂ → d x * |g (x, s)| ≤ Λ) →
        ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b → ∀ s, t₁ ≤ s → s ≤ T₂ →
          d x * |g (x, s)| ≤ Λ / 2 + A := by
      intro Λ hΛ hP x hx1 hx2 s hs1 hs2
      have hdx := hdpos x hx1 hx2
      set ρ : ℝ := min (d x / 4) ρ₀ with hρ
      have hρpos : 0 < ρ := lt_min (by positivity) hρ₀pos
      have hρd : ρ ≤ d x / 4 := min_le_left _ _
      have hρρ₀ : ρ ≤ ρ₀ := min_le_right _ _
      have hρ1 : ρ ≤ 1 := hρρ₀.trans hρ₀1
      have hρτ : ρ ^ 2 ≤ τ := (pow_le_pow_left₀ hρpos.le hρρ₀ 2).trans hρ₀τ
      have hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ 2 * ρ →
          a < vec3EuclideanNorm y ∧ vec3EuclideanNorm y < b := by
        intro y hy
        have hl := abs_le.mp (abs_sub_vec3EuclideanNorm_le x y)
        have h1 := min_le_left (vec3EuclideanNorm x - a) (b - vec3EuclideanNorm x)
        have h2 := min_le_right (vec3EuclideanNorm x - a) (b - vec3EuclideanNorm x)
        constructor
        · linarith only [hl.1, hy, hρd, h1, hdx]
        · linarith only [hl.2, hy, hρd, h2, hdx]
      have hwin : ∀ (y : Vec3) (s' : ℝ), vec3EuclideanNorm (y - x) ≤ 2 * ρ → s - ρ ^ 2 ≤ s' →
          s' ≤ s → |g (y, s')| ≤ 2 * Λ / d x + E := by
        intro y s' hy hs'1 hs'2
        obtain ⟨hy1, hy2⟩ := hball y hy
        by_cases hs't : t₁ ≤ s'
        · have hdy : d x / 2 ≤ d y := by
            have := hdlip x y
            linarith only [this, hy, hρd]
          have hdypos : 0 < d y := by linarith only [hdy, hdx]
          have hPy := hP y hy1 hy2 s' hs't (hs'2.trans hs2)
          have hgy : |g (y, s')| ≤ Λ / d y := by
            rw [le_div_iff₀ hdypos]
            linarith only [hPy]
          have : Λ / d y ≤ 2 * Λ / d x := by
            rw [div_le_div_iff₀ hdypos hdx]
            nlinarith only [hdy, hΛ]
          linarith only [hgy, this, hE0]
        · have hmem : ((y, s') : Vec3 × ℝ) ∈ A₀ ×ˢ Icc (t₁ - τ) t₁ :=
            ⟨⟨hy1.le, hy2.le⟩, by linarith only [hs'1, hρτ, hs1], (lt_of_not_ge hs't).le⟩
          have := hE₀ _ hmem
          rw [Real.norm_eq_abs] at this
          exact le_add_of_nonneg_of_le (by positivity) (this.trans (le_max_left _ _))
      have hloc := hlocal x s ρ (2 * Λ / d x + E) hx1 hx2 hs1 (lt_of_le_of_lt hs2 hT₂) hρpos
        hρ1 hρτ hball hwin
      -- multiply by the weight
      have hdρ : d x / ρ ≤ 4 + 1 / ρ₀ := by
        rcases le_total (d x / 4) ρ₀ with h | h
        · have : ρ = d x / 4 := min_eq_left h
          rw [this]
          have : d x / (d x / 4) = 4 := by field_simp
          rw [this]
          have : 0 ≤ 1 / ρ₀ := by positivity
          linarith only [this]
        · have : ρ = ρ₀ := min_eq_right h
          rw [this, div_eq_mul_one_div]
          have : 0 ≤ 1 / ρ₀ := by positivity
          nlinarith only [hdle x, this, hdx]
      calc d x * |g (x, s)| ≤ d x * (c₁ * ρ * (2 * Λ / d x + E) + c₂ / ρ) :=
            mul_le_mul_of_nonneg_left hloc hdx.le
        _ = 2 * c₁ * ρ * Λ + c₁ * (ρ * d x) * E + c₂ * (d x / ρ) := by
            field_simp
        _ ≤ Λ / 2 + A := by
            have h1 : 2 * c₁ * ρ * Λ ≤ Λ / 2 := by
              have : 4 * c₁ * ρ ≤ 1 := by nlinarith only [hρ₀c, hρρ₀, hc₁]
              nlinarith only [this, hΛ]
            have h2 : c₁ * (ρ * d x) * E ≤ c₁ * E := by
              have : ρ * d x ≤ 1 := by nlinarith only [hρ1, hdle x, hρpos, hdx]
              have := mul_le_mul_of_nonneg_left this hc₁
              nlinarith only [this, hE0, hc₁]
            have h3 : c₂ * (d x / ρ) ≤ c₂ * (4 + 1 / ρ₀) :=
              mul_le_mul_of_nonneg_left hdρ hc₂
            linarith only [h1, h2, h3]
    -- iterate
    have hiter : ∀ n : ℕ, ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
        ∀ s, t₁ ≤ s → s ≤ T₂ → d x * |g (x, s)| ≤ (1 / 2) ^ n * Λ₀ + 2 * A := by
      intro n
      induction n with
      | zero =>
        intro x hx1 hx2 s hs1 hs2
        have hmem : ((x, s) : Vec3 × ℝ) ∈ A₀ ×ˢ Icc (t₁ - τ) T₂ :=
          ⟨⟨hx1.le, hx2.le⟩, by linarith only [hs1, hτ], hs2⟩
        have hg := hΛ₀' _ hmem
        rw [Real.norm_eq_abs] at hg
        have hdx := hdpos x hx1 hx2
        have : d x * |g (x, s)| ≤ 1 * Λ₀ :=
          mul_le_mul (hdle x) (hg.trans (le_max_left _ _)) (abs_nonneg _) zero_le_one
        simp only [pow_zero]
        linarith only [this, hA0]
      | succ m ih =>
        intro x hx1 hx2 s hs1 hs2
        have h := hstep _ (by positivity) ih x hx1 hx2 s hs1 hs2
        calc d x * |g (x, s)| ≤ ((1 / 2) ^ m * Λ₀ + 2 * A) / 2 + A := h
          _ = (1 / 2) ^ (m + 1) * Λ₀ + 2 * A := by ring
    intro x hx1 hx2 s hs1 hs2
    have htend : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * Λ₀ + 2 * A) atTop (𝓝 (0 * Λ₀ + 2 * A)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const Λ₀).add_const _
    rw [zero_mul, zero_add] at htend
    exact ge_of_tendsto' htend (fun n => hiter n x hx1 hx2 s hs1 hs2)
  -- conclusion on the inner annulus
  set δ : ℝ := min (a' - a) (b - b') with hδ
  have hδpos : 0 < δ := lt_min (by linarith only [haa']) (by linarith only [hb'b])
  refine ⟨2 * A / δ, fun x hx1 hx2 s hs1 hs2 => ?_⟩
  have hxa : a < vec3EuclideanNorm x := by linarith only [hx1, haa']
  have hxb : vec3EuclideanNorm x < b := by linarith only [hx2, hb'b]
  have hdx : δ ≤ d x := by
    simp only [hd, hδ]
    exact min_le_min (by linarith only [hx1]) (by linarith only [hx2])
  have hm := hmain s hs1 hs2 x hxa hxb s hs1 le_rfl
  rw [le_div_iff₀ hδpos]
  nlinarith only [hm, hdx, abs_nonneg (g (x, s))]

end CIV
