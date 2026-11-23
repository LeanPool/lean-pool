/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.KohnSham.Iteration

/-!
# Moreau–Yosida envelopes of functionals on a compact convex domain

For a convex, lower semicontinuous `f` on a nonempty compact convex set `D` (extended by `+∞`
outside `D`) and `ε > 0`:

* `prox D f ε x` minimises `f q + ‖x - q‖² / (2ε)` over `q ∈ D` (`prox_spec`);
* `myEnv D f ε x = f (prox x) + ‖x - prox x‖² / (2ε)` is the Moreau envelope
  `inf_q [f q + ‖x-q‖²/(2ε)]`;
* `myGrad D f ε x = ε⁻¹ (x - prox x)` is its gradient, in the sense of `IsMYSmooth`
  (`isMYSmooth_myEnv`);
* the proximal points are bounded and the sublevel sets of `myEnv + ⟪w,·⟫` are bounded
  (`myEnv_sublevel_bounded`), the remaining hypotheses of the MYKSODA theorem.
-/

@[expose] public section

open RealInnerProductSpace

namespace DFT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section MY

variable (D : Set E) (f : E → ℝ) (ε : ℝ)

open Classical in
/-- The proximal point (a minimiser of `f q + ‖x - q‖²/(2ε)` over `D`, when one exists). -/
noncomputable def prox (x : E) : E :=
  if h : ∃ p ∈ D, ∀ q ∈ D, f p + ‖x - p‖ ^ 2 / (2 * ε) ≤ f q + ‖x - q‖ ^ 2 / (2 * ε) then h.choose
  else x

/-- The Moreau envelope. -/
noncomputable def myEnv (x : E) : ℝ := f (prox D f ε x) + ‖x - prox D f ε x‖ ^ 2 / (2 * ε)

/-- Its gradient. -/
noncomputable def myGrad (x : E) : E := ε⁻¹ • (x - prox D f ε x)

variable {D f ε}

omit [InnerProductSpace ℝ E] in
lemma prox_spec (hD : IsCompact D) (hne : D.Nonempty) (hf : LowerSemicontinuousOn f D) (x : E) :
    prox D f ε x ∈ D ∧ ∀ q ∈ D, myEnv D f ε x ≤ f q + ‖x - q‖ ^ 2 / (2 * ε) := by
  have hex : ∃ p ∈ D, ∀ q ∈ D, f p + ‖x - p‖ ^ 2 / (2 * ε) ≤ f q + ‖x - q‖ ^ 2 / (2 * ε) := by
    have hl : LowerSemicontinuousOn (fun q => f q + ‖x - q‖ ^ 2 / (2 * ε)) D :=
      hf.add (Continuous.continuousOn (by fun_prop)).lowerSemicontinuousOn
    obtain ⟨p, hp, hmin⟩ := hl.exists_isMinOn hne hD
    exact ⟨p, hp, fun q hq => hmin hq⟩
  unfold myEnv prox
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- `A + t C ≥ 0` for all small `t > 0` forces `A ≥ 0`. -/
lemma nonneg_of_forall_small {A C : ℝ} (hC : 0 ≤ C) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * C) :
    0 ≤ A := by
  by_contra hA
  push Not at hA
  set t := min 1 (-A / (2 * (C + 1)))
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ -A / (2 * (C + 1)) := min_le_right _ _
  have h1 := h t ht0 (min_le_left _ _)
  have h2 : t * C ≤ -A / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right ht1 hC
  have h3 : -A / (2 * (C + 1)) * C ≤ -A / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- Variational inequality of the proximal point. -/
lemma prox_vi (hD : IsCompact D) (hne : D.Nonempty) (hDc : Convex ℝ D) (hfc : ConvexOn ℝ D f)
    (hf : LowerSemicontinuousOn f D) (hε : 0 < ε) (x : E) {q : E} (hq : q ∈ D) :
    f (prox D f ε x) + ε⁻¹ * ⟪x - prox D f ε x, q - prox D f ε x⟫ ≤ f q := by
  obtain ⟨hp, hmin⟩ := prox_spec (ε := ε) hD hne hf x
  set p := prox D f ε x
  set b := x - p
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ (f q - f p - ε⁻¹ * ⟪b, q - p⟫) + t * (‖q - p‖ ^ 2 / (2 * ε)) := by
    intro t ht0 ht1
    have hpt : (1 - t) • p + t • q ∈ D := hDc hp hq (by linarith) ht0.le (by ring)
    have hconv := hfc.2 hp hq (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at hconv
    have h1 := hmin _ hpt
    rw [show myEnv D f ε x = f p + ‖b‖ ^ 2 / (2 * ε) from rfl] at h1
    have e : x - ((1 - t) • p + t • q) = b - t • (q - p) := by
      simp only [b, sub_smul, one_smul, smul_sub]; abel
    rw [e, norm_sub_sq_real b (t • (q - p)), norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
        inner_smul_right] at h1
    have h2 : 0 ≤ t * ((f q - f p - ε⁻¹ * ⟪b, q - p⟫) + t * (‖q - p‖ ^ 2 / (2 * ε))) := by
      have e2 : t * ((f q - f p - ε⁻¹ * ⟪b, q - p⟫) + t * (‖q - p‖ ^ 2 / (2 * ε))) =
          (1 - t) * f p + t * f q + (‖b‖ ^ 2 - 2 * (t * ⟪b, q - p⟫) + (t * ‖q - p‖) ^ 2) / (2 * ε)
            - (f p + ‖b‖ ^ 2 / (2 * ε)) := by
        field_simp; ring
      rw [e2]; linarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp h2
  have := nonneg_of_forall_small (by positivity) key
  linarith

/-- **The Moreau envelope is `IsMYSmooth`.** -/
theorem isMYSmooth_myEnv (hD : IsCompact D) (hne : D.Nonempty) (hDc : Convex ℝ D)
    (hfc : ConvexOn ℝ D f)
    (hf : LowerSemicontinuousOn f D) (hε : 0 < ε) : IsMYSmooth ε (myEnv D f ε) (myGrad D f ε) where
  lower x y := by
    set p := prox D f ε x
    set q := prox D f ε y
    have hvi := prox_vi hD hne hDc hfc hf hε x (prox_spec (ε := ε) hD hne hf y).1
    set b := x - p
    set u := y - q
    have hqp : q - p = (y - x) - u + b := by simp only [u, b]; abel
    have hT : 0 ≤ ⟪b, q - p⟫ - ⟪b, y - x⟫ + ‖u‖ ^ 2 / 2 - ‖b‖ ^ 2 / 2 := by
      rw [hqp, inner_add_right, inner_sub_right, real_inner_self_eq_norm_sq]
      have := norm_sub_sq_real u b
      rw [real_inner_comm] at this
      nlinarith [sq_nonneg ‖u - b‖]
    have e : f p + ε⁻¹ * ⟪b,
        q - p⟫ + ‖u‖ ^ 2 / (2 * ε) - (f p + ‖b‖ ^ 2 / (2 * ε) + ε⁻¹ * ⟪b, y - x⟫) =
        ε⁻¹ * (⟪b, q - p⟫ - ⟪b, y - x⟫ + ‖u‖ ^ 2 / 2 - ‖b‖ ^ 2 / 2) := by
      field_simp; ring
    have := mul_nonneg (inv_nonneg.mpr hε.le) hT
    unfold myEnv myGrad
    rw [real_inner_smul_left]
    linarith
  upper x y := by
    set p := prox D f ε x
    have h1 := (prox_spec (ε := ε) hD hne hf y).2 p (prox_spec (ε := ε) hD hne hf x).1
    have e : y - p = (y - x) + (x - p) := by abel
    rw [e, norm_add_sq_real] at h1
    rw [show myEnv D f ε x = f p + ‖x - p‖ ^ 2 / (2 * ε) from rfl]
    unfold myGrad
    rw [real_inner_smul_left, real_inner_comm]
    have e2 : (‖y - x‖ ^ 2 + 2 * ⟪y - x, x - p⟫ + ‖x - p‖ ^ 2) / (2 * ε) =
        ‖x - p‖ ^ 2 / (2 * ε) + ε⁻¹ * ⟪y - x, x - p⟫ + ‖y - x‖ ^ 2 / (2 * ε) := by
      field_simp; ring
    linarith

/-- The proximal points `y - ε ∇myEnv y` lie in `D`. -/
lemma sub_smul_myGrad (hε : 0 < ε) (y : E) : y - ε • myGrad D f ε y = prox D f ε y := by
  unfold myGrad
  rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul, sub_sub_cancel]

lemma myEnv_prox_bounded (hD : IsCompact D) (hne : D.Nonempty) (hf : LowerSemicontinuousOn f D)
    (hε : 0 < ε) : ∃ B, ∀ y, ‖y - ε • myGrad D f ε y‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hD.isBounded
  exact ⟨B, fun y => by rw [sub_smul_myGrad hε]; exact hB _ (prox_spec hD hne hf y).1⟩

/-- **Sublevel sets of `myEnv + ⟪w,·⟫` are bounded** (the envelope grows quadratically). -/
lemma myEnv_sublevel_bounded (hD : IsCompact D) (hne : D.Nonempty) (hf : LowerSemicontinuousOn f D)
    (hε : 0 < ε) (w : E) (c : ℝ) : ∃ R, ∀ y, myEnv D f ε y + ⟪w, y⟫ ≤ c → ‖y‖ ≤ R := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hD.isBounded
  obtain ⟨p0, hp0, hmin⟩ := hf.exists_isMinOn hne hD
  set m0 := f p0
  set K := 2 * ε * (c - m0 + ‖w‖ * B)
  refine ⟨B + (4 * ε * ‖w‖ + |K| + 1), fun y hy => ?_⟩
  obtain ⟨hp, -⟩ := prox_spec (ε := ε) hD hne hf y
  set p := prox D f ε y
  set s := ‖y - p‖
  have hpB := hB p hp
  have hys : ‖y‖ ≤ B + s := by
    calc ‖y‖ = ‖(y - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ s + ‖p‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hfp : m0 ≤ f p := hmin hp
  have hw : -(‖w‖ * (B + s)) ≤ ⟪w, y⟫ := by
    have := abs_real_inner_le_norm w y
    have : ‖w‖ * ‖y‖ ≤ ‖w‖ * (B + s) := mul_le_mul_of_nonneg_left hys (norm_nonneg w)
    linarith [neg_abs_le ⟪w, y⟫]
  unfold myEnv at hy
  have hq : s ^ 2 ≤ 2 * ε * ‖w‖ * s + K := by
    have h1 : f p + s ^ 2 / (2 * ε) - ‖w‖ * (B + s) ≤ c := by linarith
    have h2 : s ^ 2 / (2 * ε) ≤ c - m0 + ‖w‖ * B + ‖w‖ * s := by linarith
    rw [div_le_iff₀ (by positivity)] at h2
    simp only [K]; nlinarith
  have hs0 : 0 ≤ s := norm_nonneg _
  have hs : s ≤ 4 * ε * ‖w‖ + |K| + 1 := by
    by_contra hc
    push Not at hc
    have hK := le_abs_self K
    have hwε : 0 ≤ ε * ‖w‖ := by positivity
    nlinarith [abs_nonneg K]
  linarith

end MY

end DFT
