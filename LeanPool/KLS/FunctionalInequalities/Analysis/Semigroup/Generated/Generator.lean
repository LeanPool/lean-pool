/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Laws
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Exponential.MeanValue

/-!
# Generator of the strong Yosida semigroup

Let `T` be a closed densely defined operator between real Hilbert spaces.
`Generated.yosida_converges` makes convergence of the Yosida exponentials uniform
on each compact nonnegative time interval. `yosida_error_le` gives the quantitative
estimate on the domain of `T†T`.

For `f ∈ D(T†T)`, `Generated.generator_limit` identifies the right derivative at zero
with `-T†T f`; `generator_error_le` is its quantitative remainder bound.
The semigroup laws belong to `Generated/Laws.lean` and the exponential mean-value
estimate to `Exponential/MeanValue.lean`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

/-- A real squeeze: if `a ≤ b + η` for every `η > 0` then `a ≤ b`.  Used to pass from an estimate
that still carries an arbitrarily small error (coming from a limit taken at a fixed point) to the
clean inequality. -/
theorem le_of_forall_pos_add_le {a b : ℝ} (h : ∀ η : ℝ, 0 < η → a ≤ b + η) : a ≤ b := by
  by_contra hc
  rw [not_le] at hc
  have := h ((a - b) / 2) (by linarith)
  linarith

/-- The triangle inequality in the shape used repeatedly below: `‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖`. -/
theorem norm_sub_le_add_norm_sub {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  simpa using norm_add_le (x - y) (y - z)

section Generator

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

namespace Generated

/--
**the generator right derivative on `D(T†T)`.** For `b ∈ D(T†T)`, `0 ≤ t` and `ε > 0` there is `δ >
0` such that for
every `0 < s < δ` **and every `τ ∈ [0, t]` simultaneously**

`‖exp (-τ • L_s) b - P_τ b‖ ≤ ε`.

The point is the uniformity in `τ`: the adjoint-product identification convergence
`Generated.yosida_limit` is a pointwise
statement at a fixed time, whereas the bound here has a single `δ` for the whole interval.

Proof: `norm_exp_neg_smul_sub_le` bounds `‖exp (-τ • L_s) b - exp (-τ • L_r) b‖` by
`τ ‖L_s b - L_r b‖ ≤ t ‖L_s b - L_r b‖`, and `exists_delta_norm_yosida_sub_adjointComp_lt` makes
`‖L_s b - T†T b‖ < ε / (2 (t + 1))` for `s < δ`; letting `r ↓ 0` at the fixed `τ`
through `Generated.yosida_limit` and squeezing removes the auxiliary parameter. -/
theorem yosida_error_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (b : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ {s : ℝ} (hs : 0 < s),
          s < δ →
            ∀ τ ∈ Set.Icc 0 t,
              ‖NormedSpace.exp (-τ • yosida T hT hs) (b : H₀) -
                    Generated.apply T hT hd τ (b : H₀)‖ ≤
                ε := by
  have htp : (0 : ℝ) < t + 1 := by linarith
  obtain ⟨δ, hδ, hY5⟩ :=
    exists_delta_norm_yosida_sub_adjointComp_lt T hT hd b
      (show (0 : ℝ) < ε / (2 * (t + 1)) by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ τ hτ
  refine le_of_forall_pos_add_le ?_
  intro η hη
  obtain ⟨δ₂, hδ₂, hspec⟩ := Generated.yosida_limit T hT hd hτ.1 (b : H₀) hη
  obtain ⟨r, hr0, hrδ, hrδ₂⟩ : ∃ r : ℝ, 0 < r ∧ r < δ ∧ r < δ₂ := by
    have hmin : 0 < min δ δ₂ := lt_min hδ hδ₂
    have h1 : min δ δ₂ ≤ δ := min_le_left _ _
    have h2 : min δ δ₂ ≤ δ₂ := min_le_right _ _
    exact
      ⟨min δ δ₂ / 2, by linarith, by linarith, by linarith⟩
  -- The two Yosida orbits are uniformly close on `[0, t]`.
  have hY6 :
    ‖NormedSpace.exp (-τ • yosida T hT hs) (b : H₀) -
          NormedSpace.exp (-τ • yosida T hT hr0) (b : H₀)‖ ≤
      τ * ‖yosida T hT hs (b : H₀) - yosida T hT hr0 (b : H₀)‖ :=
    norm_exp_neg_smul_sub_le _ _ (yosida_nonneg T hT hs) (yosida_nonneg T hT hr0)
      (yosida_comp_comm T hT hs hr0) hτ.1 (b : H₀)
  have hdiff :
    ‖yosida T hT hs (b : H₀) - yosida T hT hr0 (b : H₀)‖ ≤
      ‖yosida T hT hs (b : H₀) - adjointComp T b‖ +
        ‖yosida T hT hr0 (b : H₀) - adjointComp T b‖ := by
    have h :=
      norm_sub_le (yosida T hT hs (b : H₀) - adjointComp T b)
        (yosida T hT hr0 (b : H₀) - adjointComp T b)
    rwa [sub_sub_sub_cancel_right] at h
  have hsY := hY5 hs hsδ
  have hrY := hY5 hr0 hrδ
  have hboundτ : τ * ‖yosida T hT hs (b : H₀) - yosida T hT hr0 (b : H₀)‖ ≤ ε := by
    have hle :
      τ * ‖yosida T hT hs (b : H₀) - yosida T hT hr0 (b : H₀)‖ ≤
        t * (ε / (2 * (t + 1)) + ε / (2 * (t + 1))) :=
      mul_le_mul hτ.2 (le_trans hdiff (by linarith)) (norm_nonneg _) ht
    have harith : t * (ε / (2 * (t + 1)) + ε / (2 * (t + 1))) ≤ ε := by
      have hne : (2 : ℝ) * (t + 1) ≠ 0 := by positivity
      have hcmul : ε / (2 * (t + 1)) * (2 * (t + 1)) = ε := by field_simp
      have hcpos : 0 < ε / (2 * (t + 1)) := by positivity
      nlinarith
    linarith
  -- Let `r ↓ 0` at the fixed time `τ`.
  have hlim := hspec hr0 hrδ₂
  have htri :=
    norm_sub_le_add_norm_sub (NormedSpace.exp (-τ • yosida T hT hs) (b : H₀))
      (NormedSpace.exp (-τ • yosida T hT hr0) (b : H₀)) (Generated.apply T hT hd τ (b : H₀))
  linarith

/--
**the generator right derivative.** For every `g : H₀`, every `0 ≤ t` and every `ε > 0` there is `δ
> 0` such that for
all `0 < s < δ` and **all** `τ ∈ [0, t]`

`‖exp (-τ • L_s) g - P_τ g‖ < ε`,

i.e. the adjoint-product identification convergence of `Generated.yosida_limit` is uniform on
compact time intervals.

Proof: approximate `g` within `ε/3` by `b ∈ D(T†T)` (`dense_adjointComp_domain`), apply
`Generated.yosida_error_le` to `b` with `ε/3`, and absorb the two
approximation errors with the contraction bounds resolvent contraction
(`norm_exp_neg_smul_apply_le`) and contraction
(`Generated.norm_apply_le`). -/
theorem yosida_converges (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (g : H₀) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ {s : ℝ} (hs : 0 < s),
          s < δ →
            ∀ τ ∈ Set.Icc 0 t,
              ‖NormedSpace.exp (-τ • yosida T hT hs) g - Generated.apply T hT hd τ g‖ < ε := by
  obtain ⟨b, hbmem, hbdist⟩ :=
    Metric.mem_closure_iff.mp (dense_adjointComp_domain T hT hd g) (ε / 3) (by positivity)
  have hbnorm : ‖g - b‖ < ε / 3 := by rwa [dist_eq_norm] at hbdist
  have hbnorm' : ‖b - g‖ < ε / 3 := by rwa [norm_sub_rev] at hbnorm
  obtain ⟨δ, hδ, hb⟩ :=
    Generated.yosida_error_le T hT hd (⟨b, hbmem⟩ : (adjointComp T).domain) ht
      (show (0 : ℝ) < ε / 3 by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ τ hτ
  have hmid : ‖NormedSpace.exp (-τ • yosida T hT hs) b - Generated.apply T hT hd τ b‖ ≤ ε / 3 :=
    hb hs hsδ τ hτ
  have hleft :
    ‖NormedSpace.exp (-τ • yosida T hT hs) g - NormedSpace.exp (-τ • yosida T hT hs) b‖ ≤
      ‖g - b‖ := by
    rw [← _root_.map_sub]
    exact norm_exp_neg_smul_apply_le _ (yosida_nonneg T hT hs) hτ.1 _
  have hright : ‖Generated.apply T hT hd τ b - Generated.apply T hT hd τ g‖ ≤ ‖b - g‖ := by
    rw [← Generated.map_sub T hT hd hτ.1]
    exact Generated.norm_apply_le T hT hd hτ.1 _
  have h1 :=
    norm_sub_le_add_norm_sub (NormedSpace.exp (-τ • yosida T hT hs) g)
      (NormedSpace.exp (-τ • yosida T hT hs) b) (Generated.apply T hT hd τ g)
  have h2 :=
    norm_sub_le_add_norm_sub (NormedSpace.exp (-τ • yosida T hT hs) b)
      (Generated.apply T hT hd τ b) (Generated.apply T hT hd τ g)
  linarith

/--
**The quantitative form of the semigroup limit.** For `f ∈ D(T†T)` and `ε > 0` there is `δ > 0` with

`‖P_t f - f + t • T†T f‖ ≤ (7 ε / 8) * t` for every `0 < t < δ`,

i.e. `P_t f = f - t • T†T f + o(t)` as `t ↓ 0`, with an explicit modulus.

Proof: the exponential mean-value bound applied to `A = L_s` needs `‖exp (-τ • L_s) (L_s f) - L_s
f‖` bounded on all of
`[0, t]`, which is exactly what the generator right derivative (uniformity in `τ`),
`exists_delta_norm_yosida_sub_adjointComp_lt` and `Generated.continuous_at_zero` supply; then
`s ↓ 0` at the fixed `t` through `Generated.yosida_limit`, squeezed by `le_of_forall_pos_add_le`. -/
theorem generator_error_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (f : (adjointComp T).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ t : ℝ,
          0 < t →
            t < δ →
              ‖Generated.apply T hT hd t (f : H₀) - (f : H₀) + t • adjointComp T f‖ ≤
                7 * ε / 8 * t := by
  obtain ⟨δ, hδ, hP7⟩ :=
    Generated.continuous_at_zero T hT hd (adjointComp T f) (show (0 : ℝ) < ε / 4 by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t htpos htδ
  refine le_of_forall_pos_add_le ?_
  intro η
    hη
  -- Choose one Yosida parameter `s` small enough for all three inputs at once.
  obtain ⟨δa, hδa, hY5⟩ :=
    exists_delta_norm_yosida_sub_adjointComp_lt T hT hd f (show (0 : ℝ) < ε / 8 by positivity)
  obtain ⟨δb, hδb, hG1⟩ :=
    Generated.yosida_converges T hT hd (adjointComp T f) htpos.le
      (show (0 : ℝ) < ε / 4 by positivity)
  obtain ⟨δc, hδc, hspec⟩ := Generated.yosida_limit T hT hd htpos.le (f : H₀) hη
  obtain ⟨s, hs, hsa, hsb, hsc⟩ : ∃ s : ℝ, 0 < s ∧ s < δa ∧ s < δb ∧ s < δc := by
    have hmin : 0 < min (min δa δb) δc := lt_min (lt_min hδa hδb) hδc
    have h1 : min (min δa δb) δc ≤ min δa δb := min_le_left _ _
    have h2 : min (min δa δb) δc ≤ δc := min_le_right _ _
    have h3 : min δa δb ≤ δa := min_le_left _ _
    have h4 : min δa δb ≤ δb := min_le_right _ _
    exact ⟨min (min δa δb) δc / 2, by linarith, by linarith, by linarith, by linarith⟩
  have hYs : ‖yosida T hT hs (f : H₀) - adjointComp T f‖ < ε / 8 := hY5 hs hsa
  have hYs' : ‖adjointComp T f - yosida T hT hs (f : H₀)‖ < ε / 8 := by
    rwa [norm_sub_rev] at hYs
  -- The hypothesis of the exponential mean-value bound, uniformly on `[0, t]`.
  have hC :
    ∀ τ ∈ Set.Icc 0 t,
      ‖NormedSpace.exp (-τ • yosida T hT hs) (yosida T hT hs (f : H₀)) -
            yosida T hT hs (f : H₀)‖ ≤
        3 * ε / 4 := by
    intro τ hτ
    have e1 :
      ‖NormedSpace.exp (-τ • yosida T hT hs) (yosida T hT hs (f : H₀)) -
            NormedSpace.exp (-τ • yosida T hT hs) (adjointComp T f)‖ ≤
        ‖yosida T hT hs (f : H₀) - adjointComp T f‖ := by
      rw [← _root_.map_sub]
      exact norm_exp_neg_smul_apply_le _ (yosida_nonneg T hT hs) hτ.1 _
    have e2 :
      ‖NormedSpace.exp (-τ • yosida T hT hs) (adjointComp T f) -
            Generated.apply T hT hd τ (adjointComp T f)‖ <
        ε / 4 :=
      hG1 hs hsb τ hτ
    have e3 : ‖Generated.apply T hT hd τ (adjointComp T f) - adjointComp T f‖ < ε / 4 :=
      hP7 τ hτ.1 (lt_of_le_of_lt hτ.2 htδ)
    have h1 :=
      norm_sub_le_add_norm_sub (NormedSpace.exp (-τ • yosida T hT hs) (yosida T hT hs (f : H₀)))
        (NormedSpace.exp (-τ • yosida T hT hs) (adjointComp T f)) (yosida T hT hs (f : H₀))
    have h2 :=
      norm_sub_le_add_norm_sub (NormedSpace.exp (-τ • yosida T hT hs) (adjointComp T f))
        (Generated.apply T hT hd τ (adjointComp T f)) (yosida T hT hs (f : H₀))
    have h3 :=
      norm_sub_le_add_norm_sub (Generated.apply T hT hd τ (adjointComp T f)) (adjointComp T f)
        (yosida T hT hs (f : H₀))
    linarith
  have hG2 := norm_exp_neg_smul_sub_add_smul_le (yosida T hT hs) (f : H₀) htpos.le hC
  have hlim :=
    hspec hs
      hsc
  -- Assemble.
  have hdecomp :
    Generated.apply T hT hd t (f : H₀) - (f : H₀) + t • adjointComp T f =
      (Generated.apply T hT hd t (f : H₀) - NormedSpace.exp (-t • yosida T hT hs) (f : H₀)) +
          (NormedSpace.exp (-t • yosida T hT hs) (f : H₀) - (f : H₀) +
            t • yosida T hT hs (f : H₀)) +
        (t • adjointComp T f - t • yosida T hT hs (f : H₀)) := by
    abel
  have hlast :
    ‖t • adjointComp T f - t • yosida T hT hs (f : H₀)‖ =
      t * ‖adjointComp T f - yosida T hT hs (f : H₀)‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hlast' : t * ‖adjointComp T f - yosida T hT hs (f : H₀)‖ ≤ t * (ε / 8) :=
    mul_le_mul_of_nonneg_left hYs'.le htpos.le
  rw [hdecomp]
  have htri1 :=
    norm_add_le
      ((Generated.apply T hT hd t (f : H₀) - NormedSpace.exp (-t • yosida T hT hs) (f : H₀)) +
        (NormedSpace.exp (-t • yosida T hT hs) (f : H₀) - (f : H₀) +
          t • yosida T hT hs (f : H₀)))
      (t • adjointComp T f - t • yosida T hT hs (f : H₀))
  have htri2 :=
    norm_add_le
      (Generated.apply T hT hd t (f : H₀) - NormedSpace.exp (-t • yosida T hT hs) (f : H₀))
      (NormedSpace.exp (-t • yosida T hT hs) (f : H₀) - (f : H₀) + t • yosida T hT hs (f : H₀))
  have hfirst :
    ‖Generated.apply T hT hd t (f : H₀) - NormedSpace.exp (-t • yosida T hT hs) (f : H₀)‖ < η := by
    rwa [norm_sub_rev] at hlim
  linarith

/-- **The semigroup limit: the generator of `P_t` is `-T†T` on `D(T†T)`.** For `f ∈ D(T†T)` and
`ε > 0` there is `δ > 0` with

`‖t⁻¹ • (P_t f - f) + T†T f‖ < ε` for every `0 < t < δ`,

that is, `(P_t f - f)/t → -T†T f` as `t ↓ 0`.

Immediate from the quantitative form `Generated.generator_error_le` after dividing by
`t > 0`. -/
theorem generator_limit (T : H₀ →ₗ.[ℝ] H₁)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : (adjointComp T).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ‖t⁻¹ • (Generated.apply T hT hd t (f : H₀) - (f : H₀)) + adjointComp T f‖ < ε := by
  obtain ⟨δ, hδ, hq⟩ := Generated.generator_error_le T hT hd f hε
  refine ⟨δ, hδ, ?_⟩
  intro t htpos htδ
  have htne : t ≠ 0 := ne_of_gt htpos
  have hrw : t⁻¹ • (Generated.apply T hT hd t (f : H₀) - (f : H₀)) + adjointComp T f
      = t⁻¹ • (Generated.apply T hT hd t (f : H₀) - (f : H₀) + t • adjointComp T f) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ htne, one_smul]
  rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
  have h1 : t⁻¹ * ‖Generated.apply T hT hd t (f : H₀) - (f : H₀) + t • adjointComp T f‖
      ≤ t⁻¹ * (7 * ε / 8 * t) :=
    mul_le_mul_of_nonneg_left (hq t htpos htδ) (inv_pos.mpr htpos).le
  have h2 : t⁻¹ * (7 * ε / 8 * t) = 7 * ε / 8 := by field_simp
  linarith

end Generated

end Generator

end FunctionalInequalities.Analysis.Semigroup
