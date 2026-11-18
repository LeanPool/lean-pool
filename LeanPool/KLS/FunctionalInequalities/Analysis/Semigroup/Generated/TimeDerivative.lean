/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Smoothing

/-!
# Time derivatives of `P_t = exp (-t T†T)` and of its gradient orbit

For a closed densely defined `T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces, with `A = T†T` and
the generated semigroup `P_t`, this module turns the ε–δ right derivative of `Domain.lean` into
Mathlib derivatives and adds the time regularity of the **gradient orbit** `t ↦ T (P_t g)`:

* `hasDerivWithinAt_apply_Ici`, `hasDerivWithinAt_apply_Iic`, `hasDerivAt_apply`: for
  `f ∈ D(A)`, `t ↦ P_t f` has derivative `-A (P_t f)`, from the right at `t ≥ 0` and two-sided
  at `t > 0`;
* `norm_map_sq_le_mul`: `‖T x‖² ≤ ‖A x‖ ‖x‖` on `D(A)`, the form bound used throughout;
* `adjointComp_apply_mem_adjointComp_domain_of_pos`: `A (P_t g) ∈ D(A)` for arbitrary `g` and
  `t > 0`, so `P_t g ∈ D(A²)`;
* `hasDerivWithinAt_map_apply_Ici`: for arbitrary `g` and `t > 0`, the gradient orbit has right
  derivative `-T (A (P_t g))` in `H₁`;
* `continuousOn_map_apply`: the gradient orbit is continuous on `(0, ∞)`;
* `tendsto_map_apply_zero`: for `f ∈ D(T)`, `T (P_s f) → T f` as `s → 0⁺`;
* `hasDerivAt_apply_of_pos`: for arbitrary `g`, `t ↦ P_t g` has derivative `-A (P_t g)` at
  every `t > 0`;
* `hasDerivAt_apply_curve` and `hasDerivAt_apply_curve_of_mem_domain`: the product rule
  for `P_t F(t)`, with the generator commuted inside when `F(t)` belongs to D(A).

Because `T` is only partially defined, the gradient orbit is passed as any function `u` that
agrees with `s ↦ T (P_s g)` where that is defined; no total extension of `T` is introduced.
Nothing here uses a measure, a Markov property or a Bakry–Émery estimate.
-/

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

include hd in
omit [CompleteSpace H₁] in
/-- The form bound `‖T x‖² = ⟪A x, x⟫ ≤ ‖A x‖ ‖x‖` on `D(A)`. -/
theorem norm_map_sq_le_mul (x : (adjointComp T).domain) :
    ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 ≤ ‖adjointComp T x‖ * ‖(x : H₀)‖ := by
  rw [← inner_adjointComp_self hd x]
  exact real_inner_le_norm _ _

/-- **Right derivative of the orbit**: for `f ∈ D(A)` and `t ≥ 0`,
`d/ds P_s f = -A (P_t f)` from the right at `s = t`. -/
theorem hasDerivWithinAt_apply_Ici (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht⟩) (Ici t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := right_derivative T hT hd f ht hε
  refine ⟨δ, hδ, fun s hs hsd => ?_⟩
  have hs' : 0 < s - t := sub_pos.mpr hs
  have hlt : s - t < δ := by
    rw [Real.dist_eq, abs_of_pos hs'] at hsd; exact hsd
  rw [dist_eq_norm, slope_def_module, sub_neg_eq_add]
  have := h (s - t) hs' hlt
  rwa [add_sub_cancel] at this

/-- **Left derivative of the orbit**: for `f ∈ D(A)` and `t > 0`,
`d/ds P_s f = -A (P_t f)` from the left at `s = t`. -/
theorem hasDerivWithinAt_apply_Iic (f : (adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht.le⟩) (Iic t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Iic_sdiff_right, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := generator_limit T hT hd f (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.mp
    ((continuousOn T hT hd (adjointComp T f)) t ht.le) (ε / 2) (half_pos hε)
  refine ⟨min (min δ₁ δ₂) t, lt_min (lt_min hδ₁ hδ₂) ht, fun s hs hsd => ?_⟩
  have hh : 0 < t - s := sub_pos.mpr hs
  have hlt : t - s < min (min δ₁ δ₂) t := by
    rw [Real.dist_eq, abs_of_neg (by linarith)] at hsd; linarith
  have hs0 : 0 ≤ s := by linarith [min_le_right (min δ₁ δ₂) t]
  set h := t - s with hhdef
  have hPt : apply T hT hd t f = apply T hT hd s (apply T hT hd h f) := by
    rw [← add_time T hT hd hs0 hh.le]; congr 1; ring
  have key : slope (fun s => apply T hT hd s f) t s =
      apply T hT hd s (h⁻¹ • (apply T hT hd h (f : H₀) - f)) := by
    rw [slope_def_module, hPt, map_smul T hT hd hs0, map_sub T hT hd hs0,
      show s - t = -h by rw [hhdef]; ring, inv_neg, neg_smul, ← smul_neg, neg_sub]
  rw [dist_eq_norm, key, generator_comm T hT hd f ht.le, sub_neg_eq_add]
  have hsplit : apply T hT hd s (h⁻¹ • (apply T hT hd h (f : H₀) - f)) +
      apply T hT hd t (adjointComp T f) =
      apply T hT hd s (h⁻¹ • (apply T hT hd h (f : H₀) - f) + adjointComp T f) +
        (apply T hT hd t (adjointComp T f) - apply T hT hd s (adjointComp T f)) := by
    rw [map_add T hT hd hs0]; abel
  have hA : ‖apply T hT hd s (h⁻¹ • (apply T hT hd h (f : H₀) - f) + adjointComp T f)‖ <
      ε / 2 :=
    (norm_apply_le T hT hd hs0 _).trans_lt (h₁ h hh (hlt.trans_le
      ((min_le_left _ _).trans (min_le_left _ _))))
  have hB : ‖apply T hT hd t (adjointComp T f) - apply T hT hd s (adjointComp T f)‖ < ε / 2 := by
    rw [← dist_eq_norm, dist_comm]
    refine h₂ (mem_Ici.mpr hs0) ?_
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    linarith [(min_le_left (min δ₁ δ₂) t).trans (min_le_right δ₁ δ₂)]
  rw [hsplit]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- The backward orbit has right derivative `A P_(t-r) f` when `r < t`. -/
theorem hasDerivWithinAt_apply_sub_Ici (f : (adjointComp T).domain) {r t : ℝ}
    (htr : 0 < t - r) :
    HasDerivWithinAt (fun a => apply T hT hd (t - a) f)
      (adjointComp T ⟨apply T hT hd (t - r) f,
        preserves_domain T hT hd f htr.le⟩) (Ici r) r := by
  have hP := hasDerivWithinAt_apply_Iic T hT hd f htr
  have hlin : HasDerivWithinAt (fun a : ℝ => t - a) (-1) (Ici r) r :=
    ((hasDerivAt_id r).const_sub t).hasDerivWithinAt
  have hmaps : MapsTo (fun a : ℝ => t - a) (Ici r) (Iic (t - r)) := fun a ha => by
    simp only [mem_Iic]; linarith [mem_Ici.mp ha]
  have hq := hP.scomp r hlin hmaps
  simp only [neg_smul, one_smul, neg_neg] at hq
  exact hq

/-- The backward orbit is continuous on every interval ending at `t`. -/
theorem continuousOn_apply_sub (f : H₀) {a t : ℝ} :
    ContinuousOn (fun r => apply T hT hd (t - r) f) (Icc a t) := by
  exact (continuousOn T hT hd f).comp
    (continuous_const.sub continuous_id).continuousOn
    (fun r hr => by simp only [mem_Ici]; linarith [hr.2])

/-- Sending the backward time increment to zero recovers the positive-time orbit. -/
theorem tendsto_apply_sub_zero (f : H₀) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a : ℝ => apply T hT hd (t - a) f) (𝓝[>] 0)
      (𝓝 (apply T hT hd t f)) := by
  have hsub : Tendsto (fun a : ℝ => t - a) (𝓝[>] 0) (𝓝[Ici 0] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun a : ℝ => t - a) (𝓝 0) (𝓝 (t - 0)) :=
        ((continuous_const.sub continuous_id).tendsto (0 : ℝ))
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT ht] with a ha
      simp only [mem_Ici]; linarith [ha.2]
  exact ((continuousOn T hT hd f) t (mem_Ici.mpr ht.le)).tendsto.comp hsub

/-- **Two-sided derivative of the orbit** at positive times. -/
theorem hasDerivAt_apply (f : (adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht.le⟩) t := by
  have h := (hasDerivWithinAt_apply_Iic T hT hd f ht).union
    (hasDerivWithinAt_apply_Ici T hT hd f ht.le)
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- `A (P_t g) ∈ D(A)` for arbitrary `g` and `t > 0`: positive times land in `D(A²)`. -/
theorem adjointComp_apply_mem_adjointComp_domain_of_pos (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : apply T hT hd t g ∈ (adjointComp T).domain) :
    (adjointComp T ⟨apply T hT hd t g, h⟩ : H₀) ∈ (adjointComp T).domain := by
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hmem2 : apply T hT hd (t / 2) g ∈ (adjointComp T).domain :=
    mem_adjointComp_domain_apply_of_pos T hT hd g hhalf
  have heq : apply T hT hd (t / 2) (apply T hT hd (t / 2) g) = apply T hT hd t g := by
    rw [← add_time T hT hd hhalf.le hhalf.le]
    norm_num
  have hsub : (⟨apply T hT hd (t / 2) (apply T hT hd (t / 2) g),
        preserves_domain T hT hd ⟨_, hmem2⟩ hhalf.le⟩ : (adjointComp T).domain) =
      ⟨apply T hT hd t g, h⟩ := Subtype.ext heq
  rw [← hsub, generator_comm T hT hd ⟨_, hmem2⟩ hhalf.le]
  exact mem_adjointComp_domain_apply_of_pos T hT hd _ hhalf

/-- **Right derivative of the gradient orbit.** For arbitrary `g` and `t > 0`, any `u` agreeing
with `s ↦ T (P_s g)` for `s > 0` has right derivative `-T (A (P_t g))` at `t`. With
`F = P_t g ∈ D(A²)`, the difference quotient minus the limit is `T x_h` for
`x_h = h⁻¹ (P_h F - F) + A F ∈ D(A)`, and `‖T x_h‖² ≤ ‖A x_h‖ ‖x_h‖` with both factors tending
to zero by the right derivatives of `F` and `A F`. -/
theorem hasDerivWithinAt_map_apply_Ici (g : H₀) {u : ℝ → H₁}
    (hu : ∀ s (hs : 0 < s), u s = T ⟨apply T hT hd s g, mem_domain_apply_of_pos T hT hd g hs⟩)
    {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt u (-T ⟨adjointComp T ⟨apply T hT hd t g,
        mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩,
      mem_domain_adjointComp_apply_of_pos T hT hd g ht _⟩) (Ici t) t := by
  set F : (adjointComp T).domain :=
    ⟨apply T hT hd t g, mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩ with hFdef
  have hG : (adjointComp T F : H₀) ∈ (adjointComp T).domain :=
    adjointComp_apply_mem_adjointComp_domain_of_pos T hT hd g ht _
  set G : (adjointComp T).domain := ⟨_, hG⟩ with hGdef
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := generator_limit T hT hd F hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := generator_limit T hT hd G hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hsd => ?_⟩
  have hs0 : 0 < s := ht.trans hs
  have hh : 0 < s - t := sub_pos.mpr hs
  have hlt : s - t < min δ₁ δ₂ := by
    rw [Real.dist_eq, abs_of_pos hh] at hsd; exact hsd
  have hPs : apply T hT hd s g = apply T hT hd (s - t) (F : H₀) := by
    rw [hFdef, ← add_time T hT hd hh.le ht.le, sub_add_cancel]
  have hPhF : apply T hT hd (s - t) (F : H₀) ∈ (adjointComp T).domain :=
    preserves_domain T hT hd F hh.le
  have hx : (s - t)⁻¹ • (apply T hT hd (s - t) (F : H₀) - F) + adjointComp T F ∈
      (adjointComp T).domain :=
    (adjointComp T).domain.add_mem
      ((adjointComp T).domain.smul_mem _ ((adjointComp T).domain.sub_mem hPhF F.2)) hG
  have eT : (⟨(s - t)⁻¹ • (apply T hT hd (s - t) (F : H₀) - F) + adjointComp T F, hx.2⟩ :
      T.domain) = (s - t)⁻¹ • (⟨_, hPhF.2⟩ - ⟨(F : H₀), F.2.2⟩) + ⟨_, hG.2⟩ := rfl
  have eA : (⟨(s - t)⁻¹ • (apply T hT hd (s - t) (F : H₀) - F) + adjointComp T F, hx⟩ :
      (adjointComp T).domain) = (s - t)⁻¹ • (⟨_, hPhF⟩ - F) + G := rfl
  have hus : u s = T ⟨_, hPhF.2⟩ := by
    rw [hu s hs0]; congr 1; exact Subtype.ext hPs
  have hut : u t = T ⟨(F : H₀), F.2.2⟩ := hu t ht
  have hTx : T ⟨_, hx.2⟩ = (s - t)⁻¹ • (u s - u t) + T ⟨_, hG.2⟩ := by
    rw [eT, LinearPMap.map_add, LinearPMap.map_smul, LinearPMap.map_sub, hus, hut]
  have hAx : adjointComp T ⟨_, hx⟩ =
      (s - t)⁻¹ • (apply T hT hd (s - t) (G : H₀) - G) + adjointComp T G := by
    rw [eA, LinearPMap.map_add, LinearPMap.map_smul, LinearPMap.map_sub]
    congr 3
    exact generator_comm T hT hd F hh.le
  have hxn : ‖(s - t)⁻¹ • (apply T hT hd (s - t) (F : H₀) - F) + adjointComp T F‖ < ε :=
    h₁ (s - t) hh (hlt.trans_le (min_le_left _ _))
  have hAxn : ‖adjointComp T ⟨_, hx⟩‖ < ε := by
    rw [hAx]; exact h₂ (s - t) hh (hlt.trans_le (min_le_right _ _))
  have hsq : ‖T ⟨_, hx.2⟩‖ ^ 2 ≤ ‖adjointComp T ⟨_, hx⟩‖ *
      ‖(s - t)⁻¹ • (apply T hT hd (s - t) (F : H₀) - F) + adjointComp T F‖ :=
    norm_map_sq_le_mul T hd ⟨_, hx⟩
  rw [dist_eq_norm, slope_def_module, sub_neg_eq_add, ← hTx]
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [norm_nonneg (T ⟨_, hx.2⟩), norm_nonneg (adjointComp T ⟨_, hx⟩),
    norm_nonneg ((s - t)⁻¹ • (apply T hT hd (s - t) (F : H₀) - F) + adjointComp T F)]

/-- **Continuity of the gradient orbit** on `(0, ∞)`. For `s, t ≥ t₀/2 > 0` the difference
`y = P_s g - P_t g` lies in `D(A)` with `A y = P_{s-t₀/2}(A G) - P_{t-t₀/2}(A G)`,
`G = P_{t₀/2} g`, and `‖T y‖² ≤ ‖A y‖ ‖y‖`. -/
theorem continuousOn_map_apply (g : H₀) {u : ℝ → H₁}
    (hu : ∀ s (hs : 0 < s), u s = T ⟨apply T hT hd s g, mem_domain_apply_of_pos T hT hd g hs⟩) :
    ContinuousOn u (Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hhalf : 0 < t / 2 := half_pos ht0
  set G : (adjointComp T).domain :=
    ⟨apply T hT hd (t / 2) g, mem_adjointComp_domain_apply_of_pos T hT hd g hhalf⟩ with hGdef
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ :=
    Metric.continuousWithinAt_iff.mp ((continuousOn T hT hd (G : H₀)) (t / 2) hhalf.le) ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ :=
    Metric.continuousWithinAt_iff.mp ((continuousOn T hT hd (adjointComp T G)) (t / 2) hhalf.le)
      ε hε
  refine ⟨min (min δ₁ δ₂) (t / 2), lt_min (lt_min hδ₁ hδ₂) hhalf, fun s hs hsd => ?_⟩
  have hs0 : 0 < s := hs
  have hd' : |s - t| < min (min δ₁ δ₂) (t / 2) := by rwa [Real.dist_eq] at hsd
  have hτ : 0 ≤ s - t / 2 := by
    have := (abs_lt.mp (hd'.trans_le (min_le_right _ _))).1;
    linarith
  have hPs : apply T hT hd s g = apply T hT hd (s - t / 2) (G : H₀) := by
    rw [hGdef, ← add_time T hT hd hτ hhalf.le, sub_add_cancel]
  have hPt : apply T hT hd t g = apply T hT hd (t / 2) (G : H₀) := by
    rw [hGdef, ← add_time T hT hd hhalf.le hhalf.le, add_halves]
  have hm₁ : apply T hT hd (s - t / 2) (G : H₀) ∈ (adjointComp T).domain :=
    preserves_domain T hT hd G hτ
  have hm₂ : apply T hT hd (t / 2) (G : H₀) ∈ (adjointComp T).domain :=
    preserves_domain T hT hd G hhalf.le
  have hy := (adjointComp T).domain.sub_mem hm₁ hm₂
  have hus : u s - u t = T ⟨_, hy.2⟩ := by
    rw [hu s hs0, hu t ht0]
    have e : (⟨_, hy.2⟩ : T.domain) = ⟨_, hm₁.2⟩ - ⟨_, hm₂.2⟩ := rfl
    rw [e, LinearPMap.map_sub]
    congr 2 <;> exact Subtype.ext (by assumption)
  have hAy :
    adjointComp T ⟨_, hy⟩ =
      apply T hT hd (s - t / 2) (adjointComp T G) - apply T hT hd (t / 2) (adjointComp T G) := by
    have e : (⟨_, hy⟩ : (adjointComp T).domain) = ⟨_, hm₁⟩ - ⟨_, hm₂⟩ := rfl
    rw [e, LinearPMap.map_sub, generator_comm T hT hd G hτ, generator_comm T hT hd G hhalf.le]
  have hdist : dist (s - t / 2) (t / 2) = |s - t| := by rw [Real.dist_eq]; congr 1; ring
  have hd₁ : dist (s - t / 2) (t / 2) < δ₁ := by
    rw [hdist];
    exact hd'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hd₂ : dist (s - t / 2) (t / 2) < δ₂ := by
    rw [hdist];
    exact hd'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hyn : ‖apply T hT hd (s - t / 2) (G : H₀) - apply T hT hd (t / 2) (G : H₀)‖ < ε := by
    rw [← dist_eq_norm]
    exact h₁ (mem_Ici.mpr hτ) hd₁
  have hAyn : ‖adjointComp T ⟨_, hy⟩‖ < ε := by
    rw [hAy, ← dist_eq_norm]
    exact h₂ (mem_Ici.mpr hτ) hd₂
  have hsq :
    ‖T ⟨_, hy.2⟩‖ ^ 2 ≤
      ‖adjointComp T ⟨_, hy⟩‖ *
        ‖apply T hT hd (s - t / 2) (G : H₀) - apply T hT hd (t / 2) (G : H₀)‖ :=
    norm_map_sq_le_mul T hd ⟨_, hy⟩
  rw [dist_eq_norm, hus]
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [norm_nonneg (T ⟨_, hy.2⟩), norm_nonneg (adjointComp T ⟨_, hy⟩),
    norm_nonneg (apply T hT hd (s - t / 2) (G : H₀) - apply T hT hd (t / 2) (G : H₀))]

/-- **Form-domain continuity at time zero.** For `f ∈ D(T)`, any `u` agreeing with
`s ↦ T (P_s f)` for `s ≥ 0` tends to `T f` as `s → 0⁺`. The proof approximates `f` by
`y ∈ D(A)` in the graph norm, uses the contraction `‖T (P_s (f - y))‖ ≤ ‖T (f - y)‖`, and
`‖T (P_s y - y)‖² ≤ 2 ‖A y‖ ‖P_s y - y‖`. -/
theorem tendsto_map_apply_zero (f : T.domain) {u : ℝ → H₁}
    (hu : ∀ s (hs : 0 ≤ s), u s = T ⟨apply T hT hd s f, preserves_form_domain T hT hd f hs⟩) :
    Tendsto u (𝓝[≥] 0) (𝓝 (T f)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨y, hy, -, hy₂⟩ := exists_seq_mem_adjointComp_domain_tendsto_graph T hT hd f
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hy₂ (ε / 3) (by positivity)
  have hn' := hn n le_rfl
  set Y : (adjointComp T).domain := ⟨y n, hy n⟩ with hYdef
  set η := (ε / 3) ^ 2 / (2 * ‖adjointComp T Y‖ + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hc⟩ := Metric.continuousWithinAt_iff.mp
    ((continuousOn T hT hd (Y : H₀)) 0 self_mem_Ici) η hη
  refine ⟨δ, hδ, fun s hs hsd => ?_⟩
  have hs0 : 0 ≤ s := hs
  have hfY : (f : H₀) - Y ∈ T.domain := T.domain.sub_mem f.2 Y.2.2
  have hPfY := preserves_form_domain T hT hd ⟨_, hfY⟩ hs0
  have hPY : apply T hT hd s (Y : H₀) ∈ (adjointComp T).domain := preserves_domain T hT hd Y hs0
  have hz := (adjointComp T).domain.sub_mem hPY Y.2
  have hsplit : u s - T f = T ⟨_, hPfY⟩ + T ⟨_, hz.2⟩ +
      (T ⟨(Y : H₀), Y.2.2⟩ - T f) := by
    rw [hu s hs0]
    have e1 : (⟨_, hPfY⟩ : T.domain) = ⟨apply T hT hd s f, preserves_form_domain T hT hd f hs0⟩ -
        ⟨_, hPY.2⟩ := Subtype.ext (map_sub T hT hd hs0 _ _)
    have e2 : (⟨_, hz.2⟩ : T.domain) = ⟨_, hPY.2⟩ - ⟨(Y : H₀), Y.2.2⟩ := rfl
    rw [e1, e2, LinearPMap.map_sub, LinearPMap.map_sub]
    abel
  have hb₁ : ‖T ⟨_, hPfY⟩‖ < ε / 3 := by
    refine (norm_map_apply_le T hT hd ⟨_, hfY⟩ hs0 hPfY).trans_lt ?_
    have e : (⟨_, hfY⟩ : T.domain) = f - ⟨(Y : H₀), Y.2.2⟩ := rfl
    rw [e, LinearPMap.map_sub, ← dist_eq_norm, dist_comm]
    exact hn'
  have hAz : ‖adjointComp T ⟨_, hz⟩‖ ≤ 2 * ‖adjointComp T Y‖ := by
    have e : (⟨_, hz⟩ : (adjointComp T).domain) = ⟨_, hPY⟩ - Y := rfl
    rw [e, LinearPMap.map_sub, generator_comm T hT hd Y hs0]
    calc _ ≤ ‖apply T hT hd s (adjointComp T Y)‖ + ‖adjointComp T Y‖ := norm_sub_le _ _
      _ ≤ ‖adjointComp T Y‖ + ‖adjointComp T Y‖ := by
          gcongr; exact norm_apply_le T hT hd hs0 _
      _ = _ := by ring
  have hzn : ‖apply T hT hd s (Y : H₀) - Y‖ < η := by
    have h := hc (mem_Ici.mpr hs0) hsd
    rwa [zero_time, dist_eq_norm] at h
  have hsq : ‖T ⟨_, hz.2⟩‖ ^ 2 ≤ ‖adjointComp T ⟨_, hz⟩‖ * ‖apply T hT hd s (Y : H₀) - Y‖ :=
    norm_map_sq_le_mul T hd ⟨_, hz⟩
  have hb₂ : ‖T ⟨_, hz.2⟩‖ < ε / 3 := by
    have hA0 := norm_nonneg (adjointComp T Y)
    have hprod : ‖adjointComp T ⟨_, hz⟩‖ * ‖apply T hT hd s (Y : H₀) - Y‖ < (ε / 3) ^ 2 := by
      calc _ ≤ (2 * ‖adjointComp T Y‖) * η :=
            mul_le_mul hAz hzn.le (norm_nonneg _) (by positivity)
        _ < (2 * ‖adjointComp T Y‖ + 1) * η := by nlinarith
        _ = (ε / 3) ^ 2 := by rw [hηdef]; field_simp
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [norm_nonneg (T ⟨_, hz.2⟩)]
  have hb₃ : ‖T ⟨(Y : H₀), Y.2.2⟩ - T f‖ < ε / 3 := by rw [← dist_eq_norm]; exact hn'
  rw [dist_eq_norm, hsplit]
  calc _ ≤ ‖T ⟨_, hPfY⟩ + T ⟨_, hz.2⟩‖ + ‖T ⟨(Y : H₀), Y.2.2⟩ - T f‖ := norm_add_le _ _
    _ ≤ ‖T ⟨_, hPfY⟩‖ + ‖T ⟨_, hz.2⟩‖ + ‖T ⟨(Y : H₀), Y.2.2⟩ - T f‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- **Derivative of the orbit of arbitrary data** at positive times: for every `g` and `t > 0`,
`d/ds P_s g = -A (P_t g)` at `s = t`. Near `t` the orbit agrees with `s ↦ P_{s - t/2} F` for
`F = P_{t/2} g ∈ D(A)`. -/
theorem hasDerivAt_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => apply T hT hd s g)
      (-adjointComp T ⟨apply T hT hd t g, mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩) t := by
  have hhalf : 0 < t / 2 := half_pos ht
  set F : (adjointComp T).domain :=
    ⟨apply T hT hd (t / 2) g, mem_adjointComp_domain_apply_of_pos T hT hd g hhalf⟩ with hFdef
  have h1 := hasDerivAt_apply T hT hd F (show 0 < t - t / 2 by linarith)
  have h2 : HasDerivAt (fun s => apply T hT hd (s - t / 2) (F : H₀))
      (-adjointComp T ⟨apply T hT hd (t - t / 2) F,
        preserves_domain T hT hd F (by linarith)⟩) t := by
    have := HasDerivAt.scomp t h1 ((hasDerivAt_id' t).sub_const (t / 2))
    simpa [Function.comp_def] using this
  have heq : (⟨apply T hT hd (t - t / 2) F, preserves_domain T hT hd F (by linarith)⟩ :
      (adjointComp T).domain) =
      ⟨apply T hT hd t g, mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩ := by
    apply Subtype.ext
    simp only [hFdef]
    rw [← add_time T hT hd (by linarith) hhalf.le]
    congr 1; ring
  rw [heq] at h2
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (half_lt_self ht)] with s hs
  simp only [hFdef]
  rw [← add_time T hT hd (by linarith) hhalf.le]
  congr 1; ring

/-- Product rule for heat evolution of a differentiable, varying datum. Only strong
continuity and contraction are used for the varying-datum term. -/
theorem hasDerivAt_apply_curve {F : ℝ → H₀} {v : H₀} {t : ℝ}
    (hF : HasDerivAt F v t) (ht : 0 < t) :
    HasDerivAt (fun s ↦ apply T hT hd s (F s))
      (apply T hT hd t v - adjointComp T
        ⟨apply T hT hd t (F t), mem_adjointComp_domain_apply_of_pos T hT hd (F t) ht⟩) t := by
  have hq := hF.tendsto_slope
  have hp : Tendsto (fun s ↦ apply T hT hd s v) (𝓝[≠] t) (𝓝 (apply T hT hd t v)) :=
    (hasDerivAt_apply_of_pos T hT hd v ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s ↦ apply T hT hd s (slope F t s)) (𝓝[≠] t)
      (𝓝 (apply T hT hd t v)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb := (tendsto_iff_norm_sub_tendsto_zero.mp hq).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hp)
    simp only [add_zero] at hb
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hb
    filter_upwards [(lt_mem_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs
    calc ‖apply T hT hd s (slope F t s) - apply T hT hd t v‖ ≤
          ‖apply T hT hd s (slope F t s) - apply T hT hd s v‖ +
            ‖apply T hT hd s v - apply T hT hd t v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖slope F t s - v‖ + ‖apply T hT hd s v - apply T hT hd t v‖ := by
        rw [← map_sub T hT hd hs.le]
        exact add_le_add (norm_apply_le T hT hd hs.le _) le_rfl
  have hh := hlim.add (hasDerivAt_apply_of_pos T hT hd (F t) ht).tendsto_slope
  rw [hasDerivAt_iff_tendsto_slope]
  simp only [sub_eq_add_neg]
  apply hh.congr'
  filter_upwards [(lt_mem_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs
  simp only [slope_def_module]
  rw [map_smul T hT hd hs.le, map_sub T hT hd hs.le, ← smul_add]
  congr 1
  abel

/-- When the current datum belongs to D(A), commute the generator through the
heat operator to obtain the derivative as P_t applied to the chain-rule remainder. -/
theorem hasDerivAt_apply_curve_of_mem_domain {F : ℝ → H₀} {v : H₀} {t : ℝ}
    (hF : HasDerivAt F v t) (ht : 0 < t) (hmem : F t ∈ (adjointComp T).domain) :
    HasDerivAt (fun s ↦ apply T hT hd s (F s))
      (apply T hT hd t (v - adjointComp T ⟨F t, hmem⟩)) t := by
  have h := hasDerivAt_apply_curve T hT hd hF ht
  have hc := generator_comm T hT hd ⟨F t, hmem⟩ ht.le
  rw [map_sub T hT hd ht.le]
  exact h.congr_deriv (by rw [hc])

/-- Strong continuity also holds for varying continuous data, including at time zero. -/
theorem continuousOn_apply_curve {S : Set ℝ} (hS : S ⊆ Set.Ici 0)
    {F : ℝ → H₀} (hF : ContinuousOn F S) :
    ContinuousOn (fun s ↦ apply T hT hd s (F s)) S := by
  intro t ht
  have hp := (continuousOn T hT hd (F t)).mono hS t ht
  have hb := (tendsto_iff_norm_sub_tendsto_zero.mp (hF t ht)).add
    (tendsto_iff_norm_sub_tendsto_zero.mp hp)
  simp only [add_zero] at hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with s hs
  calc ‖apply T hT hd s (F s) - apply T hT hd t (F t)‖ ≤
      ‖apply T hT hd s (F s) - apply T hT hd s (F t)‖ +
        ‖apply T hT hd s (F t) - apply T hT hd t (F t)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖F s - F t‖ + ‖apply T hT hd s (F t) - apply T hT hd t (F t)‖ := by
      rw [← map_sub T hT hd (hS hs)]
      exact add_le_add (norm_apply_le T hT hd (hS hs) _) le_rfl

end FunctionalInequalities.Analysis.Semigroup.Generated
