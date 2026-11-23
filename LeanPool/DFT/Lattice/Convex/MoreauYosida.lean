/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Convex.Smooth
import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.FunProp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Ring

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
open scoped NNReal

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

/-- Variational inequality of the proximal point, obtained from Tau Ceti’s resolvent inequality
by extending the energy to `⊤` off its domain. -/
lemma prox_vi (hD : IsCompact D) (hne : D.Nonempty) (hfc : ConvexOn ℝ D f)
    (hf : LowerSemicontinuousOn f D) (hε : 0 < ε) (x : E) {q : E} (hq : q ∈ D) :
    f (prox D f ε x) + ε⁻¹ * ⟪x - prox D f ε x, q - prox D f ε x⟫ ≤ f q := by
  classical
  set p := prox D f ε x
  obtain ⟨hp, hmin⟩ := prox_spec (ε := ε) hD hne hf x
  let energy (z : E) : EReal := if z ∈ D then f z else ⊤
  have on_domain {z : E} (hz : z ∈ D) : energy z = (f z : EReal) := by simp [energy, hz]
  have mem_domain {z : E} (hz : energy z ≠ ⊤) : z ∈ D := by
    by_contra outside
    exact hz (by simp [energy, outside])
  let τ : ℝ≥0 := ⟨ε, hε.le⟩
  have hτ : 0 < τ := hε
  have convex_energy : TauCeti.GeodesicallyConvex 0 energy := by
    rw [TauCeti.geodesicallyConvex_def]
    intro u v hu hv
    have huD := mem_domain hu
    have hvD := mem_domain hv
    have line : TauCeti.IsGeodesicSegment (AffineMap.lineMap u v) u v := by
      refine TauCeti.isGeodesicSegment_of_dist_le (by simp) (by simp) fun s _ t _ hst => ?_
      rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    refine ⟨_, line, (line.convexAlong_iff).mpr fun t ht => ?_⟩
    have ht0 := ht.1
    have h1t := sub_nonneg.mpr ht.2
    have hadd : 1 - t + t = 1 := sub_add_cancel 1 t
    rw [AffineMap.lineMap_apply_module, on_domain (hfc.1 huD hvD h1t ht0 hadd),
      on_domain huD, on_domain hvD]
    simp only [zero_div, zero_mul, EReal.coe_zero, sub_zero, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    exact hfc.2 huD hvD h1t ht0 hadd
  have resolvent : p ∈ TauCeti.moreauYosidaResolvent energy τ x := by
    refine TauCeti.mem_moreauYosidaResolvent_iff.mpr ⟨edist_ne_top _ _, fun z _ => ?_⟩
    rw [TauCeti.coe_edist_sq_div_eq_coe_dist_sq_div hτ,
      TauCeti.coe_edist_sq_div_eq_coe_dist_sq_div hτ, on_domain hp]
    by_cases hz : z ∈ D
    · rw [on_domain hz, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      rw [dist_eq_norm, dist_eq_norm, show (τ : ℝ) = ε from rfl]
      exact hmin z hz
    · simp [energy, hz, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
  have bound := convex_energy.penalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent
    hτ resolvent (on_domain hq ▸ EReal.coe_ne_top _)
  rw [on_domain hp, on_domain hq, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at bound
  have distance_expansion : dist x q ^ 2 =
      ‖x - p‖ ^ 2 - 2 * ⟪x - p, q - p⟫ + ‖q - p‖ ^ 2 := by
    rw [dist_eq_norm, show x - q = (x - p) - (q - p) by abel, norm_sub_sq_real]
  rw [zero_div, zero_mul, add_zero, distance_expansion, dist_comm p q, dist_eq_norm x p,
    dist_eq_norm q p] at bound
  change f p + (‖x - p‖ ^ 2 / (2 * ε) + ‖q - p‖ ^ 2 / (2 * ε)) ≤ _ at bound
  have step : f p + ε⁻¹ * ⟪x - p, q - p⟫ =
      f p + (‖x - p‖ ^ 2 / (2 * ε) + ‖q - p‖ ^ 2 / (2 * ε)) -
        (‖x - p‖ ^ 2 - 2 * ⟪x - p, q - p⟫ + ‖q - p‖ ^ 2) / (2 * ε) := by
    field_simp
    ring
  rw [step]
  exact sub_le_iff_le_add.mpr bound

/-- **The Moreau envelope is `IsMYSmooth`.** -/
theorem isMYSmooth_myEnv (hD : IsCompact D) (hne : D.Nonempty)
    (hfc : ConvexOn ℝ D f)
    (hf : LowerSemicontinuousOn f D) (hε : 0 < ε) : IsMYSmooth ε (myEnv D f ε) (myGrad D f ε) where
  lower x y := by
    set p := prox D f ε x
    set q := prox D f ε y
    have hvi := prox_vi hD hne hfc hf hε x (prox_spec (ε := ε) hD hne hf y).1
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
