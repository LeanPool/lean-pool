/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Variation.Attainment
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Existence and compact-local bounds of supporting slopes

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

section
open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section SubgradientMaxFormula

open scoped RealInnerProductSpace

/-! Max formula and existence of subgradients. -/

/-- Riesz representation turns a linear minorant of the directional envelope
into a supporting vector. This is the common last step of both Hahn–Banach cases. -/
private theorem exists_supporting_vector_of_linear_minorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : E → ℝ) (x : E) (p : E → ℝ)
    (hp : ∀ w, p w ≤ u (x + w) - u x)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ∀ w, ℓ w ≤ p w) :
    ∃ g : E, (∀ w, ⟪g, w⟫ = ℓ w) ∧ ∀ y, u x + ⟪g, y - x⟫ ≤ u y := by
  let L : E →L[ℝ] ℝ :=
    { toLinearMap := ℓ
      cont := LinearMap.continuous_of_finiteDimensional ℓ }
  let g : E := (InnerProductSpace.toDual ℝ E).symm L
  have hpair : ∀ w : E, ⟪g, w⟫ = ℓ w := by
    intro w
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = ℓ w
    calc
      inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = L w :=
        InnerProductSpace.toDual_symm_apply
      _ = ℓ w := rfl
  refine ⟨g, hpair, ?_⟩
  intro y
  have hq := hp (y - x)
  have hy : x + (y - x) = y := by abel
  rw [hy] at hq
  have hminorant := hℓ (y - x)
  rw [← hpair] at hminorant
  linarith

/-- **Max formula for the one-sided directional derivative of a finite convex function** ("singleton
subdifferential ⇒ C¹"): for a convex `u : E → ℝ` on a
finite-dimensional inner product space, every point `x` and every direction `v`, there is a
subgradient `g` of `u` at `x` whose pairing with `v` is the right derivative
`inf_{t>0} (u(x + t v) - u(x))/t`: it is a subgradient and the difference quotients come
arbitrarily close to `⟪g, v⟫` (they are `≥ ⟪g, v⟫` by the subgradient inequality).

First construct the sublinear right-derivative envelope. Hahn–Banach extends its
minorant on the line spanned by v (the zero direction is handled separately).
The private Riesz step supplies the supporting vector in both cases. -/
theorem exists_subgradient_slope_le_inner_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) :
    ∃ g : E, (∀ y, u x + ⟪g, y - x⟫ ≤ u y) ∧
      ∀ ε > 0, ∃ t > 0, (u (x + t • v) - u x) / t ≤ ⟪g, v⟫ + ε := by
  -- Positive difference quotients and their finite infimum.

  -- Construct the one-sided directional slope and its lower envelope.
  let slope : E → ℝ → ℝ := fun w t => (u (x + t • w) - u x) / t
  let p : E → ℝ := fun w =>
    sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
  have hconvex :
      ∀ {z₁ z₂ : E} {a b : ℝ}, z₁ ∈ Set.univ → z₂ ∈ Set.univ →
        0 ≤ a → 0 ≤ b → a + b = 1 →
          u (a • z₁ + b • z₂) ≤ a * u z₁ + b * u z₂ := by
    intro z₁ z₂ a b hz₁ hz₂ ha hb hab
    exact hconv.2 hz₁ hz₂ ha hb hab
  have hslope_mono :
      ∀ {w : E} {a b : ℝ}, 0 < a → a ≤ b → slope w a ≤ slope w b := by
    intro w a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hab0 : 0 ≤ a / b := div_nonneg ha.le hb.le
    have hab1 : 0 ≤ 1 - a / b := sub_nonneg.mpr ((div_le_one hb).2 hab)
    have hsum : a / b + (1 - a / b) = 1 := by
      abel
    have hab' : (a / b) * b = a := div_mul_cancel₀ a (ne_of_gt hb)
    have heq :
        (a / b) • (x + b • w) + (1 - a / b) • x = x + a • w := by
      calc
        (a / b) • (x + b • w) + (1 - a / b) • x =
            (a / b + (1 - a / b)) • x + (a / b * b) • w := by
              module
        _ = x + a • w := by rw [hsum, hab', one_smul]
    have hc := hconvex (z₁ := x + b • w) (z₂ := x) (by simp) (by simp)
      hab0 hab1 hsum
    rw [heq] at hc
    have hc' :
        b * (u (x + a • w) - u x) ≤ a * (u (x + b • w) - u x) := by
      field_simp [ne_of_gt hb] at hc
      nlinarith [hc]
    apply (div_le_div_iff₀ ha hb).2
    nlinarith [hc']
  have hslope_lower :
      ∀ {w : E} {t : ℝ}, 0 < t → u x - u (x - w) ≤ slope w t := by
    intro w t ht
    have htp : 0 < t + 1 := by linarith
    have ha : 0 ≤ t / (t + 1) := div_nonneg ht.le htp.le
    have hb : 0 ≤ (1 : ℝ) / (t + 1) := by positivity
    have hsum : t / (t + 1) + (1 : ℝ) / (t + 1) = 1 := by
      calc
        t / (t + 1) + (1 : ℝ) / (t + 1) =
            (t + 1) / (t + 1) := by
              ring
        _ = 1 := div_self (ne_of_gt htp)
    have hcoef : (1 : ℝ) / (t + 1) * t = t / (t + 1) := by
      ring
    have heq :
        (t / (t + 1)) • (x - w) +
            ((1 : ℝ) / (t + 1)) • (x + t • w) = x := by
      calc
        (t / (t + 1)) • (x - w) +
              ((1 : ℝ) / (t + 1)) • (x + t • w) =
            (t / (t + 1) + (1 : ℝ) / (t + 1)) • x +
              (-(t / (t + 1)) + (1 : ℝ) / (t + 1) * t) • w := by
                module
        _ = x := by rw [hsum, hcoef]; simp
    have hc := hconvex (z₁ := x - w) (z₂ := x + t • w) (by simp) (by simp)
      ha hb hsum
    rw [heq] at hc
    have hc' : t * (u x - u (x - w)) ≤ u (x + t • w) - u x := by
      field_simp [ne_of_gt htp] at hc
      nlinarith [hc]
    apply (le_div_iff₀ ht).2
    nlinarith [hc']
  have hnonempty (w : E) :
      (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)).Nonempty := by
    let t : {t : ℝ // 0 < t} := ⟨1, by norm_num⟩
    exact ⟨slope w t, ⟨t, rfl⟩⟩
  have hbdd (w : E) :
      BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)) := by
    refine ⟨u x - u (x - w), ?_⟩
    rintro z ⟨t, rfl⟩
    exact hslope_lower t.property
  have hp_lower : ∀ w : E, u x - u (x - w) ≤ p w := by
    intro w
    change u x - u (x - w) ≤
      sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
    apply le_csInf (hnonempty w)
    rintro z ⟨t, rfl⟩
    exact hslope_lower t.property
  have hp_le : ∀ (w : E) (t : {t : ℝ // 0 < t}), p w ≤ slope w t := by
    intro w t
    change sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)) ≤ slope w t
    exact csInf_le (hbdd w) ⟨t, rfl⟩
  have hp_zero : p 0 = 0 := by
    apply le_antisymm
    · simpa [slope] using hp_le 0 ⟨1, by norm_num⟩
    · simpa [slope] using hp_lower 0

  -- Prove positive homogeneity and subadditivity of the slope envelope.
  have hslope_scale :
      ∀ {w : E} {c t : ℝ}, 0 < c → 0 < t →
        slope (c • w) t = c * slope w (c * t) := by
    intro w c t hc ht
    change
      (u (x + t • (c • w)) - u x) / t =
        c * ((u (x + (c * t) • w) - u x) / (c * t))
    rw [smul_smul, mul_comm t c]
    have hct : 0 < c * t := mul_pos hc ht
    field_simp [ne_of_gt hc, ne_of_gt ht, ne_of_gt hct]
  -- Positive homogeneity and subadditivity make p a sublinear envelope.
  have hp_scale :
      ∀ {w : E} {c : ℝ}, 0 < c → p (c • w) = c * p w := by
    intro w c hc
    have h₁ : p (c • w) / c ≤ p w := by
      change p (c • w) / c ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
      apply le_csInf (hnonempty w)
      rintro z ⟨t, rfl⟩
      let r : {t : ℝ // 0 < t} := ⟨(t : ℝ) / c, div_pos t.property hc⟩
      have harg : c * ((t : ℝ) / c) = (t : ℝ) := by
        field_simp [ne_of_gt hc]
      calc
        p (c • w) / c ≤ slope (c • w) r / c :=
          div_le_div_of_nonneg_right (hp_le (c • w) r) hc.le
        _ = slope w t := by
          rw [hslope_scale hc r.property, harg]
          apply (div_eq_iff (ne_of_gt hc)).2
          ring
    have h₁' : p (c • w) ≤ c * p w := by
      have h := (div_le_iff₀ hc).1 h₁
      simpa [mul_comm] using h
    have h₂ : c * p w ≤ p (c • w) := by
      change c * p w ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope (c • w) t))
      apply le_csInf (hnonempty (c • w))
      rintro z ⟨t, rfl⟩
      let r : {t : ℝ // 0 < t} := ⟨c * (t : ℝ), mul_pos hc t.property⟩
      calc
        c * p w ≤ c * slope w r :=
          mul_le_mul_of_nonneg_left (hp_le w r) hc.le
        _ = slope (c • w) t := by
          rw [hslope_scale hc t.property]
    exact le_antisymm h₁' h₂
  have slope_add :
      ∀ {w₁ w₂ : E} {t : ℝ}, 0 < t →
        slope (w₁ + w₂) t ≤
          slope w₁ (2 * t) + slope w₂ (2 * t) := by
    intro w₁ w₂ t ht
    have heq :
        (1 / 2 : ℝ) • (x + (2 * t) • w₁) +
            (1 / 2 : ℝ) • (x + (2 * t) • w₂) =
          x + t • (w₁ + w₂) := by
      module
    have hc := hconvex (z₁ := x + (2 * t) • w₁) (z₂ := x + (2 * t) • w₂)
      (by simp) (by simp)
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [heq] at hc
    dsimp [slope]
    apply (div_le_iff₀ ht).2
    have hid :
        ((u (x + (2 * t) • w₁) - u x) / (2 * t) +
            (u (x + (2 * t) • w₂) - u x) / (2 * t)) * t =
          (u (x + (2 * t) • w₁) + u (x + (2 * t) • w₂) - 2 * u x) / 2 := by
      field_simp [ne_of_gt ht]
      ring
    rw [hid]
    linarith [hc]
  have hexists :
      ∀ (w : E) {ε : ℝ}, 0 < ε →
        ∃ t : {t : ℝ // 0 < t}, slope w t < p w + ε := by
    intro w ε hε
    by_contra hnot
    have hforall : ∀ t : {t : ℝ // 0 < t}, p w + ε ≤ slope w t := by
      intro t
      exact le_of_not_gt (fun hlt => hnot ⟨t, hlt⟩)
    have hp' : p w + ε ≤ p w := by
      change p w + ε ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
      apply le_csInf (hnonempty w)
      rintro z ⟨t, rfl⟩
      exact hforall t
    linarith
  have hp_add : ∀ w₁ w₂ : E, p (w₁ + w₂) ≤ p w₁ + p w₂ := by
    intro w₁ w₂
    by_contra h
    have hlt : p w₁ + p w₂ < p (w₁ + w₂) := lt_of_not_ge h
    let ε : ℝ := (p (w₁ + w₂) - p w₁ - p w₂) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨t₁, ht₁⟩ := hexists w₁ hε
    obtain ⟨t₂, ht₂⟩ := hexists w₂ hε
    have htmin : 0 < min (t₁ : ℝ) (t₂ : ℝ) :=
      lt_min t₁.property t₂.property
    let t : {t : ℝ // 0 < t} :=
      ⟨min (t₁ : ℝ) t₂ / 2, div_pos htmin (by norm_num)⟩
    have h2t₁ : 2 * (t : ℝ) ≤ (t₁ : ℝ) := by
      dsimp [t]
      linarith [min_le_left (t₁ : ℝ) t₂]
    have h2t₂ : 2 * (t : ℝ) ≤ (t₂ : ℝ) := by
      dsimp [t]
      linarith [min_le_right (t₁ : ℝ) t₂]
    have hpos : 0 < 2 * (t : ℝ) := mul_pos (by norm_num) t.property
    have h₁ := hslope_mono (w := w₁) (a := 2 * (t : ℝ)) (b := t₁)
      hpos h2t₁
    have h₂ := hslope_mono (w := w₂) (a := 2 * (t : ℝ)) (b := t₂)
      hpos h2t₂
    have hsum := slope_add (w₁ := w₁) (w₂ := w₂) t.property
    have hp := hp_le (w₁ + w₂) t
    have hbound :
        p (w₁ + w₂) < p w₁ + p w₂ + 2 * ε := by
      calc
        p (w₁ + w₂) ≤ slope (w₁ + w₂) t := hp
        _ ≤ slope w₁ (2 * (t : ℝ)) + slope w₂ (2 * (t : ℝ)) := hsum
        _ ≤ slope w₁ (t₁ : ℝ) + slope w₂ (t₂ : ℝ) := add_le_add h₁ h₂
        _ < (p w₁ + ε) + (p w₂ + ε) := add_lt_add ht₁ ht₂
        _ = p w₁ + p w₂ + 2 * ε := by ring
    dsimp [ε] at hε hbound ⊢
    linarith
  -- The unit difference quotient bounds the envelope by the actual increment.

  -- Apply the supporting-functional argument to obtain a subgradient.
  have hp_increment : ∀ w, p w ≤ u (x + w) - u x := by
    intro w
    simpa [slope] using hp_le w ⟨1, by norm_num⟩
  -- Extend a linear minorant, then use the shared supporting-vector construction.
  by_cases hv : v = 0
  · let f : E →ₗ.[ℝ] ℝ := (0 : E →ₗ[ℝ] ℝ).toPMap ⊥
    have hf : ∀ z : f.domain, f z ≤ p z := by
      intro z
      have hz : (z : E) = 0 := by
        have hz' : (z : E) ∈ (⊥ : Submodule ℝ E) := by
          exact z.property
        simpa only [Submodule.mem_bot] using hz'
      have hz'' : z = 0 := Subtype.ext hz
      rw [hz'']
      simp [f, hp_zero]
    obtain ⟨ℓ, hℓf, hℓp⟩ :=
      exists_extension_of_le_sublinear f p
        (fun c hc w => hp_scale (w := w) hc)
        (fun w₁ w₂ => hp_add w₁ w₂) hf
    obtain ⟨g, hpair, hsubgradient⟩ :=
      exists_supporting_vector_of_linear_minorant u x p hp_increment ℓ hℓp
    refine ⟨g, hsubgradient, ?_⟩
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    have hg0 : ⟪g, (0 : E)⟫ = 0 := by
      rw [hpair]
      exact ℓ.map_zero
    simp only [hv, smul_zero, add_zero, sub_self, zero_div, hg0, add_zero]
    linarith
  · let f : E →ₗ.[ℝ] ℝ :=
      LinearPMap.mkSpanSingleton v (p v) hv
    have hf : ∀ z : f.domain, f z ≤ p z := by
      intro z
      have hzdom : (z : E) ∈ ℝ ∙ v := z.property
      rcases Submodule.mem_span_singleton.mp hzdom with ⟨c, hc⟩
      let z₀ : f.domain :=
        ⟨v, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
      have hz : z = c • z₀ := by
        apply Subtype.ext
        change (z : E) = c • v
        exact hc.symm
      have hf₀ : f z₀ = p v := by
        change (LinearPMap.mkSpanSingleton v (p v) hv) ⟨v, _⟩ = p v
        exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hv (p v)
      rw [hz, f.map_smul, hf₀]
      change c * p v ≤ p (c • v)
      rcases lt_trichotomy c 0 with hcneg | rfl | hcpos
      · have hzero : 0 ≤ p (c • v) + p ((-c) • v) := by
          have h := hp_add (c • v) ((-c) • v)
          have hcv : c • v + (-c) • v = 0 := by module
          rw [hcv, hp_zero] at h
          exact h
        have hpc : p (c • v) = (-c) * p (-v) := by
          have heq : c • v = (-c) • (-v) := by module
          rw [heq, hp_scale (w := -v) (c := -c) (neg_pos.mpr hcneg)]
        have hpneg : p ((-c) • v) = (-c) * p v :=
          hp_scale (w := v) (c := -c) (neg_pos.mpr hcneg)
        rw [hpc, hpneg] at hzero
        calc
          c * p v = -((-c) * p v) := by ring
          _ ≤ (-c) * p (-v) := by linarith
          _ = p (c • v) := hpc.symm
      · simp [hp_zero]
      · rw [hp_scale (w := v) (c := c) hcpos]
    obtain ⟨ℓ, hℓf, hℓp⟩ :=
      exists_extension_of_le_sublinear f p
        (fun c hc w => hp_scale (w := w) hc)
        (fun w₁ w₂ => hp_add w₁ w₂) hf
    obtain ⟨g, hpair, hsubgradient⟩ :=
      exists_supporting_vector_of_linear_minorant u x p hp_increment ℓ hℓp
    have hℓv : ℓ v = p v := by
      let z₀ : f.domain :=
        ⟨v, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
      have hf₀ : f z₀ = p v := by
        change (LinearPMap.mkSpanSingleton v (p v) hv) ⟨v, _⟩ = p v
        exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hv (p v)
      change ℓ v = p v
      calc
        ℓ v = ℓ (z₀ : E) := rfl
        _ = f z₀ := hℓf z₀
        _ = p v := hf₀
    refine ⟨g, hsubgradient, ?_⟩
    intro ε hε
    obtain ⟨t, ht⟩ := hexists v hε
    refine ⟨(t : ℝ), t.property, ?_⟩
    have hlt : slope v t < p v + ε := ht
    have heq : p v + ε = ⟪g, v⟫ + ε := by
      rw [← hℓv, hpair]
    dsimp [slope] at hlt
    exact le_of_lt (heq ▸ hlt)

end SubgradientMaxFormula

end FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis

open Set Metric

/-- Uniform boundedness of all domain-relative supporting slopes on a compact subset
of an open convex domain. -/
theorem exists_uniform_subgradient_bound_on_compact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {Ω K : Set E} {v : E → ℝ} (hΩ : IsOpen Ω)
    (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ R : ℝ,
      0 ≤ R ∧
        (∀ x ∈ K, ∃ p : E, ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y) ∧
          (∀ x ∈ K, ∀ p : E, (∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y) → ‖p‖ ≤ R) := by
  classical
  have hsupport : ∀ x ∈ Ω, ∃ p : E, ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y := by
    intro x hx
    let f : E → EReal := fun z => if z + x ∈ Ω then (v (z + x) : EReal) else ⊤
    have hfbot : ∀ z, f z ≠ ⊥ := by
      intro z
      by_cases hz : z + x ∈ Ω <;> simp [f, hz]
    have hfconv : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      intro p hp q hq a b ha hb hab
      change f p.1 ≤ (p.2 : EReal) at hp
      change f q.1 ≤ (q.2 : EReal) at hq
      have hpΩ : p.1 + x ∈ Ω := by
        by_contra hpΩ
        simp [f, hpΩ] at hp
      have hqΩ : q.1 + x ∈ Ω := by
        by_contra hqΩ
        simp [f, hqΩ] at hq
      have harg : a • p.1 + b • q.1 + x = a • (p.1 + x) + b • (q.1 + x) := by
        calc
          _ = a • p.1 + b • q.1 + (a + b) • x := by rw [hab, one_smul]
          _ = _ := by rw [smul_add, smul_add, add_smul]; abel
      have hdom : a • p.1 + b • q.1 + x ∈ Ω := by
        rw [harg]
        exact hv.1 hpΩ hqΩ ha hb hab
      have hval : v (a • (p.1 + x) + b • (q.1 + x)) ≤ a • v (p.1 + x) + b • v (q.1 + x) :=
        hv.2 hpΩ hqΩ ha hb hab
      change f (a • p.1 + b • q.1) ≤ ((a • p.2 + b • q.2 : ℝ) : EReal)
      rw [show f (a • p.1 + b • q.1) = (v (a • p.1 + b • q.1 + x) : EReal) by
          simp only [f, ite_eq_left hdom]]
      have hpv : v (p.1 + x) ≤ p.2 :=
        EReal.coe_le_coe_iff.mp (by simpa only [f, ite_eq_left hpΩ] using hp)
      have hqv : v (q.1 + x) ≤ q.2 :=
        EReal.coe_le_coe_iff.mp (by simpa only [f, ite_eq_left hqΩ] using hq)
      apply EReal.coe_le_coe_iff.mpr
      rw [harg]
      have hbnd : a * v (p.1 + x) + b * v (q.1 + x) ≤ a * p.2 + b * q.2 :=
        add_le_add (mul_le_mul_of_nonneg_left hpv ha) (mul_le_mul_of_nonneg_left hqv hb)
      exact hval.trans (by simpa only [smul_eq_mul] using hbnd)
    have hf : ConvexPotential f := ⟨hfbot, hfconv⟩
    have hzero : (0 : E) ∈ interior {z | f z ≠ ⊤} := by
      apply mem_interior_iff_mem_nhds.mpr
      have ht : ContinuousAt (fun z : E => z + x) 0 := continuousAt_id.add continuousAt_const
      have ht' : Filter.Tendsto (fun z : E => z + x) (nhds 0) (nhds x) := by
        change Filter.Tendsto (fun z : E => z + x) (nhds 0) (nhds (0 + x)) at ht
        simpa only [zero_add] using ht
      filter_upwards [ht'.eventually (hΩ.mem_nhds hx)] with z hz
      change z + x ∈ Ω at hz
      dsimp only [f]
      rw [ite_eq_left hz]
      exact EReal.coe_ne_top _
    obtain ⟨a, ha⟩ := exists_supporting_affine_at_zero f hf hzero
    refine ⟨a, ?_⟩
    intro y hy
    have hh : ((⟪a, y - x⟫ + v x : ℝ) : EReal) ≤ (v y : EReal) := by
      simpa [f, hx, hy] using ha (y - x)
    simpa only [add_comm] using EReal.coe_le_coe_iff.mp hh
  have hlocal :
    ∀ x ∈ Ω,
      ∃ r : ℝ,
        0 < r ∧
          ∀ z,
            dist z x < r / 2 →
              ∀ p : E, (∀ y ∈ Ω, v z + ⟪p, y - z⟫ ≤ v y) → ‖p‖ ≤ 8 * (|v x| + 1) / r := by
    intro x hx
    have hcx : ContinuousAt v x := (hvc x hx).continuousAt (hΩ.mem_nhds hx)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcx 1 zero_lt_one
    let r : ℝ := min ε δ
    have hr : 0 < r := lt_min hεpos hδpos
    have hclose : ∀ w, dist w x < r → |v w - v x| < 1 := by
      intro w hw
      have hwδ : dist w x < δ := lt_of_lt_of_le hw (min_le_right ε δ)
      have h := hδ hwδ
      simpa [Real.dist_eq] using h
    refine ⟨r, hr, ?_⟩
    intro z hz p hp
    have hbound_value : ∀ w, dist w x < r → |v w| ≤ |v x| + 1 := by
      intro w hw
      have hdiff : |v w - v x| < 1 := hclose w hw
      calc
        |v w| = |(v w - v x) + v x| := by
          congr 1
          ring
        _ ≤ |v w - v x| + |v x| := abs_add_le _ _
        _ ≤ 1 + |v x| := by linarith only [hdiff]
        _ = |v x| + 1 := by ring
    have hball : closedBall z (r / 4) ⊆ Ω := by
      intro y hy
      have hyx : dist y x < r := by
        have ht := dist_triangle y z x
        have hyd : dist y z ≤ r / 4 := mem_closedBall.mp hy
        linarith
      exact hε (mem_ball.mpr (lt_of_lt_of_le hyx (min_le_left ε δ)))
    have hvalues : ∀ y ∈ closedBall z (r / 4), |v y| ≤ |v x| + 1 := by
      intro y hy
      apply hbound_value
      have ht := dist_triangle y z x
      have hyd : dist y z ≤ r / 4 := mem_closedBall.mp hy
      linarith
    have hnorm :=
      norm_subgradient_le_of_closedBall (show 0 < r / 4 by positivity) hball hvalues hp
    convert hnorm using 1
    ring
  let ρ : Ω → ℝ := fun z => Classical.choose (hlocal z z.property)
  have hρ :
    ∀ z : Ω,
      0 < ρ z ∧
        ∀ w,
          dist w (z : E) < ρ z / 2 →
            ∀ p : E, (∀ y ∈ Ω, v w + ⟪p, y - w⟫ ≤ v y) → ‖p‖ ≤ 8 * (|v (z : E)| + 1) / ρ z := by
    intro z
    exact Classical.choose_spec (hlocal z z.property)
  have hcover : K ⊆ ⋃ z : Ω, ball (z : E) (ρ z / 2) := by
    intro x hx
    let z : Ω := ⟨x, hKΩ hx⟩
    have hz : dist x (z : E) < ρ z / 2 := by
      simp only [z, dist_self]
      linarith [hρ z |>.1]
    refine mem_iUnion.mpr ⟨z, ?_⟩
    exact mem_ball.mpr hz
  obtain ⟨s, hs⟩ :=
    hK.elim_finite_subcover (fun z : Ω => ball (z : E) (ρ z / 2)) (fun _ => isOpen_ball) hcover
  let B : Ω → ℝ := fun z => 8 * (|v (z : E)| + 1) / ρ z
  let R : ℝ := ∑ z ∈ s, B z
  have hB : ∀ z : Ω, 0 ≤ B z := by
    intro z
    dsimp [B]
    have hzρ : 0 < ρ z := hρ z |>.1
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg (fun z hz => hB z)
  refine ⟨R, hR, ?_, ?_⟩
  · intro x hx
    exact hsupport x (hKΩ hx)
  · intro x hx p hp
    have hxs := hs hx
    rcases mem_iUnion.mp hxs with ⟨z, hxs⟩
    rcases mem_iUnion.mp hxs with ⟨hzs, hball⟩
    have hdist : dist x (z : E) < ρ z / 2 := mem_ball.mp hball
    have hpz : ‖p‖ ≤ B z := by
      dsimp [B]
      exact (hρ z).2 x hdist p hp
    have hsum : B z ≤ ∑ w ∈ s, B w := by exact Finset.single_le_sum (fun w hw => hB w) hzs
    calc
      ‖p‖ ≤ B z := hpz
      _ ≤ ∑ w ∈ s, B w := hsum
      _ = R := by rfl


end FunctionalInequalities.Analysis
