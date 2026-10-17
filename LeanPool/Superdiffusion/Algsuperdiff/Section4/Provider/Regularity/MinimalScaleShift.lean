/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# MinimalScaleShift

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 1/Step 2: the parameter names, the `+ k + 3` shift, and the
# tail arithmetic

## Contents

* `stepOneS`, `stepOneSEighth`, `stepOneDelta` — the Step-1 parameter names of
  `e.parameter.choices.regularity`: `s := 1/4`, the minimal-scale argument
  `s/8`, and `δ := C₁⁻¹(1-α)`.
* `minimalScaleX` — `e.def.X.m.alpha`: `X_m(α) := Z_m + k + 3`, written for an
  arbitrary `ℕ∞`-valued `Z` so that the shift is a lemma about `Z`, never about
  a particular producer.
* `measurable_minimalScaleX`, `le_minimalScaleX`, `tail_minimalScaleX_subset` —
  the three facts the shift contributes: measurability is inherited (`ℕ∞` is
  discrete), `Z ≤ X` pointwise (so every `a.s.` clause gated by `Z` transports
  to the strictly smaller gate `X`), and the tail event of `X` at level `N` is
  contained in the tail event of `Z` at level `N - (k+3)`.
* `exp_tail_dom`, `rate_dom`, `gate_of_sq_le` — the three abstract-real
  inequalities behind the conversion of the `p.minimal.scale.separation.sec4`
  tail into the shape printed in the anchor's minimal-scale clause.  Every
  transcendental atom is opaque: `Real.exp` is touched only through
  `Real.exp_le_exp`, and no nonlinear-arithmetic closer is used anywhere.

## References

* ABK26, `t.regularity` Steps 1--2.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory

/-! ## The Step-1 parameters -/

/-- The Step-1 scale parameter `s := 1/4` of `e.parameter.choices.regularity`. -/
noncomputable def stepOneS : ℝ := 1 / 4

/-- The minimal-scale argument `s/8` of `e.def.X.m.alpha`, i.e. the first argument
of `Z_m(s/8, δ)`. -/
noncomputable def stepOneSEighth : ℝ := stepOneS / 8

/-- The Step-1 tolerance `δ := C₁⁻¹(1-α)` of `e.parameter.choices.regularity`.
`C₁` is the abstract Step-1 constant. -/
noncomputable def stepOneDelta (C1 alpha : ℝ) : ℝ := C1⁻¹ * (1 - alpha)

/-- `s/8 = 1/32`. -/
theorem stepOneSEighth_eq : stepOneSEighth = 1 / 32 := by
  norm_num [stepOneSEighth, stepOneS]

/-- `0 < s/8`. -/
theorem stepOneSEighth_pos : 0 < stepOneSEighth := by
  rw [stepOneSEighth_eq]
  norm_num

/-- `s/8 ∈ (0, 1/4]`: the `s`-window of `p.minimal.scale.separation.sec4`. -/
theorem stepOneSEighth_mem : stepOneSEighth ∈ Set.Ioc (0 : ℝ) (1 / 4) := by
  rw [stepOneSEighth_eq]
  exact ⟨by norm_num, by norm_num⟩

/-- `(s/8)^9 ≤ 1`. -/
theorem stepOneSEighth_pow_le_one : stepOneSEighth ^ (9 : ℕ) ≤ 1 := by
  rw [stepOneSEighth_eq]
  norm_num

/-- `0 < (s/8)^9`. -/
theorem stepOneSEighth_pow_pos : 0 < stepOneSEighth ^ (9 : ℕ) :=
  pow_pos stepOneSEighth_pos 9

/-- `δ ∈ (0, 1/2]`: the `δ`-window of `p.minimal.scale.separation.sec4`, at the
pin `C₁ ≥ 2`. -/
theorem stepOneDelta_mem {C1 alpha : ℝ} (hC1 : 2 ≤ C1) (halpha0 : 0 < alpha)
    (halpha1 : alpha < 1) : stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1]
  have hinv : C1⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hC1pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hC1]
  refine ⟨mul_pos (inv_pos.mpr hC1pos) (by linarith only [halpha1]), ?_⟩
  calc stepOneDelta C1 alpha = C1⁻¹ * (1 - alpha) := rfl
    _ ≤ C1⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left (by linarith only [halpha0])
          (le_of_lt (inv_pos.mpr hC1pos))
    _ = C1⁻¹ := mul_one _
    _ ≤ 1 / 2 := hinv

/-! ## The `+ k + 3` shift -/

section Shift

variable {Omega : Type*}

/-- `e.def.X.m.alpha`: the Step-2 minimal scale `X_m(α) := Z_m(s/8, δ) + k + 3`, as
a function of an arbitrary `ℕ∞`-valued minimal scale `Z` and the abstract
Step-1 constant `k`. -/
def minimalScaleX (Z : Omega → ℕ∞) (k : ℕ) : Omega → ℕ∞ :=
  fun omega => Z omega + (k : ℕ∞) + 3

/-- `X_m(α) = Z_m + (k+3)` with the offset collected into a single natural cast. -/
theorem minimalScaleX_eq_add_cast (Z : Omega → ℕ∞) (k : ℕ) (omega : Omega) :
    minimalScaleX Z k omega = Z omega + ((k + 3 : ℕ) : ℕ∞) := by
  simp only [minimalScaleX]
  push_cast
  ring

/-- `Z_m ≤ X_m(α)` pointwise.  This is what transports a good-scales clause gated
by `Z_m ≤ m - n` to the same clause gated by `X_m(α) ≤ m - n`. -/
theorem le_minimalScaleX (Z : Omega → ℕ∞) (k : ℕ) (omega : Omega) :
    Z omega ≤ minimalScaleX Z k omega := by
  rw [minimalScaleX_eq_add_cast]
  exact le_self_add

/-- Measurability of `X_m(α)` is inherited from `Z_m`: `ℕ∞` is a discrete
measurable space, so post-composition with `· + k + 3` is measurable. -/
theorem measurable_minimalScaleX [MeasurableSpace Omega] {Z : Omega → ℕ∞}
    (hZ : Measurable Z) (k : ℕ) : Measurable (minimalScaleX Z k) :=
  (Measurable.of_discrete (f := fun x : ℕ∞ => x + (k : ℕ∞) + 3)).comp hZ

/-- The `+ k + 3` index shift on tail events: `{N ≤ X_m(α)} ⊆ {N - (k+3) ≤ Z_m}`. -/
theorem tail_minimalScaleX_subset (Z : Omega → ℕ∞) (k N : ℕ) :
    {omega | (N : ℕ∞) ≤ minimalScaleX Z k omega} ⊆
      {omega | ((N - (k + 3) : ℕ) : ℕ∞) ≤ Z omega} := by
  intro omega homega
  simp only [Set.mem_ofPred_eq, minimalScaleX_eq_add_cast] at homega
  simp only [Set.mem_ofPred_eq]
  rcases eq_or_ne (Z omega) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hj] at homega ⊢
    rw [← Nat.cast_add, Nat.cast_le] at homega
    exact Nat.cast_le.mpr (by omega)

end Shift

/-! ## The abstract-real tail arithmetic

All three lemmas are stated for opaque reals.  `Real.exp` is used only through
`Real.exp_le_exp`; the rest is monotonicity of multiplication and division. -/

/-- Prefactor-and-rate domination for exponential tails: a larger prefactor and a
smaller rate weaken the bound. -/
theorem exp_tail_dom {Cm Co A B : ℝ} (hCm : 0 < Cm) (hCmCo : Cm ≤ Co)
    (hBA : B ≤ A) : Cm * Real.exp (-A) ≤ Co * Real.exp (-B) := by
  have hexp : Real.exp (-A) ≤ Real.exp (-B) :=
    Real.exp_le_exp.mpr (by linarith only [hBA])
  calc Cm * Real.exp (-A) ≤ Cm * Real.exp (-B) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hCm)
    _ ≤ Co * Real.exp (-B) :=
        mul_le_mul_of_nonneg_right hCmCo (le_of_lt (Real.exp_pos _))

/-- With `a := 1 - α`, `v := N - C`, `t := N - k - 4`, `Cm` the
`p.minimal.scale.separation.sec4` constant and `Co` the produced one, the
anchor's rate `a²·v/(Co·g)` is dominated by the producer's rate
`t·s⁹·cs²·(C₁⁻¹a)²/(Cm·g)` as soon as `Cm ≤ s⁹ cs² C₁⁻² Co`. -/
theorem rate_dom {a g s cs C1 Cm Co t v : ℝ} (hg : 0 < g) (hCm : 0 < Cm)
    (hCo : 0 < Co) (ht : 0 ≤ t) (hvt : v ≤ t)
    (hkey : Cm ≤ s ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) * Co) :
    a ^ (2 : ℕ) * v / (Co * g) ≤
      t * s ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹ * a) ^ (2 : ℕ) / (Cm * g) := by
  have hnn : 0 ≤ a ^ (2 : ℕ) * t / g :=
    div_nonneg (mul_nonneg (sq_nonneg a) ht) (le_of_lt hg)
  have h1 : a ^ (2 : ℕ) * v / (Co * g) ≤ a ^ (2 : ℕ) * t / (Co * g) := by
    gcongr
  have h2 : a ^ (2 : ℕ) * t / (Co * g) = a ^ (2 : ℕ) * t / g * (1 / Co) := by
    ring
  have h3 : t * s ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹ * a) ^ (2 : ℕ) / (Cm * g) =
      a ^ (2 : ℕ) * t / g * (s ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) / Cm) := by
    ring
  have h4 : (1 : ℝ) / Co ≤
      s ^ (9 : ℕ) * cs ^ (2 : ℕ) * (C1⁻¹) ^ (2 : ℕ) / Cm := by
    rw [div_le_div_iff₀ hCo hCm]
    linarith only [hkey]
  rw [h3]
  refine h1.trans ?_
  rw [h2]
  exact mul_le_mul_of_nonneg_left h4 hnn

/-- **The `γ`-gate of `p.minimal.scale.separation.sec4` at the Step-1 parameters.**
From the theorem's own hypothesis `α ≤ 1 - C γ^{1/2}` in the squared form `Co²
g ≤ a²` (with `a:= 1 - α`), together with a size condition on `Co`, the second
branch of the producer's `min` is met at `δ = C₁⁻¹(1-α)`. -/
theorem gate_of_sq_le {a g s cs C1 Cm Co : ℝ} (hg : 0 < g) (hs : 0 ≤ s)
    (hsq : Co ^ (2 : ℕ) * g ≤ a ^ (2 : ℕ))
    (hkey : 1 ≤ (Cm⁻¹) ^ (10 : ℕ) *
      ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) * Co ^ (2 : ℕ)) :
    g ≤ (Cm⁻¹) ^ (10 : ℕ) *
      ((C1⁻¹ * a) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) := by
  have hR : 0 ≤ (Cm⁻¹) ^ (10 : ℕ) *
      ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) := by
    have h9 : 0 ≤ s ^ (9 : ℕ) := pow_nonneg hs 9
    positivity
  calc g = 1 * g := (one_mul g).symm
    _ ≤ (Cm⁻¹) ^ (10 : ℕ) *
          ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) * Co ^ (2 : ℕ) * g :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hg)
    _ = (Cm⁻¹) ^ (10 : ℕ) * ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) *
          (Co ^ (2 : ℕ) * g) := by ring
    _ ≤ (Cm⁻¹) ^ (10 : ℕ) * ((C1⁻¹) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) *
          a ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hsq hR
    _ = (Cm⁻¹) ^ (10 : ℕ) *
          ((C1⁻¹ * a) ^ (2 : ℕ) * cs ^ (2 : ℕ) * s ^ (9 : ℕ)) := by ring

/-- The small-`N` branch of the shifted tail: when `N ≤ C`, the printed right-hand
side is at least `1`, so the trivial probability bound already gives the
estimate. -/
theorem one_le_shifted_exp {a g x Co : ℝ} (hCo : 1 ≤ Co) (hg : 0 < g)
    (hx : x ≤ Co) :
    (1 : ℝ) ≤ Co * Real.exp (-(a ^ (2 : ℕ) * (x - Co)) / (Co * g)) := by
  have hCo0 : (0 : ℝ) < Co := lt_of_lt_of_le one_pos hCo
  have hxle : a ^ (2 : ℕ) * (x - Co) ≤ a ^ (2 : ℕ) * 0 :=
    mul_le_mul_of_nonneg_left (by linarith only [hx]) (sq_nonneg a)
  rw [mul_zero] at hxle
  have harg : 0 ≤ -(a ^ (2 : ℕ) * (x - Co)) / (Co * g) :=
    div_nonneg (by linarith only [hxle]) (le_of_lt (mul_pos hCo0 hg))
  have hexp : (1 : ℝ) ≤ Real.exp (-(a ^ (2 : ℕ) * (x - Co)) / (Co * g)) :=
    Real.one_le_exp harg
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ Co * Real.exp (-(a ^ (2 : ℕ) * (x - Co)) / (Co * g)) :=
        mul_le_mul hCo hexp zero_le_one (le_of_lt hCo0)

end Algsuperdiff.Section4.Provider.Regularity
