/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# EnnrealShell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `ℝ≥0∞` shell of the harmonic-approximation clauses

The frozen §4.3 anchor states both of its clauses in `ℝ≥0∞`: an indicator on
the good event on the left, and `ENNReal.ofReal`-scalars multiplying `ℝ≥0∞`-valued norm
carriers on the right.  This module is the (analysis-free) bridge between the
two, in three atoms:

* `ofReal_mul_toReal_le` — the product regrouping
  `ofReal (c * X.toReal) ≤ ofReal c * X`, valid at `X = ⊤` as well (there the
  left side collapses to `0`), so that no finiteness hypothesis on the
  right-hand carriers is ever needed;
* `le_ofReal_mul_add_ofReal_mul` — the two-summand shell: a real inequality
  between `toReal` values plus finiteness of the *left* side gives the frozen
  `ℝ≥0∞` inequality;
* `indicator_le_of_mem` — the indicator collapse on the good event.

The fourth atom, `eLpNorm_ne_top_of_eq_h10`, supplies the one finiteness fact
the shell does need: the anchor's left-hand side is `‖u - v‖_{L²(x+□_n)}` and
the anchor's own binders give `u - v = w` for an `H¹₀(x+□_n)` witness `w`, whose
`L²` datum is part of its type.

No mathematics of the manuscript enters here; nothing in this file knows what a
good event, a coefficient field or a scale is.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the two clauses whose `ℝ≥0∞`
  shape is targeted).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `ofReal`-product regrouping -/

/-- **The product regrouping.**  Pushing a nonnegative real scalar through a
`toReal` never increases the value, *including* at `X = ⊤`, where the left-hand
side collapses to `0` while the right-hand side is `0` or `⊤`.

This is what makes the shell free of finiteness hypotheses on the right-hand
carriers: the frozen theorem's `[g]_{H^s}` and `‖∇h‖_{L²}` legs are never
known to be finite (the anchor's clause (iv) gives `MemLp` of the *kernel*, on
`□_m`, not on the intersected window). -/
theorem ofReal_mul_toReal_le {c : ℝ} (hc : 0 ≤ c) (X : ℝ≥0∞) :
    ENNReal.ofReal (c * X.toReal) ≤ ENNReal.ofReal c * X := by
  rcases eq_or_ne X ⊤ with hX | hX
  · rw [hX, ENNReal.toReal_top, mul_zero, ENNReal.ofReal_zero]
    exact zero_le
  · exact le_of_eq (by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hX])

/-- **The two-summand shell.**

From a real inequality between `toReal` values, plus finiteness of the
left-hand side alone, to the frozen theorem's `ℝ≥0∞` shape `A ≤ ofReal c₁ * X +
ofReal c₂ * Y`. -/
theorem le_ofReal_mul_add_ofReal_mul {A X Y : ℝ≥0∞} {c₁ c₂ : ℝ} (hA : A ≠ ⊤)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : A.toReal ≤ c₁ * X.toReal + c₂ * Y.toReal) :
    A ≤ ENNReal.ofReal c₁ * X + ENNReal.ofReal c₂ * Y := by
  have hx : (0 : ℝ) ≤ c₁ * X.toReal := mul_nonneg hc₁ ENNReal.toReal_nonneg
  have hy : (0 : ℝ) ≤ c₂ * Y.toReal := mul_nonneg hc₂ ENNReal.toReal_nonneg
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal (c₁ * X.toReal + c₂ * Y.toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (c₁ * X.toReal) + ENNReal.ofReal (c₂ * Y.toReal) :=
        ENNReal.ofReal_add hx hy
    _ ≤ ENNReal.ofReal c₁ * X + ENNReal.ofReal c₂ * Y :=
        add_le_add (ofReal_mul_toReal_le hc₁ X) (ofReal_mul_toReal_le hc₂ Y)

/-- **The four-summand shell with the in-bracket companion.**

The frozen theorem's *general* clause has the shape `ofReal c₁ * (X + ofReal b)
+ ofReal c₂ * Y + ofReal c₃ * Z + ofReal c₄ * W`, the companion `b` sitting
inside the bracket with no constant of its own.  Same principle as the
two-summand shell: only the left-hand side must be finite. -/
theorem le_ofReal_mul_bracket_add_three {A X Y Z W : ℝ≥0∞} {c₁ b c₂ c₃ c₄ : ℝ}
    (hA : A ≠ ⊤) (hc₁ : 0 ≤ c₁) (hb : 0 ≤ b) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hc₄ : 0 ≤ c₄)
    (h : A.toReal ≤
      c₁ * (X.toReal + b) + c₂ * Y.toReal + c₃ * Z.toReal + c₄ * W.toReal) :
    A ≤ ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
      ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W := by
  have hxb : (0 : ℝ) ≤ c₁ * (X.toReal + b) :=
    mul_nonneg hc₁ (add_nonneg ENNReal.toReal_nonneg hb)
  have hy : (0 : ℝ) ≤ c₂ * Y.toReal := mul_nonneg hc₂ ENNReal.toReal_nonneg
  have hz : (0 : ℝ) ≤ c₃ * Z.toReal := mul_nonneg hc₃ ENNReal.toReal_nonneg
  have hw : (0 : ℝ) ≤ c₄ * W.toReal := mul_nonneg hc₄ ENNReal.toReal_nonneg
  have hbracket : ENNReal.ofReal (c₁ * (X.toReal + b)) ≤
      ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) := by
    have hsplit : c₁ * (X.toReal + b) = c₁ * X.toReal + c₁ * b := by ring
    calc ENNReal.ofReal (c₁ * (X.toReal + b))
        = ENNReal.ofReal (c₁ * X.toReal) + ENNReal.ofReal (c₁ * b) := by
          rw [hsplit, ENNReal.ofReal_add (mul_nonneg hc₁ ENNReal.toReal_nonneg)
            (mul_nonneg hc₁ hb)]
      _ ≤ ENNReal.ofReal c₁ * X + ENNReal.ofReal c₁ * ENNReal.ofReal b :=
          add_le_add (ofReal_mul_toReal_le hc₁ X)
            (le_of_eq (ENNReal.ofReal_mul hc₁))
      _ = ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) := (mul_add _ _ _).symm
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal
          (c₁ * (X.toReal + b) + c₂ * Y.toReal + c₃ * Z.toReal + c₄ * W.toReal) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (c₁ * (X.toReal + b)) + ENNReal.ofReal (c₂ * Y.toReal) +
          ENNReal.ofReal (c₃ * Z.toReal) + ENNReal.ofReal (c₄ * W.toReal) := by
        rw [ENNReal.ofReal_add (by linarith only [hxb, hy, hz]) hw,
          ENNReal.ofReal_add (by linarith only [hxb, hy]) hz,
          ENNReal.ofReal_add hxb hy]
    _ ≤ ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
          ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ * W :=
        add_le_add (add_le_add (add_le_add hbracket (ofReal_mul_toReal_le hc₂ Y))
          (ofReal_mul_toReal_le hc₃ Z)) (ofReal_mul_toReal_le hc₄ W)

/-- **Constant monotonicity of a two-summand `ℝ≥0∞` right-hand side.**  Used to
raise a clause proved at one constant to the joint constant of the assembly,
without ever writing the (large) carriers out. -/
theorem two_summand_coeff_mono {a a' b b' : ℝ} {X Y : ℝ≥0∞} (ha : a ≤ a')
    (hb : b ≤ b') :
    ENNReal.ofReal a * X + ENNReal.ofReal b * Y ≤
      ENNReal.ofReal a' * X + ENNReal.ofReal b' * Y :=
  add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal ha) X)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hb) Y)

/-! ## 2. The indicator collapse -/

/-- **The indicator collapse on the good event.**  Off the event the indicator
is `0`; on it, the estimate is the hypothesis. -/
theorem indicator_le_of_mem {α : Type*} {G : Set α} {f : α → ℝ≥0∞} {R : ℝ≥0∞}
    {omega : α} (h : omega ∈ G → f omega ≤ R) :
    Set.indicator G f omega ≤ R := by
  by_cases hmem : omega ∈ G
  · rw [Set.indicator_of_mem hmem]
    exact h hmem
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

/-! ## 3. The one finiteness fact the shell needs -/

/-- **The anchor's left-hand side is finite.**

The frozen statement's `u - v` is, by its own two pointwise clauses, the `H¹₀`
witness `w` on `x+□_n`; an `H¹₀` function carries its `L²` datum in its type,
and the normalized volume measure is a finite rescaling of the restricted
Lebesgue measure as soon as the window has positive volume. -/
theorem eLpNorm_ne_top_of_eq_h10 {A : Set (Vec d)} (hA : volume A ≠ 0)
    {f : Vec d → ℝ} (w : H10Function A) (hf : ∀ y, f y = w.toH1Function.toFun y) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn A) ≠ ⊤ := by
  have hfun : f = w.toH1Function.toFun := funext hf
  have hmem : MemLp f 2 (Support.normalizedVolumeMeasureOn A) := by
    rw [hfun, Support.normalizedVolumeMeasureOn_def]
    exact w.toH1Function.memL2.smul_measure (ENNReal.inv_ne_top.mpr hA)
  exact hmem.eLpNorm_lt_top.ne

end

end Algsuperdiff.Section4.Provider.ExcessDecay
