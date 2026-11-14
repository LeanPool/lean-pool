/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api

/-!
# RebaseEpsilon

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The clause-threshold calculus

**Conditional-free provider helpers, not a node realization.**  Everything in
this module is arithmetic on the frozen good-event threshold `ε = C⁻¹ s⁴`
together with the *proved* `ε`-monotonicity of the good event
(`GoodEvents.goodEventAt_mono_ep`).  No analysis, no measure theory beyond a
`Set.indicator` rewrite.

Exactly two literals of the frozen statement read `C⁻¹ s⁴` rather than `(1/2)`,
at the statement's own existential constant:

* the hoisted `γ`-smallness funding line;
* the *general* clause's good-event threshold.

The interior clause's event stays at `(1/2)`.  Both read the same way, so
passing from the `(1/2)` form to the `C⁻¹ s⁴` form is a **pure weakening**; the
four lemmas of §1--§3 are exactly the two directions that weakening needs, and
§5 is the consumer-side re-pricing that lets the development's own good-scale
supply `ε = (s/8)√δ` (and the minimal-scale anchor's `ε = s√δ`) reach the
threshold.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Section4/Provider/ExcessDecay/ProviderEpsFree.lean` (read for
  the byte-verification, never imported).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The clause threshold is an admissible, sub-half `ε` -/

/-- The frozen threshold is nonnegative — the left half of the proved
`goodEventAt_mono_ep` side condition. -/
theorem clauseEpsilon_nonneg {C s : ℝ} (hC : 0 < C) (hs : 0 ≤ s) :
    0 ≤ C⁻¹ * s ^ (4 : ℕ) :=
  mul_nonneg (inv_pos.mpr hC).le (pow_nonneg hs 4)

/-- The frozen threshold is at most `1/2`, as soon as the
statement's own existential constant is at least `2` and `s ≤ 1`. -/
theorem clauseEpsilon_le_half {C s : ℝ} (hC : 2 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    C⁻¹ * s ^ (4 : ℕ) ≤ 1 / 2 := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hCi : (0 : ℝ) < C⁻¹ := inv_pos.mpr hCpos
  have hpone : s ^ (4 : ℕ) ≤ 1 := pow_le_one₀ hs hs1
  have hone : C⁻¹ * C = 1 := inv_mul_cancel₀ (ne_of_gt hCpos)
  have htwo : C⁻¹ * 2 ≤ 1 := by
    calc C⁻¹ * 2 ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hC hCi.le
      _ = 1 := hone
  have hhalf : C⁻¹ ≤ 1 / 2 := by linarith only [htwo]
  calc C⁻¹ * s ^ (4 : ℕ) ≤ C⁻¹ * 1 := mul_le_mul_of_nonneg_left hpone hCi.le
    _ = C⁻¹ := mul_one _
    _ ≤ 1 / 2 := hhalf

/-- The threshold is **antitone** in the constant: raising `C` shrinks the
clause event.  This is the whole reason a joint constant `max _ _` can be handed
to a producer stated at its own smaller constant. -/
theorem clauseEpsilon_anti {C C' s : ℝ} (hC : 0 < C) (hCC : C ≤ C') (hs : 0 ≤ s) :
    C'⁻¹ * s ^ (4 : ℕ) ≤ C⁻¹ * s ^ (4 : ℕ) :=
  mul_le_mul_of_nonneg_right (inv_anti₀ hC hCC) (pow_nonneg hs 4)

/-! ## 2. The funding back-port -/

/-- **The back-port.**  The anchor's hoisted `γ`-smallness line is *monotone* in
its trailing `ε` factor, so funding at the smaller `C⁻¹ s⁴` threshold funds every
larger one — in particular the literal `(1/2)` and the producer's own
`C₀⁻¹ s⁴`.

This is `DirectionProbe`'s `hfund'` step, isolated. -/
theorem funding_le_of_epsilon_le {M : ABKModel d} {s ep ep' : ℝ} (hs : 0 < s)
    (hep : ep ≤ ep')
    (h : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep) :
    M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep' := by
  refine h.trans (mul_le_mul_of_nonneg_left hep ?_)
  exact mul_nonneg (Real.rpow_nonneg (by linarith only [hs]) _) (sq_nonneg _)

/-- The standing regime hypothesis is back-ported the same way: it reads `C⁻¹`
directly, and `C ≤ C'` makes the `C'` form the stronger one. -/
theorem regime_le_of_const_le {M : ABKModel d} {C C' : ℝ} (hC : 0 < C) (hCC : C ≤ C')
    (h : M.gamma ≤ C'⁻¹ * Disorder.cstar M ^ (10 : ℕ)) :
    M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
  refine h.trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC hCC) ?_)
  have h5 : Disorder.cstar M ^ (10 : ℕ) = (Disorder.cstar M ^ (5 : ℕ)) ^ (2 : ℕ) := by
    ring
  rw [h5]
  exact sq_nonneg _

/-! ## 3. The event and its indicator -/

/-- **The slot transfer at a witnessed `ω`.**

An indicator bound at *one* threshold `ε₁` transfers to *any* other threshold
`ε₂`, provided the sample `ω` is known to sit in the good event at a threshold
`ε` below both.  Off the event an indicator is `0`; at a witnessed `ω` both
indicators collapse to the same value `F ω`, so the transfer is free in **both**
directions.

This is the mechanism that turns every proved `(1/2)`-gated `hharm` binder into
its `C⁻¹ s⁴`-gated sibling, and back: the consumer always carries `hmem`. -/
theorem indicator_goodEventAt_transfer {M : ABKModel d} {Ccg : ℝ} {j : ℤ} {y : Vec d}
    {t : {t : ℝ // 0 < t}} {ep ep₁ ep₂ : ℝ} {F : Cutoff.CutoffSample d → ℝ≥0∞}
    {B : ℝ≥0∞} {omega : Cutoff.CutoffSample d} (hep0 : 0 ≤ ep) (h1 : ep ≤ ep₁)
    (h2 : ep ≤ ep₂)
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j y t ep)
    (h : Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j y t ep₁) F omega
      ≤ B) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j y t ep₂) F omega ≤ B := by
  have hsub₁ :=
    Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M Ccg j y t hep0 h1
  have hsub₂ :=
    Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M Ccg j y t hep0 h2
  rw [Set.indicator_of_mem (hsub₁ hmem)] at h
  rwa [Set.indicator_of_mem (hsub₂ hmem)]

/-! ## 4. The general clause's bracket -/

/-- Nonnegativity of the frozen general clause's four-summand bracket, stated
abstractly in the legs (so it is blind to every `s`-exponent the freeze moved).
In-repo public sibling of the join lane's private bracket helper. -/
theorem fourSummandBracket_nonneg {a b e f X c Y Z W : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hX : 0 ≤ X) (hc : 0 ≤ c) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hW : 0 ≤ W) : 0 ≤ a * (X + c) + b * Y + e * Z + f * W := by
  have h1 : 0 ≤ a * (X + c) := mul_nonneg ha (add_nonneg hX hc)
  have h2 : 0 ≤ b * Y := mul_nonneg hb hY
  have h3 : 0 ≤ e * Z := mul_nonneg he hZ
  have h4 : 0 ≤ f * W := mul_nonneg hf hW
  linarith only [h1, h2, h3, h4]

/-- Raising a four-summand real right-hand side from a producer's constant to
the assembly's joint constant. -/
theorem fourSummandBracket_absorb {C₀ C t₁ t₂ t₃ t₄ : ℝ} (h : C₀ ≤ C)
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (h₄ : 0 ≤ t₄) :
    C₀ * (t₁ + t₂ + t₃ + t₄) ≤ C * t₁ + C * t₂ + C * t₃ + C * t₄ := by
  have e₁ := mul_le_mul_of_nonneg_right h h₁
  have e₂ := mul_le_mul_of_nonneg_right h h₂
  have e₃ := mul_le_mul_of_nonneg_right h h₃
  have e₄ := mul_le_mul_of_nonneg_right h h₄
  have hexp : C₀ * (t₁ + t₂ + t₃ + t₄) =
      C₀ * t₁ + C₀ * t₂ + C₀ * t₃ + C₀ * t₄ := by ring
  rw [hexp]
  linarith only [e₁, e₂, e₃, e₄]

/-! ## 5. The `δ` re-pricing -/

/-- `√t ≤ a` from `t ≤ a²` at nonnegative `a` — the only square-root step the
re-pricing needs. -/
theorem sqrt_le_of_le_sq {a t : ℝ} (ha : 0 ≤ a) (h : t ≤ a ^ (2 : ℕ)) :
    Real.sqrt t ≤ a := by
  have h1 : Real.sqrt t ≤ Real.sqrt (a ^ (2 : ℕ)) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha] at h1

/-- **The excess-decay consumer's supply reaches the clause event.**

The development's good-scale supply is `ε = (s/8)√δ` (the printed
good-event-cap slot).  It sits below the frozen threshold exactly when `δ
≤ (8 C⁻¹ s³)²`. -/
theorem excessDecayEpsilon_le_clauseEpsilon {C s delta : ℝ} (hC : 0 < C) (hs : 0 ≤ s)
    (hdelta : delta ≤ (8 * C⁻¹ * s ^ (3 : ℕ)) ^ (2 : ℕ)) :
    s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) := by
  have ha : (0 : ℝ) ≤ 8 * C⁻¹ * s ^ (3 : ℕ) :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_pos.mpr hC).le) (pow_nonneg hs 3)
  have hsq := sqrt_le_of_le_sq ha hdelta
  have hmul : s / 8 * Real.sqrt delta ≤ s / 8 * (8 * C⁻¹ * s ^ (3 : ℕ)) :=
    mul_le_mul_of_nonneg_left hsq (by linarith only [hs])
  refine hmul.trans (le_of_eq ?_)
  ring

/-- **The consumer's `δ` price, written out.**

`δ ≤ 64 C⁻² s⁶` is `(8 C⁻¹ s³)²` written out; at that price the good-scale
supply feeds the general clause with no further analysis. -/
theorem excessDecayDelta_repriced {C s delta : ℝ} (hC : 0 < C) (hs : 0 ≤ s)
    (hdelta : delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ)) :
    s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) := by
  refine excessDecayEpsilon_le_clauseEpsilon hC hs (hdelta.trans (le_of_eq ?_))
  rw [show (C ^ (2 : ℕ))⁻¹ = (C⁻¹) ^ (2 : ℕ) from (inv_pow C 2).symm]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
