/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.PrekopaLeindler

/-!
# Log-concave functions, and the log-concavity of a marginal

A function `f` with values in `ℝ≥0∞` is *log-concave* if

`f x ^ a * f y ^ b ≤ f (a • x + b • y)`  for all `x`, `y` and all `a, b > 0` with `a + b = 1`,

which for a positive real-valued function says exactly that `log ∘ f` is concave. The two facts
about log-concave functions that Vaaler's cube-slicing theorem needs are here: the set where such
a function is nonzero is convex, and a marginal of a log-concave function over a convex set is
log-concave. The second is Bombieri–Gubler's Lemma C.3.4, and it is the only consumer of the
Prékopa–Leindler inequality inside the roadmap.

## Main definitions

* `LogConcave f`: `f : E → ℝ≥0∞` is log-concave.

## Main results

* `LogConcave.convex_support`: `{x | f x ≠ 0}` is convex (Bombieri–Gubler, Remark C.3.2).
* `LogConcave.convex_lt`: every strict superlevel set `{x | c < f x}` is convex.
* `logConcave_indicator`: the indicator of a convex set, at any value, is log-concave.
* `LogConcave.mul`: a product of log-concave functions is log-concave.
* `LogConcave.setLIntegral_prod_right`: **Bombieri–Gubler, Lemma C.3.4.** If `f` is a log-concave
  function on `E × F` and `A ⊆ F` is convex and measurable, then `x ↦ ∫⁻ y in A, f (x, y)` is
  log-concave on `E`, provided Prékopa–Leindler holds on `F`.

## Implementation notes

⚠ **Log-concavity is stated for `ℝ≥0∞`-valued functions, not for the book's nonnegative real
ones.** The functions that C.3.4 and C.3.7 apply it to are *measures of slices* —
`y ↦ vol (B ∩ A_y)` in Bombieri–Gubler's own induction step — so `ℝ≥0∞` is where they naturally
live, and there the
statement carries no finiteness hypothesis at all. Bombieri–Gubler have to say "if the integral is
always finite" in C.3.4; here that hypothesis is absent, and so is the nonnegativity hypothesis,
because the codomain supplies both.

⚠ **`0 ^ a = 0` for `a > 0` is what makes the characteristic function of a convex set log-concave**,
with no case distinction beyond membership, and that is the whole of Bombieri–Gubler's step from
C.3.3 to C.3.4: their `f i y = χ_A y * f (x i, y)` is log-concave because a product of log-concave
functions is, and `χ_A` is log-concave because `A` is convex. The proof of
`LogConcave.setLIntegral_prod_right` below inlines that product rather than forming it, since the
Prékopa–Leindler hypothesis is checked pointwise anyway.

⚠ **C.3.4 needs nothing of `E` but that it is a real vector space.** There is no measure on `E`, no
finite-dimensionality, and no measurability hypothesis on the marginal: log-concavity is a
pointwise statement in `x`, and the Prékopa–Leindler inequality is applied on `F` alone, once for
each pair `x₁`, `x₂`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition C.3.1, Remark C.3.2 and Lemma C.3.4.

This is Layer 4.5 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open MeasureTheory Set

/-- A function `f : E → ℝ≥0∞` on a real vector space is **log-concave** if
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` for all `x`, `y` and all weights `a, b > 0` summing to
`1`; for positive real-valued `f` this says that `log ∘ f` is concave. -/
@[expose] def LogConcave {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ENNReal) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 → ∀ x y, f x ^ a * f y ^ b ≤ f (a • x + b • y)

/-- **The set where a log-concave function is nonzero is convex** (Bombieri–Gubler, Remark
C.3.2). -/
theorem LogConcave.convex_support {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ENNReal}
    (hf : LogConcave f) : Convex ℝ {x | f x ≠ 0} := by
  intro x hx y hy a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by rw [← hab, ← ha0, zero_add]
    simpa [← ha0, hb1] using hy
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha1 : a = 1 := by rw [← hab, ← hb0, add_zero]
    simpa [← hb0, ha1] using hx
  refine ne_of_gt (lt_of_lt_of_le ?_ (hf a b ha0 hb0 hab x y))
  refine pos_iff_ne_zero.mpr (mul_ne_zero ?_ ?_)
  · exact fun hc => hx (by simpa [ENNReal.rpow_eq_zero_iff, ha0, ha0.not_gt] using hc)
  · exact fun hc => hy (by simpa [ENNReal.rpow_eq_zero_iff, hb0, hb0.not_gt] using hc)

/-- **Every strict superlevel set of a log-concave function is convex.** This is what makes the
layer-cake decomposition of a log-concave density a superposition of convex symmetric sets, which
is the form Bombieri–Gubler's Lemma C.3.7 consumes. -/
theorem LogConcave.convex_lt {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ENNReal}
    (hf : LogConcave f) (c : ENNReal) : Convex ℝ {x | c < f x} := by
  intro x hx y hy a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by rw [← hab, ← ha0, zero_add]
    simpa [← ha0, hb1] using hy
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha1 : a = 1 := by rw [← hab, ← hb0, add_zero]
    simpa [← hb0, ha1] using hx
  refine (lt_min hx hy).trans_le (le_trans ?_ (hf a b ha0 hb0 hab x y))
  calc min (f x) (f y) = min (f x) (f y) ^ (a + b) := by rw [hab, ENNReal.rpow_one]
    _ = min (f x) (f y) ^ a * min (f x) (f y) ^ b :=
        ENNReal.rpow_add_of_nonneg a b ha0.le hb0.le
    _ ≤ f x ^ a * f y ^ b :=
        mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ha0.le)
          (ENNReal.rpow_le_rpow (min_le_right _ _) hb0.le)

/-- **The indicator of a convex set is log-concave**, at any value `c`. -/
theorem logConcave_indicator {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    (hs : Convex ℝ s) (c : ENNReal) : LogConcave (Set.indicator s (fun _ => c)) := by
  intro a b ha hb hab x y
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        Set.indicator_of_mem (hs hx hy ha.le hb.le hab),
        ← ENNReal.rpow_add_of_nonneg a b ha.le hb.le, hab, ENNReal.rpow_one]
    · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
  · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

/-- A product of log-concave functions is log-concave. -/
theorem LogConcave.mul {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → ENNReal}
    (hf : LogConcave f) (hg : LogConcave g) : LogConcave (f * g) := by
  intro a b ha hb hab x y
  have h1 : (f x * g x) ^ a = f x ^ a * g x ^ a := ENNReal.mul_rpow_of_nonneg _ _ ha.le
  have h2 : (f y * g y) ^ b = f y ^ b * g y ^ b := ENNReal.mul_rpow_of_nonneg _ _ hb.le
  simp only [Pi.mul_apply, h1, h2]
  calc f x ^ a * g x ^ a * (f y ^ b * g y ^ b)
      = f x ^ a * f y ^ b * (g x ^ a * g y ^ b) := by ring
    _ ≤ f (a • x + b • y) * g (a • x + b • y) :=
        mul_le_mul' (hf a b ha hb hab x y) (hg a b ha hb hab x y)

/-- **Bombieri–Gubler, Lemma C.3.4: a marginal of a log-concave function over a convex set is
log-concave.** If `f : E × F → ℝ≥0∞` is measurable and log-concave and `A ⊆ F` is convex and
measurable, then `x ↦ ∫⁻ y in A, f (x, y) ∂ν` is log-concave on `E`, for any measure `ν` on `F`
satisfying the Prékopa–Leindler inequality. -/
theorem LogConcave.setLIntegral_prod_right {E F : Type*} [MeasurableSpace E] [AddCommGroup E]
    [Module ℝ E] [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {ν : Measure F}
    (hF : HasPrekopaLeindler ν) {f : E × F → ENNReal} (hf : Measurable f) (hlc : LogConcave f)
    {A : Set F} (hA : MeasurableSet A) (hAc : Convex ℝ A) :
    LogConcave fun x => ∫⁻ y in A, f (x, y) ∂ν := by
  intro a b ha hb hab x₁ x₂
  have hind : ∀ x : E, (∫⁻ y in A, f (x, y) ∂ν)
      = ∫⁻ y, Set.indicator A (fun y => f (x, y)) y ∂ν :=
    fun x => (lintegral_indicator hA _).symm
  have hmeas : ∀ x : E, Measurable (Set.indicator A fun y => f (x, y)) :=
    fun x => (hf.comp measurable_prodMk_left).indicator hA
  simp only [hind]
  refine hF a b ha hb hab _ _ _ (hmeas x₁) (hmeas x₂) (hmeas (a • x₁ + b • x₂)) fun y₁ y₂ => ?_
  by_cases hy₁ : y₁ ∈ A
  · by_cases hy₂ : y₂ ∈ A
    · rw [Set.indicator_of_mem hy₁, Set.indicator_of_mem hy₂,
        Set.indicator_of_mem (hAc hy₁ hy₂ ha.le hb.le hab)]
      exact hlc a b ha hb hab (x₁, y₁) (x₂, y₂)
    · simp [Set.indicator_of_notMem hy₂, ENNReal.zero_rpow_of_pos hb]
  · simp [Set.indicator_of_notMem hy₁, ENNReal.zero_rpow_of_pos ha]

end
