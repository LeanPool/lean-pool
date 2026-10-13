/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# WeakGradientLocality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Locality of the weak gradient

The weak gradient is a *local* object: if `u` has weak gradient `Du` on each
member of an open cover of `W`, it has weak gradient `Du` on `W` itself.  This
fact is absent from Mathlib and from the compiled part of CoarseGraining, and
it is the first frontier item of the §4.3 odd-reflection chain: it is what
turns the one-face harmonicity transfer into a statement about the whole
reflected window, and what upgrades a *localized* zero-trace hypothesis (a
hypothesis about `η · v` for cutoffs `η`) into a statement about `v`.

## The argument

Only one ingredient is genuinely missing: a smooth partition of a compactly
supported test function subordinate to the cover.  It is built here from
scratch and *without* any manifold machinery, by a telescoping product:

* `exists_contDiff_eq_one_nhds` upgrades Mathlib's
  `exists_smooth_tsupport_subset` (a bump equal to `1` at one point) to a bump
  identically `1` on a *neighbourhood* of the point, by composing with a
  rescaled `Real.smoothTransition`;
* the compact set `tsupport φ` is covered by finitely many such neighbourhoods,
  so the product `∏ (1 - gᶜ)` of the corresponding bump defects vanishes on
  `tsupport φ`, hence `φ · ∏ (1 - gᶜ) = 0` everywhere;
* `exists_smooth_decomposition_of_open_cover` then telescopes
  `1 - ∏_{c ∈ t} (1 - gᶜ) = ∑ gᶜ ∏_{earlier} (1 - g)` by induction on the
  finite index set, producing finitely many smooth compactly supported pieces
  `ψ j` summing to `φ`, each supported in one member of the cover.

No normalization, no division, and no `SmoothPartitionOfUnity` is needed: the
telescoping identity is exact, and the pieces need not be nonnegative or sum to
one off `tsupport φ`.

The `L²` hypotheses in the locality statements are not decoration.  The weak
derivative predicate `HasWeakPartialDerivOn` is an identity between Bochner
integrals, and splitting the integral of `φ = ∑ ψ j` across the sum requires
each summand to be genuinely integrable; `u, Du ∈ L²(W)` (the `H¹` carrier's
own data) is exactly what makes the Hölder pairing with the smooth compactly
supported pieces integrable.

## Main results

* `exists_contDiff_eq_one_nhds` — a smooth compactly supported bump equal to `1`
  on a neighbourhood of a point and supported in a prescribed neighbourhood.
* `exists_smooth_decomposition_of_open_cover` — the finite smooth decomposition
  of a compactly supported test function subordinate to an open cover.
* `hasWeakPartialDerivOn_iUnion`, `hasWeakGradientOn_iUnion` — locality on a
  union of open sets.
* `hasWeakGradientOn_of_open_cover` — the cover form (the shape consumers use).
* `hasWeakGradientOn_union` — the two-set specialization.

The opposite (easy) direction — restriction of a weak gradient to an open
subset — is CoarseGraining's `HasWeakGradientOn.restrict` and is not repeated
here.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. A smooth bump identically one near a point -/

/-- Mathlib's smooth transition, rescaled to vanish on `(-∞, 1/2]` and to equal
`1` on `[3/4, ∞)`. -/
def oneNear (t : ℝ) : ℝ :=
  Real.smoothTransition (4 * t - 2)

private theorem contDiff_oneNear : ContDiff ℝ (⊤ : ℕ∞) oneNear := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 4 * t - 2 :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  exact Real.smoothTransition.contDiff.comp h

private theorem oneNear_eq_zero {t : ℝ} (ht : t ≤ 1 / 2) : oneNear t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [ht])

private theorem oneNear_eq_one {t : ℝ} (ht : 3 / 4 ≤ t) : oneNear t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [ht])

/-- **A smooth bump identically one on a neighbourhood.**

Mathlib's `exists_smooth_tsupport_subset` produces a smooth compactly supported
bump supported in `s` and equal to `1` *at* `x`.  Composing it with the
rescaled smooth transition `oneNear` produces one equal to `1` on a whole open
neighbourhood of `x`, which is what the telescoping decomposition below needs
(a product of defects `1 - g` must vanish *identically* on the covered
compact set, not merely at chosen points). -/
theorem exists_contDiff_eq_one_nhds {s : Set (Vec d)} {x : Vec d} (hs : s ∈ 𝓝 x) :
    ∃ (g : Vec d → ℝ) (W : Set (Vec d)),
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ s ∧
        IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, g y = 1 := by
  obtain ⟨f, hfs, hfc, hf, -, hfx⟩ := exists_contDiff_tsupport_subset (n := ⊤) hs
  have hsupp : Function.support (fun y => oneNear (f y)) ⊆ Function.support f := by
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [h0]; exact oneNear_eq_zero (by norm_num))
  have htsupp : tsupport (fun y => oneNear (f y)) ⊆ tsupport f :=
    closure_mono hsupp
  refine ⟨fun y => oneNear (f y), {y | 3 / 4 < f y}, contDiff_oneNear.comp hf, ?_,
    htsupp.trans hfs, isOpen_lt continuous_const hf.continuous, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hfc isClosed_closure htsupp
  · change (3 : ℝ) / 4 < f x
    rw [hfx]
    norm_num
  · intro y hy
    exact oneNear_eq_one (le_of_lt hy)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
