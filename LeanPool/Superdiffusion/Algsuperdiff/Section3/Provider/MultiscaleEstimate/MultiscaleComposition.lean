/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleBaseBranch

/-!
# MultiscaleComposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the composition of the two scale branches of `p.multiscale.estimate`

## What is delivered, and what is NOT

`multiscale_estimate_composed` is the frozen root's statement body
(`Frozen/Section3/MultiscaleEstimate.lean`, the block between) **verbatim,
binder for binder and amplitude spelling for amplitude spelling, with NO
premise inserted** and nothing else changed: the same `exists Cms`, the same
five source binders (`M`, `m`, `E`, the induction state, `epsilon`), the same
window `cstar^{-1} eps^{-Cms} <= E`, the same smallness `cgamma <=
(E^{-1})^{10}`, the same `s in [8 cgamma, 1]`, ONE `(Y, Z)` pair serving the
main conjunct AND the refinement clause, and the two amplitudes

```text
    Cms E s^{-1} sqrt(eps cgamma)   and   Cms eps (s^{-1})^2 exp(-E^{-3} cgamma^{-1}) .
```

Until that licensed edit happens, `p.multiscale.estimate` is not a closed
source node, and no docstring here may say otherwise.

## The two inputs (consumed, never re-derived)

Both are proved publics of this namespace, each proving the frozen body on one
side of the landmark `mStarStar M`:

* `multiscale_estimate_of_mStarStar` --- the frozen body with the single
  premise `mStarStar M < m`;
* `multiscale_estimate_of_le_mStarStar` --- the frozen body with the single
  premise `m <= mStarStar M`.

## The composition is not a plain `max`

The obvious composition --- take `Cms := max Cms_1 Cms_2` and transfer every
hypothesis by monotonicity --- **does not typecheck**, because one hypothesis of
the frozen body points the wrong way.  The frozen conclusion's second conjunct
is an *implication*

```text
    s <= Cms eps  ->  IsBigOWith mu Gamma_2 Y (Cms eps E s^{-1} sqrt cgamma) ,
```

so the composed `Cms` occurs there in *negative* position: enlarging `Cms` W
the guard we are handed and therefore weakens what the branch clause can be
fed.  The monotone transfer of the composed guard `s <= Cms eps` to the branch
guard `s <= Cms_i eps` needs `Cms <= Cms_i`, while the window hypothesis
`cstar^{-1} eps^{-Cms} <= E` and all three amplitudes need `Cms_i <= Cms`; the
two are compatible only at `Cms = Cms_1 = Cms_2`.  (That the branches' own
proofs never consume their guards is irrelevant here: this module consumes
their *statements*, in which the guard is an antecedent.)

Nor do the two routes below rescue the constant `max Cms_1 Cms_2` itself.  At
`Cms = max Cms_1 Cms_2`, take the branch whose constant `a` satisfies `Cms / 2 <
a < Cms`, and the regime `a / 2 < s <= Cms eps`.  Feeding the branch at an
enlarged parameter `eps'` (leaf 3) would need `s <= a eps'` with `eps' <= 1/2`,
i.e. `s <= a / 2`, which that regime denies; and reading the refinement off the
main amplitude (leaf 2) would need `a <= Cms sqrt eps`, i.e.  `eps >= (a /
Cms)^2`, while the regime gives only `eps > a / (2 Cms)`, which is smaller than
`(a / Cms)^2` exactly when `Cms < 2 a`.  Those two are the only sources of a
`Gamma_2` tail for `Y` that the branch statements expose, so the composed
constant must exceed `2 a`.

The branch window in fact admits any `eps' >= eps^{Cms/a}` (the window
transfers whenever `(eps')^{-a} <= eps^{-Cms}`), and shrinking `eps'` makes the
leaf-2 comparison easier.  So the conclusion stands on the full route family.
It is in any case immaterial to the theorem: the frozen statement is
existential in `Cms`.

The route taken instead --- which weakens nothing, the frozen statement being
existential in `Cms` --- is the constant

```text
    Cms := 2 * max Cms_1 Cms_2
```

together with a three-leaf case analysis, run inside `display_of_branch` for
whichever branch the scale `m` selects.  Write `a` for that branch's constant, so
`2 a <= Cms`.  Given the model datum and the frozen window at `Cms`:

1. **No guard** (`Cms eps < s`).  Apply the branch at `eps` itself; the main
   conjunct transfers by amplitude monotonicity (`a <= Cms`), and the refinement
   clause is vacuous.
2. **Guard, and `a < 2 s`.**  Apply the branch at `eps`.  Here `s <= Cms eps`
   and `a < 2 s` force `a < 2 Cms eps`, whence `a^2 <= Cms^2 eps` (this is where
   `2 a <= Cms` is spent) and so `a sqrt eps <= Cms eps`.  The refinement is then
   read off the *main* conjunct's own `Y`-tail (the `IsBigOWith` at the first
   amplitude bundled in `IsTwoTermBigOWithWitnesses`), whose amplitude
   `a E s^{-1} sqrt(eps cgamma)` is at most the refinement target
   `Cms eps E s^{-1} sqrt cgamma` exactly by that inequality.  No branch guard is
   needed.
3. **Guard, and `2 s <= a`.**  Apply the branch at the *enlarged* parameter
   `eps' := max eps (s / a)`, which lies in `(0, 1/2]` precisely because
   `2 s <= a`.  Then `a eps' = max (a eps) s <= Cms eps` (using the guard), which
   drives all three amplitude comparisons, while `s <= a eps'` is the branch
   guard, available by `le_max_right`.  Enlarging `eps` is legitimate in the
   window because `eps |-> eps^{-a}` is antitone: `eps <= eps'` gives
   `(eps')^{-a} <= eps^{-a} <= eps^{-Cms}`.

Leaf 2 is the only place where the composed constant must exceed `max Cms_1
Cms_2`, and `2 x` is the cheapest factor that works: the argument needs
`(a / Cms)^2 <= a / (2 Cms)`, i.e. exactly `2 a <= Cms`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Section3.Cutoff

noncomputable section

/-! ## 1. Amplitude arithmetic

Three real-variable lemmas, stated over abstract reals so that no square root,
exponential or `rpow` is ever handed to a decision procedure. -/

/-- `a √x ≤ c √y` follows from the *linear* comparison `a x ≤ c y` when
`0 ≤ a ≤ c` and `0 ≤ y`: both sides are square roots of `a ^ 2 * x` and
`c ^ 2 * y`, and `a ^ 2 * x = a * (a * x) ≤ a * (c * y) ≤ c * (c * y)`. -/
private theorem mul_sqrt_le_mul_sqrt {a c x y : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hy : 0 ≤ y) (h : a * x ≤ c * y) :
    a * Real.sqrt x ≤ c * Real.sqrt y := by
  have hc : (0 : ℝ) ≤ c := ha.trans hac
  have hcy : (0 : ℝ) ≤ c * y := mul_nonneg hc hy
  have hsq : a ^ 2 * x ≤ c ^ 2 * y :=
    calc a ^ 2 * x = a * (a * x) := by ring
      _ ≤ a * (c * y) := mul_le_mul_of_nonneg_left h ha
      _ ≤ c * (c * y) := mul_le_mul_of_nonneg_right hac hcy
      _ = c ^ 2 * y := by ring
  have hleft : a * Real.sqrt x = Real.sqrt (a ^ 2 * x) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  have hright : c * Real.sqrt y = Real.sqrt (c ^ 2 * y) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
  rw [hleft, hright]
  exact Real.sqrt_le_sqrt hsq

/-- The window transfer.  For `0 < eps ≤ 1`, `0 ≤ a ≤ C` and `eps ≤ eps'` the
map `t ↦ eps ^ (-t)` is monotone increasing and `t ↦ t ^ (-a)` is antitone, so
the frozen window at the composed exponent `C` implies the branch window at the
branch exponent `a` and the enlarged parameter `eps'`. -/
private theorem window_transfer {eps eps' a C v E : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hle : eps ≤ eps') (hac : a ≤ C)
    (hwin : v * eps ^ (-C) ≤ E) :
    v * eps' ^ (-a) ≤ E := by
  have h1 : eps' ^ (-a) ≤ eps ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos heps0 hle (by linarith)
  have h2 : eps ^ (-a) ≤ eps ^ (-C) :=
    Real.rpow_le_rpow_of_exponent_ge heps0 heps1 (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_left (h1.trans h2) hv) hwin

/-- Leaf 2 of the case analysis: when the branch constant `a` satisfies
`a < 2 s` while the composed guard `s ≤ C * eps` holds, the doubling
`2 * a ≤ C` upgrades `a` to `a * √eps ≤ C * eps`.  This is what lets the
refinement clause be read off the main conjunct's own amplitude. -/
private theorem mul_sqrt_le_of_two_mul {a C eps s : ℝ} (ha : 0 < a)
    (h2aC : 2 * a ≤ C) (heps : 0 < eps) (hD : a < 2 * s) (hg : s ≤ C * eps) :
    a * Real.sqrt eps ≤ C * eps := by
  have hC : (0 : ℝ) < C := by linarith
  have hkey : a ^ 2 ≤ C ^ 2 * eps := by nlinarith
  have hle : a ≤ C * Real.sqrt eps := by
    have h := Real.sqrt_le_sqrt hkey
    rwa [Real.sqrt_sq ha.le, Real.sqrt_mul (by positivity), Real.sqrt_sq hC.le] at h
  calc a * Real.sqrt eps ≤ C * Real.sqrt eps * Real.sqrt eps :=
        mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
    _ = C * eps := by rw [mul_assoc, Real.mul_self_sqrt heps.le]

/-! ## 2. The carrier-level transfer

The composition never rebuilds a witness pair: it keeps the branch's `(Y, Z)`
and enlarges the three amplitudes.  The refinement clause travels with it, and
may be fed either by the branch's own clause or by the first amplitude's
`Y`-tail, which `IsTwoTermBigOWithWitnesses` bundles. -/

/-- Enlargement of a two-term bound **together with its refinement clause**,
preserving the witnesses.

`h₃` is the disjunctive route for the refinement: under the composed guard `Q`,
either the branch guard `P` holds and the branch's refinement amplitude fits, or
the *main* amplitude `A₁` already fits.  The first amplitude's tail is the ninth
component of `Probability.IsTwoTermBigOWithWitnesses`. -/
private theorem exists_witnesses_transfer {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ₁ Ψ₂ : ℝ → ℝ} {X : Ω → ℝ}
    {A₁ A₂ A₃ B₁ B₂ B₃ : ℝ} {P Q : Prop}
    (h : ∃ Y Z : Ω → ℝ,
      Probability.IsTwoTermBigOWithWitnesses μ Ψ₁ Ψ₂ X Y Z A₁ A₂ ∧
        (P → IsBigOWith μ Ψ₁ Y A₃))
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂)
    (h₃ : Q → (P ∧ A₃ ≤ B₃) ∨ A₁ ≤ B₃) :
    ∃ Y Z : Ω → ℝ,
      Probability.IsTwoTermBigOWithWitnesses μ Ψ₁ Ψ₂ X Y Z B₁ B₂ ∧
        (Q → IsBigOWith μ Ψ₁ Y B₃) := by
  obtain ⟨Y, Z, hw, href⟩ := h
  refine ⟨Y, Z, Provider.Orlicz.isTwoTermBigOWithWitnesses_mono_scales hw h₁ h₂,
    fun hq => ?_⟩
  rcases h₃ hq with ⟨hp, hA₃⟩ | hA₁
  · exact (href hp).mono_scale hA₃
  · exact hw.2.2.2.2.2.2.2.2.1.mono_scale hA₁

/-! ## 3. The branch-to-composed transfer

One model datum at a time.  `hbranch` is exactly what either proved branch
delivers after its scale premise and the induction state have been supplied. -/

/-- The frozen display at the composed constant `C`, from the frozen display at
a branch constant `a` with `2 * a ≤ C`.

The three leaves of the proof are the three cases described in the module
header; only leaf 3 moves the parameter `epsilon`, and only leaf 2 spends the
doubling `2 * a ≤ C`. -/
private theorem display_of_branch {d : ℕ} {a C : ℝ} (ha : 0 < a) (haC : 2 * a ≤ C)
    (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E})
    (hbranch : ∀ eps : ℝ, eps ∈ Set.Ioc 0 (1 / 2) →
        (Disorder.cstar M)⁻¹ * eps ^ (-a) ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
          ∃ Y Z : Cutoff.CutoffSample d → ℝ,
            Probability.IsTwoTermBigOWithWitnesses
                (Cutoff.cutoffSampleLaw M).toMeasure
                (HCPolySupport.IndependentSums.gammaSigma 2)
                (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
                (Observable.cutoffHomogenizationError M m
                  ⟨s,
                    (mul_pos (by norm_num : (0 : ℝ) < 8)
                      M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                Y Z
                (a * (E : ℝ) * s⁻¹ * Real.sqrt (eps * M.gamma))
                (a * eps * (s⁻¹) ^ 2 *
                  Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
              (s ≤ a * eps →
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 2)
                  Y
                  (a * eps * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma)))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioc 0 (1 / 2))
    (hwin : (Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (s : ℝ) (hsWindow : s ∈ Set.Icc (8 * M.gamma) 1) :
    ∃ Y Z : Cutoff.CutoffSample d → ℝ,
      Probability.IsTwoTermBigOWithWitnesses
          (Cutoff.cutoffSampleLaw M).toMeasure
          (HCPolySupport.IndependentSums.gammaSigma 2)
          (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M m
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          Y Z
          (C * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma))
          (C * epsilon * (s⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
        (s ≤ C * epsilon →
          HCPolySupport.IndependentSums.IsBigOWith
            (Cutoff.cutoffSampleLaw M).toMeasure
            (HCPolySupport.IndependentSums.gammaSigma 2)
            Y
            (C * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma)) := by
  have heps0 : (0 : ℝ) < epsilon := hepsilon.1
  have heps2 : epsilon ≤ 1 / 2 := hepsilon.2
  have heps1 : epsilon ≤ 1 := by linarith
  have haC' : a ≤ C := by linarith
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs0 : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) hgam).trans_le hsWindow.1
  have hsinv : (0 : ℝ) ≤ s⁻¹ := (inv_pos.mpr hs0).le
  have hEnn : (0 : ℝ) ≤ (E : ℝ) := le_trans zero_le_one E.2
  have hEs : (0 : ℝ) ≤ (E : ℝ) * s⁻¹ := mul_nonneg hEnn hsinv
  have hEsg : (0 : ℝ) ≤ (E : ℝ) * s⁻¹ * Real.sqrt M.gamma :=
    mul_nonneg hEs (Real.sqrt_nonneg _)
  have hcstar : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr (Disorder.cstar_characterization M).1).le
  -- the uniform leaf: the branch at a parameter `eps'` at least `epsilon`,
  -- with the single linear comparison `a * eps' ≤ C * epsilon` driving all
  -- three amplitude slots.
  have key : ∀ eps' : ℝ, eps' ∈ Set.Ioc 0 (1 / 2) → epsilon ≤ eps' →
      a * eps' ≤ C * epsilon →
      (s ≤ C * epsilon → s ≤ a * eps' ∨ a * Real.sqrt eps' ≤ C * epsilon) →
      ∃ Y Z : Cutoff.CutoffSample d → ℝ,
        Probability.IsTwoTermBigOWithWitnesses
            (Cutoff.cutoffSampleLaw M).toMeasure
            (HCPolySupport.IndependentSums.gammaSigma 2)
            (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
            (Observable.cutoffHomogenizationError M m
              ⟨s,
                (mul_pos (by norm_num : (0 : ℝ) < 8)
                  M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
            Y Z
            (C * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma))
            (C * epsilon * (s⁻¹) ^ 2 *
              Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
          (s ≤ C * epsilon →
            HCPolySupport.IndependentSums.IsBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 2)
              Y
              (C * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma)) := by
    intro eps' heps' hle hlin hroute
    have heps'0 : (0 : ℝ) < eps' := heps'.1
    have hbr := hbranch eps' heps'
      (window_transfer hcstar ha.le heps0 heps1 hle haC' hwin) hgammaE s hsWindow
    refine exists_witnesses_transfer hbr ?_ ?_ ?_
    · -- the ordinary lane
      have hsq : a * Real.sqrt (eps' * M.gamma) ≤
          C * Real.sqrt (epsilon * M.gamma) := by
        refine mul_sqrt_le_mul_sqrt ha.le haC' (by positivity) ?_
        calc a * (eps' * M.gamma) = a * eps' * M.gamma := by ring
          _ ≤ C * epsilon * M.gamma := mul_le_mul_of_nonneg_right hlin hgam.le
          _ = C * (epsilon * M.gamma) := by ring
      calc a * (E : ℝ) * s⁻¹ * Real.sqrt (eps' * M.gamma)
          = a * Real.sqrt (eps' * M.gamma) * ((E : ℝ) * s⁻¹) := by ring
        _ ≤ C * Real.sqrt (epsilon * M.gamma) * ((E : ℝ) * s⁻¹) :=
            mul_le_mul_of_nonneg_right hsq hEs
        _ = C * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma) := by ring
    · -- the rare lane
      calc a * eps' * (s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))
          = a * eps' *
            ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) := by ring
        _ ≤ C * epsilon *
            ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) :=
            mul_le_mul_of_nonneg_right hlin (by positivity)
        _ = C * epsilon * (s⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by ring
    · -- the refinement lane
      intro hq
      rcases hroute hq with hguard | hsqrt
      · refine Or.inl ⟨hguard, ?_⟩
        calc a * eps' * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma
            = a * eps' * ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma) := by ring
          _ ≤ C * epsilon * ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma) :=
              mul_le_mul_of_nonneg_right hlin hEsg
          _ = C * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma := by ring
      · refine Or.inr ?_
        have hsplit : Real.sqrt (eps' * M.gamma) =
            Real.sqrt eps' * Real.sqrt M.gamma := Real.sqrt_mul heps'0.le _
        calc a * (E : ℝ) * s⁻¹ * Real.sqrt (eps' * M.gamma)
            = a * Real.sqrt eps' * ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma) := by
              rw [hsplit]; ring
          _ ≤ C * epsilon * ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma) :=
              mul_le_mul_of_nonneg_right hsqrt hEsg
          _ = C * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma := by ring
  by_cases hg : s ≤ C * epsilon
  · by_cases hD : a < 2 * s
    · -- leaf 2: the branch constant is small against the scale
      exact key epsilon hepsilon le_rfl
        (mul_le_mul_of_nonneg_right haC' heps0.le)
        (fun _ => Or.inr (mul_sqrt_le_of_two_mul ha haC heps0 hD hg))
    · -- leaf 3: the enlarged parameter `max epsilon (s / a)`
      push Not at hD
      have hsa : s / a ≤ 1 / 2 := by
        rw [div_le_div_iff₀ ha (by norm_num : (0 : ℝ) < 2)]
        linarith
      have hmem : max epsilon (s / a) ∈ Set.Ioc 0 (1 / 2) :=
        ⟨lt_of_lt_of_le heps0 (le_max_left _ _), max_le heps2 hsa⟩
      have hmul : a * max epsilon (s / a) = max (a * epsilon) s := by
        rw [mul_max_of_nonneg _ _ ha.le, mul_div_cancel₀ _ (ne_of_gt ha)]
      refine key (max epsilon (s / a)) hmem (le_max_left _ _) ?_ ?_
      · rw [hmul]
        exact max_le (mul_le_mul_of_nonneg_right haC' heps0.le) hg
      · exact fun _ => Or.inl (by rw [hmul]; exact le_max_right _ _)
  · -- leaf 1: the refinement clause is vacuous
    exact key epsilon hepsilon le_rfl
      (mul_le_mul_of_nonneg_right haC' heps0.le) (fun hq => absurd hq hg)

/-! ## 4. The composition -/

/-- **The frozen `p.multiscale.estimate` body, with no premise.**

This is `Algsuperdiff.Frozen.Section3.multiscale_estimate`'s statement body
(the block between in `Frozen/Section3/MultiscaleEstimate.lean`) verbatim ---
binder for binder and amplitude spelling for amplitude spelling --- under a
different declaration name.

The proof is the tautological case split `lt_or_ge (mStarStar M) m` feeding the
two proved branches, `multiscale_estimate_of_mStarStar` above the landmark and
`multiscale_estimate_of_le_mStarStar` at or below it, through
`display_of_branch` at the common constant `2 * max Cms₁ Cms₂`.  The doubling
is forced by the refinement clause's guard, which occurs negatively; see the
module header, "The composition is not a plain `max`". -/
theorem multiscale_estimate_composed
    (d : ℕ) :
    ∃ Cms : ℝ, 0 < Cms ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            ∃ Y Z : Cutoff.CutoffSample d → ℝ,
              Probability.IsTwoTermBigOWithWitnesses
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 2)
                  (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
                  (Observable.cutoffHomogenizationError M m
                    ⟨s,
                      (mul_pos (by norm_num : (0 : ℝ) < 8)
                        M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                  Y Z
                  (Cms * (E : ℝ) * s⁻¹ *
                    Real.sqrt (epsilon * M.gamma))
                  (Cms * epsilon * (s⁻¹) ^ 2 *
                    Real.exp
                      (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
                (s ≤ Cms * epsilon →
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma 2)
                    Y
                    (Cms * epsilon * (E : ℝ) * s⁻¹ *
                      Real.sqrt M.gamma)) := by
  obtain ⟨Cms₁, hCms₁, hbr₁⟩ := multiscale_estimate_of_mStarStar d
  obtain ⟨Cms₂, hCms₂, hbr₂⟩ := multiscale_estimate_of_le_mStarStar d
  have h₁ : Cms₁ ≤ max Cms₁ Cms₂ := le_max_left _ _
  have h₂ : Cms₂ ≤ max Cms₁ Cms₂ := le_max_right _ _
  refine ⟨2 * max Cms₁ Cms₂, by linarith, ?_⟩
  intro M m E hS epsilon hepsilon hwin hgammaE s hsWindow
  rcases lt_or_ge (mStarStar M) m with hm | hm
  · exact display_of_branch hCms₁ (by linarith) M m E (hbr₁ M m E hm hS)
      epsilon hepsilon hwin hgammaE s hsWindow
  · exact display_of_branch hCms₂ (by linarith) M m E (hbr₂ M m E hm hS)
      epsilon hepsilon hwin hgammaE s hsWindow

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
