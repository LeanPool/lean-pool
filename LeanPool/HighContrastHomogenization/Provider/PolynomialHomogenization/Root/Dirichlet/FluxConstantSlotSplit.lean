/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitFoldedFluxConstant

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FluxConstantSlotSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (α) part two: the flux constant's three-slot split

The restated the negative-Sobolev Dirichlet error clause hole fixes `C₀ : ℝ → ℝ → ℝ → ℝ`
**before** `∀ g`, and `Lg`
**after** `g, κ` but before `abar, s₀, ρ, Rad, U, ε`.  So every factor of the
flux constant must be routed to exactly one of

| slot | may depend on |
|---|---|
| `C₀ s₀ ρ Rad` | `d, s₀, ρ, Rad` |
| `Lg` | `d, g, κ` |
| `eccentricityFoldFactor abar pEcc` | `abar` only |

The explicit `foldedAnchoredFrameConstant` **mixes** the two
non-fold classes: `(2 Rad) ^ (s₀ − b)` carries `g` through `b` and `Rad`;
`frameFoldConstant`'s bracket factor carries `g`, `κ` **and** `J`; and
`responseOneFromTwoGapFactor b s₀` carries `g` and `s₀` at once.  A factor in
two classes fits no slot.

Each of the three is separated here by the same device the energy collapse uses for the
geometric factor — **trim the order dependence against the window's own
endpoints**:

* `0 ≤ s₀ − b ≤ 1/2` turns `(2 Rad) ^ (s₀ − b)` into `max 1 ((2 Rad) ^ (1/2))`,
  which is `Rad`-level;
* `b − κ ≤ 1/2` together with the bracket `3 ^ J ≤ 1 + 3 (2 Rad)` turns
  `max 1 (3 ^ ((b − κ)(J + 2)))` into `3 · max 1 ((1 + 3 (2 Rad)) ^ (1/2))`,
  which is `Rad`-level — this is the resolution of the `J`-versus-`Rad`
  ambiguity flagged earlier;
* the frozen window `s₀ ≥ (1 + g)/4` and `b = (3 + 5 g)/16` give
  `s₀ − b ≥ (1 − g)/16`, which trims the gap factor's `s₀`-dependence away and
  leaves it `g`-level.  Its remaining `s₀`-factor `geometricDiscount s₀ 1` is
  below `1` and is simply dropped.

The certificate amplitude leaves through `√δ ≤ 1`.  What remains is exactly

```
3 ^ b · foldedAnchoredFrameConstant …  ≤  fluxC0Factor d s₀ Rad cnorm · fluxLgFactor d g κ
```

with `fluxC0Factor` a function of `(d, s₀, Rad, cnorm)` and `fluxLgFactor` a
function of `(d, g, κ)` — no `abar`, and no crossing between the slots.  At the
frozen normalization radius `cnorm = 1/(3√d)` the first is `(d, s₀, Rad)`-level,
which is inside `C₀ s₀ ρ Rad`'s permitted dependence.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## Two order-trimming lemmas -/

/-- **The order trim.**  A positive base raised to an order in `[0, 1/2]` is
below the truncated square root of that base — a quantity free of the order. -/
theorem rpow_le_max_one_rpow_half {t e : ℝ} (ht : 0 < t) (he : 0 ≤ e)
    (he2 : e ≤ 1 / 2) :
    t ^ e ≤ max 1 (t ^ (1 / 2 : ℝ)) := by
  rcases le_or_gt 1 t with h1 | h1
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 he2) (le_max_right _ _)
  · refine le_trans ?_ (le_max_left _ _)
    have hstep := Real.rpow_le_rpow_of_exponent_ge ht h1.le he
    rwa [Real.rpow_zero] at hstep

/-- **The `J`-to-`Rad` trade.**  The bracket factor of `frameFoldConstant` is
below a `Rad`-level quantity: the generation `J` enters only through
`3 ^ J ≤ 1 + 3 (2 Rad)`, and the order `b − κ` is trimmed at `1/2`. -/
theorem max_one_rpow_three_bracket_le {e Jr B : ℝ}
    (he2 : e ≤ 1 / 2) (hJr : 0 ≤ Jr) (hB1 : 1 ≤ B)
    (hJB : (3 : ℝ) ^ Jr ≤ B) :
    max 1 ((3 : ℝ) ^ (e * (Jr + 2))) ≤ 3 * max 1 (B ^ (1 / 2 : ℝ)) := by
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hmax1 : (1 : ℝ) ≤ max 1 (B ^ (1 / 2 : ℝ)) := le_max_left _ _
  have hRHS : (3 : ℝ) ≤ 3 * max 1 (B ^ (1 / 2 : ℝ)) := by linarith only [hmax1]
  refine max_le (by linarith only [hRHS]) ?_
  rcases le_or_gt e 0 with hle | hgt
  · have hexp : e * (Jr + 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (by linarith only [hJr])
    have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    rw [Real.rpow_zero] at h3
    linarith only [h3, hRHS]
  · have hsplit : (3 : ℝ) ^ (e * (Jr + 2)) =
        ((3 : ℝ) ^ Jr) ^ e * (3 : ℝ) ^ (2 * e) := by
      rw [show e * (Jr + 2) = Jr * e + 2 * e by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hbase : ((3 : ℝ) ^ Jr) ^ e ≤ max 1 (B ^ (1 / 2 : ℝ)) := by
      refine le_trans (Real.rpow_le_rpow
        (Real.rpow_nonneg (by norm_num) _) hJB hgt.le) ?_
      exact rpow_le_max_one_rpow_half hB0 hgt.le he2
    have htwo : (3 : ℝ) ^ (2 * e) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [he2] : 2 * e ≤ 1)
      rwa [Real.rpow_one] at h
    have htwo0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * e) :=
      Real.rpow_nonneg (by norm_num) _
    rw [hsplit]
    calc ((3 : ℝ) ^ Jr) ^ e * (3 : ℝ) ^ (2 * e)
        ≤ max 1 (B ^ (1 / 2 : ℝ)) * 3 :=
          mul_le_mul hbase htwo htwo0 (le_trans zero_le_one hmax1)
      _ = 3 * max 1 (B ^ (1 / 2 : ℝ)) := by ring

/-- The geometric discount is monotone in its order. -/
theorem geometricDiscount_mono_order {s₁ s₂ q : ℝ} (hq : 0 ≤ q) (h : s₁ ≤ s₂) :
    Book.Ch02.geometricDiscount s₁ q ≤ Book.Ch02.geometricDiscount s₂ q := by
  have hstep : -s₂ * q ≤ -s₁ * q :=
    mul_le_mul_of_nonneg_right (by linarith only [h]) hq
  have h3 : Real.rpow (3 : ℝ) (-s₂ * q) ≤ Real.rpow (3 : ℝ) (-s₁ * q) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hstep
  simp only [Book.Ch02.geometricDiscount]
  linarith only [h3]

/-! ## The two slot classes -/

/-- The `C₀` class of the flux constant: a function of `(d, s₀, Rad, cnorm)`,
and at the frozen `cnorm = 1/(3√d)` a function of `(d, s₀, Rad)` — inside
`C₀ s₀ ρ Rad`'s permitted dependence. -/
@[expose]
noncomputable def fluxC0Factor (d : ℕ) [NeZero d] (s₀ Rad cnorm : ℝ) : ℝ :=
  (max 1 ((2 * Rad) ^ (1 / 2 : ℝ)) *
      (3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)))) *
    (coarseFluxResponseConstant d * s₀⁻¹ *
        Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
      max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)))

/-- The `Lg` class of the flux constant: a function of `(d, g, κ)` — inside the
per-`g` length factor's permitted dependence. -/
@[expose]
noncomputable def fluxLgFactor (d : ℕ) (g kappaRate : ℝ) : ℝ :=
  ((Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount (responseWindowOrder g) 2))⁻¹) *
    (foldedResponseFillingConstant d g *
      activationFoldConstant d g kappaRate
        (max (responseWindowOrder g) kappaRate))

theorem activationFoldConstant_nonneg (d : ℕ) [NeZero d] (g kappaRate c : ℝ) :
    0 ≤ activationFoldConstant d g kappaRate c := by
  have h1 : (1 : ℝ) ≤ max 1 (foldPrefactorBase d g kappaRate) := le_max_left _ _
  rw [activationFoldConstant]
  exact Real.rpow_nonneg (by linarith only [h1]) _

/-! ## The split -/

/-- **(α), part two.**  The explicit flux frame constant splits
into a `(d, s₀, Rad, cnorm)`-level factor and a `(d, g, κ)`-level factor, with
no factor left in two classes and no dependence on `abar`. -/
theorem three_rpow_mul_foldedAnchoredFrameConstant_le [NeZero d]
    {g kappaRate s₀ Rad cnorm delta Jr : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hs₀ : s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hRad : 0 < Rad)
    (hJr : 0 ≤ Jr) (hJB : (3 : ℝ) ^ Jr ≤ 1 + 3 * (2 * Rad))
    (hdelta1 : Real.sqrt delta ≤ 1) :
    Real.rpow (3 : ℝ) (responseWindowOrder g) *
        foldedAnchoredFrameConstant d g kappaRate s₀
          (coarseFluxResponseConstant d) Rad cnorm delta Jr ≤
      fluxC0Factor d s₀ Rad cnorm * fluxLgFactor d g kappaRate := by
  have hg0 : (0 : ℝ) ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hbeq : responseWindowOrder g = (3 + 5 * g) / 16 := rfl
  have hb0 : 0 < responseWindowOrder g := by rw [hbeq]; linarith only [hg0]
  have hbHalf : responseWindowOrder g ≤ 1 / 2 := by
    rw [hbeq]; linarith only [hg1]
  have hs₀low : (1 + g) / 4 ≤ s₀ := hs₀.1
  have hs₀Half : s₀ < 1 / 2 := hs₀.2
  have hgap : (1 - g) / 16 ≤ s₀ - responseWindowOrder g := by
    rw [hbeq]; linarith only [hs₀low]
  have hgap0 : (0 : ℝ) < (1 - g) / 16 := by linarith only [hg1]
  have hs₀0 : 0 < s₀ := by linarith only [hs₀low, hg0]
  -- the pieces of the `C₀` class
  have h2Rad : (0 : ℝ) < 2 * Rad := by linarith only [hRad]
  have hP1 : (2 * Rad) ^ (s₀ - responseWindowOrder g) ≤
      max 1 ((2 * Rad) ^ (1 / 2 : ℝ)) :=
    rpow_le_max_one_rpow_half h2Rad (by linarith only [hgap, hgap0])
      (by linarith only [hs₀Half, hb0])
  have hMJ : max 1 ((3 : ℝ) ^
        ((responseWindowOrder g - kappaRate) * (Jr + 2))) ≤
      3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) :=
    max_one_rpow_three_bracket_le
      (by linarith only [hbHalf, hkappa]) hJr
      (by linarith only [hRad]) hJB
  -- the pieces of the `Lg` class
  have hdisc0 : (0 : ℝ) < Book.Ch02.geometricDiscount ((1 - g) / 16) 2 :=
    Book.Ch02.book_geometricDiscount_pos (by linarith only [hgap0])
  have hdiscMono : Book.Ch02.geometricDiscount ((1 - g) / 16) 2 ≤
      Book.Ch02.geometricDiscount (s₀ - responseWindowOrder g) 2 :=
    geometricDiscount_mono_order (by norm_num) hgap
  have hsqrtPos : (0 : ℝ) <
      Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2) :=
    Real.sqrt_pos.mpr hdisc0
  have hG1 : (Real.sqrt (Book.Ch02.geometricDiscount
        (s₀ - responseWindowOrder g) 2))⁻¹ ≤
      (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hsqrtPos (Real.sqrt_le_sqrt hdiscMono)
  have hG0 : Book.Ch02.geometricDiscount s₀ 1 ≤ 1 := by
    have h3 : (0 : ℝ) < Real.rpow (3 : ℝ) (-s₀ * 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    simp only [Book.Ch02.geometricDiscount]
    linarith only [h3]
  have hG00 : (0 : ℝ) ≤ Book.Ch02.geometricDiscount s₀ 1 :=
    Book.Ch02.book_geometricDiscount_nonneg (by linarith only [hs₀0])
  -- nonnegativity
  have hP10 : (0 : ℝ) ≤ (2 * Rad) ^ (s₀ - responseWindowOrder g) :=
    Real.rpow_nonneg h2Rad.le _
  have hMJ0 : (0 : ℝ) ≤ max 1 ((3 : ℝ) ^
      ((responseWindowOrder g - kappaRate) * (Jr + 2))) :=
    le_trans zero_le_one (le_max_left _ _)
  have hM10 : (0 : ℝ) ≤ max 1 ((2 * Rad) ^ (1 / 2 : ℝ)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hM20 : (0 : ℝ) ≤ 3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) := by
    have h1 : (1 : ℝ) ≤ max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) :=
      le_max_left _ _
    linarith only [h1]
  have hCX0 : (0 : ℝ) ≤ coarseFluxResponseConstant d := by
    dsimp only [coarseFluxResponseConstant]
    positivity
  have hNH0 : (0 : ℝ) ≤
      Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) := by
    unfold Book.Ch03.constantCoeffMatrixNormHalf
    exact Real.rpow_nonneg
      (Book.Ch02.matrixNorm_nonneg (identityConstantCoeffMatrix d).matrix) _
  have hMR0 : (0 : ℝ) ≤ max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hsi0 : (0 : ℝ) ≤ s₀⁻¹ := (inv_pos.mpr hs₀0).le
  have hG10 : (0 : ℝ) ≤ (Real.sqrt (Book.Ch02.geometricDiscount
      (s₀ - responseWindowOrder g) 2))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hG1'0 : (0 : ℝ) ≤ (Real.sqrt (Book.Ch02.geometricDiscount
      ((1 - g) / 16) 2))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hG20 : (0 : ℝ) ≤ (Real.sqrt (Book.Ch02.geometricDiscount
      (responseWindowOrder g) 2))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hSD0 : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hFC0 : (0 : ℝ) ≤ foldedResponseFillingConstant d g :=
    foldedResponseFillingConstant_nonneg d g
  have hAF0 : (0 : ℝ) ≤ activationFoldConstant d g kappaRate
      (max (responseWindowOrder g) kappaRate) :=
    activationFoldConstant_nonneg d g kappaRate _
  have hcancel : Real.rpow (3 : ℝ) (responseWindowOrder g) *
      Real.rpow (3 : ℝ) (-responseWindowOrder g) = 1 := by
    show (3 : ℝ) ^ responseWindowOrder g * (3 : ℝ) ^ (-responseWindowOrder g) = 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show responseWindowOrder g + -responseWindowOrder g = 0 by ring,
      Real.rpow_zero]
  -- the two grouped bounds
  have hCblock : (2 * Rad) ^ (s₀ - responseWindowOrder g) *
        max 1 ((3 : ℝ) ^
          ((responseWindowOrder g - kappaRate) * (Jr + 2))) ≤
      max 1 ((2 * Rad) ^ (1 / 2 : ℝ)) *
        (3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ))) :=
    mul_le_mul hP1 hMJ hMJ0 hM10
  have hLblock : Book.Ch02.geometricDiscount s₀ 1 *
        (Real.sqrt (Book.Ch02.geometricDiscount
          (s₀ - responseWindowOrder g) 2))⁻¹ *
        (Real.sqrt (Book.Ch02.geometricDiscount (responseWindowOrder g) 2))⁻¹ *
        Real.sqrt delta ≤
      (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
        (Real.sqrt (Book.Ch02.geometricDiscount (responseWindowOrder g) 2))⁻¹ := by
    have hstep1 : Book.Ch02.geometricDiscount s₀ 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (s₀ - responseWindowOrder g) 2))⁻¹ ≤
        1 * (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ :=
      mul_le_mul hG0 hG1 hG10 zero_le_one
    have hstep2 : Book.Ch02.geometricDiscount s₀ 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (s₀ - responseWindowOrder g) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (responseWindowOrder g) 2))⁻¹ ≤
        1 * (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (responseWindowOrder g) 2))⁻¹ :=
      mul_le_mul_of_nonneg_right hstep1 hG20
    have hprod0 : (0 : ℝ) ≤
        1 * (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (responseWindowOrder g) 2))⁻¹ := by
      rw [one_mul]
      exact mul_nonneg hG1'0 hG20
    calc Book.Ch02.geometricDiscount s₀ 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (s₀ - responseWindowOrder g) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount
            (responseWindowOrder g) 2))⁻¹ * Real.sqrt delta
        ≤ 1 * (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
            (Real.sqrt (Book.Ch02.geometricDiscount
              (responseWindowOrder g) 2))⁻¹ * 1 :=
          mul_le_mul hstep2 hdelta1 hSD0 hprod0
      _ = (Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
            (Real.sqrt (Book.Ch02.geometricDiscount
              (responseWindowOrder g) 2))⁻¹ := by ring
  -- assemble
  have hrest0 : (0 : ℝ) ≤ coarseFluxResponseConstant d * s₀⁻¹ *
      Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
      max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCX0 hsi0) hNH0) hMR0
  have hfa0 : (0 : ℝ) ≤ foldedResponseFillingConstant d g *
      activationFoldConstant d g kappaRate
        (max (responseWindowOrder g) kappaRate) :=
    mul_nonneg hFC0 hAF0
  have hLleft0 : (0 : ℝ) ≤ Book.Ch02.geometricDiscount s₀ 1 *
        (Real.sqrt (Book.Ch02.geometricDiscount
          (s₀ - responseWindowOrder g) 2))⁻¹ *
        (Real.sqrt (Book.Ch02.geometricDiscount (responseWindowOrder g) 2))⁻¹ *
        Real.sqrt delta :=
    mul_nonneg (mul_nonneg (mul_nonneg hG00 hG10) hG20) hSD0
  have hCleft0 : (0 : ℝ) ≤ (2 * Rad) ^ (s₀ - responseWindowOrder g) *
      max 1 ((3 : ℝ) ^
        ((responseWindowOrder g - kappaRate) * (Jr + 2))) :=
    mul_nonneg hP10 hMJ0
  rw [foldedAnchoredFrameConstant, foldedAnchoredResponseConstant,
    frameFoldConstant, responseOneFromTwoGapFactor, fluxC0Factor, fluxLgFactor]
  calc Real.rpow (3 : ℝ) (responseWindowOrder g) *
        (Real.rpow (3 : ℝ) (-responseWindowOrder g) *
              (2 * Rad) ^ (s₀ - responseWindowOrder g) *
              coarseFluxResponseConstant d * s₀⁻¹ *
              Book.Ch03.constantCoeffMatrixNormHalf
                (identityConstantCoeffMatrix d) *
              (Book.Ch02.geometricDiscount s₀ 1 *
                  (Real.sqrt (Book.Ch02.geometricDiscount
                    (s₀ - responseWindowOrder g) 2))⁻¹ *
                (Real.sqrt (Book.Ch02.geometricDiscount
                  (responseWindowOrder g) 2))⁻¹) *
            (foldedResponseFillingConstant d g * Real.sqrt delta *
                (activationFoldConstant d g kappaRate
                    (max (responseWindowOrder g) kappaRate) *
                  max 1 ((3 : ℝ) ^
                    ((responseWindowOrder g - kappaRate) * (Jr + 2)))) *
              max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ))))
      = (Real.rpow (3 : ℝ) (responseWindowOrder g) *
            Real.rpow (3 : ℝ) (-responseWindowOrder g)) *
          (((2 * Rad) ^ (s₀ - responseWindowOrder g) *
                max 1 ((3 : ℝ) ^
                  ((responseWindowOrder g - kappaRate) * (Jr + 2)))) *
              (coarseFluxResponseConstant d * s₀⁻¹ *
                  Book.Ch03.constantCoeffMatrixNormHalf
                    (identityConstantCoeffMatrix d) *
                max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ))) *
            ((Book.Ch02.geometricDiscount s₀ 1 *
                    (Real.sqrt (Book.Ch02.geometricDiscount
                      (s₀ - responseWindowOrder g) 2))⁻¹ *
                    (Real.sqrt (Book.Ch02.geometricDiscount
                      (responseWindowOrder g) 2))⁻¹ *
                  Real.sqrt delta) *
              (foldedResponseFillingConstant d g *
                activationFoldConstant d g kappaRate
                  (max (responseWindowOrder g) kappaRate)))) := by ring
    _ = ((2 * Rad) ^ (s₀ - responseWindowOrder g) *
              max 1 ((3 : ℝ) ^
                ((responseWindowOrder g - kappaRate) * (Jr + 2)))) *
            (coarseFluxResponseConstant d * s₀⁻¹ *
                Book.Ch03.constantCoeffMatrixNormHalf
                  (identityConstantCoeffMatrix d) *
              max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ))) *
          ((Book.Ch02.geometricDiscount s₀ 1 *
                  (Real.sqrt (Book.Ch02.geometricDiscount
                    (s₀ - responseWindowOrder g) 2))⁻¹ *
                  (Real.sqrt (Book.Ch02.geometricDiscount
                    (responseWindowOrder g) 2))⁻¹ *
                Real.sqrt delta) *
            (foldedResponseFillingConstant d g *
              activationFoldConstant d g kappaRate
                (max (responseWindowOrder g) kappaRate))) := by
        rw [hcancel, one_mul]
    _ ≤ ((max 1 ((2 * Rad) ^ (1 / 2 : ℝ)) *
                (3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)))) *
            (coarseFluxResponseConstant d * s₀⁻¹ *
                Book.Ch03.constantCoeffMatrixNormHalf
                  (identityConstantCoeffMatrix d) *
              max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)))) *
          (((Real.sqrt (Book.Ch02.geometricDiscount ((1 - g) / 16) 2))⁻¹ *
                (Real.sqrt (Book.Ch02.geometricDiscount
                  (responseWindowOrder g) 2))⁻¹) *
            (foldedResponseFillingConstant d g *
              activationFoldConstant d g kappaRate
                (max (responseWindowOrder g) kappaRate))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hCblock hrest0)
          (mul_le_mul_of_nonneg_right hLblock hfa0)
          (mul_nonneg hLleft0 hfa0) ?_
        exact mul_nonneg (mul_nonneg hM10 hM20) hrest0

end

end RowSupply
end HighContrast
end HCPolySupport
