/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.LocalizationAssemblyCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.BadEventPreCeiling
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.BadEventSummed

/-!
# LocalizationAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the localization assembly `l.localization.mathcalE`

Here the per-cube estimate is averaged over the printed grid, summed over the
scales and composed into the printed five-term display.

## Contents

* §4 — the grid reindexing.  `injOn_triadicCubeShift_descendantsAtScale` and
  `indicator_average_image_eq` move the printed `⨍_{z ∈ 3^l ℤ^d ∩ □_m}` average
  of the bad-event indicator between the development's descendant index set and
  the `Vec d`-indexed grid at which the frozen `goodLocalEventAt` — and
  therefore `e.local.bad.events.summed` — is stated.
* §5 — the bad lane.
* §7 — `localization_mathcalE_estimate_ae`, the endpoint.

## The five terms, and what each costs

Writing `Cinj(Ccg) = 324·Cresp(d)·(16Ccg + 8Ccg²)`, the delivered display is

```text
𝓔_{s,∞,2}(□_m; a_m, σ_m)²
  ≤ 12 c_{2s} Σ_l 3^{-s(m-l)} (⨍_z legA(z+□_l; a_{l-h}, σ_{l-h})^{d/s})^{s/d}
  + 12 c_{2s} Σ_l 3^{-s(m-l)} (⨍_z legB(z+□_l; a_{l-h}, σ_{l-h})^{d/s})^{s/d}
  + 32 Cinj(Ccg) c⋆⁻¹ γ · waveSizesTotalW2(m, h, s)
  + 8 (max_l 3^{-s(m-l)/2}(⨍_z 1_{¬𝒬(l,l-h,z)})^{s/d}) · 𝓔_{s/4,∞,2}(□_m; a_m, σ_m)²
  + 1024 Cs·48Ccg · γ² (h² + s^{-2} + E⁴|log γ|⁴) .
```

against the printed `6 / 6 / C c⋆⁻¹γs / C / Cγ²`.  The delivered leading
numeral is `12` at the leg carrier.  Measured at the printed `max_{|e|=1}`
carrier it is `24` against the printed `6` — a factor-`4` loss — because each
leg is twice that maximum and `legScaleAverage` is degree-one homogeneous,
while the left-hand side `𝓔²` of *this* display carries no doubling at all.
(The doubling sits on both sides only for the breakdown identity and for the
per-`(l,z)` endpoint, where both sides are legs.) The factor-`4`
reading is the conservative one and is what both module headers record.  The
numeral is `8 × 3 / 2`.  Writing `C` (or `12`, or `24`) in place of the printed
explicit `6` changes nothing downstream.  The remaining three printed constants
are `C`'s, and the delivered `32 Cinj c⋆⁻¹γ`, `8` and `1024 Cs·48Ccg` are
explicit admissible values of them.

## The scale gate on `m0`

The landmark premise carried by the endpoint below is `mStarStar M < m0`,
**not** the printed `m0 in (mstar, infty) cap Z`: `l.shom.continuity`'s
hypothesis is corrected to `m0 in (mstarstar, infty) cap Z`, and its whole
downstream chain is re-gated the same way.  Nothing else moved: the premise is
forwarded verbatim to the proved producers consumed here, no proof step here
consumes it, and no frozen statement changes.

## The `h`-window

The printed `h ∈ ℕ₀ ∩ [0, γ⁻¹]` window is one point too large:
`e.local.bad.events.summed` needs `1 ≤ h`, because at `h = 0` its fourth-term
lane would demand the frozen bad-event estimate at the induction level itself.

## Carried, not closed

The printed grid `3^l ℤ^d ∩ □_m` is read as
`triadicCubeShift '' descendantsAtScale (□_m) l`. §4 proves only the
injectivity that reindexing an average needs; the identity of the image with
the printed lattice is NOT proved here and remains a convention.
-/

namespace Algsuperdiff.Section3.Provider.Localization

open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 4. The grid reindexing of the printed `z`-average

The printed average runs over the lattice points `z ∈ 3^l ℤ^d ∩ □_m`; every
proved carrier of this development runs over `descendantsAtScale (□_m) l`.  The
identification of the two index sets is the development's standing grid
convention ((i) / `-017` (ii) / `-027` (iii)) and is NOT closed here: what is
proved below is only that `triadicCubeShift` is injective on a descendant
family, which is all the reindexing of an *average* needs.  Whether its image
is literally `3^l ℤ^d ∩ □_m` remains the open half of that convention. -/

/-- **`triadicCubeShift` is injective on a descendant family.**  All members
have the same scale, and at a fixed scale the shift determines the index. -/
theorem injOn_triadicCubeShift_descendantsAtScale (Q : TriadicCube d) (k : ℤ) :
    ∀ R ∈ descendantsAtScale Q k, ∀ R' ∈ descendantsAtScale Q k,
      triadicCubeShift R = triadicCubeShift R' → R = R' := by
  intro R hR R' hR' hshift
  have hRs : R.scale = k :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hR's : R'.scale = k :=
    descendant_scale_eq_of_mem_descendantsAtScale hR'
  have hpow : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have hindex : R.index = R'.index := by
    funext i
    have hi : (R.index i : ℝ) * (3 : ℝ) ^ k = (R'.index i : ℝ) * (3 : ℝ) ^ k := by
      have := congrFun hshift i
      simpa [triadicCubeShift, cubeScaleFactor, hRs, hR's] using this
    have hcast : (R.index i : ℝ) = (R'.index i : ℝ) :=
      mul_right_cancel₀ hpow hi
    exact_mod_cast hcast
  cases R with
  | mk sc idx =>
    cases R' with
    | mk sc' idx' =>
      simp only at hRs hR's hindex
      subst hindex
      subst hRs
      subst hR's
      rfl

/-- **The printed `z`-average of the bad-event indicator, reindexed.**  The
descendant-indexed average of `1_{¬𝒬(l,l-h,z)}` equals the average over the
image grid `F j = triadicCubeShift '' (descendants at depth j)`, at the frozen
`goodLocalEventAt` spelling that `e.local.bad.events.summed` consumes.  The
bridge from the cube-indexed to the centred event is the proved
`BadEvents.goodLocalEventAt_triadicCubeShift`. -/
theorem indicator_average_image_eq (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (hgap : ℕ) (j : ℕ) (omega : CutoffSample d) :
    (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
          (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ.indicator
            (fun _ => (1 : ℝ)) omega) =
      ((((descendantsAtScale (originCube d m) (m - (j : ℤ))).image
            triadicCubeShift).card : ℝ)⁻¹ *
        ∑ z ∈ (descendantsAtScale (originCube d m) (m - (j : ℤ))).image
            triadicCubeShift,
          (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg (m - (j : ℤ))
            (m - (j : ℤ) - (hgap : ℤ)) z)ᶜ.indicator (fun _ => (1 : ℝ)) omega) := by
  classical
  have hinj := injOn_triadicCubeShift_descendantsAtScale (originCube d m) (m - (j : ℤ))
  have hinj' : Set.InjOn triadicCubeShift
      ((descendantsAtScale (originCube d m) (m - (j : ℤ)) : Finset (TriadicCube d)) :
        Set (TriadicCube d)) :=
    fun R hR R' hR' h => hinj R (Finset.mem_coe.1 hR) R' (Finset.mem_coe.1 hR') h
  rw [Finset.card_image_of_injOn hinj', Finset.sum_image hinj]
  refine congrArg _ (Finset.sum_congr rfl fun R hR => ?_)
  have hscale : R.scale = m - (j : ℤ) :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hset : Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg (m - (j : ℤ))
      (m - (j : ℤ) - (hgap : ℤ)) (triadicCubeShift R) =
        goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)) := by
    rw [← hscale]
    exact goodLocalEventAt_triadicCubeShift M Ccg R (R.scale - (hgap : ℤ))
  rw [hset]

/-! ## 5. The bad lane

Printed step 1 (`BadEventPreCeiling.preCeiling_average_le`) extracts the grid
maximum out of the `L^{d/s}` average; the proved max engine
(`BadEventMaxSplit.tsum_badMax_le_four_mul_homogenizationErrorOnCube_sq`) then
pays the whole `l`-sum once against `𝓔²_{s/4}`.  This is the fourth term of the
printed display, at its `max_l 3^{-s(m-l)/2}(⨍_z 1_{¬𝒬})^{s/d}` shape
and the pure constant `4` per leg. -/

/-- **The printed bad-event factor at depth `j`**, `(⨍_{z ∈ 3^{m-j} ℤ^d ∩ □_m}
1_{¬𝒬(m-j, m-j-h, z)})^{s/d}`, at the frozen `goodLocalEventAt` spelling and at
the grid `F j` obtained by shifting the scale-`(m-j)` descendants of `□_m` (the
development's grid convention (i)).  `badGridAverage_eq` records that this is a
definitional abbreviation, not a new object. -/
def badGridAverage (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (hgap : ℕ) (s : ℝ) (j : ℕ)
    (omega : CutoffSample d) : ℝ :=
  ((((descendantsAtScale (originCube d m) (m - (j : ℤ))).image
        triadicCubeShift).card : ℝ)⁻¹ *
      ∑ z ∈ (descendantsAtScale (originCube d m) (m - (j : ℤ))).image triadicCubeShift,
        (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg (m - (j : ℤ))
          (m - (j : ℤ) - (hgap : ℤ)) z)ᶜ.indicator (fun _ => (1 : ℝ)) omega) ^
    (s / (d : ℝ))

theorem badGridAverage_eq (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (hgap : ℕ) (s : ℝ)
    (j : ℕ) (omega : CutoffSample d) :
    badGridAverage M Ccg m hgap s j omega =
      ((((descendantsAtScale (originCube d m) (m - (j : ℤ))).image
            triadicCubeShift).card : ℝ)⁻¹ *
          ∑ z ∈ (descendantsAtScale (originCube d m) (m - (j : ℤ))).image
              triadicCubeShift,
            (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg (m - (j : ℤ))
              (m - (j : ℤ) - (hgap : ℤ)) z)ᶜ.indicator (fun _ => (1 : ℝ)) omega) ^
        (s / (d : ℝ)) := rfl

/-- The printed bad-event factor is `[0,1]`-valued ([P]).  The ceiling is NOT
re-derived here: it is the proved
`MultiscaleEstimate.weightedIndicatorAverage_rpow_mem_Icc`
(`BadEventCeiling.lean`) at the trivial weight `w := 1`. -/
theorem badGridAverage_mem_Icc (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (hgap : ℕ)
    {s : ℝ} (hs : 0 < s) (j : ℕ) (omega : CutoffSample d) :
    badGridAverage M Ccg m hgap s j omega ∈ Set.Icc (0 : ℝ) 1 := by
  have hrho : (0 : ℝ) ≤ s / (d : ℝ) := by positivity
  have hceil := MultiscaleEstimate.weightedIndicatorAverage_rpow_mem_Icc
    ((descendantsAtScale (originCube d m) (m - (j : ℤ))).image triadicCubeShift)
    (fun z : Vec d => (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg
      (m - (j : ℤ)) (m - (j : ℤ) - (hgap : ℤ)) z)ᶜ)
    (w := 1) zero_le_one le_rfl hrho omega
  rw [badGridAverage_eq]
  simpa using hceil

/-- The per-scale pre-ceiling at the development's leg carriers. -/
private theorem legScaleAverage_bad_le [NeZero d] (M : ABKModel d) (Ccg : ℝ)
    (m : ℤ) (hgap : ℕ) {s : ℝ} (hs : 0 < s) (a : Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {leg : TriadicCube d → ℝ} (hleg0 : ∀ R, 0 ≤ leg R)
    (j : ℕ)
    (hlegle : ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      leg R ≤ 2 * Ch02.normalizedBlockResponseMax R a a0)
    (omega : CutoffSample d) :
    legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => leg R *
          ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
            (fun _ => (1 : ℝ)) omega) ≤
      2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
          (m - (j : ℤ)) a a0 * badGridAverage M Ccg m hgap s j omega := by
  classical
  rw [badGridAverage_eq]
  have hd : d ≠ 0 := NeZero.ne d
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [legScaleAverage_indicator_eq (originCube d m) (m - (j : ℤ)) hs hd
      (fun R => (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ) omega,
    ← indicator_average_image_eq M Ccg m hgap j omega]
  refine MultiscaleEstimate.preCeiling_average_le
    (descendantsAtScale (originCube d m) (m - (j : ℤ)))
    (A := 2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
      (m - (j : ℤ)) a a0)
    (p := (d : ℝ) / s) (rho := s / (d : ℝ)) ?_ (by positivity) (by field_simp)
    (fun R _ => hleg0 R) (fun R hR => ?_)
    (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  · have := Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
      (show m - (j : ℤ) ≤ (originCube d m).scale from by
        change m - (j : ℤ) ≤ m
        omega) a a0
    linarith
  · exact le_trans (hlegle R hR)
      (by
        have := Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
          a a0 hR
        linarith)

/-- The majorant summability of the bad lane's right-hand family: the printed
`3^{-sj}` weight is below the `E²_{s/4}`-series weight `3^{-sj/2}`, and the
`[0,1]` ceiling kills the second factor. -/
private theorem summable_badMax_terms [NeZero d] (m : ℤ) {s : ℝ} (hs : 0 < s)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {G : ℕ → ℝ}
    (hG : ∀ j, G j ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun j : ℕ => Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
        (m - (j : ℤ)) a a0 * G j)) := by
  have hs4 : (0 : ℝ) < s / 4 := by linarith
  have hc1 : (0 : ℝ) < Ch02.geometricDiscount (s / 4) 2 :=
    MultiscaleEstimate.geometricDiscount_quarter_two_pos hs
  have hc2 : (0 : ℝ) ≤ Ch02.geometricDiscount s 2 :=
    geometricDiscount_two_nonneg hs.le
  have hbase : Summable (fun j : ℕ => Ch02.geometricWeight (s / 4) 2 j *
      Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
        (m - (j : ℤ)) a a0) :=
    Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      (originCube d m) a a0 hs4
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    (hbase.mul_left (2 * Ch02.geometricDiscount s 2 / Ch02.geometricDiscount (s / 4) 2))
  · have hmax0 := Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
      (show m - (j : ℤ) ≤ (originCube d m).scale from by
        change m - (j : ℤ) ≤ m
        omega) a a0
    have hw0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hG0 := (Set.mem_Icc.1 (hG j)).1
    exact mul_nonneg (mul_nonneg hc2 hw0) (mul_nonneg (by linarith) hG0)
  · obtain ⟨hG0, hG1⟩ := Set.mem_Icc.1 (hG j)
    have hmax0 := Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
      (show m - (j : ℤ) ≤ (originCube d m).scale from by
        change m - (j : ℤ) ≤ m
        omega) a a0
    have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hwle : Real.rpow (3 : ℝ) (-s * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hw0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hkey : Ch02.geometricWeight (s / 4) 2 j *
        Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
          (m - (j : ℤ)) a a0 =
        Ch02.geometricDiscount (s / 4) 2 *
          (Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
              (m - (j : ℤ)) a a0) := by
      rw [MultiscaleEstimate.geometricWeight_quarter_two_eq j]
      ring
    rw [hkey]
    have hsimp : 2 * Ch02.geometricDiscount s 2 / Ch02.geometricDiscount (s / 4) 2 *
        (Ch02.geometricDiscount (s / 4) 2 *
          (Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
              (m - (j : ℤ)) a a0)) =
        2 * Ch02.geometricDiscount s 2 *
          (Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
              (m - (j : ℤ)) a a0) := by
      field_simp
    rw [hsimp]
    have s1 : Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
          (m - (j : ℤ)) a a0 * G j) ≤
        Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
            (m - (j : ℤ)) a a0) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hc2 hw0)
    have hwm : Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
          (m - (j : ℤ)) a a0 ≤
        Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
          Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
            (m - (j : ℤ)) a a0 :=
      mul_le_mul_of_nonneg_right hwle hmax0
    nlinarith [s1, hwm, hc2]

/-- ```text
8 · max_{l ≤ m} 3^{-s(m-l)/2} (⨍_z 1_{¬𝒬(l,l-h,z)})^{s/d} · 𝓔²_{s/4,∞,2}(□_m; a, a₀) .
```

Printed step 1 is the proved `BadEventPreCeiling.preCeiling_average_le`; the
`l`-sum is paid once by the proved `BadEventMaxSplit` max engine at its pure
constant `4`, and the extra `2` is the frame doubling of the leg. -/
theorem geometricDiscount_mul_gridScaleSeries_bad_le [NeZero d] (M : ABKModel d)
    (Ccg : ℝ) (m : ℤ) (hgap : ℕ) {s : ℝ} (hs : 0 < s)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {leg : TriadicCube d → ℝ} (hleg0 : ∀ R, 0 ≤ leg R)
    (hlegle : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      leg R ≤ 2 * Ch02.normalizedBlockResponseMax R a a0)
    (omega : CutoffSample d) :
    Ch02.geometricDiscount s 2 *
        gridScaleSeries m s (fun _ R => leg R *
          ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
            (fun _ => (1 : ℝ)) omega) ≤
      8 * (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            badGridAverage M Ccg m hgap s j omega) *
        (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
          Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
            a a0) ^ 2 := by
  classical
  have hc2 : (0 : ℝ) ≤ Ch02.geometricDiscount s 2 := geometricDiscount_two_nonneg hs.le
  have hGIcc : ∀ j : ℕ, badGridAverage M Ccg m hgap s j omega ∈ Set.Icc (0 : ℝ) 1 :=
    fun j => badGridAverage_mem_Icc M Ccg m hgap hs j omega
  have hbdd := MultiscaleEstimate.bddAbove_range_three_rpow_mul hs.le hGIcc
  have hW : ∀ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
      badGridAverage M Ccg m hgap s j omega ≤
      ⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
        badGridAverage M Ccg m hgap s j omega := fun j => le_ciSup hbdd j
  have hmax := MultiscaleEstimate.tsum_badMax_le_four_mul_homogenizationErrorOnCube_sq
    (d := d) m hs a a0 (g := fun j => badGridAverage M Ccg m hgap s j omega)
    (fun j => (Set.mem_Icc.1 (hGIcc j)).1) hW
  have hw0 : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := fun j =>
    Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ j : ℕ,
      Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s
            (fun R => leg R *
              ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
                (fun _ => (1 : ℝ)) omega) ≤
        Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
            (m - (j : ℤ)) a a0 * badGridAverage M Ccg m hgap s j omega) := by
    intro j
    exact mul_le_mul_of_nonneg_left
      (legScaleAverage_bad_le M Ccg m hgap hs a a0 hleg0 j (hlegle j) omega)
      (mul_nonneg hc2 (hw0 j))
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤
      Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => leg R *
            ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
              (fun _ => (1 : ℝ)) omega) := by
    intro j
    refine mul_nonneg (mul_nonneg hc2 (hw0 j)) (legScaleAverage_nonneg _ _ _ ?_)
    intro R _
    exact mul_nonneg (hleg0 R)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hsumR := summable_badMax_terms (d := d) m hs a a0 hGIcc
  have hsumL := Summable.of_nonneg_of_le hnn hterm hsumR
  have hgs : gridScaleSeries m s (fun _ R => leg R *
        ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
          (fun _ => (1 : ℝ)) omega) =
      ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => leg R *
            ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
              (fun _ => (1 : ℝ)) omega) := rfl
  have hE0 : (0 : ℝ) ≤ (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
      Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2) a a0) ^ 2 :=
    sq_nonneg _
  calc Ch02.geometricDiscount s 2 *
        gridScaleSeries m s (fun _ R => leg R *
          ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
            (fun _ => (1 : ℝ)) omega)
      = ∑' j : ℕ, Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s
            (fun R => leg R *
              ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
                (fun _ => (1 : ℝ)) omega) := by
        rw [hgs, ← tsum_mul_left]
        exact tsum_congr fun j => by ring
    _ ≤ ∑' j : ℕ, Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
            (m - (j : ℤ)) a a0 * badGridAverage M Ccg m hgap s j omega) :=
        hsumL.tsum_le_tsum hterm hsumR
    _ = 2 * ∑' j : ℕ, Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
            (m - (j : ℤ)) a a0 * badGridAverage M Ccg m hgap s j omega) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun j => by ring
    _ ≤ 2 * (4 * (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            badGridAverage M Ccg m hgap s j omega) *
          (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
            Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
              a a0) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hmax (by norm_num)
    _ = 8 * (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            badGridAverage M Ccg m hgap s j omega) *
          (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
            Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
              a a0) ^ 2 := by ring

/-! ## 6. The good/bad split of the printed left-hand side and the wave series -/

/-- **The indicator split of `e.mathcal.E.breakdown`'s leg sum.**  The printed
left-hand side splits into its good and bad parts with constant `1`: the
indicator of the manuscript's `𝒬(l,l-h,z)` and its complement add to `1`, and
the per-scale power mean is subadditive (`Breakdown.legScaleAverage_le_add`, the
`d/s ≥ 1` Minkowski step). -/
theorem breakdownLegSum_le_good_add_bad [NeZero d] (M : ABKModel d) (Ccg : ℝ)
    (m : ℤ) (hgap : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {leg : TriadicCube d → ℝ} (hleg0 : ∀ R, 0 ≤ leg R) {D : ℝ} (hD : 0 ≤ D)
    (hlegD : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      leg R ≤ D)
    (omega : CutoffSample d) :
    breakdownLegSum m s leg ≤
      gridScaleSeries m s (fun _ R => leg R *
          (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))).indicator
            (fun _ => (1 : ℝ)) omega) +
        gridScaleSeries m s (fun _ R => leg R *
          ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
            (fun _ => (1 : ℝ)) omega) := by
  classical
  have hd : d ≠ 0 := NeZero.ne d
  have hpt : ∀ R : TriadicCube d,
      leg R ≤ leg R * (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))).indicator
          (fun _ => (1 : ℝ)) omega +
        leg R * ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
          (fun _ => (1 : ℝ)) omega := by
    intro R
    by_cases hmem : omega ∈ goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))
    · rw [Set.indicator_of_mem hmem,
        Set.indicator_of_notMem (by simpa using hmem)]
      simp
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem (by simpa using hmem)]
      simp
  have hgood0 : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      (0 : ℝ) ≤ leg R * (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))).indicator
        (fun _ => (1 : ℝ)) omega := fun _ R _ =>
    mul_nonneg (hleg0 R) (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hbad0 : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      (0 : ℝ) ≤ leg R * ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
        (fun _ => (1 : ℝ)) omega := fun _ R _ =>
    mul_nonneg (hleg0 R) (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hindle : ∀ (B : Set (CutoffSample d)) (R : TriadicCube d),
      leg R * B.indicator (fun _ => (1 : ℝ)) omega ≤ leg R := by
    intro B R
    by_cases hmem : omega ∈ B
    · rw [Set.indicator_of_mem hmem]; simp
    · rw [Set.indicator_of_notMem hmem]
      simpa using hleg0 R
  have hsumG := summable_gridScaleSeries_terms m hs hD hgood0
    (fun j R hR => le_trans (hindle _ R) (hlegD j R hR))
  have hsumB := summable_gridScaleSeries_terms m hs hD hbad0
    (fun j R hR => le_trans (hindle _ R) (hlegD j R hR))
  have hsumL := summable_breakdownLegSum_terms m hs hD (fun R => hleg0 R) hlegD
  have hterm : ∀ j : ℕ,
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s leg ≤
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => leg R *
                (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))).indicator
                  (fun _ => (1 : ℝ)) omega) +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            legScaleAverage (originCube d m) (m - (j : ℤ)) s
              (fun R => leg R *
                ((goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)))ᶜ).indicator
                  (fun _ => (1 : ℝ)) omega) := by
    intro j
    have hstep := legScaleAverage_le_add (originCube d m) (m - (j : ℤ)) hs hs1 hd
      (hgood0 j) (hbad0 j) (fun R _ => hleg0 R) (fun R _ => hpt R)
    have hw0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have := mul_le_mul_of_nonneg_left hstep hw0
    linarith [this]
  have hle := hsumL.tsum_le_tsum hterm (hsumG.add hsumB)
  rwa [hsumG.tsum_add hsumB] at hle

theorem waveSizesTotalW2_eq_gridScaleSeries (M : ABKModel d) (m : ℤ) (h : ℕ)
    (s : ℝ) (omega : ShellSeq d) :
    MultiscaleEstimate.waveSizesTotalW2 M m h s omega =
      s * gridScaleSeries m s
        (fun _ R => MultiscaleEstimate.waveSizeW2 M m h R omega ^ 2) := rfl

/-- **The wave lane is summable almost surely.**  On the printed window
`8γ ≤ s ≤ 1` the depth family of the wave lane is a.s. summable, so the
endpoint below carries NO summability premise on that lane.

The hypothesis list is character-identical to the one the sibling
`MultiscaleEstimate.isBigOWith_gammaSigma_waveSizesTotalW2` assembles for
`Orlicz.isBigOWith_gammaSigma_tsum`; only the terminal bridge differs.

The two deep lanes are NOT closed — see the endpoint's disclosure. -/
private theorem ae_summable_wave_scale_series (M : ABKModel d) (m : ℤ) (hgap : ℕ)
    {s : ℝ} (hs8 : 8 * M.gamma ≤ s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)) := by
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs : (0 : ℝ) < s := (mul_pos (by norm_num : (0 : ℝ) < 8) hgam).trans_le hs8
  have hw0 : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := fun _ =>
    Real.rpow_nonneg (by norm_num) _
  refine Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma (sigma := 1)
    (X := fun (j : ℕ) (omega : CutoffSample d) => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2))
    (a := fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (Real.rpow (3 : ℝ) (2 * M.gamma * (j : ℝ)) *
        ((1 + (j : ℝ)) ^ 2 * MultiscaleEstimate.waveKW2 d hgap)))
    one_pos ?_ ?_ ?_ ?_ ?_
  · exact fun j omega => mul_nonneg (hw0 j)
      (legScaleAverage_nonneg _ _ _ (fun _ _ => by positivity))
  · exact fun j => (((MultiscaleEstimate.measurable_waveScaleAverageW2 M m hgap j
      hs).comp measurable_subtype_coe).const_mul _).aemeasurable
  · intro j
    have h1 : (0 : ℝ) < Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < Real.rpow (3 : ℝ) (2 * M.gamma * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0 : ℝ) < MultiscaleEstimate.waveKW2 d hgap :=
      MultiscaleEstimate.waveKW2_pos d hgap
    positivity
  · exact MultiscaleEstimate.summable_weighted_sq hs hs1 hs8
      (MultiscaleEstimate.waveKW2_nonneg d hgap)
  · intro j
    refine isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val
      (X := fun w : ShellSeq d => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s
          (fun R => MultiscaleEstimate.waveSizeW2 M m hgap R w ^ 2))
      (fun _ => rfl) ?_
    have hlayer :=
      (MultiscaleEstimate.isBigOWith_gammaSigma_waveSizeMaxW2_sq M m hgap j).of_le
        (fun w => MultiscaleEstimate.legScaleAverage_waveSizeW2_sq_le M m hgap j hs w)
    exact (hlayer.const_mul (hw0 j)).mono_scale
      (mul_le_mul_of_nonneg_left (MultiscaleEstimate.waveLayerAmpW2_le M hgap j) (hw0 j))

/-! ## 7. The endpoint: `l.localization.mathcalE` at the printed five-term display -/

private theorem localizationWave_ennrealSeries_domination :
    ∀ (d : ℕ) (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (hgap : ℕ)
      (s : ℝ),
      (0 : ℝ) < s →
        ∀ (omega : CutoffSample d),
          (0 : ℝ) ≤
              (324 : ℝ) * responseSensitivityConst d * ((16 : ℝ) * Ccg + (8 : ℝ) * Ccg ^ (2 : ℕ)) *
                ((Disorder.cstar M)⁻¹ * M.gamma) →
            ((0 : ℝ) ≤
                gridScaleSeries m s fun (x : ℕ) (R : TriadicCube d) =>
                  MultiscaleEstimate.waveSizeW2 M m hgap R (↑omega : ShellSeq d) ^ (2 : ℕ)) →
              (8 : ℝ) *
                    ((324 : ℝ) * responseSensitivityConst d * ((16 : ℝ) * Ccg + (8 : ℝ) * Ccg ^ (2 : ℕ)) *
                      ((Disorder.cstar M)⁻¹ * M.gamma)) *
                  (Ch02.geometricDiscount s (2 : ℝ) *
                    gridScaleSeries m s fun (x : ℕ) (R : TriadicCube d) =>
                      MultiscaleEstimate.waveSizeW2 M m hgap R (↑omega : ShellSeq d) ^ (2 : ℕ)) ≤
                (4 : ℝ) *
                    ((8 : ℝ) *
                      ((324 : ℝ) * responseSensitivityConst d * ((16 : ℝ) * Ccg + (8 : ℝ) * Ccg ^ (2 : ℕ)) *
                        ((Disorder.cstar M)⁻¹ * M.gamma))) *
                  MultiscaleEstimate.waveSizesTotalW2 M m hgap s (↑omega : ShellSeq d) := by
  intro d M Ccg m hgap s hs omega hCinj0 hwavenn
  rw [waveSizesTotalW2_eq_gridScaleSeries]
  have hK0 : (0 : ℝ) ≤ 8 * (324 * responseSensitivityConst d *
      (16 * Ccg + 8 * Ccg ^ 2) * ((Disorder.cstar M)⁻¹ * M.gamma)) := by
    linarith [hCinj0]
  have hdisc : Ch02.geometricDiscount s 2 ≤ 4 * s :=
    geometricDiscount_two_le_four_mul hs.le
  have hstep : Ch02.geometricDiscount s 2 * gridScaleSeries m s
      (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2) ≤
      4 * (s * gridScaleSeries m s
        (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)) := by
    calc Ch02.geometricDiscount s 2 * gridScaleSeries m s
          (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)
        ≤ (4 * s) * gridScaleSeries m s
            (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2) :=
          mul_le_mul_of_nonneg_right hdisc hwavenn
      _ = 4 * (s * gridScaleSeries m s
            (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)) := by
          ring
  calc (8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
          ((Disorder.cstar M)⁻¹ * M.gamma))) *
        (Ch02.geometricDiscount s 2 * gridScaleSeries m s
          (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2))
      ≤ (8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma))) *
          (4 * (s * gridScaleSeries m s
            (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2))) :=
        mul_le_mul_of_nonneg_left hstep hK0
    _ = 4 * (8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma))) *
          (s * gridScaleSeries m s
            (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)) := by
        ring

private theorem localizationAssembly_comparisonBounds1 :
    ∀ (d : ℕ) [NeZero d] (CsA : ℝ) (_ : (0 : ℝ) < CsA) (CsB : ℝ) (M : ABKModel d)
      (E : { E : ℝ // (1 : ℝ) ≤ E }) (Ccg : ℝ) (_ : (0 : ℝ) < Ccg) (m : ℤ) (hgap : ℕ) (s : ℝ) (_ : (0 : ℝ) < M.gamma)
      (_ : (0 : ℝ) < s) (omega : CutoffSample d)
      (_ :
        ∀ (j : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (↑j : ℤ)),
            omega ∈ goodLocalEvent M Ccg R (R.scale - (↑hgap : ℤ)) →
              breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
                (24 : ℝ) *
                      breakdownLegA R (coefficientCutoffTriadicCoeffFamily M (R.scale - (↑hgap : ℤ)) omega)
                        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - (↑hgap : ℤ)))) +
                    (8 : ℝ) *
                        ((324 : ℝ) * responseSensitivityConst d * ((16 : ℝ) * Ccg + (8 : ℝ) * Ccg ^ (2 : ℕ)) *
                          ((Disorder.cstar M)⁻¹ * M.gamma)) *
                      MultiscaleEstimate.waveSizeW2 M m hgap R (↑omega : ShellSeq d) ^ (2 : ℕ) +
                  CsA * ((48 : ℝ) * Ccg) * switchRemainder M.gamma (↑E : ℝ) hgap j)
      (_ :
        (0 : ℝ) ≤
          (2 : ℝ) *
            Ch02.normalizedBlockResponseUniformBound (originCube d m) (coefficientCutoffTriadicCoeffFamily M m omega)
              (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))),
      (∀ (j : ℕ),
          ∀ R ∈ descendantsAtScale (originCube d m) (m - (↑j : ℤ)),
            breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
              (2 : ℝ) *
                Ch02.normalizedBlockResponseUniformBound (originCube d m) (coefficientCutoffTriadicCoeffFamily M m omega)
                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) ∧
        (∀ (j : ℕ),
            ∀ R ∈ descendantsAtScale (originCube d m) (m - (↑j : ℤ)),
              breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
                (2 : ℝ) *
                  Ch02.normalizedBlockResponseUniformBound (originCube d m) (coefficientCutoffTriadicCoeffFamily M m omega)
                    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) ∧
          (0 : ℝ) ≤ Ch02.geometricDiscount s (2 : ℝ) ∧
            (0 : ℝ) ≤
                (324 : ℝ) * responseSensitivityConst d * ((16 : ℝ) * Ccg + (8 : ℝ) * Ccg ^ (2 : ℕ)) *
                  ((Disorder.cstar M)⁻¹ * M.gamma) ∧
              (0 : ℝ) ≤ max CsA CsB * ((48 : ℝ) * Ccg) ∧
                (∀ (j : ℕ), (0 : ℝ) ≤ switchRemainder M.gamma (↑E : ℝ) hgap j) ∧
                  (0 : ℝ) ≤ (48 : ℝ) * Ccg ∧
                    (Summable fun (j : ℕ) =>
                        Real.rpow (3 : ℝ) (-s * (↑j : ℝ)) *
                          legScaleAverage (originCube d m) (m - (↑j : ℤ)) s fun (R : TriadicCube d) =>
                            breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
                                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) *
                              (goodLocalEvent M Ccg R (R.scale - (↑hgap : ℤ))).indicator
                                (fun (_ : CutoffSample d) => (1 : ℝ)) omega) ∧
                      (Summable fun (j : ℕ) =>
                          Real.rpow (3 : ℝ) (-s * (↑j : ℝ)) *
                            legScaleAverage (originCube d m) (m - (↑j : ℤ)) s fun (R : TriadicCube d) =>
                              breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
                                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) *
                                (goodLocalEvent M Ccg R (R.scale - (↑hgap : ℤ))).indicator
                                  (fun (_ : CutoffSample d) => (1 : ℝ)) omega) ∧
                        ∀ (j : ℕ),
                          ∀ R ∈ descendantsAtScale (originCube d m) (m - (↑j : ℤ)),
                            omega ∈ goodLocalEvent M Ccg R (R.scale - (↑hgap : ℤ)) →
                              breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
                                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
                                (24 : ℝ) *
                                      breakdownLegA R
                                        (coefficientCutoffTriadicCoeffFamily M (m - (↑j : ℤ) - (↑hgap : ℤ)) omega)
                                        (Observable.isotropicComparatorMatrix
                                          (Annealed.sigmaBar M (m - (↑j : ℤ) - (↑hgap : ℤ)))) +
                                    (8 : ℝ) *
                                        ((324 : ℝ) * responseSensitivityConst d *
                                            ((16 : ℝ) * Ccg + (8 : ℝ) * Ccg ^ (2 : ℕ)) *
                                          ((Disorder.cstar M)⁻¹ * M.gamma)) *
                                      MultiscaleEstimate.waveSizeW2 M m hgap R (↑omega : ShellSeq d) ^ (2 : ℕ) +
                                  max CsA CsB * ((48 : ℝ) * Ccg) * switchRemainder M.gamma (↑E : ℝ) hgap j := by
  intro d _ CsA hCsA CsB M E Ccg hCcg m hgap s _ hs omega hstepA hU0
  have hlegAD : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
        2 * Ch02.normalizedBlockResponseUniformBound (originCube d m)
          (coefficientCutoffTriadicCoeffFamily M m omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
    intro j R hR
    have h1 := breakdownLegA_le_two_mul_normalizedBlockResponseMax
      (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hR
    have h2 := Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
      (a := coefficientCutoffTriadicCoeffFamily M m omega) (Q := originCube d m)
      (R := R) (k := m - (j : ℤ))
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hR
    linarith
  have hlegBD : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
        2 * Ch02.normalizedBlockResponseUniformBound (originCube d m)
          (coefficientCutoffTriadicCoeffFamily M m omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
    intro j R hR
    have h1 := breakdownLegB_le_two_mul_normalizedBlockResponseMax
      (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hR
    have h2 := Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
      (a := coefficientCutoffTriadicCoeffFamily M m omega) (Q := originCube d m)
      (R := R) (k := m - (j : ℤ))
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hR
    linarith
  -- the good lane, both legs
  have hc2s : (0 : ℝ) ≤ Ch02.geometricDiscount s 2 := geometricDiscount_two_nonneg hs.le
  have hcstar : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hresp : (0 : ℝ) ≤ responseSensitivityConst d :=
    (responseSensitivityConst_pos M.shellPrefix.dimension).le
  have hCinj0 : (0 : ℝ) ≤ 324 * responseSensitivityConst d *
      (16 * Ccg + 8 * Ccg ^ 2) * ((Disorder.cstar M)⁻¹ * M.gamma) := by
    have := hCcg.le
    positivity
  have hCrem0 : (0 : ℝ) ≤ max CsA CsB * (48 * Ccg) := by
    have h1 : (0 : ℝ) ≤ max CsA CsB := le_of_lt (lt_of_lt_of_le hCsA (le_max_left _ _))
    have h2 : (0 : ℝ) ≤ 48 * Ccg := by linarith [hCcg.le]
    exact mul_nonneg h1 h2
  have hswr : ∀ j : ℕ, (0 : ℝ) ≤ switchRemainder M.gamma (E : ℝ) hgap j :=
    fun j => switchRemainder_nonneg _ _ _ _
  have h48 : (0 : ℝ) ≤ 48 * Ccg := by linarith [hCcg.le]
  have hindnn : ∀ (Bset : Set (CutoffSample d)) (x : ℝ), 0 ≤ x →
      (0 : ℝ) ≤ x * Bset.indicator (fun _ => (1 : ℝ)) omega := fun _ x hx =>
    mul_nonneg hx (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hindle : ∀ (Bset : Set (CutoffSample d)) (x : ℝ), 0 ≤ x →
      x * Bset.indicator (fun _ => (1 : ℝ)) omega ≤ x := by
    intro Bset x hx
    by_cases hmem : omega ∈ Bset
    · rw [Set.indicator_of_mem hmem]; simp
    · rw [Set.indicator_of_notMem hmem]; simpa using hx
  have hsumGoodA : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) *
          (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))).indicator
            (fun _ => (1 : ℝ)) omega)) :=
    summable_gridScaleSeries_terms m hs hU0
      (fun _ R _ => hindnn _ _ (breakdownLegA_nonneg R _ _))
      (fun j R hR => le_trans (hindle _ _ (breakdownLegA_nonneg R _ _)) (hlegAD j R hR))
  have hsumGoodB : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) *
          (goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))).indicator
            (fun _ => (1 : ℝ)) omega)) :=
    summable_gridScaleSeries_terms m hs hU0
      (fun _ R _ => hindnn _ _ (breakdownLegB_nonneg R _ _))
      (fun j R hR => le_trans (hindle _ _ (breakdownLegB_nonneg R _ _)) (hlegBD j R hR))
  have hstepA' : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      omega ∈ goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)) →
        breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
          24 * breakdownLegA R
              (coefficientCutoffTriadicCoeffFamily M
                (m - (j : ℤ) - (hgap : ℤ)) omega)
              (Observable.isotropicComparatorMatrix
                (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) +
            8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
                ((Disorder.cstar M)⁻¹ * M.gamma)) *
              MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 +
            max CsA CsB * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j := by
    intro j R hR hmem
    have h := hstepA j R hR hmem
    have hscale : R.scale = m - (j : ℤ) :=
      descendant_scale_eq_of_mem_descendantsAtScale hR
    rw [hscale] at h
    have hrem : CsA * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j ≤
        max CsA CsB * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left CsA CsB) h48) (hswr j)
    linarith
  exact ⟨hlegAD, hlegBD, hc2s, hCinj0, hCrem0, hswr, h48, hsumGoodA, hsumGoodB, hstepA'⟩

/-- For the multiscale root's own regime, every gap `h ∈ ℕ₀` with `γ h ≤ 1` and
every `s ∈ [8γ, 1]`, almost surely:

```text
𝓔_{s,∞,2}(□_m; a_m, σ_m)²
  ≤ 12 c_{2s} Σ_{l ≤ m} 3^{-s(m-l)} (⨍_z legA(z+□_l; a_{l-h}, σ_{l-h})^{d/s})^{s/d}
  + 12 c_{2s} Σ_{l ≤ m} 3^{-s(m-l)} (⨍_z legB(z+□_l; a_{l-h}, σ_{l-h})^{d/s})^{s/d}
  + 32 Cinj(Ccg) c⋆⁻¹ γ · [a majorant of] s Σ_{l ≤ m} 3^{-s(m-l)} (⨍_z
  (3^{(2-γ)l}‖k_m-k_{l-h}‖_{W^{2,∞}})^{2d/s})^{s/d}
  + 8 max_{l ≤ m} 3^{-s(m-l)/2} (⨍_z 1_{¬𝒬(l,l-h,z)})^{s/d} · 𝓔_{s/4,∞,2}(□_m; a_m, σ_m)²
  + 1024 Cs 48Ccg γ² (h² + s^{-2} + E⁴|log γ|⁴) .
```

The five summands are the five printed terms in order.  Term-by-term against
the print:

* **first two** — the printed `6 c_{2s} Σ_l 3^{-s(m-l)}(⨍_z max_e
  J(·;a_{l-h}))^{s/d}` and its adjoint, at the development's frame-sup carriers
  `breakdownLeg{A,B}`, each of which is twice the printed `max_{|e|=1}` object.
  The resulting factor is dimension-free and is absorbed downstream by
  `e.what.homogenization.gives`'s own `C`.
* The delivered term is therefore a majorant of the printed one, which is the
  admissible direction here; it is not an equality and must not be read as one.
* Its `𝓔²_{s/4}` factor is stated at CoarseGraining's
  `Ch02.HomogenizationErrorOnCube (□_m) (s/4) ∞ 2 a_m (isotropic σ_m)` rather
  than at `Observable.cutoffHomogenizationError M m ⟨s/4, _⟩`, which is where
  the left-hand side sits.  This is a deliberate carrier choice, not an
  obstruction, and the consumer's bridge is one line:
  `BadEventSummed.ae_sq_cutoffHomogenizationError_eq_homogenizationErrorOnCube_sq`.
* **fifth** — the remainder at the proved absolute constant `1024`, in the
  corrected `min{γ²Δ²,1}3^{2γΔ}` shape.

The hypotheses are `0 < Ccg` (the manuscript's good-event constant is a free
parameter here, so that the consumer may thread the same `Cbad` into this
display and into `e.local.bad.events.summed`) and the two `Summable`
premises on the deep lanes (`a_{l-h}, σ_{l-h}`, one per leg).  There is no
wave-lane premise: it is discharged in §6 by `ae_summable_wave_scale_series`.
The good lane's own summability is discharged internally from the proved
uniform descendant bound. -/
theorem localization_mathcalE_estimate_ae (d : ℕ) [NeZero d] :
    ∃ Cs Cg Ci : ℝ, 0 < Cs ∧ 0 < Cg ∧ 0 < Ci ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Cg * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Ci * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ (m : ℤ), m ≤ m0 →
            ∀ (hgap : ℕ), M.gamma * (hgap : ℝ) ≤ 1 →
              ∀ (s : ℝ) (hs8 : 8 * M.gamma ≤ s), s ≤ 1 →
                ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
                  Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                      legScaleAverage (originCube d m) (m - (j : ℤ)) s
                        (fun R => breakdownLegA R
                          (coefficientCutoffTriadicCoeffFamily M
                            (m - (j : ℤ) - (hgap : ℤ)) omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) →
                  Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                      legScaleAverage (originCube d m) (m - (j : ℤ)) s
                        (fun R => breakdownLegB R
                          (coefficientCutoffTriadicCoeffFamily M
                            (m - (j : ℤ) - (hgap : ℤ)) omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) →
                    Observable.cutoffHomogenizationError M m
                          ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8)
                            M.shellPrefix.gamma_pos).trans_le hs8⟩ omega ^ 2 ≤
                      12 * (Ch02.geometricDiscount s 2 *
                          gridScaleSeries m s (fun j R => breakdownLegA R
                            (coefficientCutoffTriadicCoeffFamily M
                              (m - (j : ℤ) - (hgap : ℤ)) omega)
                            (Observable.isotropicComparatorMatrix
                              (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) +
                        12 * (Ch02.geometricDiscount s 2 *
                          gridScaleSeries m s (fun j R => breakdownLegB R
                            (coefficientCutoffTriadicCoeffFamily M
                              (m - (j : ℤ) - (hgap : ℤ)) omega)
                            (Observable.isotropicComparatorMatrix
                              (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) +
                        4 * (8 * (324 * responseSensitivityConst d *
                            (16 * Ccg + 8 * Ccg ^ 2) *
                            ((Disorder.cstar M)⁻¹ * M.gamma))) *
                          MultiscaleEstimate.waveSizesTotalW2 M m hgap s omega.1 +
                        8 * (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
                            badGridAverage M Ccg m hgap s j omega) *
                          (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
                            Ch02.MultiscaleExponent.infinity
                            (Ch02.MultiscaleExponent.finite 2)
                            (coefficientCutoffTriadicCoeffFamily M m omega)
                            (Observable.isotropicComparatorMatrix
                              (Annealed.sigmaBar M m))) ^ 2 +
                        1024 * (Cs * (48 * Ccg)) * M.gamma ^ 2 *
                          ((hgap : ℝ) ^ 2 + (s ^ 2)⁻¹ +
                            (E : ℝ) ^ 4 * |Real.log M.gamma| ^ 4) := by
  classical
  obtain ⟨CsA, CgA, CiA, hCsA, hCgA, hCiA, hlegA⟩ :=
    breakdownLegA_le_deep_wave_remainder_ae d
  obtain ⟨CsB, CgB, CiB, hCsB, hCgB, hCiB, hlegB⟩ :=
    breakdownLegB_le_deep_wave_remainder_ae d
  refine ⟨max CsA CsB, max CgA CgB, max CiA CiB,
    lt_of_lt_of_le hCsA (le_max_left _ _), lt_of_lt_of_le hCgA (le_max_left _ _),
    lt_of_lt_of_le hCiA (le_max_left _ _), ?_⟩
  intro M m0 E hm0 hstate hCEs hCEg hCEi hgammaE Ccg hCcg m hmm0 hgap hgh s hs8 hs1
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs8
  have hd : d ≠ 0 := NeZero.ne d
  have hcinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ :=
    inv_nonneg.2 (Provider.Orlicz.cstar_pos M).le
  have hmono : ∀ {x y : ℝ}, x ≤ y → y * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
      x * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    intro x y hxy h
    exact le_trans (mul_le_mul_of_nonneg_right hxy hcinv) h
  filter_upwards
    [hlegA M m0 E hm0 hstate (hmono (le_max_left _ _) hCEs)
      (hmono (le_max_left _ _) hCEg) (hmono (le_max_left _ _) hCEi) hgammaE Ccg
      hCcg m hmm0 hgap hgh,
     hlegB M m0 E hm0 hstate (hmono (le_max_right _ _) hCEs)
      (hmono (le_max_right _ _) hCEg) (hmono (le_max_right _ _) hCEi) hgammaE Ccg
      hCcg m hmm0 hgap hgh,
     cutoffHomogenizationError_sq_ae_le_breakdown M m ⟨s, hs⟩ hs1,
     ae_summable_wave_scale_series M m hgap hs8 hs1]
    with omega hstepA hstepB hbreak hsumWave hsumDeepA hsumDeepB
  -- the uniform descendant bound of the printed left-hand side
  have hroot : m ≤ (originCube d m).scale := le_of_eq rfl
  obtain ⟨R0, hR0⟩ := descendantsAtScale_nonempty (originCube d m) hroot
  have hU0 : (0 : ℝ) ≤ 2 * Ch02.normalizedBlockResponseUniformBound (originCube d m)
      (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
    have h1 := (Ch02.normalizedBlockResponseMax_nonneg R0
      (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))).trans
      (Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
        (a := coefficientCutoffTriadicCoeffFamily M m omega) (Q := originCube d m)
        (R := R0) (k := m)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hR0)
    linarith
  obtain ⟨hlegAD, hlegBD, hc2s, hCinj0, hCrem0, hswr, h48, hsumGoodA, hsumGoodB, hstepA'⟩ :=
    @localizationAssembly_comparisonBounds1 (d) (by infer_instance) (CsA) (hCsA) (CsB) (M) (E)
      (Ccg) (hCcg) (m) (hgap) (s) (hgam) (hs) (omega) (hstepA) (hU0)
  have hstepB' : ∀ j : ℕ, ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      omega ∈ goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)) →
        breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
          24 * breakdownLegB R
              (coefficientCutoffTriadicCoeffFamily M
                (m - (j : ℤ) - (hgap : ℤ)) omega)
              (Observable.isotropicComparatorMatrix
                (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) +
            8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
                ((Disorder.cstar M)⁻¹ * M.gamma)) *
              MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 +
            max CsA CsB * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j := by
    intro j R hR hmem
    have h := hstepB j R hR hmem
    have hscale : R.scale = m - (j : ℤ) :=
      descendant_scale_eq_of_mem_descendantsAtScale hR
    rw [hscale] at h
    have hrem : CsB * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j ≤
        max CsA CsB * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right CsA CsB) h48) (hswr j)
    linarith
  have hgoodA := geometricDiscount_mul_gridScaleSeries_good_le (d := d) m
    (gam := M.gamma) (Eval := (E : ℝ)) (h := hgap) (c := 24)
    (b := 8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
      ((Disorder.cstar M)⁻¹ * M.gamma)))
    (Crem := max CsA CsB * (48 * Ccg)) hgam hs8 hs1 hgh hd (by norm_num)
    (by linarith [hCinj0]) hCrem0
    (leg := fun _ R => breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (deep := fun j R => breakdownLegA R
      (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))
    (wave := fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)
    (fun _ R => goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))) omega
    (fun _ R _ => breakdownLegA_nonneg R _ _) (fun _ R _ => breakdownLegA_nonneg R _ _)
    (fun _ _ _ => sq_nonneg _) hstepA' hsumGoodA hsumDeepA hsumWave
  have hgoodB := geometricDiscount_mul_gridScaleSeries_good_le (d := d) m
    (gam := M.gamma) (Eval := (E : ℝ)) (h := hgap) (c := 24)
    (b := 8 * (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
      ((Disorder.cstar M)⁻¹ * M.gamma)))
    (Crem := max CsA CsB * (48 * Ccg)) hgam hs8 hs1 hgh hd (by norm_num)
    (by linarith [hCinj0]) hCrem0
    (leg := fun _ R => breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (deep := fun j R => breakdownLegB R
      (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))
    (wave := fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2)
    (fun _ R => goodLocalEvent M Ccg R (R.scale - (hgap : ℤ))) omega
    (fun _ R _ => breakdownLegB_nonneg R _ _) (fun _ R _ => breakdownLegB_nonneg R _ _)
    (fun _ _ _ => sq_nonneg _) hstepB' hsumGoodB hsumDeepB hsumWave
  -- the bad lane, both legs
  have hbadA := geometricDiscount_mul_gridScaleSeries_bad_le M Ccg m hgap hs
    (coefficientCutoffTriadicCoeffFamily M m omega)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))
    (leg := fun R => breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (fun R => breakdownLegA_nonneg R _ _)
    (fun _ R hR => breakdownLegA_le_two_mul_normalizedBlockResponseMax _ _ hR) omega
  have hbadB := geometricDiscount_mul_gridScaleSeries_bad_le M Ccg m hgap hs
    (coefficientCutoffTriadicCoeffFamily M m omega)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))
    (leg := fun R => breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (fun R => breakdownLegB_nonneg R _ _)
    (fun _ R hR => breakdownLegB_le_two_mul_normalizedBlockResponseMax _ _ hR) omega
  -- the good/bad split of the printed left-hand side
  have hsplitA := breakdownLegSum_le_good_add_bad M Ccg m hgap hs hs1
    (leg := fun R => breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (fun R => breakdownLegA_nonneg R _ _) hU0 hlegAD omega
  have hsplitB := breakdownLegSum_le_good_add_bad M Ccg m hgap hs hs1
    (leg := fun R => breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (fun R => breakdownLegB_nonneg R _ _) hU0 hlegBD omega
  have hmulA := mul_le_mul_of_nonneg_left hsplitA hc2s
  have hmulB := mul_le_mul_of_nonneg_left hsplitB hc2s
  have hwavenn : (0 : ℝ) ≤ gridScaleSeries m s
      (fun _ R => MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2) :=
    gridScaleSeries_nonneg m s (fun _ _ _ => sq_nonneg _)
  have hwaveconv := @localizationWave_ennrealSeries_domination (d) (M) (Ccg) (m) (hgap) (s) (hs)
    (omega) (hCinj0) (hwavenn)
  beta_reduce at hgoodA hgoodB hbadA hbadB hsplitA hsplitB hmulA hmulB
  linarith [hbreak, hgoodA, hgoodB, hbadA, hbadB, hmulA, hmulB, hwaveconv]

end

end Algsuperdiff.Section3.Provider.Localization
