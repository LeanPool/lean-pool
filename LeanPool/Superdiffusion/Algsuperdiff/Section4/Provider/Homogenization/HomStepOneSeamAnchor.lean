/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneAnchor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamRepin

/-!
# HomStepOneSeamAnchor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 1 RE-PINNED: the anchor at the base
# `s/8` and at the two enlarged-`Y` indices

## What this module is

The SIBLING of the anchor's Step-1 factor moments, at the two
re-pins the §4.5 lane now carries:

* the BASE re-pin `s ↦ s/8` of `HomSeamRepin.homSeamBase` (an INSTANTIATION of
  the `HomStepEnvelope.ethmB`, no new object): the two mesoscale `𝓔`
  factors move from `s/2`, `s/4` to `s/16`, `s/32`;
* the `Y`-slot ENLARGEMENT of `HomSpineTopScale.stepTwoEnlargedY`
  (discharged at `K_idx = 1` by
  `HomSpineTopScale.stepTwoIndexBridge_of_representative`): the printed
  minimal-scale slot `Y = 3^{(1-α)X_m(α)}` is multiplied by the two honest
  Step-2 indices `(1 + 𝓔_{t/2,∞,2}(□_m))(1 + 𝓔_{t,∞,2}(□_m))`.  Those are two
  MORE `𝓔` factors for the print's own Step-1 Hölder budget
  (the `bounds_mathcal_E_aL` lemma moments), and they are produced here.

So the eighth anchor is applied FIVE times rather than three:

| factor | anchor exponent `s'` | gap `m − n` | anchor bracket `s'⁻¹ + √(m−n)` |
|---|---|---|---|
| `𝓔_{s'/2}(□_m, n)`, `s' = s/8` | `s/16` | `k` | `≤ 18|log γ|` |
| `𝓔_{1/4}(□_m)`                 | `1/4`  | `0` | `= 4`         |
| `𝓔_{s'/4}(□_m, n)`, `s' = s/8` | `s/32` | `k` | `≤ 34|log γ|` |
| `𝓔_{t/2}(□_m)` (enlarged `Y`)  | `t/2`  | `0` | `= 2 t⁻¹`     |
| `𝓔_{t}(□_m)` (enlarged `Y`)    | `t`    | `0` | `= t⁻¹`       |

with `s = |log γ|⁻¹`, `k = ⌈10|log γ|⌉`, `n = m − k`.

## The three numerals, machine-measured

* **the quartic γ-gauge `16 → 128`**.  The anchor's lower `s`-endpoint
  `C_A² √γ ≤ s'` binds at the SMALLEST slot, which is now
  `homQuarterOf (homSeamBase M hs) = s/32` instead of the `s/4`.  Via
  `absLog_mul_sqrt_le` (`|log γ|√γ ≤ 4 γ^{1/4}`) the requirement is
  `32 · 4 · C_A² γ^{1/4} ≤ 1`, i.e. `γ^{1/4} ≤ (128 C_A²)⁻¹` — exactly eight
  times the `(16 C_A²)⁻¹`.  This is `homSeamGamma0` below.
* **the `q`-range lower gate `8d|log γ| → 64 d |log γ|`**.  The binding slot is
  again `s/32`: the anchor asks `2d (s/32)⁻¹ = 64 d |log γ| ≤ q`, and the
  hypothesis `hq_lo` sits AT that equality.  The scaling is therefore exactly
  `×8` off the `8 d |log γ|`, matching the gauge's `×8`.  The
  `32 d |log γ|` was understated by a factor two.
* **the upper endpoint `homConst C_A = 200 max(C_A, 1)` is UNCHANGED**.  The
  tightest divisor of the `q`-upper endpoint moves `4 → 32`, and the
  produced constant must dominate `3 · C_A · 34 = 102 C_A` (the `s/32` slot,
  with the IMPROVED `3`-power, see below); both fit under `200 max(C_A,1)`,
  headroom `200/32` on the endpoint and `200/102` on the majorant.

The `3`-power budget IMPROVES and is what keeps `200` sufficient: at the
re-pinned base the anchor exponents are `(1/2)(s/16)k ≤ 3/8` and `(1/2)(s/32)k
≤ 3/16`, so `3^{·} ≤ 3` (`rpow_three_le_three`) replaces the `3^{·} ≤ 27`.
With the `27` the `s/32` slot would need `27 · 34 C_A = 918 C_A` and `200`
would NOT suffice.

## The index bookkeeping of the enlarged `Y` (the honest binders)

The two new factors sit at gap `0` (`n = m`), so their `3`-power is `3^0 = 1`
and their bracket is exactly `(t/2)⁻¹ = 2 t⁻¹` resp. `t⁻¹`.  The anchor's own
admissible range then forces exactly two binders on `t`, both DISPLAYED:

* `t ≤ 1/4` — the anchor's `s`-range has the CLOSED right endpoint `1/4`.  This
  is a genuine NARROWING of the correction's `t < 1/2`; the consumer
  must choose its Step-2 Besov index at or below `1/4`.  Nothing else in the
  Step-2 chain resists: `t ≤ 1/4 < 1/2` is strictly stronger than what
 needs.
* `homS M / 8 ≤ t` — i.e. `t` at or above the re-pinned base.  This is what
  keeps BOTH new slots inside the single gate `64 d |log γ|`:
  `2d (t/2)⁻¹ = 4 d t⁻¹ ≤ 32 d |log γ|` and `2 d t⁻¹ ≤ 16 d |log γ|`.  It also
  supplies the anchor's lower `s`-endpoint for them, since
  `C_A² √γ ≤ s/32 ≤ s/16 ≤ t/2`.  It is a vanishing constraint (`s/8 ≤ 1/32`
  and `s → 0` with `γ`), so any fixed positive Step-2 index satisfies it for
  small `γ`.

CORRECTION to this file brief: the gate moves to `64 d |log γ|` because of the
`s/32` slot of the BASE re-pin, NOT because of the two new factors.  The new
factors are merely ACCOMMODATED by `64 d |log γ|`, and only under
`homS M / 8 ≤ t`.

`t⁻¹` is kept VISIBLE in the two new majorants rather than absorbed into
`|log γ|` (no silent absorption of a parameter-dependent
quantity).  At the consumer's natural choice `t = 1/4` it is the constant `4`,
so the Step-1 display's `|log γ|²` is NOT degraded; had it been absorbed by
`t⁻¹ ≤ 8|log γ|` the display would have had to carry `|log γ|³`.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The re-pinned `γ`-threshold -/

/-- The `γ`-threshold of the RE-PINNED Step-1 factor bounds.  Branch one is the
anchor's lower `s`-endpoint at the SMALLEST slot `s/32`
(`128 C_A² γ^{1/4} ≤ 1` in the quartic gauge — eight times the `16` of
the anchor's own threshold), branch two is the anchor's own `γ`-gate,
unchanged. -/
def homSeamGamma0 (CA : ℝ) : ℝ :=
  min ((128 * max CA 1 ^ (2 : ℕ))⁻¹ ^ (4 : ℕ)) ((max CA 1)⁻¹ ^ (10 : ℕ))

theorem homSeamGamma0_pos (CA : ℝ) : 0 < homSeamGamma0 CA := by
  have hK : (0 : ℝ) < max CA 1 := maxOne_pos CA
  refine lt_min ?_ ?_
  · have h : (0 : ℝ) < (128 * max CA 1 ^ (2 : ℕ))⁻¹ := by positivity
    exact pow_pos h 4
  · exact pow_pos (inv_pos.mpr hK) 10

/-! ## 2. `3^x ≤ 3`: the improved exponent budget -/

/-- At the re-pinned base the anchor's `3`-power exponents are below `1`, so the
`3^x ≤ 27` can be sharpened to `3^x ≤ 3`.  This is exactly the slack
that keeps the produced constant at `200 max(C_A,1)`. -/
theorem rpow_three_le_three {x : ℝ} (hx : x ≤ 1) : Real.rpow (3 : ℝ) x ≤ 3 := by
  have h : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hx
  rwa [Real.rpow_one] at h

/-! ## 3. The majorant core, over abstract reals -/

/-- **The one arithmetic step of every slot**, away from `rpow`/`exp`.

`A` is the anchor's factor constant, `P` its `3`-power, `W = √q`,
`Br` its bracket, `G = √γ`; `L` is the scale the slot's majorant displays
(`|log γ|` for the two mesoscale slots, `1` for the `1/4` slot, `t⁻¹` for the
two enlarged-`Y` slots) and `B` the slot's bracket budget. -/
private theorem factor_majorant_le {A P W Br G L B C : ℝ}
    (hA : 0 ≤ A) (hP : P ≤ 3) (hW : 0 ≤ W) (hG : 0 ≤ G) (hBr0 : 0 ≤ Br)
    (hL0 : 0 ≤ L) (hBr : Br ≤ B * L) (hconst : 3 * A * B ≤ C) :
    A * P * W * Br * G ≤ C * L * W * G := by
  have hWG : (0 : ℝ) ≤ W * G := mul_nonneg hW hG
  have ha : A * P ≤ A * 3 := mul_le_mul_of_nonneg_left hP hA
  have h1 : A * P * Br ≤ A * 3 * (B * L) :=
    mul_le_mul ha hBr hBr0 (by linarith only [hA])
  have h2 : A * 3 * (B * L) = 3 * A * B * L := by ring
  have h3 : 3 * A * B * L ≤ C * L := mul_le_mul_of_nonneg_right hconst hL0
  calc A * P * W * Br * G = A * P * Br * (W * G) := by ring
    _ ≤ A * 3 * (B * L) * (W * G) := mul_le_mul_of_nonneg_right h1 hWG
    _ = 3 * A * B * L * (W * G) := by rw [h2]
    _ ≤ C * L * (W * G) := mul_le_mul_of_nonneg_right h3 hWG
    _ = C * L * W * G := by ring

/-! ## 4. The five re-pinned Step-1 factor moments -/

private theorem homStepOneSeamAnchor_comparisonBounds1 :
    ∀ (d : ℕ) (CA : ℝ) (_ : (0 : ℝ) < CA) (M : ABKModel d) (_ : (0 : ℝ) < homS M) (m : ℤ) (t : ℝ)
      (_ : (0 : ℝ) < t) (_ : homS M / (8 : ℝ) ≤ t) (q : ℝ) (_ : (64 : ℝ) * (↑d : ℝ) * |Real.log
        M.gamma| ≤ q)
      (_ : q ≤ (homConst CA)⁻¹ * M.gamma⁻¹ * homS M) (_ : (0 : ℝ) < M.gamma⁻¹) (_ : CA ≤ max CA (1
        : ℝ))
      (_ : (4 : ℝ) ≤ |Real.log M.gamma|) (_ : (0 : ℝ) < |Real.log M.gamma|) (_ : |Real.log
        M.gamma| ≠ (0 : ℝ))
      (_ : homS M ≤ (1 / 4 : ℝ)) (_ : (↑m : ℝ) - (↑(homN M m) : ℝ) = (↑(homK M) : ℝ))
      (_ : (0 : ℝ) < (32 : ℝ) * |Real.log M.gamma|) (_ : (homS M / (8 : ℝ))⁻¹ = (8 : ℝ) *
        |Real.log M.gamma|)
      (_ : (homS M / (16 : ℝ))⁻¹ = (16 : ℝ) * |Real.log M.gamma|)
      (_ : (homS M / (32 : ℝ))⁻¹ = (32 : ℝ) * |Real.log M.gamma|),
      (0 : ℝ) < t⁻¹ ∧
        (t / (2 : ℝ))⁻¹ = (2 : ℝ) * t⁻¹ ∧
          (0 : ℝ) ≤ q ∧
            (2 : ℝ) * (↑d : ℝ) * (homS M / (16 : ℝ))⁻¹ ≤ q ∧
              (2 : ℝ) * (↑d : ℝ) * (homS M / (32 : ℝ))⁻¹ ≤ q ∧
                (2 : ℝ) * (↑d : ℝ) * (1 / 4 : ℝ)⁻¹ ≤ q ∧
                  (2 : ℝ) * (↑d : ℝ) * (t / (2 : ℝ))⁻¹ ≤ q ∧
                    (2 : ℝ) * (↑d : ℝ) * t⁻¹ ≤ q ∧
                      q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / (16 : ℝ)) ∧
                        q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / (32 : ℝ)) ∧
                          q ≤ CA⁻¹ * M.gamma⁻¹ * (1 / 4 : ℝ) ∧
                            q ≤ CA⁻¹ * M.gamma⁻¹ * (t / (2 : ℝ)) ∧
                              q ≤ CA⁻¹ * M.gamma⁻¹ * t ∧
                                (↑(homK M) : ℝ) ≤ (12 : ℝ) * |Real.log M.gamma| ∧
                                  (1 / 2 : ℝ) * (homS M / (16 : ℝ)) * ((↑m : ℝ) - (↑(homN M m) :
                                    ℝ)) ≤ (1 : ℝ) := by
  intro d CA hCApos M hs m t ht htlo q hq_lo hq_hi hginv hCAK hL4 hLpos _ hs4 hgap h32L hinv8
    hinv16 hinv32
  have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  have hinvhalf : (t / 2)⁻¹ = 2 * t⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
  have htinv8 : t⁻¹ ≤ 8 * |Real.log M.gamma| := by
    have h8pos : (0 : ℝ) < homS M / 8 := by linarith only [hs]
    have h := one_div_le_one_div_of_le h8pos htlo
    rw [one_div, one_div, hinv8] at h
    exact h
  /- ### the `q`-range, lower endpoints (the gate is `64 d |log γ|`) -/
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdL : (0 : ℝ) ≤ (d : ℝ) * |Real.log M.gamma| := mul_nonneg hd0 hLpos.le
  have hqnn : (0 : ℝ) ≤ q := by
    have hlow : (0 : ℝ) ≤ 64 * (d : ℝ) * |Real.log M.gamma| := by positivity
    linarith only [hq_lo, hlow]
  have hqlo16 : 2 * (d : ℝ) * (homS M / 16)⁻¹ ≤ q := by
    rw [hinv16]
    have he1 : 2 * (d : ℝ) * (16 * |Real.log M.gamma|) =
        32 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    have he2 : 64 * (d : ℝ) * |Real.log M.gamma| =
        64 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    linarith only [hdL, he1, he2, hq_lo]
  have hqlo32 : 2 * (d : ℝ) * (homS M / 32)⁻¹ ≤ q := by
    rw [hinv32]
    have he : 2 * (d : ℝ) * (32 * |Real.log M.gamma|) =
        64 * (d : ℝ) * |Real.log M.gamma| := by ring
    linarith only [he, hq_lo]
  have hqloQ : 2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ ≤ q := by
    have hprodd : (0 : ℝ) ≤ (d : ℝ) * (8 * |Real.log M.gamma| - 1) :=
      mul_nonneg hd0 (by linarith only [hL4])
    have he1 : 2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ = 8 * (d : ℝ) := by norm_num; ring
    have he2 : 64 * (d : ℝ) * |Real.log M.gamma| - 8 * (d : ℝ) =
        8 * ((d : ℝ) * (8 * |Real.log M.gamma| - 1)) := by ring
    have hstep : 2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ ≤ 64 * (d : ℝ) * |Real.log M.gamma| := by
      linarith only [hprodd, he1, he2]
    linarith only [hstep, hq_lo]
  have hqloT2 : 2 * (d : ℝ) * (t / 2)⁻¹ ≤ q := by
    rw [hinvhalf]
    have hfac : (0 : ℝ) ≤ 2 * (d : ℝ) * 2 := by positivity
    have h := mul_le_mul_of_nonneg_left htinv8 hfac
    have hstep : 2 * (d : ℝ) * (2 * t⁻¹) ≤ 32 * ((d : ℝ) * |Real.log M.gamma|) := by
      calc 2 * (d : ℝ) * (2 * t⁻¹) = 2 * (d : ℝ) * 2 * t⁻¹ := by ring
        _ ≤ 2 * (d : ℝ) * 2 * (8 * |Real.log M.gamma|) := h
        _ = 32 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    have he2 : 64 * (d : ℝ) * |Real.log M.gamma| =
        64 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    linarith only [hstep, he2, hq_lo, hdL]
  have hqloT : 2 * (d : ℝ) * t⁻¹ ≤ q := by
    have hfac : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left htinv8 hfac
    have he : 2 * (d : ℝ) * (8 * |Real.log M.gamma|) =
        16 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    have he2 : 64 * (d : ℝ) * |Real.log M.gamma| =
        64 * ((d : ℝ) * |Real.log M.gamma|) := by ring
    linarith only [h, he, he2, hq_lo, hdL]
  /- ### the `q`-range, upper endpoints (the divisor `200` covers every slo -/
  have hCinv : (homConst CA)⁻¹ = (200 * max CA 1)⁻¹ := by rw [homConst]
  have hCApos' : (0 : ℝ) < CA⁻¹ := inv_pos.mpr hCApos
  have hKle : (max CA 1)⁻¹ ≤ CA⁻¹ := by
    have h := one_div_le_one_div_of_le hCApos hCAK
    rwa [one_div, one_div] at h
  have hconst_le : (homConst CA)⁻¹ ≤ (max CA 1)⁻¹ / 200 := by
    rw [hCinv, mul_inv]
    have h : (200 : ℝ)⁻¹ * (max CA 1)⁻¹ = (max CA 1)⁻¹ / 200 := by ring
    linarith only [h]
  have hupper : ∀ s' : ℝ, homS M / 200 ≤ s' → q ≤ CA⁻¹ * M.gamma⁻¹ * s' := by
    intro s' hle
    have h1 : (homConst CA)⁻¹ * homS M ≤ ((max CA 1)⁻¹ / 200) * homS M :=
      mul_le_mul_of_nonneg_right hconst_le hs.le
    have h2 : ((max CA 1)⁻¹ / 200) * homS M ≤ CA⁻¹ * s' := by
      have hstep1 : (max CA 1)⁻¹ * (homS M / 200) ≤ CA⁻¹ * (homS M / 200) :=
        mul_le_mul_of_nonneg_right hKle (by linarith only [hs])
      have hstep2 : CA⁻¹ * (homS M / 200) ≤ CA⁻¹ * s' :=
        mul_le_mul_of_nonneg_left hle hCApos'.le
      have he : ((max CA 1)⁻¹ / 200) * homS M = (max CA 1)⁻¹ * (homS M / 200) := by ring
      linarith only [hstep1, hstep2, he]
    have hbase : (homConst CA)⁻¹ * homS M ≤ CA⁻¹ * s' := by linarith only [h1, h2]
    have hstep : (homConst CA)⁻¹ * M.gamma⁻¹ * homS M ≤ CA⁻¹ * M.gamma⁻¹ * s' := by
      have e1 : (homConst CA)⁻¹ * M.gamma⁻¹ * homS M =
          M.gamma⁻¹ * ((homConst CA)⁻¹ * homS M) := by ring
      have e2 : CA⁻¹ * M.gamma⁻¹ * s' = M.gamma⁻¹ * (CA⁻¹ * s') := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hbase hginv.le
    linarith only [hq_hi, hstep]
  have hup16 : q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / 16) := hupper _ (by linarith only [hs])
  have hup32 : q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / 32) := hupper _ (by linarith only [hs])
  have hupQ : q ≤ CA⁻¹ * M.gamma⁻¹ * (1 / 4) := hupper _ (by linarith only [hs, hs4])
  have hupT2 : q ≤ CA⁻¹ * M.gamma⁻¹ * (t / 2) := hupper _ (by linarith only [hs, htlo])
  have hupT : q ≤ CA⁻¹ * M.gamma⁻¹ * t := hupper _ (by linarith only [hs, htlo])
  /- ### the IMPROVED `3`-power budge -/
  have hkle : (homK M : ℝ) ≤ 12 * |Real.log M.gamma| := by
    have h := homK_le M
    linarith only [h, hL4]
  have hexp16 : 1 / 2 * (homS M / 16) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 1 := by
    rw [hgap, homS]
    have hval : 1 / 2 * (|Real.log M.gamma|⁻¹ / 16) * (homK M : ℝ) =
        (homK M : ℝ) / (32 * |Real.log M.gamma|) := by field_simp; ring
    rw [hval, div_le_iff₀ h32L]
    linarith only [hkle, hLpos]
  exact ⟨htinv, hinvhalf, hqnn, hqlo16, hqlo32, hqloQ, hqloT2, hqloT, hup16, hup32, hupQ, hupT2,
    hupT, hkle, hexp16⟩

/-- **THE RE-PINNED STEP-1 FACTOR MOMENTS.**

The sibling of the anchor's Step-1 factor moments at the re-pinned
base `homSeamBase M hs = s/8` AND at the two enlarged-`Y` indices `t/2`, `t` of
`HomSpineTopScale.stepTwoEnlargedY`.  The `bounds_mathcal_E_aL` lemma
is applied five times; every hypothesis below is either one of the anchor's own
binders, discharged here, or one of the four displayed gates
(`homS M / 8 ≤ t`, `t ≤ 1/4`, `64 d |log γ| ≤ q`, `q ≤ C⁻¹ γ⁻¹ s`).

The `t⁻¹` of the last two majorants is deliberately NOT absorbed into
`|log γ|`; see the module docstring. -/
theorem exists_ethmB_seam_factor_moments (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 1 ≤ C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ hs : 0 < homS M, ∀ m : ℤ, ∀ t : ℝ, ∀ ht : 0 < t,
          homS M / 8 ≤ t → t ≤ 1 / 4 →
          ∀ q : ℝ,
            64 * (d : ℝ) * |Real.log M.gamma| ≤ q →
            q ≤ C⁻¹ * M.gamma⁻¹ * homS M →
              (∫⁻ omega,
                  fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
                      (homHalf (homSeamBase M hs)) omega ^ q
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma) ^ q ∧
              (∫⁻ omega,
                  fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ^ q
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (C * Real.sqrt q * Real.sqrt M.gamma) ^ q ∧
              (∫⁻ omega,
                  fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
                      (homQuarterOf (homSeamBase M hs)) omega ^ q
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma) ^ q ∧
              (∫⁻ omega,
                  fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ omega ^ q
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (C * t⁻¹ * Real.sqrt q * Real.sqrt M.gamma) ^ q ∧
              (∫⁻ omega,
                  fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ omega ^ q
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (C * t⁻¹ * Real.sqrt q * Real.sqrt M.gamma) ^ q := by
  obtain ⟨CA, hCApos, hanchor⟩ := Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL d cstar hcstar
  refine ⟨homSeamGamma0 CA, homConst CA, homSeamGamma0_pos CA, one_le_homConst CA, ?_⟩
  intro M hcs hgamma hs m t ht htlo hthi q hq_lo hq_hi
  /- ### the model's own positivi -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.mpr hgpos
  have hK1 : (1 : ℝ) ≤ max CA 1 := one_le_maxOne CA
  have hKpos : (0 : ℝ) < max CA 1 := maxOne_pos CA
  have hCAK : CA ≤ max CA 1 := le_max_left _ _
  have hCA0 : (0 : ℝ) ≤ CA := hCApos.le
  /- ### the two branches of the re-pinned `γ`-ga -/
  have hg_a : M.gamma ≤ (128 * max CA 1 ^ (2 : ℕ))⁻¹ ^ (4 : ℕ) :=
    le_trans hgamma (min_le_left _ _)
  have hg_b : M.gamma ≤ (max CA 1)⁻¹ ^ (10 : ℕ) := le_trans hgamma (min_le_right _ _)
  /- ### the quartic gauge at `128` -/
  have hbnn : (0 : ℝ) ≤ (128 * max CA 1 ^ (2 : ℕ))⁻¹ := by positivity
  have hroot : Real.sqrt (Real.sqrt M.gamma) ≤ (128 * max CA 1 ^ (2 : ℕ))⁻¹ :=
    quarticRoot_le hgpos.le hbnn hg_a
  have hKsq : (1 : ℝ) ≤ max CA 1 ^ (2 : ℕ) := one_le_pow₀ hK1
  have h128 : (128 : ℝ) ≤ 128 * max CA 1 ^ (2 : ℕ) := by linarith only [hKsq]
  have h128pos : (0 : ℝ) < 128 * max CA 1 ^ (2 : ℕ) := by linarith only [h128]
  have hroot128 : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 128 := by
    refine le_trans hroot ?_
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128) h128
    rwa [one_div (128 * max CA 1 ^ (2 : ℕ))] at hinv
  have hroot16 : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 16 := by linarith only [hroot128]
  have hgsmall : M.gamma ≤ 1 / 65536 := by
    have h4 := quarticRoot_pow_four (gamma := M.gamma) hgpos.le
    rw [← h4]
    calc Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) ≤ (1 / 16 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot16 4
      _ = 1 / 65536 := by norm_num
  have hg1 : M.gamma < 1 := by linarith only [hgsmall]
  have hL4 : 4 ≤ |Real.log M.gamma| :=
    four_le_absLog hgpos (by linarith only [hgsmall])
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hLne : |Real.log M.gamma| ≠ 0 := ne_of_gt hLpos
  have hs4 : homS M ≤ 1 / 4 := homS_le_quarter hL4
  /- ### the anchor's `γ`-ga -/
  have hanchor_gate : M.gamma ≤ CA⁻¹ ^ (10 : ℕ) := by
    refine le_trans hg_b (pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hKpos)) ?_ 10)
    have h := one_div_le_one_div_of_le hCApos hCAK
    rwa [one_div, one_div] at h
  /- ### the mesoscale binde -/
  have hnm : homN M m ≤ m := homN_le M m
  have hgap : ((m : ℝ)) - ((homN M m : ℤ) : ℝ) = (homK M : ℝ) := homN_gap M m
  have hmn : (m : ℝ) ≤ ((homN M m : ℤ) : ℝ) + M.gamma⁻¹ := by
    have hk := homK_le_inv_gamma M hgpos hg1 hroot16
    linarith only [hgap, hk]
  have hmm : (m : ℝ) ≤ (m : ℝ) + M.gamma⁻¹ := by linarith only [hginv]
  /- ### the anchor's lower `s`-endpoint, at the smallest slot `s/32` -/
  have hLsq : |Real.log M.gamma| * Real.sqrt M.gamma ≤
      4 * Real.sqrt (Real.sqrt M.gamma) := absLog_mul_sqrt_le hgpos hg1
  have hCAsq : CA ^ (2 : ℕ) ≤ max CA 1 ^ (2 : ℕ) := pow_le_pow_left₀ hCApos.le hCAK 2
  have h32L : (0 : ℝ) < 32 * |Real.log M.gamma| := by linarith only [hLpos]
  have h64L : (0 : ℝ) < 64 * |Real.log M.gamma| := by linarith only [hLpos]
  have hprod : CA ^ (2 : ℕ) * Real.sqrt M.gamma * (32 * |Real.log M.gamma|) ≤ 1 := by
    have e1 : CA ^ (2 : ℕ) * Real.sqrt M.gamma * (32 * |Real.log M.gamma|) =
        32 * CA ^ (2 : ℕ) * (|Real.log M.gamma| * Real.sqrt M.gamma) := by ring
    rw [e1]
    have hnn : (0 : ℝ) ≤ 32 * CA ^ (2 : ℕ) := by positivity
    have ht0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt M.gamma) := Real.sqrt_nonneg _
    calc 32 * CA ^ (2 : ℕ) * (|Real.log M.gamma| * Real.sqrt M.gamma)
        ≤ 32 * CA ^ (2 : ℕ) * (4 * Real.sqrt (Real.sqrt M.gamma)) :=
          mul_le_mul_of_nonneg_left hLsq hnn
      _ = 128 * CA ^ (2 : ℕ) * Real.sqrt (Real.sqrt M.gamma) := by ring
      _ ≤ 128 * max CA 1 ^ (2 : ℕ) * Real.sqrt (Real.sqrt M.gamma) := by
          have h : 128 * CA ^ (2 : ℕ) ≤ 128 * max CA 1 ^ (2 : ℕ) := by
            linarith only [hCAsq]
          exact mul_le_mul_of_nonneg_right h ht0
      _ ≤ 128 * max CA 1 ^ (2 : ℕ) * (128 * max CA 1 ^ (2 : ℕ))⁻¹ :=
          mul_le_mul_of_nonneg_left hroot h128pos.le
      _ = 1 := by field_simp
  have hlow32 : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ homS M / 32 := by
    have hdiv : homS M / 32 = 1 / (32 * |Real.log M.gamma|) := by
      rw [homS]; field_simp
    rw [hdiv]
    exact (le_div_iff₀ h32L).mpr hprod
  have hlow16 : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ homS M / 16 := by
    have h : homS M / 32 ≤ homS M / 16 := by linarith only [hs]
    linarith only [hlow32, h]
  have hlow8 : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ homS M / 8 := by
    have h : homS M / 32 ≤ homS M / 8 := by linarith only [hs]
    linarith only [hlow32, h]
  have hlowT2 : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ t / 2 := by
    have h : homS M / 16 ≤ t / 2 := by linarith only [htlo]
    linarith only [hlow16, h]
  have hlowT : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ t := by
    linarith only [hlow8, htlo]
  have hlowQ : CA ^ (2 : ℕ) * Real.sqrt M.gamma ≤ 1 / 4 := by
    have h : homS M / 32 ≤ 1 / 4 := by linarith only [hs4, hs]
    linarith only [hlow32, h]
  /- ### the three inverse identities of the re-pinned slo -/
  have hinv8 : (homS M / 8)⁻¹ = 8 * |Real.log M.gamma| := by rw [homS]; field_simp
  have hinv16 : (homS M / 16)⁻¹ = 16 * |Real.log M.gamma| := by rw [homS]; field_simp
  have hinv32 : (homS M / 32)⁻¹ = 32 * |Real.log M.gamma| := by rw [homS]; field_simp
  have htne : t ≠ 0 := ne_of_gt ht
  obtain ⟨htinv, hinvhalf, hqnn, hqlo16, hqlo32, hqloQ, hqloT2, hqloT, hup16, hup32, hupQ, hupT2,
    hupT, hkle, hexp16⟩ :=
    (show ((0 : ℝ) < t⁻¹) ∧ ((t / 2)⁻¹ = 2 * t⁻¹) ∧ ((0 : ℝ) ≤ q) ∧ (2 * (d : ℝ) * (homS M / 16)⁻¹
      ≤ q) ∧ (2 * (d : ℝ) * (homS M / 32)⁻¹ ≤ q) ∧ (2 * (d : ℝ) * ((1 : ℝ) / 4)⁻¹ ≤ q) ∧ (2 * (d :
        ℝ) * (t / 2)⁻¹ ≤ q) ∧ (2 * (d : ℝ) * t⁻¹ ≤ q) ∧ (q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / 16)) ∧
          (q ≤ CA⁻¹ * M.gamma⁻¹ * (homS M / 32)) ∧ (q ≤ CA⁻¹ * M.gamma⁻¹ * (1 / 4)) ∧ (q ≤ CA⁻¹ *
            M.gamma⁻¹ * (t / 2)) ∧ (q ≤ CA⁻¹ * M.gamma⁻¹ * t) ∧ ((homK M : ℝ) ≤ 12 * |Real.log
              M.gamma|) ∧ (1 / 2 * (homS M / 16) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 1) from
      @homStepOneSeamAnchor_comparisonBounds1 (d) (CA) (hCApos) (M) (hs) (m) (t) (ht) (htlo) (q)
        (hq_lo) (hq_hi) (hginv) (hCAK) (hL4) (hLpos) (hLne) (hs4) (hgap) (h32L) (hinv8) (hinv16)
          (hinv32))
  have hexp32 : 1 / 2 * (homS M / 32) * ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤ 1 := by
    rw [hgap, homS]
    have hval : 1 / 2 * (|Real.log M.gamma|⁻¹ / 32) * (homK M : ℝ) =
        (homK M : ℝ) / (64 * |Real.log M.gamma|) := by field_simp; ring
    rw [hval, div_le_iff₀ h64L]
    linarith only [hkle, hLpos]
  /- ### the bracket budge -/
  have hsqrtk : Real.sqrt ((homK M : ℝ)) ≤ 2 * |Real.log M.gamma| := sqrt_homK_le M hL4
  have hbr16 : (homS M / 16)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤
      18 * |Real.log M.gamma| := by
    rw [hgap, hinv16]
    linarith only [hsqrtk]
  have hbr32 : (homS M / 32)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) ≤
      34 * |Real.log M.gamma| := by
    rw [hgap, hinv32]
    linarith only [hsqrtk]
  have hbr16nn : (0 : ℝ) ≤ (homS M / 16)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) := by
    have h : (0 : ℝ) ≤ (homS M / 16)⁻¹ := by rw [hinv16]; linarith only [hLpos]
    linarith only [h, Real.sqrt_nonneg ((m : ℝ) - ((homN M m : ℤ) : ℝ))]
  have hbr32nn : (0 : ℝ) ≤ (homS M / 32)⁻¹ + Real.sqrt ((m : ℝ) - ((homN M m : ℤ) : ℝ)) := by
    have h : (0 : ℝ) ≤ (homS M / 32)⁻¹ := by rw [hinv32]; linarith only [hLpos]
    linarith only [h, Real.sqrt_nonneg ((m : ℝ) - ((homN M m : ℤ) : ℝ))]
  /- ### the five constant budgets, all under `200 max(C_A, 1)` -/
  have hc16 : 3 * CA * 18 ≤ homConst CA := by
    rw [homConst]; linarith only [hCAK, hKpos]
  have hc32 : 3 * CA * 34 ≤ homConst CA := by
    rw [homConst]; linarith only [hCAK, hKpos]
  have hcQ : 3 * CA * 4 ≤ homConst CA := by
    rw [homConst]; linarith only [hCAK, hKpos]
  have hcT2 : 3 * CA * 2 ≤ homConst CA := by
    rw [homConst]; linarith only [hCAK, hKpos]
  have hcT : 3 * CA * 1 ≤ homConst CA := by
    rw [homConst]; linarith only [hCAK, hKpos]
  have hsqq : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqg : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
  have hzero : (m : ℝ) - (m : ℝ) = 0 := sub_self _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · /- slot (i): the re-pinned first factor, `s'/2 = s/16`, gap `k` -/
    have hcong : fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homHalf (homSeamBase M hs)) =
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          ⟨homS M / 16, by linarith only [hs]⟩ :=
      fluxCorrectedTwoScaleErrorObservableSup_congr_order M m (homN M m)
        (by simp only [homHalf_val, homSeamBase_val]; ring)
    rw [hcong]
    have happ := hanchor M hcs hanchor_gate m (homN M m) hnm hmn (homS M / 16)
      ⟨hlow16, by linarith only [hs4, hs]⟩ (by linarith only [hs]) q ⟨hqlo16, hup16⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    exact factor_majorant_le (L := |Real.log M.gamma|) (B := 18) hCA0
      (rpow_three_le_three hexp16) hsqq hsqg hbr16nn hLpos.le hbr16 hc16
  · /- slot (ii): the fixed exponent `1/4` at the CLOSED endpoint, gap `0` -/
    have happ := hanchor M hcs hanchor_gate m m (le_refl m) hmm (1 / 4)
      ⟨hlowQ, le_refl _⟩ (by norm_num) q ⟨hqloQ, hupQ⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    rw [hzero, Real.sqrt_zero]
    have hexp0 : (1 : ℝ) / 2 * (1 / 4) * 0 = 0 := by ring
    rw [hexp0, rpow_three_zero]
    calc CA * 1 * Real.sqrt q * (((1 : ℝ) / 4)⁻¹ + 0) * Real.sqrt M.gamma
        ≤ homConst CA * 1 * Real.sqrt q * Real.sqrt M.gamma :=
          factor_majorant_le (L := 1) (B := 4) hCA0 (by norm_num) hsqq hsqg
            (by norm_num) (by norm_num) (by norm_num) hcQ
      _ = homConst CA * Real.sqrt q * Real.sqrt M.gamma := by ring
  · /- slot (iii): the re-pinned gap factor, `s'/4 = s/32`, gap `k` -/
    have hcong : fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) =
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          ⟨homS M / 32, by linarith only [hs]⟩ :=
      fluxCorrectedTwoScaleErrorObservableSup_congr_order M m (homN M m)
        (by simp only [homQuarterOf_val, homSeamBase_val]; ring)
    rw [hcong]
    have happ := hanchor M hcs hanchor_gate m (homN M m) hnm hmn (homS M / 32)
      ⟨hlow32, by linarith only [hs4, hs]⟩ (by linarith only [hs]) q ⟨hqlo32, hup32⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    exact factor_majorant_le (L := |Real.log M.gamma|) (B := 34) hCA0
      (rpow_three_le_three hexp32) hsqq hsqg hbr32nn hLpos.le hbr32 hc32
  · /- slot (iv): the FIRST enlarged-`Y` factor, `t/2`, gap `0` -/
    have happ := hanchor M hcs hanchor_gate m m (le_refl m) hmm (t / 2)
      ⟨hlowT2, by linarith only [hthi, ht]⟩ (half_pos ht) q ⟨hqloT2, hupT2⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    rw [hzero, Real.sqrt_zero]
    have hexp0 : (1 : ℝ) / 2 * (t / 2) * 0 = 0 := by ring
    rw [hexp0, rpow_three_zero]
    exact factor_majorant_le (L := t⁻¹) (B := 2) hCA0 (by norm_num) hsqq hsqg
      (by rw [hinvhalf, add_zero]; linarith only [htinv]) htinv.le
      (le_of_eq (by rw [hinvhalf, add_zero])) hcT2
  · /- slot (v): the SECOND enlarged-`Y` factor, `t`, gap `0` -/
    have happ := hanchor M hcs hanchor_gate m m (le_refl m) hmm t
      ⟨hlowT, hthi⟩ ht q ⟨hqloT, hupT⟩
    refine le_trans happ (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hqnn)
    rw [hzero, Real.sqrt_zero]
    have hexp0 : (1 : ℝ) / 2 * t * 0 = 0 := by ring
    rw [hexp0, rpow_three_zero]
    exact factor_majorant_le (L := t⁻¹) (B := 1) hCA0 (by norm_num) hsqq hsqg
      (by rw [add_zero]; linarith only [htinv]) htinv.le
      (le_of_eq (by rw [add_zero, one_mul])) hcT

end

end Algsuperdiff.Section4.Provider.Homogenization
