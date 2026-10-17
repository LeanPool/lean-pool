/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ProportionAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2ThresholdSharp

/-!
# ProportionFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `§4.1` proportion display with the `𝒢₂` slot discharged

`ProportionAssembly.exists_proportionTail_of_honestG1` proves the display with
the `𝒢₂` lane left open as a caller-supplied obligation in `LaneTailFrom` shape,
at the split level `θ/(32(r+1))` and the assembly rate `c₁ = 2A`.
`G2ThresholdSharp.g2ThresholdSharp_le_of_anchor` discharges the `ε`-threshold of
that lane from the anchor's own clauses plus two `d`-only constant floors on the
anchor constant.  This module performs the stitch: the two floors are absorbed
into one constant `proportionConst d`, and the resulting theorem has **no
hypothesis beyond the anchor's own printed clauses**.

## The constant, and what it dominates

```
proportionConst d = max (max (6·assemblyConst d)           -- the assembly's own C
                             (g2LaneConst d ^ 10))          -- the lane's regime clause
                        (max (g2SharpAnchorConst    d r C N) -- the binding 𝒢₂ floor
                             (g2SharpAnchorConstTwo d r C N)) -- the exp-small 𝒢₂ floor
```

with `r = laneRange d`, `C = g2LaneConst d` and `N = 32(r+1)`.  The max-fold works
because the anchor's strength is **linear** in its constant: raising `C` only
strengthens the regime and level clauses and only weakens the conclusion, while
the assembly is applied at its own constant through
`ProportionArith.anchorRegime_shrink` / `anchorLevel_weaken`, and the `𝒢₁`
coupling is read at `C_a = C/2` — which is exactly why the assembly's floor is
`6·assemblyConst d` and why the rate identity `C_a·(2A γ) = c⋆²s⁷ε²θ` holds with
equality.

The stitch consumes the **rate-parametrised** assembly
`exists_proportionTail_of_honestG1` rather than a fixed-constant consumer of it,
and this is forced: the rate of the `𝒢₂`
obligation is `2A = 2c⋆²s⁷ε²θ/(Cγ)`, which *decreases* in `C`, so a lane endpoint
produced at the absorbing constant is too weak for a slot read at a smaller one.
Keeping `A` a free parameter — the assembly's own interface — lets the slot, the
two floors and the displayed exponent all be read at the single constant
`proportionConst d`.  Nothing else about the composition changes: the level
`θ/(32(r+1))` and the rate `2A` of the assembly's slot are, character for
character, the level and rate of `G2ThresholdSharp`'s endpoint at
`r = laneRange d`, `N = 32(r+1)`, `C_a = proportionConst d`, so no monotonicity
step in the level or the rate is used.

## What is and is not claimed

`exists_proportion_good_scales_provider` is a **proved local Provider
helper**.  No Frozen.Section4 statement module is imported.

## Contents

* `assemblyConst`, `g2LaneConst` — the two constants entering the stitch;
* `proportionConst` and its four domination lemmas — the `C`-absorption record;
* `laneTailFrom_eventG2_of_anchor` — the `𝒢₂` obligation of the assembly, proved
  from the anchor's own clauses at `proportionConst d`;
* `exists_proportion_good_scales_provider` — the composed display.

## References

* ABK26, `p.independence.between.scales`;
  `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

/-! ## 1. The two constants of the stitch -/

/-- **The constant of the proportion assembly** at the honest `𝒢₁` condition
(`ProportionAssembly.exists_proportionTail_of_honestG1`). -/
def assemblyConst (d : ℕ) : ℝ := (exists_proportionTail_of_honestG1 d).choose

theorem one_le_assemblyConst (d : ℕ) : 1 ≤ assemblyConst d :=
  (exists_proportionTail_of_honestG1 d).choose_spec.1

theorem assemblyConst_pos (d : ℕ) : 0 < assemblyConst d := by
  have h := one_le_assemblyConst d
  linarith only [h]

/-- **The dimensional constant of the sharp `𝒢₂` lane endpoint**
(`G2ThresholdSharp.ratioTail_eventG2_of_thresholdSharp_shift`): the constant of
the two-term per-cube display. -/
def g2LaneConst (d : ℕ) : ℝ := (ratioTail_eventG2_of_thresholdSharp_shift d).choose

theorem g2LaneConst_pos (d : ℕ) : 0 < g2LaneConst d :=
  (ratioTail_eventG2_of_thresholdSharp_shift d).choose_spec.1

/-! ## 2. The absorbing constant -/

/-- **The constant of the composed proportion provider.**

A single `max`-fold of the four floors the stitch needs:

* `6·assemblyConst d` — the assembly, read at `C_a = C/2` in the `𝒢₁` coupling;
* `g2LaneConst d ^ 10` — the lane's own regime clause `γ ≤ C⁻¹⁰c⋆¹⁰`;
* `g2SharpAnchorConst d r — the binding clause of the sharp `𝒢₂` threshold;
* `g2SharpAnchorConstTwo d r — its exponentially small clause;

at `r = laneRange d`, `C = g2LaneConst d`, `N = 32(r+1)`.  All four are functions
of `d` alone. -/
def proportionConst (d : ℕ) : ℝ :=
  max (max (6 * assemblyConst d) (g2LaneConst d ^ (10 : ℕ)))
    (max (g2SharpAnchorConst d (laneRange d) (g2LaneConst d)
        (32 * ((laneRange d : ℝ) + 1)))
      (g2SharpAnchorConstTwo d (laneRange d) (g2LaneConst d)
        (32 * ((laneRange d : ℝ) + 1))))

theorem six_assemblyConst_le_proportionConst (d : ℕ) :
    6 * assemblyConst d ≤ proportionConst d := by
  rw [proportionConst]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem g2LaneConst_pow_le_proportionConst (d : ℕ) :
    g2LaneConst d ^ (10 : ℕ) ≤ proportionConst d := by
  rw [proportionConst]
  exact le_trans (le_max_right _ _) (le_max_left _ _)

theorem g2SharpAnchorConst_le_proportionConst (d : ℕ) :
    g2SharpAnchorConst d (laneRange d) (g2LaneConst d) (32 * ((laneRange d : ℝ) + 1))
      ≤ proportionConst d := by
  rw [proportionConst]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem g2SharpAnchorConstTwo_le_proportionConst (d : ℕ) :
    g2SharpAnchorConstTwo d (laneRange d) (g2LaneConst d) (32 * ((laneRange d : ℝ) + 1))
      ≤ proportionConst d := by
  rw [proportionConst]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem six_le_proportionConst (d : ℕ) : 6 ≤ proportionConst d := by
  have h1 := one_le_assemblyConst d
  have h6 := six_assemblyConst_le_proportionConst d
  linarith only [h1, h6]

theorem one_le_proportionConst (d : ℕ) : 1 ≤ proportionConst d := by
  have h := six_le_proportionConst d
  linarith only [h]

theorem proportionConst_pos (d : ℕ) : 0 < proportionConst d := by
  have h := six_le_proportionConst d
  linarith only [h]

theorem assemblyConst_le_proportionConst (d : ℕ) : assemblyConst d ≤ proportionConst d := by
  have h0 := assemblyConst_pos d
  have h6 := six_assemblyConst_le_proportionConst d
  linarith only [h0, h6]

/-! ## 3. The `𝒢₂` obligation of the assembly, discharged -/

/-- **The assembly's `𝒢₂` slot, proved from the anchor's own clauses.**

The `LaneTailFrom` hypothesis `hG2` of
`ProportionAssembly.exists_proportionTail_of_honestG1` — at the split level
`θ/(32(r+1))` and the assembly rate `2A`, `A = c⋆²s⁷ε²θ/(Cγ)` — holds at
`C = proportionConst d` for every model and every parameter triple obeying the
anchor's parameter ranges, its regime clause, its standing window `8γ ≤ s` and
its level clause **at `s⁻⁶`**.

The route: `G2ThresholdSharp.g2ThresholdSharp_le_of_anchor` turns the level
clause into the lane's `ε`-threshold (its two constant floors are the third and
fourth summands of `proportionConst`), and
`G2ThresholdSharp.ratioTail_eventG2_of_thresholdSharp_shift` — read at the
assembly's own range `laneRange d`, admissible by `laneRange_gap` — delivers the
tail at every base.  No hypothesis of the lane survives: the level admissibility
`θ/(32(r+1))·(r+1) < 1` is `θ/32 < 1`, and the regime is the anchor's own,
weakened through `g2LaneConst d ^ 10 ≤ proportionConst d`. -/
theorem laneTailFrom_eventG2_of_anchor (d : ℕ) (M : ABKModel d) {s ep theta : ℝ}
    (hs : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hth0 : 0 < theta) (hth12 : theta ≤ 1 / 2)
    (hreg : M.gamma ≤ (proportionConst d)⁻¹ * Disorder.cstar M ^ (10 : ℕ))
    (hgam : 8 * M.gamma ≤ s)
    (hlevel : proportionConst d * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) *
      ep⁻¹ ^ (2 : ℕ) * M.gamma ≤ theta) :
    LaneTailFrom M (fun k => Support.eventG2 M k ⟨s, hs⟩ ep)
      (theta / (32 * ((laneRange d : ℝ) + 1)))
      (2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta /
        (proportionConst d * M.gamma))) := by
  have hC0 : (0 : ℝ) < proportionConst d := proportionConst_pos d
  have hC1 : (1 : ℝ) ≤ proportionConst d := one_le_proportionConst d
  have hCg0 : (0 : ℝ) < g2LaneConst d := g2LaneConst_pos d
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hr1 : 1 ≤ laneRange d := one_le_laneRange d
  have hLcast : (1 : ℝ) ≤ ((laneRange d : ℕ) : ℝ) := by exact_mod_cast hr1
  have hN1 : (1 : ℝ) ≤ 32 * ((laneRange d : ℝ) + 1) := by linarith only [hLcast]
  have hN0 : (0 : ℝ) < 32 * ((laneRange d : ℝ) + 1) := by linarith only [hN1]
  -- the `ε`-threshold of the lane, from the anchor's clauses and the two floors
  have hthr : g2ThresholdSharp d (laneRange d) (g2LaneConst d) M s
      (theta / (32 * ((laneRange d : ℝ) + 1)))
      (2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta /
        (proportionConst d * M.gamma))) ≤ ep ^ (2 : ℕ) :=
    g2ThresholdSharp_le_of_anchor M hr1 hCg0 hN1 hC1 hs hs12 hep0 hep12 hth0 hth12
      hreg hlevel (g2SharpAnchorConst_le_proportionConst d)
      (g2SharpAnchorConstTwo_le_proportionConst d)
  -- the lane's own regime clause
  have hregCg : M.gamma ≤ ((g2LaneConst d)⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    have hpow : (0 : ℝ) < g2LaneConst d ^ (10 : ℕ) := pow_pos hCg0 10
    have hinv : ((g2LaneConst d)⁻¹) ^ (10 : ℕ) = (g2LaneConst d ^ (10 : ℕ))⁻¹ := inv_pow _ _
    have hle : (proportionConst d)⁻¹ ≤ (g2LaneConst d ^ (10 : ℕ))⁻¹ :=
      inv_anti₀ hpow (g2LaneConst_pow_le_proportionConst d)
    have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) := pow_nonneg hcs0.le 10
    calc M.gamma ≤ (proportionConst d)⁻¹ * Disorder.cstar M ^ (10 : ℕ) := hreg
      _ ≤ (g2LaneConst d ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
          mul_le_mul_of_nonneg_right hle hcs10
      _ = ((g2LaneConst d)⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by rw [hinv]
  -- the standing window and the level admissibility
  have hswin : ((⟨s, hs⟩ : {x : ℝ // 0 < x}) : ℝ) ∈ Set.Icc (8 * M.gamma) 1 :=
    Set.mem_Icc.2 ⟨hgam, by linarith only [hs12]⟩
  have hthN0 : (0 : ℝ) < theta / (32 * ((laneRange d : ℝ) + 1)) := div_pos hth0 hN0
  have hthNr : theta / (32 * ((laneRange d : ℝ) + 1)) * ((laneRange d : ℝ) + 1) < 1 := by
    have hL0 : (0 : ℝ) < (laneRange d : ℝ) + 1 := by linarith only [hLcast]
    have hne : ((laneRange d : ℝ) + 1) ≠ 0 := ne_of_gt hL0
    have hval : theta / (32 * ((laneRange d : ℝ) + 1)) * ((laneRange d : ℝ) + 1)
        = theta / 32 := by
      field_simp
    rw [hval, div_lt_one (by norm_num : (0 : ℝ) < 32)]
    linarith only [hth12]
  have hc10 : (0 : ℝ) ≤ 2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta /
      (proportionConst d * M.gamma)) := by
    have h := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hcs0.le 2)
      (pow_nonneg hs.le 7)) (pow_nonneg hep0.le 2)) hth0.le) (mul_pos hC0 hg0).le
    linarith only [h]
  intro m1 n
  exact (ratioTail_eventG2_of_thresholdSharp_shift d).choose_spec.2 (laneRange d) hr1
    (laneRange_gap d) M hregCg ⟨s, hs⟩ hswin
    (theta / (32 * ((laneRange d : ℝ) + 1))) hthN0 hthNr
    (2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta /
      (proportionConst d * M.gamma))) hc10 ep hep0 hthr m1 n

/-! ## 4. The composed display -/

/-- **The `§4.1` proportion display at the `s⁻⁶`/`s⁷` anchor clauses, with every
lane discharged.**

The standing window clause `8γ ≤ s`, unconsumed by the two proved lanes at the
split level, is genuinely consumed here: it is the lane's own standing window.

Disclosure: a proved local Provider helper. -/
theorem exists_proportion_good_scales_provider
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s ep theta : ℝ),
        s ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        ep ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        theta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        M.gamma ≤
          C⁻¹ * min (Disorder.cstar M ^ (10 : ℕ))
            (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)) →
        8 * M.gamma ≤ s →
        C * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) *
            M.gamma ≤ theta →
        ∀ (m0 : ℤ) (Mw : ℕ) (hs : 0 < s),
          (Cutoff.cutoffSampleLaw M).toMeasure
              {omega |
                (1 / ((Mw : ℝ) + 1)) *
                    ∑ k ∈ Finset.range (Mw + 1),
                      (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d)
                            (m0 + (k : ℤ)) 0 ⟨s, hs⟩ ep).indicator
                        (fun _ => (1 : ℝ)) omega ≤
                  1 - theta } ≤
            ENNReal.ofReal
              (6 *
                Real.exp
                  (-(Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) *
                        theta * ((Mw : ℝ) + 1)) /
                    (C * M.gamma))) := by
  refine ⟨proportionConst d, proportionConst_pos d, ?_⟩
  intro M s ep theta hsm hepm hthm hreg hgam hlevel m0 Mw hs
  have hs0 : (0 : ℝ) < s := hsm.1
  have hs12 : s ≤ 1 / 2 := hsm.2
  have hep0 : (0 : ℝ) < ep := hepm.1
  have hep12 : ep ≤ 1 / 2 := hepm.2
  have htheta0 : (0 : ℝ) < theta := hthm.1
  have htheta12 : theta ≤ 1 / 2 := hthm.2
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hC0 : (0 : ℝ) < proportionConst d := proportionConst_pos d
  have hC6 : (6 : ℝ) ≤ proportionConst d := six_le_proportionConst d
  have hA0' : (0 : ℝ) < assemblyConst d := assemblyConst_pos d
  have hAle : assemblyConst d ≤ proportionConst d := assemblyConst_le_proportionConst d
  have hCne : proportionConst d ≠ 0 := ne_of_gt hC0
  have hgne : M.gamma ≠ 0 := ne_of_gt hg0
  -- the anchor's clauses, read at the two smaller constants the pieces need
  have hregCa : M.gamma ≤ (proportionConst d)⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    anchorRegime_shrink hC0 (le_refl _) hreg
  have hregC0 : M.gamma ≤ (assemblyConst d)⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    anchorRegime_shrink hA0' hAle hreg
  have hlevel4 : assemblyConst d * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (4 : ℕ) *
      ep⁻¹ ^ (2 : ℕ) * M.gamma ≤ theta :=
    anchorLevel_weaken hA0' hAle hs0 hs12 hg0 hlevel
  -- the assembly rate
  obtain ⟨A, hAdef⟩ : ∃ x : ℝ,
      x = Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta /
        (proportionConst d * M.gamma) := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hAdef]
    have h := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hcs0.le 2)
      (pow_nonneg hs0.le 7)) (pow_nonneg hep0.le 2)) htheta0.le) (mul_pos hC0 hg0).le
    linarith only [h]
  have hNle : Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta ≤ 9 / 4 :=
    anchorNumerator_le hcs0 hcs32 hs0 hs12 hep0 hep12 htheta0 htheta12
  have hAceil : 2 * A * M.gamma ≤ 1 := by
    have hval : 2 * A * M.gamma
        = 2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) /
            proportionConst d := by
      rw [hAdef]
      field_simp
    rw [hval, div_le_one hC0]
    linarith only [hNle, hC6]
  -- the honest `𝒢₁` condition, at `C_a = C/2`
  have hG1 : assemblyConst d * (1 + 2 * A) * M.gamma
      ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by
    have h6 := six_assemblyConst_le_proportionConst d
    refine couplingG1_of_anchor (K := assemblyConst d) (Ca := proportionConst d / 2)
      hA0' hcs0 hcs32 hs0 hs12 hep0 hg0 (by linarith only [h6]) ?_ ?_
    · have hfac : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ ^ (2 : ℕ) *
          (s⁻¹ ^ (6 : ℕ) * (ep⁻¹ ^ (2 : ℕ) * M.gamma)) := by positivity
      have hstep := mul_le_mul_of_nonneg_right
        (show proportionConst d / 2 ≤ proportionConst d by linarith only [hC0]) hfac
      calc proportionConst d / 2 * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) *
            ep⁻¹ ^ (2 : ℕ) * M.gamma
          = proportionConst d / 2 * ((Disorder.cstar M)⁻¹ ^ (2 : ℕ) *
              (s⁻¹ ^ (6 : ℕ) * (ep⁻¹ ^ (2 : ℕ) * M.gamma))) := by ring
        _ ≤ proportionConst d * ((Disorder.cstar M)⁻¹ ^ (2 : ℕ) *
              (s⁻¹ ^ (6 : ℕ) * (ep⁻¹ ^ (2 : ℕ) * M.gamma))) := hstep
        _ = proportionConst d * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) *
              ep⁻¹ ^ (2 : ℕ) * M.gamma := by ring
        _ ≤ theta := hlevel
    · refine le_of_eq ?_
      rw [hAdef]
      field_simp
  -- the `𝒢₂` slot, discharged
  have hG2 := laneTailFrom_eventG2_of_anchor d M hs hs12 hep0 hep12 htheta0 htheta12
    hregCa hgam hlevel
  rw [← hAdef] at hG2
  have hres := (exists_proportionTail_of_honestG1 d).choose_spec.2 M s ep theta A hs0 hs12
    hep0 hep12 htheta0 htheta12 hregC0 hlevel4 hA0 hAceil hG1 m0 Mw hs hG2
  have hexp : -(A * ((Mw : ℝ) + 1))
      = -(Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta *
          ((Mw : ℝ) + 1)) / (proportionConst d * M.gamma) := by
    rw [hAdef]
    field_simp
  rw [← hexp]
  exact hres

end

end Algsuperdiff.Section4.Provider.Proportion
