/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShiftedG0Lane
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShiftedG1Lane
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LaneInterface

/-!
# ShiftedInterface

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three-lane interface of the `§4.1` proportion assembly, at an arbitrary base

ABK26, §4.1, `p.independence.between.scales`.  `LaneInterface` is the base-`0`
interface: each lane delivers a tail for the window `{0,…,n}`.  The `§4.1`
proportion display is quantified over **every** base scale `m₀ : ℤ` and reads
its window as `Finset.range (Mw+1)` shifted by `m₀`.  This module is that
interface, re-based:

* `LaneTailFrom M Ev θ c₁` — one lane's endpoint at **every** base: for every
  `m₀ : ℤ` and every window length `n`, the density of scales `k ∈ {m₀,…,m₀+n}`
  at which `Ev` fails exceeds `θ` with probability at most `exp(−c₁n)/3`.
* `measure_scaleProp_compl_goodEventBase_le_shift` /
  `measure_scaleProp_goodEventBase_le_shift` — the three-fold union bound, at
  every base.
* `exists_ratioTail_goodEventBase_shift` — the composition: the two proved lanes
  (`𝒢₀` from `ShiftedG0Lane`, `𝒢₁` from `ShiftedG1Lane`) plus the `𝒢₂` lane as a
  named `LaneTailFrom` slot of the identical shape.

## References

* ABK26, `p.independence.between.scales`; `d.good.event.for.lambda`,
  (`e.lambda.good.events`); `p.concentration.for.scales`, (the `m₀`
  reduction).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The lane endpoint at every base -/

/-- **One lane's ratio-tail endpoint at every base scale.**  `LaneTailFrom M Ev θ c₁`
says that for every base `m₀ : ℤ` and every window `{m₀,…,m₀+n}` the density of
scales at which `Ev` fails exceeds `θ` with probability at most `exp(−c₁n)/3`.

The base-`0` instance is `LaneTail M Ev θ c₁`; the prefactor `1/3` is the
union-bound share of the three-lane split. -/
def LaneTailFrom (M : ABKModel d) (Ev : ℤ → Set (Cutoff.CutoffSample d))
    (theta c1 : ℝ) : Prop :=
  ∀ m0 : ℤ, LaneTail M (fun k => Ev (m0 + k)) theta c1

/-- A based lane endpoint transfers to every larger level. -/
theorem LaneTailFrom.mono_level {M : ABKModel d} {Ev : ℤ → Set (Cutoff.CutoffSample d)}
    {theta theta' c1 : ℝ} (h : theta ≤ theta') (H : LaneTailFrom M Ev theta c1) :
    LaneTailFrom M Ev theta' c1 := fun m0 => (H m0).mono_level h

/-! ## 2. The three-fold union bound, at every base -/

/-- **The three lanes recombine into the good event, at every base.**  With the
three lane endpoints at level `θ/3`, the density of scales `k ∈ {m₀,…,m₀+n}` at
which the frozen good event's untranslated body `goodEventBase` fails exceeds `θ`
with probability at most `exp(−c₁n)`. -/
theorem measure_scaleProp_compl_goodEventBase_le_shift (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep theta c1 : ℝ)
    (h0 : LaneTailFrom M (fun k => Support.eventG0 M Ccg k) (theta / 3) c1)
    (h1 : LaneTailFrom M
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (theta / 3) c1)
    (h2 : LaneTailFrom M (fun k => Support.eventG2 M k s ep) (theta / 3) c1)
    (m0 : ℤ) (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta <
          scaleProp (fun k => (Support.goodEventBase M Ccg (m0 + k) s ep)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
  have hbase : ∀ k : ℤ, Support.goodEventBase M Ccg (m0 + k) s ep =
      Support.eventG0 M Ccg (m0 + k) ∩
        Support.eventG1 M (m0 + k) (s : ℝ)
          ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ∩
        Support.eventG2 M (m0 + k) s ep := fun _ => rfl
  have hunion := measure_bad_density_union (Cutoff.cutoffSampleLaw M).toMeasure
    (fun k => Support.eventG0 M Ccg (m0 + k))
    (fun k => Support.eventG1 M (m0 + k) (s : ℝ)
      ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (fun k => Support.eventG2 M (m0 + k) s ep) n theta
    (Real.exp (-c1 * (n : ℝ)) / 3) (Real.exp (-c1 * (n : ℝ)) / 3)
    (Real.exp (-c1 * (n : ℝ)) / 3) (h0 m0 n) (h1 m0 n) (h2 m0 n)
  have hnn : (0 : ℝ) ≤ Real.exp (-c1 * (n : ℝ)) / 3 := by positivity
  have hsum : ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)
      = ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
    rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (by linarith only [hnn]) hnn]
    congr 1
    ring
  rw [hsum] at hunion
  simp only [hbase]
  exact hunion

/-- **The good-proportion form of the three-lane union bound, at every base.**
With the three lane endpoints at level `θ/4`, the frozen display's own clause
`avsum 𝟙{𝒢} ≤ 1 − θ` over the window `{m₀,…,m₀+n}` has probability at most
`exp(−c₁n)`.  The conversion from the bad form the lanes deliver costs one strict
inequality, which is why the lanes are run at `θ/4` instead of `θ/3`. -/
theorem measure_scaleProp_goodEventBase_le_shift (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep theta c1 : ℝ) (htheta0 : 0 < theta)
    (h0 : LaneTailFrom M (fun k => Support.eventG0 M Ccg k) (theta / 4) c1)
    (h1 : LaneTailFrom M
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (theta / 4) c1)
    (h2 : LaneTailFrom M (fun k => Support.eventG2 M k s ep) (theta / 4) c1)
    (m0 : ℤ) (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | scaleProp (fun k => Support.goodEventBase M Ccg (m0 + k) s ep) n omega
          ≤ 1 - theta}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
  have hbase : ∀ k : ℤ, Support.goodEventBase M Ccg (m0 + k) s ep =
      Support.eventG0 M Ccg (m0 + k) ∩
        Support.eventG1 M (m0 + k) (s : ℝ)
          ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ∩
        Support.eventG2 M (m0 + k) s ep := fun _ => rfl
  have hsub : {omega |
        scaleProp (fun k => Support.goodEventBase M Ccg (m0 + k) s ep) n omega ≤ 1 - theta}
      ⊆ {omega | theta / 4 <
            scaleProp (fun k => (Support.eventG0 M Ccg (m0 + k))ᶜ) n omega}
        ∪ {omega | theta / 4 < scaleProp (fun k =>
            (Support.eventG1 M (m0 + k) (s : ℝ)
              ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) *
                (Real.sqrt M.gamma)⁻¹))ᶜ) n omega}
        ∪ {omega | theta / 4 <
            scaleProp (fun k => (Support.eventG2 M (m0 + k) s ep)ᶜ) n omega} := by
    intro omega homega
    simp only [Set.mem_ofPred_eq] at homega
    have hcompl := scaleProp_add_scaleProp_compl
      (fun k => Support.goodEventBase M Ccg (m0 + k) s ep) n omega
    have hbad : theta ≤ scaleProp
        (fun k => (Support.goodEventBase M Ccg (m0 + k) s ep)ᶜ) n omega := by
      linarith only [hcompl, homega]
    have hsplit := scaleProp_subadd (fun k => Support.eventG0 M Ccg (m0 + k))
      (fun k => Support.eventG1 M (m0 + k) (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (fun k => Support.eventG2 M (m0 + k) s ep) n omega
    simp only [← hbase] at hsplit
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
    linarith only [htheta0, hbad, hsplit, hc.1.1, hc.1.2, hc.2]
  have hnn : (0 : ℝ) ≤ Real.exp (-c1 * (n : ℝ)) / 3 := by positivity
  have hsum : ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)
      = ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
    rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (by linarith only [hnn]) hnn]
    congr 1
    ring
  calc (Cutoff.cutoffSampleLaw M).toMeasure
        {omega |
          scaleProp (fun k => Support.goodEventBase M Ccg (m0 + k) s ep) n omega ≤ 1 - theta}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
          ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
          ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) :=
        add_le_add (add_le_add (h0 m0 n) (h1 m0 n)) (h2 m0 n)
    _ = ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := hsum

/-! ## 3. The two proved lane certificates, at every base -/

/-- **The `𝒢₀` lane in `LaneTailFrom` shape**, with one dependence range `r(d)`
and one constant `C(d)` chosen before the level, the rate, the model and the
base.  This is `ShiftedG0Lane.exists_ratioTail_eventG0_uniform_shift` read
through `LaneTailFrom`. -/
theorem exists_laneTailFrom_eventG0 (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 6 ≤ C ∧
      ∀ (M : ABKModel d) (theta c1 : ℝ),
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        0 < theta → theta * ((r : ℝ) + 1) < 1 →
        C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) →
        0 ≤ c1 → c1 * M.gamma ≤ 1 →
        LaneTailFrom M (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k)
          theta c1 := by
  obtain ⟨r, hr1, C, hC6, hall⟩ := exists_ratioTail_eventG0_uniform_shift d
  exact ⟨r, hr1, C, hC6, fun M theta c1 hreg htheta0 hthetar hcouple hc10 hc1g m0 n =>
    hall M hreg theta htheta0 hthetar hcouple c1 hc10 hc1g m0 n⟩

/-- **The `𝒢₁` lane in `LaneTailFrom` shape**, at the substituted threshold
`s ε √c⋆ (√γ)⁻¹` of `e.lambda.good.events` and at any dependence range `r ≥ 1`.
This is `ShiftedG1Lane.ratioTail_eventG1_shellThreshold_shift` read through
`LaneTailFrom`. -/
theorem laneTailFrom_eventG1_shellThreshold (M : ABKModel d) {s ep theta c1 : ℝ}
    {r : ℕ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hep0 : 0 < ep) (hr1 : 1 ≤ r)
    (htheta0 : 0 < theta) (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hcond : g1ThresholdConst d r * (1 + c1) * M.gamma
        ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) :
    LaneTailFrom M
      (fun k => Support.eventG1 M k s
        (s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)) theta c1 :=
  fun m0 n =>
    ratioTail_eventG1_shellThreshold_shift M hs0 hs1 hep0 hr1 htheta0 hthetar hc1
      hcond m0 n

/-! ## 4. The three-lane endpoint at every base, with the `𝒢₂` slot -/

/-- **The `§4.1` proportion premise at every base, from two proved lanes and one
named slot.**

One dependence range `r(d)` and one constant `C(d)`, both fixed before every
parameter *and before the base*.  The `𝒢₀` and `𝒢₁` lanes are proved; the `𝒢₂`
lane enters as the named hypothesis `hG2`, in the identical `LaneTailFrom` shape.
Both output forms are delivered at every base `m₀ : ℤ`: the bad-density form the
union bound produces, and the good-proportion form `avsum 𝟙{𝒢} ≤ 1 − θ` in which
the printed display is stated.

Every window `n` is covered, including the short windows `n < r`.  The rate
`c₁` is the caller's, up to the `𝒢₀` lane's ceiling `c₁γ ≤ 1`. -/
theorem exists_ratioTail_goodEventBase_shift (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 6 ≤ C ∧
      ∀ (M : ABKModel d) (s : {s : ℝ // 0 < s}) (ep theta c1 : ℝ),
        (s : ℝ) ≤ 1 → 0 < ep → 0 < theta → theta * ((r : ℝ) + 1) < 1 →
        0 ≤ c1 → c1 * M.gamma ≤ 1 →
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        C ^ (10 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) →
        C * (1 + c1) * M.gamma
            ≤ theta * Disorder.cstar M * (s : ℝ) ^ (6 : ℕ) * ep ^ (2 : ℕ) →
        LaneTailFrom M (fun k => Support.eventG2 M k s ep) (theta / 4) c1 →
        (∀ (m0 : ℤ) (n : ℕ),
            (Cutoff.cutoffSampleLaw M).toMeasure
                {omega | theta < scaleProp
                  (fun k =>
                    (Support.goodEventBase M (Support.cgEllipLowerConstant d)
                      (m0 + k) s ep)ᶜ)
                  n omega}
              ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)))) ∧
          ∀ (m0 : ℤ) (n : ℕ),
            (Cutoff.cutoffSampleLaw M).toMeasure
                {omega | scaleProp
                  (fun k =>
                    Support.goodEventBase M (Support.cgEllipLowerConstant d)
                      (m0 + k) s ep)
                  n omega ≤ 1 - theta}
              ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
  obtain ⟨r, hr1, C0, hC06, hG0⟩ := exists_laneTailFrom_eventG0 d
  refine ⟨r, hr1, max C0 (max 6 (4 * g1ThresholdConst d r)), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  intro M s ep theta c1 hs1 hep0 htheta0 hthetar hc10 hc1g hreg hcoup hcond hG2
  have hC0le : C0 ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) := le_max_left _ _
  have hC6 : (6 : ℝ) ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hg1le : 4 * g1ThresholdConst d r ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0pos : (0 : ℝ) < C0 := by linarith only [hC06]
  have hCpos : (0 : ℝ) < max C0 (max 6 (4 * g1ThresholdConst d r)) := by
    linarith only [hC6]
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hth4 : (0 : ℝ) < theta / 4 := by linarith only [htheta0]
  have hthetar4 : theta / 4 * ((r : ℝ) + 1) < 1 := by
    have hrw : theta / 4 * ((r : ℝ) + 1) = theta * ((r : ℝ) + 1) / 4 := by ring
    rw [hrw]
    linarith only [hthetar]
  -- the `𝒢₀` lane at level `θ/4`, at every base
  have hlane0 : LaneTailFrom M
      (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k) (theta / 4) c1 := by
    refine hG0 M (theta / 4) c1 ?_ hth4 hthetar4 ?_ hc10 hc1g
    · refine le_trans hreg (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hC0pos hC0le) 10
    · have h9 : C0 ^ (9 : ℕ) ≤ (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (9 : ℕ) :=
        pow_le_pow_left₀ hC0pos.le hC0le 9
      have h10 : 4 * C0 ^ (9 : ℕ)
          ≤ (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (10 : ℕ) := by
        calc 4 * C0 ^ (9 : ℕ)
            ≤ 4 * (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (9 : ℕ) := by
              linarith only [h9]
          _ ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) *
                (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (9 : ℕ) :=
              mul_le_mul_of_nonneg_right (by linarith only [hC6]) (pow_nonneg hCpos.le 9)
          _ = (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (10 : ℕ) := by ring
      have hstep := mul_le_mul_of_nonneg_right h10 (pow_nonneg hg0.le 2)
      linarith only [hstep, hcoup]
  -- the `𝒢₁` lane at level `θ/4`, at every base
  have hlane1 : LaneTailFrom M
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (theta / 4) c1 := by
    refine laneTailFrom_eventG1_shellThreshold M s.2 hs1 hep0 hr1 hth4 hthetar4 hc10 ?_
    have hprod : (0 : ℝ) ≤ (1 + c1) * M.gamma := by positivity
    have h4 := mul_le_mul_of_nonneg_right hg1le hprod
    linarith only [h4, hcond]
  refine ⟨fun m0 n => ?_, fun m0 n => ?_⟩
  · exact measure_scaleProp_compl_goodEventBase_le_shift M
      (Support.cgEllipLowerConstant d) s ep theta c1
      (hlane0.mono_level (by linarith only [htheta0]))
      (hlane1.mono_level (by linarith only [htheta0]))
      (hG2.mono_level (by linarith only [htheta0])) m0 n
  · exact measure_scaleProp_goodEventBase_le_shift M (Support.cgEllipLowerConstant d)
      s ep theta c1 htheta0 hlane0 hlane1 hG2 m0 n

end

end Algsuperdiff.Section4.Provider.Proportion
