/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.StepOneGoodEvent

/-!
# StepOneWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `D₁` as a geometric window sum of the collapsed kick family

ABK26, §4.2, Step 1 of `l.minimal.scale.sep`.  This module proves the identity that
makes `D₁` a Step-1 object at all, and the pointwise estimate that turns it into a
geometric window sum of the collapsed kick variable:

```
D₁(k) = s^{1/2} 1_{𝒢(k;s,1)} ∑_{p ≥ 0} 3^{−½sp} · annularKick_{k−p}   (the IDENTITY)
      ≤ s^{1/2} ∑_{p ≥ 0} 3^{−¼sp} · X_{k−p}                       (the ESTIMATE)
```

(the estimate is ABK26)

## The weight-bridging identity

The anchor's clause-(i) annular group carries the weights `3^{−s(m−n)}` indexed by
the pair `(j, n)` with `n ≤ j−1 ≤ m−1`; after the `√`-halving of
`DDecomposition.lean` the weights are `3^{−½s(k−n)}`.  `KickFamily`'s `annularKick_j` is the
inner-scale sum at the weight `3^{−½s(j−i)}`.  The two meet through the exact
factorisation

```
3^{−½s(k−n)} = 3^{−½s(k−j)} · 3^{−½s(j−n)}                (annularHalfSum_eq_tsum)
```

so that `annularHalfSum_k = ∑_{p ≥ 0} 3^{−½sp} annularKick_{k−p}` **as an identity of
`ℝ≥0∞`** — nothing is dropped, no convergence is used, and the halved exponent of the
outer sum is exactly the halved exponent of that weight.  There is NO weight
mismatch: `annularKick` sits at the §4.2 weight `3^{−½s·}` precisely because
the §4.1 lane's `3^{−¼s·}` weight is squared and §4.2's is not.

## Main definitions

* `outerScaleEquiv` — the `ℕ`-enumeration `p ↦ k − p` of the outer scales `j ≤ k`.
* `windowKickSum` — the geometric window sum `∑_p 3^{−¼sp} X_{k−p}`, in `ℝ`, at
  the collapse coefficient supplied by the caller.

## Main results

* `annularHalfSum_eq_tsum` — the weight-bridging identity.
* `summable_windowKick_of_mem_eventG2` — the window sum converges on the good event
  (the crude majorant `√√y ≤ 2 + y` suffices; no sharp estimate is needed here).
* `dOne_le_ofReal_windowKickSum` — the Step-1 pointwise estimate, at every sample:
  off the good event the left side is `0`, on it the collapse step applies.
* `dOne_ne_top` — `D₁(k)` is finite at every sample, so it may be read in `ℝ`.

## References

* ABK26, `l.minimal.scale.sep`, Step 1.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The unsquared lattice supremum equals the `Finset` maximum -/

/-- The unsquared companion of `Proportion.errorAnnSup_eq_ofReal_errorAnnMax`: the
`ℝ≥0∞` supremum over the lattice annulus S agrees with the `0`-floored `Finset`
maximum `kickAnnMax`. -/
theorem iSup_ofReal_annularErrorObservable_eq (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {j n : ℤ} (hn : n ≤ j) (omega : Cutoff.CutoffSample d) :
    (⨆ v : ↥(latticeAnnulusSet d n j (j - 1)),
        ENNReal.ofReal
          (annularErrorObservable M n s
            (Cutoff.translateCutoffSample (triadicLatticePoint n v.1) omega)))
      = ENNReal.ofReal (kickAnnMax M s j n omega) := by
  classical
  refine le_antisymm (iSup_le fun v => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    exact le_fmax (S := latticeAnnulusFinset d n j (j - 1))
      (f := fun w : Fin d → ℤ => kickAtom M n s (triadicLatticePoint n w) omega)
      ((mem_latticeAnnulusFinset_iff (d := d) hn).2 v.2)
  · rcases Finset.eq_empty_or_nonempty (latticeAnnulusFinset d n j (j - 1)) with hE | hE
    · rw [kickAnnMax, hE, fmax_empty, ENNReal.ofReal_zero]
      exact zero_le
    · obtain ⟨v, hv, hveq⟩ :=
        exists_mem_eq_fmax (f := fun w : Fin d → ℤ =>
          kickAtom M n s (triadicLatticePoint n w) omega) hE
          (fun w _ => kickAtom_nonneg M n s _ omega)
      rw [kickAnnMax, hveq]
      exact le_iSup_of_le ⟨v, (mem_latticeAnnulusFinset_iff (d := d) hn).1 hv⟩ le_rfl

/-! ## 2. The `ℕ`-enumeration of the outer scales -/

/-- The outer scales `j ≤ k`, enumerated by the offset `p = k − j`. -/
def outerScaleEquiv (k : ℤ) : ℕ ≃ {j : ℤ // j ≤ k} where
  toFun p := ⟨k - (p : ℤ), by omega⟩
  invFun j := (k - j.1).toNat
  left_inv p := by
    show (k - (k - (p : ℤ))).toNat = p
    omega
  right_inv j := by
    refine Subtype.ext ?_
    show k - (((k - j.1).toNat : ℕ) : ℤ) = j.1
    have h := j.2
    omega

/-! ## 3. The weight-bridging identity -/

/-- The halved weight at a nonnegative offset, in `weightThird` form. -/
theorem three_rpow_half_eq_weightThird (a : ℝ) {x : ℤ} (hx : 0 ≤ x) :
    Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * a * ((x : ℤ) : ℝ)) = weightThird (a / 2) x.toNat := by
  have hexp : -(1 / 2 : ℝ) * a * ((x : ℤ) : ℝ) = -(a / 2 * ((x : ℤ) : ℝ)) := by ring
  rw [hexp]
  exact three_rpow_eq_weightThird (a / 2) hx

/-- **The weight-bridging identity.**  The halved annular group of the
`D`-decomposition IS the geometric window sum of the inner-scale sums:

```
annularHalfSum_k = ∑_{p ≥ 0} 3^{−½sp} · annularKick_{k−p} .
```

An equality of `ℝ≥0∞`: the whole content is the exponent factorisation
`3^{−½s(k−n)} = 3^{−½s(k−j)}·3^{−½s(j−n)}`. -/
theorem annularHalfSum_eq_tsum (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    annularHalfSum M s k omega
      = ∑' p : ℕ, ENNReal.ofReal (weightThird ((s : ℝ) / 2) p) *
          annularKickE M s (k - (p : ℤ)) omega := by
  have hinner : ∀ j : ℤ, j ≤ k →
      (∑' n : {n : ℤ // n ≤ j - 1},
          ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
            ⨆ v : ↥(latticeAnnulusSet d n.1 j (j - 1)),
              ENNReal.ofReal
                (annularErrorObservable M n.1 s
                  (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega)))
        = ENNReal.ofReal (weightThird ((s : ℝ) / 2) (k - j).toNat) *
            annularKickE M s j omega := by
    intro j hj
    have hstep : ∀ n : {n : ℤ // n ≤ j - 1},
        ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
            (⨆ v : ↥(latticeAnnulusSet d n.1 j (j - 1)),
              ENNReal.ofReal
                (annularErrorObservable M n.1 s
                  (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega)))
          = ENNReal.ofReal (weightThird ((s : ℝ) / 2) (k - j).toNat) *
              ENNReal.ofReal
                (weightThird ((s : ℝ) / 2) (j - n.1).toNat * kickAnnMax M s j n.1 omega) := by
      intro n
      have hnj : n.1 ≤ j := by have := n.2; omega
      have hkn : (0 : ℤ) ≤ k - n.1 := by have := n.2; omega
      have hkj : (0 : ℤ) ≤ k - j := by omega
      have hjn : (0 : ℤ) ≤ j - n.1 := by have := n.2; omega
      have hsplit : Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))
          = weightThird ((s : ℝ) / 2) (k - j).toNat *
            weightThird ((s : ℝ) / 2) (j - n.1).toNat := by
        rw [← three_rpow_half_eq_weightThird (s : ℝ) hkj,
          ← three_rpow_half_eq_weightThird (s : ℝ) hjn]
        have hexp : -(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ)
            = -(1 / 2 : ℝ) * (s : ℝ) * ((k - j : ℤ) : ℝ) +
              -(1 / 2 : ℝ) * (s : ℝ) * ((j - n.1 : ℤ) : ℝ) := by
          push_cast
          ring
        rw [hexp]
        exact Real.rpow_add (by norm_num) _ _
      rw [hsplit, iSup_ofReal_annularErrorObservable_eq M s hnj omega,
        ENNReal.ofReal_mul (weightThird_pos _).le,
        ENNReal.ofReal_mul (weightThird_pos _).le, mul_assoc]
    rw [tsum_congr hstep, ENNReal.tsum_mul_left, annularKickE]
  rw [annularHalfSum, ← (outerScaleEquiv k).tsum_eq
    (fun j : {j : ℤ // j ≤ k} => ∑' n : {n : ℤ // n ≤ j.1 - 1},
      ENNReal.ofReal
          (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
        ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
          ENNReal.ofReal
            (annularErrorObservable M n.1 s
              (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega)))]
  refine tsum_congr fun p => ?_
  have hoff : (k - (k - (p : ℤ))).toNat = p := by omega
  have h := hinner (k - (p : ℤ)) (by omega)
  rw [hoff] at h
  exact h

/-! ## 4. The geometric window sum -/

/-- **The geometric window sum**: `∑_{p ≥ 0} 3^{−¼sp} X_{k−p}`, formed in `ℝ` at
the quarter rate.  The weight is written exactly as
`Probability.window_geom_head_rearrange` writes it. -/
def windowKickSum (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam K : ℝ) (k : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
    kickCollapsed M s lam K (k - (p : ℤ)) omega

theorem windowKickSum_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) {lam : ℝ}
    (hlam : 0 ≤ lam) (K : ℝ) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ windowKickSum M s lam K k omega := by
  refine tsum_nonneg fun p => ?_
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (kickCollapsed_nonneg M s hlam K _ omega)

/-- The window sum, in the `weightThird` rendering. -/
theorem windowKickSum_eq (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam K : ℝ) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    windowKickSum M s lam K k omega
      = ∑' p : ℕ, weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K (k - (p : ℤ)) omega := by
  refine tsum_congr fun p => ?_
  rw [weightThird_eq]

/-- `√√y ≤ 2 + y` — the crude majorant that makes the window sum summable without
any sharp estimate. -/
theorem sqrt_sqrt_le_two_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt (Real.sqrt y) ≤ 2 + y := by
  have h1 : Real.sqrt (Real.sqrt y) ≤ 1 + Real.sqrt y :=
    sqrt_le_one_add (Real.sqrt_nonneg y)
  have h2 : Real.sqrt y ≤ 1 + y := sqrt_le_one_add hy
  linarith only [h1, h2]

theorem summable_weightThird {a : ℝ} (ha : 0 < a) : Summable fun p : ℕ => weightThird a p := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Algsuperdiff.Probability.three_rpow_neg_lt_one ha
  exact summable_geometric_of_lt_one hr0 hr1

/-- **The window sum converges on the good event.**  The crude majorant
`X ≤ lam + 2 + K·annularKick` and the good-event bound reduce this to two geometric
series (rates `¼s` and `⅛s`). -/
theorem summable_windowKick_of_mem_eventG2 (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {k : ℤ} {lam K : ℝ} (hlam : 0 ≤ lam) (hK : 0 ≤ K) (hs1 : (s : ℝ) ≤ 1)
    {omega : Cutoff.CutoffSample d} (hmem : omega ∈ eventG2 M k s 1) :
    Summable fun p : ℕ =>
      weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K (k - (p : ℤ)) omega := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  set Gc : ℝ := 6 * K * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ with hGcdef
  have hGc0 : (0 : ℝ) ≤ Gc :=
    mul_nonneg (mul_nonneg (by norm_num) hK) (inv_pos.2 (pow_pos hsq0 3)).le
  have hmaj : Summable fun p : ℕ =>
      (lam + 2) * weightThird ((s : ℝ) / 4) p + Gc * weightThird ((s : ℝ) / 8) p :=
    ((summable_weightThird (by linarith only [hs0] : (0 : ℝ) < (s : ℝ) / 4)).mul_left
      (lam + 2)).add
      ((summable_weightThird (by linarith only [hs0] : (0 : ℝ) < (s : ℝ) / 8)).mul_left Gc)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
  · exact mul_nonneg (weightThird_pos p).le (kickCollapsed_nonneg M s hlam K _ omega)
  · -- the termwise majorant
    have hoff : (k - (k - (p : ℤ))).toNat = p := by omega
    have hB := annularKick_le_of_mem_eventG2 M s (by omega : k - (p : ℤ) ≤ k) hs1 hmem
    rw [hoff] at hB
    have hhigh0 : 0 ≤ kickLegHigh M s lam (k - (p : ℤ)) omega :=
      kickLegHigh_nonneg M s lam _ omega
    have hhighle : kickLegHigh M s lam (k - (p : ℤ)) omega
        ≤ annularKick M s (k - (p : ℤ)) omega := by
      have h := le_min (annularKick_nonneg M s (k - (p : ℤ)) omega) hlam
      rw [kickLegHigh]
      linarith only [h]
    have hroot : Real.sqrt (Real.sqrt (K * kickLegHigh M s lam (k - (p : ℤ)) omega))
        ≤ 2 + K * annularKick M s (k - (p : ℤ)) omega := by
      refine (sqrt_sqrt_le_two_add (mul_nonneg hK hhigh0)).trans ?_
      have h := mul_le_mul_of_nonneg_left hhighle hK
      linarith only [h]
    have hX : kickCollapsed M s lam K (k - (p : ℤ)) omega
        ≤ lam + 2 + K * (6 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ *
          (weightThird ((s : ℝ) / 8) p)⁻¹) := by
      have hlowle : kickLegLow M s lam (k - (p : ℤ)) omega ≤ lam :=
        kickLegLow_le M s lam _ omega
      have hKB := mul_le_mul_of_nonneg_left hB hK
      rw [kickCollapsed]
      linarith only [hlowle, hroot, hKB]
    have hwq : weightThird ((s : ℝ) / 4) p * (weightThird ((s : ℝ) / 8) p)⁻¹
        = weightThird ((s : ℝ) / 8) p := by
      have h : (s : ℝ) / 4 = 2 * ((s : ℝ) / 8) := by ring
      rw [h, ← weightThird_sq, pow_two, mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (weightThird_pos (sprime := (s : ℝ) / 8) p)), mul_one]
    calc weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K (k - (p : ℤ)) omega
        ≤ weightThird ((s : ℝ) / 4) p *
            (lam + 2 + K * (6 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ *
              (weightThird ((s : ℝ) / 8) p)⁻¹)) :=
          mul_le_mul_of_nonneg_left hX (weightThird_pos p).le
      _ = (lam + 2) * weightThird ((s : ℝ) / 4) p +
            Gc * (weightThird ((s : ℝ) / 4) p * (weightThird ((s : ℝ) / 8) p)⁻¹) := by
          rw [hGcdef]; ring
      _ = (lam + 2) * weightThird ((s : ℝ) / 4) p + Gc * weightThird ((s : ℝ) / 8) p := by
          rw [hwq]

/-! ## 5. The Step-1 pointwise estimate -/

/-- **The Step-1 pointwise estimate, at every sample.**

```
D₁(k) ≤ s^{1/2} ∑_{p ≥ 0} 3^{−¼sp} X_{k−p} .
```

Off the good event the left side is `0` and there is nothing to prove; on it the
identity `annularHalfSum_eq_tsum` reduces the claim to the collapse step
`weighted_annularKick_le_kickCollapsed`, termwise in `p`. -/
theorem dOne_le_ofReal_windowKickSum (M : ABKModel d) (s : {s : ℝ // 0 < s}) (Ccg : ℝ)
    {k : ℤ} {lam K : ℝ} (hlam : 0 ≤ lam) (hs1 : (s : ℝ) ≤ 1)
    (hK : 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ ≤ K) (omega : Cutoff.CutoffSample d) :
    dOne M Ccg s k omega
      ≤ ENNReal.ofReal (Real.sqrt (s : ℝ) * windowKickSum M s lam K k omega) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  have hK0 : (0 : ℝ) ≤ K :=
    le_trans (mul_nonneg (by norm_num) (inv_pos.2 (pow_pos hsq0 9)).le) hK
  by_cases hmem : omega ∈ goodEventBase M Ccg k s 1
  · have hg2 : omega ∈ eventG2 M k s 1 := goodEventBase_subset_eventG2 M Ccg k s 1 hmem
    have hsum := summable_windowKick_of_mem_eventG2 M s hlam hK0 hs1 hg2
    -- the termwise collapse, in `ℝ≥0∞`
    have hterm : ∀ p : ℕ,
        ENNReal.ofReal (weightThird ((s : ℝ) / 2) p) * annularKickE M s (k - (p : ℤ)) omega
          ≤ ENNReal.ofReal
              (weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K (k - (p : ℤ)) omega) := by
      intro p
      have hoff : (k - (k - (p : ℤ))).toNat = p := by omega
      have hfin := annularKickE_le_of_mem_eventG2 M s (by omega : k - (p : ℤ) ≤ k) hs1 hg2
      have hne : annularKickE M s (k - (p : ℤ)) omega ≠ (⊤ : ℝ≥0∞) :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
      have hEq : annularKickE M s (k - (p : ℤ)) omega
          = ENNReal.ofReal (annularKick M s (k - (p : ℤ)) omega) :=
        (ENNReal.ofReal_toReal hne).symm
      have hcol := weighted_annularKick_le_kickCollapsed M s hlam
        (by omega : k - (p : ℤ) ≤ k) hs1 hK hg2
      rw [hoff] at hcol
      rw [hEq, ← ENNReal.ofReal_mul (weightThird_pos p).le]
      exact ENNReal.ofReal_le_ofReal hcol
    have hchain : annularHalfSum M s k omega
        ≤ ENNReal.ofReal (windowKickSum M s lam K k omega) := by
      rw [annularHalfSum_eq_tsum, windowKickSum_eq]
      refine le_trans (ENNReal.tsum_le_tsum hterm) (le_of_eq ?_)
      refine (ENNReal.ofReal_tsum_of_nonneg (fun p => ?_) hsum).symm
      exact mul_nonneg (weightThird_pos p).le (kickCollapsed_nonneg M s hlam K _ omega)
    rw [dOne, Set.indicator_of_mem hmem, ENNReal.ofReal_mul hsq0.le]
    exact mul_le_mul_right hchain _
  · rw [dOne, Set.indicator_of_notMem hmem]
    exact zero_le

/-- **`D₁(k)` is finite at every sample**, so it may be read in `ℝ` without a
junk-value hazard.  This is what lets the final Cesàro assembly move between `ℝ≥0∞`
and `ℝ`. -/
theorem dOne_ne_top (M : ABKModel d) (s : {s : ℝ // 0 < s}) (Ccg : ℝ) {k : ℤ}
    (hs1 : (s : ℝ) ≤ 1) (omega : Cutoff.CutoffSample d) :
    dOne M Ccg s k omega ≠ (⊤ : ℝ≥0∞) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (dOne_le_ofReal_windowKickSum M s Ccg (lam := 0) (K := 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹)
      le_rfl hs1 le_rfl omega)

/-- The real reading of the Step-1 pointwise estimate. -/
theorem dOne_toReal_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) (Ccg : ℝ) {k : ℤ}
    {lam K : ℝ} (hlam : 0 ≤ lam) (hs1 : (s : ℝ) ≤ 1)
    (hK : 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ ≤ K) (omega : Cutoff.CutoffSample d) :
    (dOne M Ccg s k omega).toReal
      ≤ Real.sqrt (s : ℝ) * windowKickSum M s lam K k omega := by
  refine ENNReal.toReal_le_of_le_ofReal ?_ (dOne_le_ofReal_windowKickSum M s Ccg hlam hs1 hK omega)
  exact mul_nonneg (Real.sqrt_nonneg _) (windowKickSum_nonneg M s hlam K k omega)

/-! ## 6. Reading the window sum at the kick family's OWN coefficient

The collapse step needs the coefficient `K' ≥ 216 s^{−9/2}`, while `K1`'s `Γ₂` tail
and first moment are supplied at `K1`'s own `C s^{−9/2}`.  The two are reconciled by
the fourth root of the ratio — a dimensional constant — so that the Cesàro engine
below is fed the family `K1` actually estimates. -/

/-- The window sum is monotone in the collapse coefficient, up to the fourth root of
the ratio (good-event version: both sums converge there). -/
theorem windowKickSum_le_mul_of_coeff_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) {k : ℤ}
    {lam K K' : ℝ} (hlam : 0 ≤ lam) (hK : 0 < K) (hKK : K ≤ K') (hs1 : (s : ℝ) ≤ 1)
    {omega : Cutoff.CutoffSample d} (hmem : omega ∈ eventG2 M k s 1) :
    windowKickSum M s lam K' k omega
      ≤ Real.sqrt (Real.sqrt (K' / K)) * windowKickSum M s lam K k omega := by
  have hsumK := summable_windowKick_of_mem_eventG2 M s hlam hK.le hs1 hmem
  have hsumK' := summable_windowKick_of_mem_eventG2 M s hlam
    (le_trans hK.le hKK) hs1 hmem
  set rho : ℝ := Real.sqrt (Real.sqrt (K' / K)) with hrhodef
  have hrho0 : (0 : ℝ) ≤ rho := Real.sqrt_nonneg _
  have hterm : ∀ p : ℕ,
      weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K' (k - (p : ℤ)) omega
        ≤ rho * (weightThird ((s : ℝ) / 4) p *
            kickCollapsed M s lam K (k - (p : ℤ)) omega) := by
    intro p
    have h := kickCollapsed_le_mul_of_coeff_le M s hlam hK hKK (k - (p : ℤ)) omega
    rw [← hrhodef] at h
    calc weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K' (k - (p : ℤ)) omega
        ≤ weightThird ((s : ℝ) / 4) p *
            (rho * kickCollapsed M s lam K (k - (p : ℤ)) omega) :=
          mul_le_mul_of_nonneg_left h (weightThird_pos p).le
      _ = rho * (weightThird ((s : ℝ) / 4) p *
            kickCollapsed M s lam K (k - (p : ℤ)) omega) := by ring
  rw [windowKickSum_eq, windowKickSum_eq]
  calc ∑' p : ℕ, weightThird ((s : ℝ) / 4) p * kickCollapsed M s lam K' (k - (p : ℤ)) omega
      ≤ ∑' p : ℕ, rho * (weightThird ((s : ℝ) / 4) p *
          kickCollapsed M s lam K (k - (p : ℤ)) omega) :=
        Summable.tsum_le_tsum hterm hsumK' (hsumK.mul_left rho)
    _ = rho * ∑' p : ℕ, weightThird ((s : ℝ) / 4) p *
          kickCollapsed M s lam K (k - (p : ℤ)) omega := tsum_mul_left

/-- **The Step-1 pointwise estimate at the kick family's own coefficient**, at every
sample: `D₁(k) ≤ s^{1/2} ρ ∑_p 3^{−¼sp} X_{k−p}` with `X` the collapsed variable at
the coefficient `K` and `ρ = (K'/K)^{1/4}` for any admissible `K' ≥ 216 s^{−9/2}`. -/
theorem dOne_toReal_le_scaled (M : ABKModel d) (s : {s : ℝ // 0 < s}) (Ccg : ℝ) {k : ℤ}
    {lam K K' : ℝ} (hlam : 0 ≤ lam) (hs1 : (s : ℝ) ≤ 1) (hK : 0 < K) (hKK : K ≤ K')
    (hK' : 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ ≤ K') (omega : Cutoff.CutoffSample d) :
    (dOne M Ccg s k omega).toReal
      ≤ Real.sqrt (s : ℝ) *
        (Real.sqrt (Real.sqrt (K' / K)) * windowKickSum M s lam K k omega) := by
  have hrho0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (K' / K)) := Real.sqrt_nonneg _
  by_cases hmem : omega ∈ goodEventBase M Ccg k s 1
  · have hg2 : omega ∈ eventG2 M k s 1 := goodEventBase_subset_eventG2 M Ccg k s 1 hmem
    refine (dOne_toReal_le M s Ccg hlam hs1 hK' omega).trans ?_
    exact mul_le_mul_of_nonneg_left
      (windowKickSum_le_mul_of_coeff_le M s hlam hK hKK hs1 hg2) (Real.sqrt_nonneg _)
  · rw [dOne, Set.indicator_of_notMem hmem, ENNReal.toReal_zero]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg hrho0 (windowKickSum_nonneg M s hlam K k omega))

end

end Algsuperdiff.Section4.Provider.MinimalScale
