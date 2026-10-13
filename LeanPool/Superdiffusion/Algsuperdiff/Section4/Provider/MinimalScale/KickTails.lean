/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2AtomTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2CubeBound

/-!
# KickTails

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-1 kick tails:, unconditionally

ABK26, §4.2, Step 1 of `l.minimal.scale.sep`.  The manuscript's Step-1 claim is

```
X_j^{(1)} ≤ 𝒪_{Γ₂}(C c⋆^{−1}s^{−5/2}√γ) ,      X_j^{(2)} ≤ 𝒪_{Γ_{1/2}}(C e^{−C^{−1}c⋆³/γ}) ,
```

uniformly in `j`, on the regime and window.  This module proves it, from the
four citations the manuscript lists (`e.induction.E.bounds`,
`e.Gamma.sigma.triangle`, `e.maxy.bound` and the good-event bound) and nothing
else.

## The chain, and where each citation enters

```
per-cube display at the inner scale i   exists_isTwoTermBigOWith_…  (e.induction.E.bounds)
  → lattice-annulus maximum             isTwoTermBigOWith_kickAnnMax  (e.maxy.bound)
  → weighted inner-scale sum            isTwoTermBigOWith_annularKick (e.Gamma.sigma.triangle)
  → closed forms in s                   kickAmpTwo_le, kickAmpHalf_le (the two closures)
  → the two legs                        KickSplit                     (the clamp)
  → the printed amplitudes              exists_kickFamily_tails       (the absorptions)
```

The §4.1 `𝒢₂` chain (`Proportion.isTwoTermBigOWith_errorAnnMax`,
`isTwoTermBigOWith_Xcal`) is the template and its two devices — the union bound
`Proportion.isBigOWith_fmax` at the machine-computed `annulusPenalty` and the
two-term countable triangle inequality `Proportion.isTwoTermBigOWith_wsum` —
are consumed by name.  The difference is that §4.2 **does not square**: the
Orlicz indices stay `(Γ₂, Γ_{1/2})` rather than moving to `(Γ₁, Γ_{1/4})`, the
weight is `3^{−½s·}` rather than `3^{−¼s·}`, and the union-bound penalties are
therefore `√(j−i+1)` and `(j−i+1)²` rather than `(j−i+1)` and `(j−i+1)⁴`.

## The `s`-bookkeeping, sharply

The `Γ₂` closure is the sharp one: `∑_r √(r+1)3^{−½sr} = O(s^{−3/2})`, which
against the anchor's own `s^{−1}` gives exactly the printed `s^{−5/2}`.  The
crude `√(r+1) ≤ r+1` would give `s^{−2}` and hence `s^{−3}`, and the printed
exponent would be missed by half a power.  On the `Γ_{1/2}` lane the `(j−i+1)²`
penalty contributes `s^{−3}`, which the printed amplitude does not carry: it is
absorbed into the exponential explicitly by `KickArith.inv_cube_mul_exp_le` on
the window `s ≥ 8γ`, at the cost of halving the exponent — i.e. of doubling the
dimensional constant, which is what the manuscript's "for `C` chosen
sufficiently large" buys.

## The regime and the window are the lemma's own hypotheses

states `l.minimal.scale.sep` under `γ ≤ C^{−10}c⋆^{10}` and `s ∈ [8γ, 1/2]`,
and the endpoint below carries **exactly** those two premises.  Both are used:
the regime twice, in the two absorptions of `KickArith` (which need a lower
bound on `c⋆³γ^{−1}`, without which the absorbed prefactor carries `c⋆^{−9}`),
and the upper window endpoint `s ≤ 1/2` in the two geometric closures
(`geomTailConst (½s) ≤ 4/s` needs `½s ≤ ½`).  The upper endpoint `1/4` was not
needed.

Inside the proof, prints the *weaker* regime `γ ≤ C^{−1}c⋆⁵`, which does not
imply the lemma's own hypothesis and which nothing here uses.  The proved
producer of the per-cube display,
`Proportion.exists_isTwoTermBigOWith_annularErrorObservable`, also carries `γ ≤
C^{−10}c⋆^{10}`.

## References

* ABK26, `l.minimal.scale.sep`, (the lemma's own hypotheses), Step 1.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion

noncomputable section

variable {d : ℕ}

/-! ## 1. The dimensional base of the union-bound penalty -/

/-- `1 + 2d log 3`, the dimensional base of the lattice-annulus penalty. -/
def penaltyBase (d : ℕ) : ℝ := 1 + 2 * (d : ℝ) * Real.log 3

theorem one_le_penaltyBase (d : ℕ) : 1 ≤ penaltyBase d := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 := by positivity
  rw [penaltyBase]
  linarith only [h]

theorem penaltyBase_pos (d : ℕ) : 0 < penaltyBase d :=
  lt_of_lt_of_le zero_lt_one (one_le_penaltyBase d)

/-- The penalty base at offset `p+1` is at most `penaltyBase d · (p+1)`: the one
comparison behind both closed forms. -/
private theorem annulusPenalty_base_le (d : ℕ) (p : ℕ) :
    1 + (d : ℝ) * ((((p + 1 : ℕ)) : ℝ) + 1) * Real.log 3
      ≤ penaltyBase d * ((p : ℝ) + 1) := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hcast : ((((p + 1 : ℕ)) : ℝ) + 1) = (p : ℝ) + 2 := by push_cast; ring
  have hprod : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 * (p : ℝ) := by positivity
  rw [hcast, penaltyBase]
  linarith only [hprod, hp]

/-- `annulusPenalty d 2 p = √(1 + d(p+1) log 3)`: the `Γ₂` penalty is a square
root, because the exponent is `1/σ = 1/2`. -/
private theorem annulusPenalty_two_eq (d : ℕ) (p : ℕ) :
    annulusPenalty d 2 p = Real.sqrt (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) := by
  rw [annulusPenalty, Real.sqrt_eq_rpow]
  norm_num

/-- **The `Γ₂` penalty comparison** `√(1+d(p+2)log 3) ≤ √(penaltyBase d)·√(p+1)`. -/
theorem annulusPenalty_two_le (d : ℕ) (p : ℕ) :
    annulusPenalty d 2 (p + 1)
      ≤ Real.sqrt (penaltyBase d) * Real.sqrt ((p : ℝ) + 1) := by
  rw [annulusPenalty_two_eq, ← Real.sqrt_mul (penaltyBase_pos d).le]
  exact Real.sqrt_le_sqrt (annulusPenalty_base_le d p)

/-- **The `Γ_{1/2}` penalty comparison** `(1+d(p+2)log 3)² ≤ penaltyBase d²(p+1)²`. -/
theorem annulusPenalty_half_le (d : ℕ) (p : ℕ) :
    annulusPenalty d (1 / 2) (p + 1) ≤ penaltyBase d ^ 2 * ((p : ℝ) + 1) ^ 2 := by
  have hcast : ((((2 : ℕ)) : ℝ))⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [← hcast, annulusPenalty_natPow d (by norm_num) (p + 1), ← mul_pow]
  exact pow_le_pow_left₀ (annulusPenalty_base_nonneg d (p + 1))
    (annulusPenalty_base_le d p) 2

/-- The `Γ₂` penalty is below the `Γ₁` penalty: `1/σ` decreases in `σ` and the base
is at least `1`.  This is what makes the proved summability instance at `N = 1`
applicable on the `Γ₂` lane. -/
theorem annulusPenalty_two_le_one (d : ℕ) (p : ℕ) :
    annulusPenalty d 2 p ≤ annulusPenalty d 1 p := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : (1 : ℝ) ≤ 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by
    have h : (0 : ℝ) ≤ (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by positivity
    linarith only [h]
  rw [annulusPenalty, annulusPenalty]
  exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)

/-- The `§4.2` weight at offset `p+1` is below the `L3`-shaped weight at offset
`p`: the single step `3^{−½s(p+1)} ≤ 3^{−½sp}`. -/
private theorem weightThird_succ_le {sprime : ℝ} (hsprime : 0 ≤ sprime) (p : ℕ) :
    weightThird sprime (p + 1) ≤ (3 : ℝ) ^ (-(sprime * (p : ℝ))) := by
  rw [weightThird, pow_succ, ← Algsuperdiff.Probability.threePow_neg_natMul]
  have h1 : (3 : ℝ) ^ (-sprime) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hsprime])
  have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(sprime * (p : ℝ))) := Real.rpow_nonneg (by norm_num) _
  calc (3 : ℝ) ^ (-(sprime * (p : ℝ))) * (3 : ℝ) ^ (-sprime)
      ≤ (3 : ℝ) ^ (-(sprime * (p : ℝ))) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = (3 : ℝ) ^ (-(sprime * (p : ℝ))) := by ring

/-! ## 2. `e.maxy.bound`: the lattice-annulus maximum -/

/-- The lattice translation is stationarity
(`GoodEvents.measurePreserving_translateCutoffSample`), not a new estimate. -/
theorem isTwoTermBigOWith_kickAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {A1 A2 : ℝ} (j i : ℤ)
    (hcube : Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M i s) A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2)) (kickAnnMax M s j i)
      (annulusPenalty d 2 (j - i).toNat * A1)
      (annulusPenalty d (1 / 2) (j - i).toNat * A2) := by
  classical
  obtain ⟨Y, Z, -, -, hA1, hA2, -, hYm, hZm, hdom, hYt, hZt⟩ := hcube
  set law := (Cutoff.cutoffSampleLaw M).toMeasure with hlaw
  set U : Cutoff.CutoffSample d → ℝ := fun omega => max (Y omega) 0 with hUdef
  set V : Cutoff.CutoffSample d → ℝ := fun omega => max (Z omega) 0 with hVdef
  have hUm : Measurable U := hYm.max measurable_const
  have hVm : Measurable V := hZm.max measurable_const
  have hUt : IsBigOWith law (gammaSigma 2) U A1 := isBigOWith_max_zero hA1 hYt
  have hVt : IsBigOWith law (gammaSigma (1 / 2)) V A2 := isBigOWith_max_zero hA2 hZt
  have hpt : ∀ (z : Vec d) (omega : Cutoff.CutoffSample d),
      kickAtom M i s z omega ≤ U (Cutoff.translateCutoffSample z omega)
        + V (Cutoff.translateCutoffSample z omega) :=
    fun z omega =>
      le_trans (hdom (Cutoff.translateCutoffSample z omega))
        (add_le_add (le_max_left _ _) (le_max_left _ _))
  set Umax : Cutoff.CutoffSample d → ℝ := fun omega =>
    fmax (latticeAnnulusFinset d i j (j - 1))
      (fun v => U (Cutoff.translateCutoffSample (Support.triadicLatticePoint i v) omega))
    with hUmax
  set Vmax : Cutoff.CutoffSample d → ℝ := fun omega =>
    fmax (latticeAnnulusFinset d i j (j - 1))
      (fun v => V (Cutoff.translateCutoffSample (Support.triadicLatticePoint i v) omega))
    with hVmax
  have hUmaxm : Measurable Umax :=
    measurable_fmax _ fun v => hUm.comp (Cutoff.measurable_translateCutoffSample _)
  have hVmaxm : Measurable Vmax :=
    measurable_fmax _ fun v => hVm.comp (Cutoff.measurable_translateCutoffSample _)
  have hUmaxt : IsBigOWith law (gammaSigma 2) Umax
      (annulusPenalty d 2 (j - i).toNat * A1) :=
    isBigOWith_fmax _ (by norm_num) hA1.le
      (one_le_annulusPenalty d (by norm_num) _)
      (log_card_le_annulusPenalty_rpow_sub_one d (by norm_num) i j (j - 1))
      (fun v _ => isBigOWith_comp_measurePreserving
        (GoodEvents.measurePreserving_translateCutoffSample M _) hUm hUt)
  have hVmaxt : IsBigOWith law (gammaSigma (1 / 2)) Vmax
      (annulusPenalty d (1 / 2) (j - i).toNat * A2) :=
    isBigOWith_fmax _ (by norm_num) hA2.le
      (one_le_annulusPenalty d (by norm_num) _)
      (log_card_le_annulusPenalty_rpow_sub_one d (by norm_num) i j (j - 1))
      (fun v _ => isBigOWith_comp_measurePreserving
        (GoodEvents.measurePreserving_translateCutoffSample M _) hVm hVt)
  have hpen1 : (0 : ℝ) < annulusPenalty d 2 (j - i).toNat * A1 :=
    mul_pos (lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) _)) hA1
  have hpen2 : (0 : ℝ) < annulusPenalty d (1 / 2) (j - i).toNat * A2 :=
    mul_pos (lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) _)) hA2
  refine Provider.Tail.isTwoTermBigOWith_of_ae_le
    (Probability.isAdmissibleTail_gammaSigma (by norm_num))
    (Probability.isAdmissibleTail_gammaSigma (by norm_num))
    hpen1 hpen2 (measurable_kickAnnMax M s j i) hUmaxm hVmaxm
    (Filter.Eventually.of_forall fun omega => ?_) hUmaxt hVmaxt
  exact fmax_le_add_fmax _ _ _ _ fun v _ => hpt _ omega

/-! ## 3. `e.Gamma.sigma.triangle`: the weighted inner-scale sum -/

/-- The `Γ₂` amplitude of the Step-1 sum, as the weighted penalty series. -/
def kickAmpTwo (d : ℕ) (s A1 : ℝ) : ℝ :=
  gammaTriangleConst 2 *
    ∑' p : ℕ, weightThird (s / 2) (p + 1) * (annulusPenalty d 2 (p + 1) * A1)

/-- The `Γ_{1/2}` amplitude of the Step-1 sum, as the weighted penalty series. -/
def kickAmpHalf (d : ℕ) (s A2 : ℝ) : ℝ :=
  gammaTriangleConst (1 / 2) *
    ∑' p : ℕ, weightThird (s / 2) (p + 1) * (annulusPenalty d (1 / 2) (p + 1) * A2)

theorem summable_kickAmpTwo (d : ℕ) {s A1 : ℝ} (hs : 0 < s) (hA1 : 0 ≤ A1) :
    Summable fun p : ℕ =>
      weightThird (s / 2) (p + 1) * (annulusPenalty d 2 (p + 1) * A1) := by
  have hbase := summable_weightThird_mul_annulusPenalty (d := d) (sprime := s / 2)
    (A := A1) (N := 1) (by linarith only [hs]) (by norm_num) hA1
  simp only [Nat.cast_one, inv_one] at hbase
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hbase
  · have hpen : (0 : ℝ) ≤ annulusPenalty d 2 (p + 1) :=
      le_trans zero_le_one (one_le_annulusPenalty d (by norm_num) _)
    exact mul_nonneg (weightThird_pos _).le (mul_nonneg hpen hA1)
  · refine mul_le_mul_of_nonneg_left ?_ (weightThird_pos _).le
    exact mul_le_mul_of_nonneg_right (annulusPenalty_two_le_one d (p + 1)) hA1

theorem summable_kickAmpHalf (d : ℕ) {s A2 : ℝ} (hs : 0 < s) (hA2 : 0 ≤ A2) :
    Summable fun p : ℕ =>
      weightThird (s / 2) (p + 1) * (annulusPenalty d (1 / 2) (p + 1) * A2) := by
  have hbase := summable_weightThird_mul_annulusPenalty (d := d) (sprime := s / 2)
    (A := A2) (N := 2) (by linarith only [hs]) (by norm_num) hA2
  have hcast : ((((2 : ℕ)) : ℝ))⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hcast] at hbase
  exact hbase

/-- **The Step-1 inner-scale sum inherits the two-term display** through the
two-term countable generalized triangle inequality, applied at `σ = 2` and
`σ = 1/2` simultaneously.  `hcube` is the per-inner-scale display, uniform in
`i`. -/
theorem isTwoTermBigOWith_annularKick (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    {A1 A2 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hcube : ∀ i : ℤ, i ≤ j - 1 →
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M i s)
        A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2)) (annularKick M s j)
      (kickAmpTwo d (s : ℝ) A1) (kickAmpHalf d (s : ℝ) A2) := by
  have hs2 : (0 : ℝ) < (s : ℝ) / 2 := by have := s.2; linarith only [this]
  have hpen1pos : ∀ p : ℕ, (0 : ℝ) < annulusPenalty d 2 (p + 1) * A1 := fun p =>
    mul_pos (lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) _)) hA1
  have hpen2pos : ∀ p : ℕ, (0 : ℝ) < annulusPenalty d (1 / 2) (p + 1) * A2 := fun p =>
    mul_pos (lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) _)) hA2
  have hterm : ∀ p : ℕ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2))
        (kickAnnMax M s j (j - 1 - (p : ℤ)))
        (annulusPenalty d 2 (p + 1) * A1)
        (annulusPenalty d (1 / 2) (p + 1) * A2) := by
    intro p
    have hidx : (j - (j - 1 - (p : ℤ))).toNat = p + 1 := by omega
    have hbase := isTwoTermBigOWith_kickAnnMax M s j (j - 1 - (p : ℤ))
      (hcube _ (by omega))
    rwa [hidx] at hbase
  have hmain := isTwoTermBigOWith_wsum
    (T := fun p => kickAnnMax M s j (j - 1 - (p : ℤ)))
    (c := fun p => weightThird ((s : ℝ) / 2) (p + 1))
    (a1 := fun p => annulusPenalty d 2 (p + 1) * A1)
    (a2 := fun p => annulusPenalty d (1 / 2) (p + 1) * A2)
    (by norm_num) (by norm_num)
    (fun p omega => kickAnnMax_nonneg M s j _ omega)
    (fun p => measurable_kickAnnMax M s j _)
    (fun p => weightThird_pos _) hpen1pos hpen2pos
    (summable_kickAmpTwo d s.2 hA1.le) (summable_kickAmpHalf d s.2 hA2.le) hterm
  rw [annularKick_eq_wsum, kickAmpTwo, kickAmpHalf]
  exact hmain

/-! ## 4. The closed forms in the window parameter -/

/-- The dimensional constant of the `Γ₂` closed form. -/
def kickTwoConst (d : ℕ) : ℝ := gammaTriangleConst 2 * (8 * Real.sqrt (penaltyBase d))

/-- The dimensional constant of the `Γ_{1/2}` closed form. -/
def kickHalfConst (d : ℕ) : ℝ := gammaTriangleConst (1 / 2) * (128 * penaltyBase d ^ 2)

theorem kickHalfConst_pos (d : ℕ) : 0 < kickHalfConst d := by
  have h1 : (0 : ℝ) < gammaTriangleConst (1 / 2) := gammaTriangleConst_pos
  have h2 : (0 : ℝ) < penaltyBase d ^ 2 := pow_pos (penaltyBase_pos d) 2
  rw [kickHalfConst]
  exact mul_pos h1 (by linarith only [h2])

/-- **The `Γ₂` closed form, sharp: `s^{−3/2}`.**  The `√(j−i+1)` penalty summed
against `3^{−½s(j−i)}` closes by Cauchy--Schwarz at `(1−3^{−½s})^{−3/2}`, i.e.
`8s^{−3/2}`; the crude comparison `√(r+1) ≤ r+1` would give `s^{−2}`. -/
theorem kickAmpTwo_le (d : ℕ) {s A1 : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hA1 : 0 ≤ A1) :
    kickAmpTwo d s A1 ≤ kickTwoConst d * (A1 * ((Real.sqrt s) ^ 3)⁻¹) := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith only [hs0]
  have hB0 : (0 : ℝ) ≤ Real.sqrt (penaltyBase d) := Real.sqrt_nonneg _
  have hle : ∀ p : ℕ,
      weightThird (s / 2) (p + 1) * (annulusPenalty d 2 (p + 1) * A1)
        ≤ A1 * Real.sqrt (penaltyBase d) *
          ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * Real.sqrt ((p : ℝ) + 1)) := by
    intro p
    have hpen : annulusPenalty d 2 (p + 1) * A1
        ≤ (Real.sqrt (penaltyBase d) * Real.sqrt ((p : ℝ) + 1)) * A1 :=
      mul_le_mul_of_nonneg_right (annulusPenalty_two_le d p) hA1
    have hrhs0 : (0 : ℝ) ≤ (Real.sqrt (penaltyBase d) * Real.sqrt ((p : ℝ) + 1)) * A1 :=
      mul_nonneg (mul_nonneg hB0 (Real.sqrt_nonneg _)) hA1
    calc weightThird (s / 2) (p + 1) * (annulusPenalty d 2 (p + 1) * A1)
        ≤ weightThird (s / 2) (p + 1) *
            ((Real.sqrt (penaltyBase d) * Real.sqrt ((p : ℝ) + 1)) * A1) :=
          mul_le_mul_of_nonneg_left hpen (weightThird_pos _).le
      _ ≤ (3 : ℝ) ^ (-((s / 2) * (p : ℝ))) *
            ((Real.sqrt (penaltyBase d) * Real.sqrt ((p : ℝ) + 1)) * A1) :=
          mul_le_mul_of_nonneg_right (weightThird_succ_le hs2.le p) hrhs0
      _ = A1 * Real.sqrt (penaltyBase d) *
            ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * Real.sqrt ((p : ℝ) + 1)) := by ring
  have hmaj : Summable fun p : ℕ => A1 * Real.sqrt (penaltyBase d) *
      ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * Real.sqrt ((p : ℝ) + 1)) :=
    (Algsuperdiff.Probability.summable_threePow_neg_sqrt hs2).mul_left _
  have hbound := Summable.tsum_le_tsum hle (summable_kickAmpTwo d hs0 hA1) hmaj
  have hmajval : ∑' p : ℕ, A1 * Real.sqrt (penaltyBase d) *
        ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * Real.sqrt ((p : ℝ) + 1))
      = A1 * Real.sqrt (penaltyBase d) *
        ∑' p : ℕ, (3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * Real.sqrt ((p : ℝ) + 1) :=
    tsum_mul_left
  have hclosure : ∑' p : ℕ, (3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * Real.sqrt ((p : ℝ) + 1)
      ≤ 8 * ((Real.sqrt s) ^ 3)⁻¹ :=
    le_trans (Algsuperdiff.Probability.tsum_threePow_neg_sqrt_le hs2)
      (geomSqrtConst_le hs0 hs1)
  have hAB0 : (0 : ℝ) ≤ A1 * Real.sqrt (penaltyBase d) := mul_nonneg hA1 hB0
  rw [kickAmpTwo]
  refine le_trans (mul_le_mul_of_nonneg_left hbound gammaTriangleConst_pos.le) ?_
  rw [hmajval]
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hclosure hAB0) gammaTriangleConst_pos.le) ?_
  rw [kickTwoConst]
  ring_nf
  exact le_rfl

/-- **The `Γ_{1/2}` closed form: `s^{−3}`.**  The `(j−i+1)²` penalty summed
against `3^{−½s(j−i)}` closes at `2(1−3^{−½s})^{−3}`, i.e. `128s^{−3}`.  This
`s^{−3}` is exactly what `inv_cube_mul_exp_le` absorbs into the exponential. -/
theorem kickAmpHalf_le (d : ℕ) {s A2 : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hA2 : 0 ≤ A2) :
    kickAmpHalf d s A2 ≤ kickHalfConst d * (A2 * s⁻¹ ^ 3) := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith only [hs0]
  have hB0 : (0 : ℝ) ≤ penaltyBase d ^ 2 := by
    exact pow_nonneg (penaltyBase_pos d).le 2
  have hle : ∀ p : ℕ,
      weightThird (s / 2) (p + 1) * (annulusPenalty d (1 / 2) (p + 1) * A2)
        ≤ A2 * penaltyBase d ^ 2 *
          ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * ((p : ℝ) + 1) ^ 2) := by
    intro p
    have hpen : annulusPenalty d (1 / 2) (p + 1) * A2
        ≤ (penaltyBase d ^ 2 * ((p : ℝ) + 1) ^ 2) * A2 :=
      mul_le_mul_of_nonneg_right (annulusPenalty_half_le d p) hA2
    have hrhs0 : (0 : ℝ) ≤ (penaltyBase d ^ 2 * ((p : ℝ) + 1) ^ 2) * A2 :=
      mul_nonneg (mul_nonneg hB0 (by positivity)) hA2
    calc weightThird (s / 2) (p + 1) * (annulusPenalty d (1 / 2) (p + 1) * A2)
        ≤ weightThird (s / 2) (p + 1) * ((penaltyBase d ^ 2 * ((p : ℝ) + 1) ^ 2) * A2) :=
          mul_le_mul_of_nonneg_left hpen (weightThird_pos _).le
      _ ≤ (3 : ℝ) ^ (-((s / 2) * (p : ℝ))) *
            ((penaltyBase d ^ 2 * ((p : ℝ) + 1) ^ 2) * A2) :=
          mul_le_mul_of_nonneg_right (weightThird_succ_le hs2.le p) hrhs0
      _ = A2 * penaltyBase d ^ 2 *
            ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * ((p : ℝ) + 1) ^ 2) := by ring
  have hmaj : Summable fun p : ℕ => A2 * penaltyBase d ^ 2 *
      ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * ((p : ℝ) + 1) ^ 2) :=
    (summable_threePow_neg_sq_succ hs2).mul_left _
  have hbound := Summable.tsum_le_tsum hle (summable_kickAmpHalf d hs0 hA2) hmaj
  have hmajval : ∑' p : ℕ, A2 * penaltyBase d ^ 2 *
        ((3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * ((p : ℝ) + 1) ^ 2)
      = A2 * penaltyBase d ^ 2 *
        ∑' p : ℕ, (3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * ((p : ℝ) + 1) ^ 2 :=
    tsum_mul_left
  have hclosure : ∑' p : ℕ, (3 : ℝ) ^ (-((s / 2) * (p : ℝ))) * ((p : ℝ) + 1) ^ 2
      ≤ 128 * s⁻¹ ^ 3 := by
    refine le_trans (tsum_threePow_neg_sq_succ_le hs2) ?_
    have h := geomTailConst_cube_le hs0 hs1
    linarith only [h]
  have hAB0 : (0 : ℝ) ≤ A2 * penaltyBase d ^ 2 := mul_nonneg hA2 hB0
  rw [kickAmpHalf]
  refine le_trans (mul_le_mul_of_nonneg_left hbound gammaTriangleConst_pos.le) ?_
  rw [hmajval]
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hclosure hAB0) gammaTriangleConst_pos.le) ?_
  rw [kickHalfConst]
  ring_nf
  exact le_rfl

/-! ## 5. The endpoint -/

/-- **The Step-1 kick family and its two tails, unconditionally.**

There is a dimensional constant `C` such that for every model in the regime
`γ ≤ C^{−10}c⋆^{10}` and every window parameter `s ∈ [8γ, 1/2]` there is a
threshold `lam` for which, **uniformly in the annulus index `j`**,

```
X_j^{(1)} = min(annularKick_j, lam)             ≤ 𝒪_{Γ₂}(C c⋆^{−1}s^{−5/2}√γ) ,
X_j^{(2)} = annularKick_j − min(annularKick_j, lam) ≤ 𝒪_{Γ_{1/2}}(C exp(−C^{−1}c⋆³γ^{−1})) ,
```

and `X_j^{(1)} + X_j^{(2)} = annularKick_j` exactly.  The `r`-dependence of the
pair is settled in `KickFamily`, which needs nothing from here.

`s^{−5/2}` is written `((√s)⁵)⁻¹`, so that no `rpow` appears in the statement.

**Hypotheses.**  Exactly the premises of `l.minimal.scale.sep` as printed: `γ ≤
C^{−10}c⋆^{10}` and `s ∈ [8γ, 1/2]`.  The positivity of `s` is the typing datum
of the observable's index and is implied by the window. -/
theorem exists_kickFamily_tails (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 2 →
          ∃ lam : ℝ, 0 ≤ lam ∧
            (∀ j : ℤ,
              IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
                (kickLegLow M s lam j)
                (C * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
                  Real.sqrt M.gamma)) ∧
            (∀ j : ℤ,
              IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 2))
                (kickLegHigh M s lam j)
                (C * Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)))) := by
  obtain ⟨C0, hC0, hprod⟩ := exists_isTwoTermBigOWith_annularErrorObservable d
  refine ⟨max (2 * C0) (max (8 * kickTwoConst d * (Real.sqrt 3 * annulusPenalty d 2 1) * C0)
      (8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1) *
        (216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15))), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith only [hC0]) (le_max_left _ _)
  intro M hreg s hs8 hs2
  set C : ℝ := max (2 * C0) (max (8 * kickTwoConst d * (Real.sqrt 3 * annulusPenalty d 2 1) * C0)
      (8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1) *
        (216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15))) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith only [hC0]) (le_max_left _ _)
  have h2C0 : 2 * C0 ≤ C := le_max_left _ _
  have hD1 : 8 * kickTwoConst d * (Real.sqrt 3 * annulusPenalty d 2 1) * C0 ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hD2 : 8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1) *
      (216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15) ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  -- the standing quantities
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs2]
  have hpen21 : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have hpenh1 : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  -- the regime at the producer's constant
  have hregC0 : M.gamma ≤ C0⁻¹ ^ 10 * (Disorder.cstar M) ^ 10 := by
    have hCC0 : C0 ≤ C := le_trans (by linarith only [hC0]) h2C0
    have h1 : C⁻¹ ≤ C0⁻¹ := inv_anti₀ hC0 hCC0
    have h2 : C⁻¹ ^ 10 ≤ C0⁻¹ ^ 10 :=
      pow_le_pow_left₀ (le_of_lt (inv_pos.2 hCpos)) h1 10
    have h3 : C⁻¹ ^ 10 * (Disorder.cstar M) ^ 10 ≤ C0⁻¹ ^ 10 * (Disorder.cstar M) ^ 10 :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hcs.le 10)
    exact hreg.trans h3
  -- the per-cube display, uniform in the inner scale
  have hcube : ∀ i : ℤ, Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) (gammaSigma (1 / 2))
      (Support.annularErrorObservable M i s)
      (Real.sqrt 3 * (annulusPenalty d 2 1 *
        (C0 * (Disorder.cstar M)⁻¹ * (s : ℝ)⁻¹ * Real.sqrt M.gamma)))
      (Real.sqrt 3 * (annulusPenalty d (1 / 2) 1 *
        Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)))) := fun i =>
    hprod M hregC0 (s : ℝ) ⟨hs8, hs1⟩ i
  set A1 : ℝ := Real.sqrt 3 * (annulusPenalty d 2 1 *
    (C0 * (Disorder.cstar M)⁻¹ * (s : ℝ)⁻¹ * Real.sqrt M.gamma)) with hA1def
  set A2 : ℝ := Real.sqrt 3 * (annulusPenalty d (1 / 2) 1 *
    Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))) with hA2def
  have hgsq : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hgam
  have hA1pos : (0 : ℝ) < A1 := by
    rw [hA1def]
    refine mul_pos hsqrt3 (mul_pos hpen21 ?_)
    exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 hcs)) (inv_pos.2 hs0)) hgsq
  have hA2pos : (0 : ℝ) < A2 := by
    rw [hA2def]
    exact mul_pos hsqrt3 (mul_pos hpenh1 (Real.exp_pos _))
  -- the two aggregated amplitudes
  set B1 : ℝ := kickAmpTwo d (s : ℝ) A1 with hB1def
  set B2 : ℝ := kickAmpHalf d (s : ℝ) A2 with hB2def
  have hB1pos : (0 : ℝ) < B1 := by
    rw [hB1def, kickAmpTwo]
    refine mul_pos gammaTriangleConst_pos ?_
    refine (summable_kickAmpTwo d hs0 hA1pos.le).tsum_pos (fun p => ?_) 0 ?_
    · exact mul_nonneg (weightThird_pos _).le
        (mul_nonneg (le_trans zero_le_one
          (one_le_annulusPenalty d (by norm_num) _)) hA1pos.le)
    · exact mul_pos (weightThird_pos _)
        (mul_pos (lt_of_lt_of_le zero_lt_one
          (one_le_annulusPenalty d (by norm_num) _)) hA1pos)
  have hB2pos : (0 : ℝ) < B2 := by
    rw [hB2def, kickAmpHalf]
    refine mul_pos gammaTriangleConst_pos ?_
    refine (summable_kickAmpHalf d hs0 hA2pos.le).tsum_pos (fun p => ?_) 0 ?_
    · exact mul_nonneg (weightThird_pos _).le
        (mul_nonneg (le_trans zero_le_one
          (one_le_annulusPenalty d (by norm_num) _)) hA2pos.le)
    · exact mul_pos (weightThird_pos _)
        (mul_pos (lt_of_lt_of_le zero_lt_one
          (one_le_annulusPenalty d (by norm_num) _)) hA2pos)
  -- the crossover threshold
  set rho : ℝ := (B1 / B2) ^ ((1 : ℝ) / 3) with hrhodef
  have hrhopos : (0 : ℝ) < rho :=
    Real.rpow_pos_of_pos (div_pos hB1pos hB2pos) _
  have hratio : rho ^ 3 * B2 = B1 := by
    have hcube3 : rho ^ 3 = B1 / B2 := by
      have h3 : ((1 : ℝ) / 3) * (((3 : ℕ)) : ℝ) = 1 := by norm_num
      rw [hrhodef, ← Real.rpow_natCast ((B1 / B2) ^ ((1 : ℝ) / 3)) 3,
        ← Real.rpow_mul (div_nonneg hB1pos.le hB2pos.le), h3, Real.rpow_one]
    rw [hcube3]
    field_simp
  refine ⟨8 * B1 * rho, ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 8 * B1 * rho := by
      exact mul_pos (by linarith only [hB1pos]) hrhopos
    linarith only [h1]
  -- the `Γ₂` leg
  · intro j
    have hdisp := isTwoTermBigOWith_annularKick M s j hA1pos hA2pos
      (fun i _ => hcube i)
    rw [← hB1def, ← hB2def] at hdisp
    have hleg := isBigOWith_min_of_isTwoTermBigOWith hratio hdisp
    refine hleg.mono_scale ?_
    -- the closed form
    have hclosed : B1 ≤ kickTwoConst d * (A1 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹) := by
      rw [hB1def]
      exact kickAmpTwo_le d hs0 hs1 hA1pos.le
    have hsplit : ((Real.sqrt (s : ℝ)) ^ 5)⁻¹
        = (s : ℝ)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ := by
      rw [← mul_inv]
      congr 1
      rw [show (5 : ℕ) = 2 + 3 from by norm_num, pow_add, Real.sq_sqrt hs0.le]
    have hval : 8 * (kickTwoConst d * (A1 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹))
        = (8 * kickTwoConst d * (Real.sqrt 3 * annulusPenalty d 2 1) * C0) *
          ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ * Real.sqrt M.gamma) := by
      rw [hA1def, hsplit]
      ring
    have hstep : 8 * B1 ≤ (8 * kickTwoConst d * (Real.sqrt 3 * annulusPenalty d 2 1) * C0) *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ * Real.sqrt M.gamma) := by
      rw [← hval]
      linarith only [hclosed]
    have hfac0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
        Real.sqrt M.gamma := by
      have h1 : (0 : ℝ) < ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ :=
        inv_pos.2 (pow_pos (Real.sqrt_pos.2 hs0) 5)
      exact mul_nonneg (mul_nonneg (le_of_lt (inv_pos.2 hcs)) h1.le) hgsq.le
    refine hstep.trans ?_
    have hmul := mul_le_mul_of_nonneg_right hD1 hfac0
    calc (8 * kickTwoConst d * (Real.sqrt 3 * annulusPenalty d 2 1) * C0) *
          ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ * Real.sqrt M.gamma)
        ≤ C * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ * Real.sqrt M.gamma) :=
          hmul
      _ = C * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ * Real.sqrt M.gamma := by
          ring
  -- the `Γ_{1/2}` leg
  · intro j
    have hdisp := isTwoTermBigOWith_annularKick M s j hA1pos hA2pos
      (fun i _ => hcube i)
    rw [← hB1def, ← hB2def] at hdisp
    have hleg := isBigOWith_sub_min_of_isTwoTermBigOWith hrhopos hratio hdisp
    refine hleg.mono_scale ?_
    -- the closed form and the absorption
    have hclosed : B2 ≤ kickHalfConst d * (A2 * (s : ℝ)⁻¹ ^ 3) := by
      rw [hB2def]
      exact kickAmpHalf_le d hs0 hs1 hA2pos.le
    have habs := inv_cube_mul_exp_le hC0 hcs hgam hregC0 hs8
    have hval : 8 * (kickHalfConst d * (A2 * (s : ℝ)⁻¹ ^ 3))
        = (8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1)) *
          ((s : ℝ)⁻¹ ^ 3 *
            Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))) := by
      rw [hA2def]
      ring
    have hcoef0 : (0 : ℝ)
        ≤ 8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1) := by
      have h1 : (0 : ℝ) < kickHalfConst d := kickHalfConst_pos d
      have h2 : (0 : ℝ) < Real.sqrt 3 * annulusPenalty d (1 / 2) 1 :=
        mul_pos hsqrt3 hpenh1
      have h3 : (0 : ℝ) < 8 * kickHalfConst d := by linarith only [h1]
      exact le_of_lt (mul_pos h3 h2)
    have hstep : 8 * B2
        ≤ (8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1)) *
          ((216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15) *
            Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ / 2))) := by
      have h1 : 8 * B2 ≤ 8 * (kickHalfConst d * (A2 * (s : ℝ)⁻¹ ^ 3)) := by
        linarith only [hclosed]
      rw [hval] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left habs hcoef0)
    refine hstep.trans ?_
    -- fold into the printed shape at the single constant `C`
    have hexpmono : Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ / 2))
        ≤ Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)) := by
      refine Real.exp_le_exp.2 ?_
      have hinv : C⁻¹ ≤ C0⁻¹ / 2 := by
        have h2 : C⁻¹ ≤ (2 * C0)⁻¹ := inv_anti₀ (by linarith only [hC0]) h2C0
        refine h2.trans (le_of_eq ?_)
        rw [mul_inv]
        ring
      have hfac : (0 : ℝ) < (Disorder.cstar M) ^ 3 * M.gamma⁻¹ := by
        exact mul_pos (pow_pos hcs 3) (inv_pos.2 hgam)
      have hmul := mul_le_mul_of_nonneg_right hinv hfac.le
      have heq : C0⁻¹ / 2 * ((Disorder.cstar M) ^ 3 * M.gamma⁻¹)
          = C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ / 2 := by ring
      have heq2 : C⁻¹ * ((Disorder.cstar M) ^ 3 * M.gamma⁻¹)
          = C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ := by ring
      rw [heq, heq2] at hmul
      linarith only [hmul]
    have hprefac : (8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1)) *
        (216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15) ≤ C := hD2
    have hE0 : (0 : ℝ) < Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ / 2)) :=
      Real.exp_pos _
    calc (8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1)) *
          ((216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15) *
            Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ / 2)))
        = ((8 * kickHalfConst d * (Real.sqrt 3 * annulusPenalty d (1 / 2) 1)) *
            (216 * C0 ^ 3 + 100000 * C0⁻¹ ^ 15)) *
            Real.exp (-(C0⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ / 2)) := by ring
      _ ≤ C * Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)) :=
          mul_le_mul hprefac hexpmono hE0.le hCpos.le

end

end Algsuperdiff.Section4.Provider.MinimalScale
