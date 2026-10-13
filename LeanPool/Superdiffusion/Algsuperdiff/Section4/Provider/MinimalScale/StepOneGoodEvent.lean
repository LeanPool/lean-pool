/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickCollapse
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.DDecomposition

/-!
# StepOneGoodEvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-1 good-event bound and the kick collapse

ABK26, §4.2, Step 1 of `l.minimal.scale.sep`.  Step 1 opens with a purely
deterministic estimate off the good event:

```
∑_{i ≤ j−1} 3^{−½s(j−i)} max_{z ∈ 3^iℤ^d ∩ (□_j∖□_{j−1})} 𝓔_{s,2,2}(z+□_i;·)
    · 1_{𝒢(k;s,1)}
  ≤ C s^{−3/2} 3^{⅛s(k−j)} ,
```

then reads the printed two-leg display

```
… ≤ X_j^{(1)} + min{X_j^{(2)}, C s^{−3/2}3^{⅛s(k−j)}} ,
```

and collapses it into `X_j = X_j^{(1)} + (Cs^{−9/2}X_j^{(2)})^{1/4}`.

## The exponent bookkeeping, honestly

There is in fact **no Cauchy--Schwarz** in the honest derivation, and the
printed constant comes out exactly:

* `𝒢₂(k;s,1)` reads `s ∑_{j'≤k} ∑_{i≤j'−1} 3^{−¼s(k−i)} (max 𝓔)² ≤ 1`; dropping all
  but ONE term gives, for every `i ≤ j−1 ≤ k−1`, the pointwise
  `max 𝓔 ≤ s^{−1/2} 3^{⅛s(k−i)}` — the `1/8` is the `1/4` halved by the square
  root of that single term, nothing else;
* summing against the §4.2 weight `3^{−½s(j−i)}` and splitting
  `3^{⅛s(k−i)} = 3^{⅛s(k−j)}·3^{⅛s(j−i)}` leaves the geometric series
  `∑_p 3^{−⅜s(p+1)} ≤ (1−3^{−⅜s})^{−1} ≤ 16/(3s) ≤ 6/s`;
* hence the bound `6 s^{−3/2}3^{⅛s(k−j)}` — the printed `s^{−3/2}` on the nose,
  at the explicit constant `6`.

A Cauchy--Schwarz argument would give the sharper `s^{−1}`; it is not needed,
and the crude termwise route is what reproduces the printed exponent, so the
`s^{−3/2}` here is not a defect.

## The collapse constant is explicit: `216 = 6³`

With `B := 6 s^{−3/2}3^{⅛s(k−j)}` and `W := 3^{−⅛s(k−j)} ≤ 1`, the printed
collapse needs `W⁸B³ ≤ K` for the coefficient `K`, and `W⁸B³ = 216 s^{−9/2} W⁵
≤ 216 s^{−9/2}`.  So `K = 216 s^{−9/2}` suffices, and any larger coefficient
does too (`kickCollapsed_le_mul_of_coeff_le`).

## Main results

* `weighted_annularKick_le_kickCollapsed` — **the collapse step**: the weighted
  inner sum at weight `3^{−½s(k−j)}` is below `3^{−¼s(k−j)}·X_j`.

## References

* ABK26, `l.minimal.scale.sep`, Step 1; `d.good.event.for.lambda`, (`𝒢₂`).
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `weightThird` algebra -/

/-- `weightThird` is multiplicative in the offset. -/
theorem weightThird_add (a : ℝ) (m n : ℕ) :
    weightThird a (m + n) = weightThird a m * weightThird a n := by
  rw [weightThird, weightThird, weightThird, pow_add]

/-- Squaring the weight doubles its rate. -/
theorem weightThird_sq (a : ℝ) (n : ℕ) :
    weightThird a n ^ 2 = weightThird (2 * a) n := by
  have hr : ((3 : ℝ) ^ (-a)) ^ 2 = (3 : ℝ) ^ (-(2 * a)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-a)) 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [weightThird, weightThird, ← pow_mul, show n * 2 = 2 * n from by ring, pow_mul, hr]

/-- Quadrupling the rate is the fourth power of the weight. -/
theorem weightThird_pow_four (a : ℝ) (n : ℕ) :
    weightThird a n ^ 4 = weightThird (4 * a) n := by
  have h1 : weightThird a n ^ 4 = (weightThird a n ^ 2) ^ 2 := by ring
  rw [h1, weightThird_sq, weightThird_sq]
  congr 1
  ring

/-- The ratio of the Step-1 weight to the good-event growth factor is geometric at
rate `⅜s`: `3^{−½s·} · 3^{⅛s·} = 3^{−⅜s·}`. -/
theorem weightThird_div_eq (a : ℝ) (n : ℕ) :
    weightThird (4 * a) n * (weightThird a n)⁻¹ = weightThird (3 * a) n := by
  have hexp : weightThird (4 * a) n = weightThird (3 * a) n * weightThird a n := by
    rw [weightThird, weightThird, weightThird, ← mul_pow]
    congr 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hexp, mul_assoc, mul_inv_cancel₀ (ne_of_gt (weightThird_pos n)), mul_one]

theorem weightThird_le_one {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : weightThird a n ≤ 1 := by
  refine pow_le_one₀ (Real.rpow_nonneg (by norm_num) _) ?_
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [ha])

/-- The geometric series of the shifted weights, at the closure constant. -/
theorem tsum_weightThird_succ_le {a : ℝ} (ha : 0 < a) :
    ∑' p : ℕ, weightThird a (p + 1) ≤ Algsuperdiff.Probability.geomTailConst a := by
  set r : ℝ := (3 : ℝ) ^ (-a) with hrdef
  have hr0 : (0 : ℝ) ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Algsuperdiff.Probability.three_rpow_neg_lt_one ha
  have hgeo : ∑' p : ℕ, r ^ p = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hsum : Summable fun p : ℕ => r ^ p := summable_geometric_of_lt_one hr0 hr1
  have heq : ∀ p : ℕ, weightThird a (p + 1) = r * r ^ p := by
    intro p
    rw [weightThird, ← hrdef, pow_succ]
    ring
  calc ∑' p : ℕ, weightThird a (p + 1) = ∑' p : ℕ, r * r ^ p := tsum_congr heq
    _ = r * (1 - r)⁻¹ := by rw [tsum_mul_left, hgeo]
    _ ≤ 1 * (1 - r)⁻¹ := by
        refine mul_le_mul_of_nonneg_right hr1.le ?_
        exact (inv_pos.2 (by linarith only [hr1])).le
    _ = Algsuperdiff.Probability.geomTailConst a := by
        rw [Algsuperdiff.Probability.geomTailConst, one_mul, hrdef]

/-- Summability of the shifted weights. -/
theorem summable_weightThird_succ {a : ℝ} (ha : 0 < a) :
    Summable fun p : ℕ => weightThird a (p + 1) := by
  set r : ℝ := (3 : ℝ) ^ (-a) with hrdef
  have hr0 : (0 : ℝ) ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Algsuperdiff.Probability.three_rpow_neg_lt_one ha
  have hsum : Summable fun p : ℕ => r * r ^ p :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left r
  refine hsum.congr fun p => ?_
  rw [weightThird, ← hrdef, pow_succ]
  ring

/-- The `ℤ`-offset rendering of the weight: at a nonnegative offset the anchor's
`3^{−a·x}` is `weightThird a x.toNat`. -/
theorem three_rpow_eq_weightThird (a : ℝ) {x : ℤ} (hx : 0 ≤ x) :
    Real.rpow (3 : ℝ) (-(a * ((x : ℤ) : ℝ))) = weightThird a x.toNat := by
  have h : ((x.toNat : ℕ) : ℝ) = ((x : ℤ) : ℝ) := by
    have h1 : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx
    exact_mod_cast h1
  rw [weightThird_eq, h]
  rfl

/-! ## 2. The `Finset` maximum of the squares -/

variable {iota : Type*}

/-- The square of a `0`-floored maximum is below the maximum of the squares. -/
theorem fmax_sq_le (S : Finset iota) (f : iota → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i) :
    fmax S f ^ 2 ≤ fmax S (fun i => f i ^ 2) := by
  rcases Finset.eq_empty_or_nonempty S with hE | hE
  · rw [hE, fmax_empty, fmax_empty]
    norm_num
  · obtain ⟨i, hi, hveq⟩ := exists_mem_eq_fmax hE hf
    rw [hveq]
    exact le_fmax (S := S) (f := fun i => f i ^ 2) hi

/-- **The unsquared lattice maximum, squared, is below the §4.1 squared
maximum.**  Both are `0`-floored maxima of the same nonnegative atom over the same
`Finset`. -/
theorem kickAnnMax_sq_le_errorAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j i : ℤ)
    (omega : Cutoff.CutoffSample d) :
    kickAnnMax M s j i omega ^ 2 ≤ errorAnnMax M s j i omega := by
  have h := fmax_sq_le (latticeAnnulusFinset d i j (j - 1))
    (fun v => kickAtom M i s (Support.triadicLatticePoint i v) omega)
    (fun v _ => kickAtom_nonneg M i s _ omega)
  refine le_trans h (le_of_eq ?_)
  rw [errorAnnMax]
  rfl

/-! ## 3. The good-event bound -/

/-- **The Step-1 good-event bound, per inner scale.**  On `𝒢₂(k;s,1)` every atom of the
inner-scale sum obeys `max 𝓔 ≤ s^{−1/2}3^{⅛s(k−i)}`: a single term of the
event's own double sum, square-rooted. -/
theorem kickAnnMax_le_of_mem_eventG2 (M : ABKModel d) (s : {s : ℝ // 0 < s}) {k j i : ℤ}
    (hjk : j ≤ k) (hij : i ≤ j - 1) {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ eventG2 M k s 1) :
    kickAnnMax M s j i omega
      ≤ (Real.sqrt (s : ℝ))⁻¹ * (weightThird ((s : ℝ) / 8) (k - i).toNat)⁻¹ := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  have hik : (0 : ℤ) ≤ k - i := by omega
  have hij' : i ≤ j := by omega
  set x : ℕ := (k - i).toNat with hxdef
  have hw8 : (0 : ℝ) < weightThird ((s : ℝ) / 8) x := weightThird_pos x
  have hw4 : (0 : ℝ) < weightThird ((s : ℝ) / 4) x := weightThird_pos x
  -- the event, in row form, and the single term
  have hrow : ENNReal.ofReal (s : ℝ) * XrowE M s k omega ≤ ENNReal.ofReal ((1 : ℝ) ^ 2) := by
    rw [eventG2_eq_row] at hmem
    exact hmem
  have hterm : annularWeight (s : ℝ) (k - i) * errorAnnSup M s j i omega
      ≤ XrowE M s k omega := by
    have h1 : annularWeight (s : ℝ) (k - i) * errorAnnSup M s j i omega
        ≤ ∑' n : {n : ℤ // n ≤ j - 1},
            annularWeight (s : ℝ) (k - n.1) * errorAnnSup M s j n.1 omega :=
      ENNReal.le_tsum (f := fun n : {n : ℤ // n ≤ j - 1} =>
          annularWeight (s : ℝ) (k - n.1) * errorAnnSup M s j n.1 omega)
        (⟨i, hij⟩ : {n : ℤ // n ≤ j - 1})
    have h2 : (∑' n : {n : ℤ // n ≤ j - 1},
          annularWeight (s : ℝ) (k - n.1) * errorAnnSup M s j n.1 omega)
        = annularWeight (s : ℝ) (k - j) * XcalE M s j omega :=
      inner_eq_annularWeight_mul_XcalE M s k j omega
    have h3 : annularWeight (s : ℝ) (k - j) * XcalE M s j omega ≤ XrowE M s k omega :=
      ENNReal.le_tsum (f := fun j' : {j : ℤ // j ≤ k} =>
          annularWeight (s : ℝ) (k - j'.1) * XcalE M s j'.1 omega)
        (⟨j, hjk⟩ : {j : ℤ // j ≤ k})
    rw [h2] at h1
    exact h1.trans h3
  -- read the real inequality off
  have hreal : (s : ℝ) * (weightThird ((s : ℝ) / 4) x * errorAnnMax M s j i omega) ≤ 1 := by
    have hcomb : ENNReal.ofReal
        ((s : ℝ) * (weightThird ((s : ℝ) / 4) x * errorAnnMax M s j i omega))
        ≤ ENNReal.ofReal ((1 : ℝ) ^ 2) := by
      refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_right hterm _) hrow)
      rw [ENNReal.ofReal_mul hs0.le, ENNReal.ofReal_mul hw4.le,
        errorAnnSup_eq_ofReal_errorAnnMax M s hij' omega, annularWeight_eq_weightThird hik]
    have h1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 hcomb
    calc (s : ℝ) * (weightThird ((s : ℝ) / 4) x * errorAnnMax M s j i omega)
        ≤ (1 : ℝ) ^ 2 := h1
      _ = 1 := one_pow 2
  -- square-root the single term
  have hsqbound : kickAnnMax M s j i omega ^ 2
      ≤ ((Real.sqrt (s : ℝ))⁻¹ * (weightThird ((s : ℝ) / 8) x)⁻¹) ^ 2 := by
    have hrw : ((Real.sqrt (s : ℝ))⁻¹ * (weightThird ((s : ℝ) / 8) x)⁻¹) ^ 2
        = ((s : ℝ) * weightThird ((s : ℝ) / 4) x)⁻¹ := by
      have hs : ((Real.sqrt (s : ℝ))⁻¹) ^ 2 = ((s : ℝ))⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hs0.le]
      have hw : ((weightThird ((s : ℝ) / 8) x)⁻¹) ^ 2 = (weightThird ((s : ℝ) / 4) x)⁻¹ := by
        rw [inv_pow, weightThird_sq]
        congr 2
        ring
      rw [mul_pow, hs, hw, mul_inv]
    rw [hrw]
    refine le_trans (kickAnnMax_sq_le_errorAnnMax M s j i omega) ?_
    have hc : (0 : ℝ) < (s : ℝ) * weightThird ((s : ℝ) / 4) x := mul_pos hs0 hw4
    have hstep := mul_le_mul_of_nonneg_left hreal (inv_pos.2 hc).le
    calc errorAnnMax M s j i omega
        = ((s : ℝ) * weightThird ((s : ℝ) / 4) x)⁻¹ *
            ((s : ℝ) * (weightThird ((s : ℝ) / 4) x * errorAnnMax M s j i omega)) := by
          field_simp
      _ ≤ ((s : ℝ) * weightThird ((s : ℝ) / 4) x)⁻¹ * 1 := hstep
      _ = ((s : ℝ) * weightThird ((s : ℝ) / 4) x)⁻¹ := mul_one _
  refine le_of_sq_le_sq' (kickAnnMax_nonneg M s j i omega) ?_ hsqbound
  exact mul_nonneg (inv_pos.2 hsq0).le (inv_pos.2 hw8).le

/-- **The Step-1 good-event bound, in `ℝ≥0∞`.**  On `𝒢₂(k;s,1)` the inner-scale sum is bounded
by `6 s^{−3/2}3^{⅛s(k−j)}` — the printed `C s^{−3/2}3^{⅛s(k−j)}` at the
explicit constant `C = 6`.  In particular the sum is on the good event; that
finiteness is the source of every summability statement in the Step-1 assembly. -/
theorem annularKickE_le_of_mem_eventG2 (M : ABKModel d) (s : {s : ℝ // 0 < s}) {k j : ℤ}
    (hjk : j ≤ k) (hs1 : (s : ℝ) ≤ 1) {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ eventG2 M k s 1) :
    annularKickE M s j omega
      ≤ ENNReal.ofReal
          (6 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ * (weightThird ((s : ℝ) / 8) (k - j).toNat)⁻¹) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  have hjk0 : (0 : ℤ) ≤ k - j := by omega
  set y : ℕ := (k - j).toNat with hydef
  have hwy : (0 : ℝ) < weightThird ((s : ℝ) / 8) y := weightThird_pos y
  set A : ℝ := (Real.sqrt (s : ℝ))⁻¹ * (weightThird ((s : ℝ) / 8) y)⁻¹ with hAdef
  have hA0 : (0 : ℝ) ≤ A :=
    mul_nonneg (inv_pos.2 hsq0).le (inv_pos.2 hwy).le
  -- the termwise bound, in the `ℕ`-enumeration of the inner scales
  have hoffset : ∀ p : ℕ, (k - (j - 1 - (p : ℤ))).toNat = y + (p + 1) := by
    intro p
    omega
  have hterm : ∀ p : ℕ,
      weightThird ((s : ℝ) / 2) (p + 1) * kickAnnMax M s j (j - 1 - (p : ℤ)) omega
        ≤ A * weightThird (3 * ((s : ℝ) / 8)) (p + 1) := by
    intro p
    have hb := kickAnnMax_le_of_mem_eventG2 M s hjk (i := j - 1 - (p : ℤ)) (by omega) hmem
    rw [hoffset p, weightThird_add] at hb
    have hstep := mul_le_mul_of_nonneg_left hb
      (weightThird_pos (sprime := (s : ℝ) / 2) (p + 1)).le
    refine hstep.trans (le_of_eq ?_)
    have h2 : (s : ℝ) / 2 = 4 * ((s : ℝ) / 8) := by ring
    rw [hAdef, h2, mul_inv]
    calc weightThird (4 * ((s : ℝ) / 8)) (p + 1) *
          ((Real.sqrt (s : ℝ))⁻¹ *
            ((weightThird ((s : ℝ) / 8) y)⁻¹ * (weightThird ((s : ℝ) / 8) (p + 1))⁻¹))
        = (Real.sqrt (s : ℝ))⁻¹ * (weightThird ((s : ℝ) / 8) y)⁻¹ *
            (weightThird (4 * ((s : ℝ) / 8)) (p + 1) *
              (weightThird ((s : ℝ) / 8) (p + 1))⁻¹) := by ring
      _ = (Real.sqrt (s : ℝ))⁻¹ * (weightThird ((s : ℝ) / 8) y)⁻¹ *
            weightThird (3 * ((s : ℝ) / 8)) (p + 1) := by
          rw [weightThird_div_eq]
  -- sum the majorant
  have hrate : (0 : ℝ) < 3 * ((s : ℝ) / 8) := by linarith only [hs0]
  have hsummaj : Summable fun p : ℕ => A * weightThird (3 * ((s : ℝ) / 8)) (p + 1) :=
    (summable_weightThird_succ hrate).mul_left A
  have hmajsum : ∑' p : ℕ, A * weightThird (3 * ((s : ℝ) / 8)) (p + 1)
      ≤ A * (6 * ((s : ℝ))⁻¹) := by
    have hgt := tsum_weightThird_succ_le hrate
    have hgle : Algsuperdiff.Probability.geomTailConst (3 * ((s : ℝ) / 8)) ≤ 6 * ((s : ℝ))⁻¹ := by
      have h := geomTailConst_le hrate
        (by linarith only [hs1] : 3 * ((s : ℝ) / 8) ≤ 1 / 2)
      have hval : (2 : ℝ) / (3 * ((s : ℝ) / 8)) = (16 / 3) * ((s : ℝ))⁻¹ := by
        field_simp
        ring
      rw [hval] at h
      refine h.trans ?_
      have hinv : (0 : ℝ) ≤ ((s : ℝ))⁻¹ := (inv_pos.2 hs0).le
      linarith only [hinv]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hgt.trans hgle) hA0
  -- assemble in `ℝ≥0∞`
  have hEle : annularKickE M s j omega
      ≤ ∑' p : ℕ, ENNReal.ofReal (A * weightThird (3 * ((s : ℝ) / 8)) (p + 1)) := by
    rw [annularKickE_eq_wsumE, wsumE]
    exact ENNReal.tsum_le_tsum fun p => ENNReal.ofReal_le_ofReal (hterm p)
  have hEq : (∑' p : ℕ, ENNReal.ofReal (A * weightThird (3 * ((s : ℝ) / 8)) (p + 1)))
      = ENNReal.ofReal (∑' p : ℕ, A * weightThird (3 * ((s : ℝ) / 8)) (p + 1)) :=
    (ENNReal.ofReal_tsum_of_nonneg
      (fun p => mul_nonneg hA0 (weightThird_pos (sprime := 3 * ((s : ℝ) / 8)) (p + 1)).le)
      hsummaj).symm
  rw [hEq] at hEle
  refine hEle.trans (ENNReal.ofReal_le_ofReal ?_)
  refine hmajsum.trans (le_of_eq ?_)
  have hcube : ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ = (Real.sqrt (s : ℝ))⁻¹ * ((s : ℝ))⁻¹ := by
    have hsq : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) :=
      Real.mul_self_sqrt hs0.le
    have hne : Real.sqrt (s : ℝ) ≠ 0 := ne_of_gt hsq0
    rw [show (Real.sqrt (s : ℝ)) ^ 3 = Real.sqrt (s : ℝ) * (Real.sqrt (s : ℝ) *
      Real.sqrt (s : ℝ)) from by ring, hsq, mul_inv]
  rw [hAdef, hcube]
  ring

/-- The real reading of the good-event bound. -/
theorem annularKick_le_of_mem_eventG2 (M : ABKModel d) (s : {s : ℝ // 0 < s}) {k j : ℤ}
    (hjk : j ≤ k) (hs1 : (s : ℝ) ≤ 1) {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ eventG2 M k s 1) :
    annularKick M s j omega
      ≤ 6 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ * (weightThird ((s : ℝ) / 8) (k - j).toNat)⁻¹ := by
  have h := annularKickE_le_of_mem_eventG2 M s hjk hs1 hmem
  exact ENNReal.toReal_le_of_le_ofReal
    (by
      have hs0 : (0 : ℝ) < (s : ℝ) := s.2
      have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
      have hwy : (0 : ℝ) < weightThird ((s : ℝ) / 8) (k - j).toNat := weightThird_pos _
      have h1 : (0 : ℝ) < 6 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ :=
        mul_pos (by norm_num) (inv_pos.2 (pow_pos hsq0 3))
      exact (mul_pos h1 (inv_pos.2 hwy)).le) h

/-! ## 4. The printed two-leg display and the collapse -/

/-- `y ≤ (x)^{1/4}` from `y⁴ ≤ x`, in nested-root form. -/
theorem le_sqrt_sqrt_of_pow_four_le {x y : ℝ} (h : y ^ 4 ≤ x) :
    y ≤ Real.sqrt (Real.sqrt x) := by
  have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) h
  have hroot4 : Real.sqrt (Real.sqrt x) ^ 4 = x := by
    rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx0]
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Real.sqrt_nonneg _) ?_
  rw [hroot4]
  exact h

/-- **The collapsed variable is monotone in its coefficient, up to the fourth root
of the ratio.**  This is the one bookkeeping step that lets the collapse be read at
the explicit coefficient `216 s^{−9/2}` of the good-event bound while the `Γ₂` tail
and the first moment are supplied by `exists_kickCollapse` at its own coefficient. -/
theorem kickCollapsed_le_mul_of_coeff_le (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {lam : ℝ} (hlam : 0 ≤ lam) {K K' : ℝ} (hK : 0 < K) (hKK : K ≤ K') (j : ℤ)
    (omega : Cutoff.CutoffSample d) :
    kickCollapsed M s lam K' j omega
      ≤ Real.sqrt (Real.sqrt (K' / K)) * kickCollapsed M s lam K j omega := by
  have hhigh0 : 0 ≤ kickLegHigh M s lam j omega := kickLegHigh_nonneg M s lam j omega
  have hlow0 : 0 ≤ kickLegLow M s lam j omega := kickLegLow_nonneg M s hlam j omega
  have hratio1 : (1 : ℝ) ≤ K' / K := (one_le_div hK).2 hKK
  have hratio0 : (0 : ℝ) ≤ K' / K := by linarith only [hratio1]
  have hrho1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (K' / K)) :=
    one_le_sqrt_of_one_le (one_le_sqrt_of_one_le hratio1)
  have hsplit : K' * kickLegHigh M s lam j omega
      = (K' / K) * (K * kickLegHigh M s lam j omega) := by
    field_simp
  have hroot : Real.sqrt (Real.sqrt (K' * kickLegHigh M s lam j omega))
      = Real.sqrt (Real.sqrt (K' / K)) *
        Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) := by
    rw [hsplit, Real.sqrt_mul hratio0, Real.sqrt_mul (Real.sqrt_nonneg (K' / K))]
  have hlowmul : kickLegLow M s lam j omega
      ≤ Real.sqrt (Real.sqrt (K' / K)) * kickLegLow M s lam j omega := by
    have h := mul_le_mul_of_nonneg_right hrho1 hlow0
    rw [one_mul] at h
    exact h
  rw [kickCollapsed, kickCollapsed, hroot]
  have hrhs : Real.sqrt (Real.sqrt (K' / K)) *
      (kickLegLow M s lam j omega +
        Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)))
      = Real.sqrt (Real.sqrt (K' / K)) * kickLegLow M s lam j omega +
        Real.sqrt (Real.sqrt (K' / K)) *
          Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) := by ring
  rw [hrhs]
  exact add_le_add hlowmul le_rfl

/-- **The collapse step.**  On the good event, the Step-1 inner sum at the §4.2 weight
`3^{−½s(k−j)}` is below the collapsed variable at the **quarter** weight
`3^{−¼s(k−j)}`:

```
3^{−½s(k−j)} · annularKick_j  ≤  3^{−¼s(k−j)} · X_j ,
   X_j = X_j^{(1)} + (K X_j^{(2)})^{1/4} ,   K ≥ 216 s^{−9/2} .
```

The exponent bookkeeping is the printed one: `−½ + ⅜·¾ = −13/32 ≤ −¼`, here in the
equivalent form `W⁸B³ ≤ K` with `W = 3^{−⅛s(k−j)} ≤ 1` and `B` the good-event
bound.  The threshold `216 = 6³` is the cube of the good-event constant. -/
theorem weighted_annularKick_le_kickCollapsed (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {k j : ℤ} {lam K : ℝ} (hlam : 0 ≤ lam) (hjk : j ≤ k) (hs1 : (s : ℝ) ≤ 1)
    (hK : 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ ≤ K)
    {omega : Cutoff.CutoffSample d} (hmem : omega ∈ eventG2 M k s 1) :
    weightThird ((s : ℝ) / 2) (k - j).toNat * annularKick M s j omega
      ≤ weightThird ((s : ℝ) / 4) (k - j).toNat * kickCollapsed M s lam K j omega := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  set y : ℕ := (k - j).toNat with hydef
  set W : ℝ := weightThird ((s : ℝ) / 8) y with hWdef
  have hW0 : (0 : ℝ) < W := weightThird_pos y
  have hW1 : W ≤ 1 := weightThird_le_one (by linarith only [hs0]) y
  have hw2 : weightThird ((s : ℝ) / 4) y = W ^ 2 := by
    rw [hWdef, weightThird_sq]
    congr 1
    ring
  have hw4 : weightThird ((s : ℝ) / 2) y = W ^ 4 := by
    rw [hWdef, weightThird_pow_four]
    congr 1
    ring
  -- the good-event bound, cleared of the inverse weight
  set G : ℝ := 6 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ with hGdef
  have hG0 : (0 : ℝ) ≤ G :=
    mul_nonneg (by norm_num) (inv_pos.2 (pow_pos hsq0 3)).le
  have hBW : W * annularKick M s j omega ≤ G := by
    have hB := annularKick_le_of_mem_eventG2 M s hjk hs1 hmem
    rw [← hydef, ← hWdef, ← hGdef] at hB
    have hstep := mul_le_mul_of_nonneg_left hB hW0.le
    refine hstep.trans (le_of_eq ?_)
    field_simp
  -- the two legs
  have hlow0 : 0 ≤ kickLegLow M s lam j omega := kickLegLow_nonneg M s hlam j omega
  have hhigh0 : 0 ≤ kickLegHigh M s lam j omega := kickLegHigh_nonneg M s lam j omega
  have hhighle : kickLegHigh M s lam j omega ≤ annularKick M s j omega := by
    have h := le_min (annularKick_nonneg M s j omega) hlam
    rw [kickLegHigh]
    linarith only [h]
  have hlowstep : W ^ 4 * kickLegLow M s lam j omega ≤ W ^ 2 * kickLegLow M s lam j omega := by
    have hpow : W ^ 4 ≤ W ^ 2 := by
      have h1 : W ^ 2 * W ^ 2 ≤ W ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hW0.le hW1) (pow_nonneg hW0.le 2)
      calc W ^ 4 = W ^ 2 * W ^ 2 := by ring
        _ ≤ W ^ 2 * 1 := h1
        _ = W ^ 2 := mul_one _
    exact mul_le_mul_of_nonneg_right hpow hlow0
  have hhighstep : W ^ 4 * kickLegHigh M s lam j omega
      ≤ W ^ 2 * Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) := by
    have hkey : W ^ 2 * kickLegHigh M s lam j omega
        ≤ Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) := by
      refine le_sqrt_sqrt_of_pow_four_le ?_
      have hcube : (W * kickLegHigh M s lam j omega) ^ 3 ≤ G ^ 3 := by
        refine pow_le_pow_left₀ (mul_nonneg hW0.le hhigh0) ?_ 3
        exact le_trans (mul_le_mul_of_nonneg_left hhighle hW0.le) hBW
      have hG3 : G ^ 3 = 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ := by
        rw [hGdef, mul_pow, inv_pow, ← pow_mul]
        norm_num
      have hW5 : W ^ 5 * kickLegHigh M s lam j omega ≤ kickLegHigh M s lam j omega := by
        have h1 : W ^ 5 ≤ 1 := pow_le_one₀ hW0.le hW1
        have h2 := mul_le_mul_of_nonneg_right h1 hhigh0
        rwa [one_mul] at h2
      calc (W ^ 2 * kickLegHigh M s lam j omega) ^ 4
          = (W * kickLegHigh M s lam j omega) ^ 3 * (W ^ 5 * kickLegHigh M s lam j omega) := by
            ring
        _ ≤ G ^ 3 * (W ^ 5 * kickLegHigh M s lam j omega) :=
            mul_le_mul_of_nonneg_right hcube
              (mul_nonneg (pow_nonneg hW0.le 5) hhigh0)
        _ ≤ K * (W ^ 5 * kickLegHigh M s lam j omega) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hW0.le 5) hhigh0)
            rw [hG3]
            exact hK
        _ ≤ K * kickLegHigh M s lam j omega := by
            refine mul_le_mul_of_nonneg_left hW5 ?_
            exact le_trans (mul_nonneg (by norm_num) (inv_pos.2 (pow_pos hsq0 9)).le) hK
    have hstep := mul_le_mul_of_nonneg_left hkey (pow_nonneg hW0.le 2)
    calc W ^ 4 * kickLegHigh M s lam j omega
        = W ^ 2 * (W ^ 2 * kickLegHigh M s lam j omega) := by ring
      _ ≤ W ^ 2 * Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) := hstep
  rw [hw2, hw4, kickCollapsed, ← kickLegLow_add_kickLegHigh M s lam j omega]
  have hexpand : W ^ 4 * (kickLegLow M s lam j omega + kickLegHigh M s lam j omega)
      = W ^ 4 * kickLegLow M s lam j omega + W ^ 4 * kickLegHigh M s lam j omega := by ring
  have hexpand' : W ^ 2 * (kickLegLow M s lam j omega +
      Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)))
      = W ^ 2 * kickLegLow M s lam j omega +
        W ^ 2 * Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) := by ring
  rw [hexpand, hexpand']
  exact add_le_add hlowstep hhighstep

end

end Algsuperdiff.Section4.Provider.MinimalScale
