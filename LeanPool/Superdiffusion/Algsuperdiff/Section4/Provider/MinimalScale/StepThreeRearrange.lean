/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.StepThreeDThree

/-!
# StepThreeRearrange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-3 window rearrangement

ABK26, §4.2, `l.minimal.scale.sep`, Step 3.  The manuscript's `D₃(k)` inner
object is the doubly indexed sum

```
Σ_{l ≤ k} 3^{−α(k−l)} Σ_{i = l−1}^{k} 3^{(2−γ)i} max_{z ∈ 3^iℤ^d ∩ □_k} ‖j_i‖_{W^{2,∞}(z+□_i)}
```

with `α = s/4`, and Step 3 rearranges it into the two channels of
`StepThreeDThree`:

```
Σ_{k=n}^m (inner) ≤ K₀ ( Σ_{i=n}^m V_i + Σ_{r≥0} 3^{−α(k−n+r+1)}-weighted H_r ) ,
K₀ = 3^α(1−3^{−α})⁻¹ .
```

## The reordering is an inequality, and it is here

The manuscript performs the `(l,i)` reordering as an identity.  At the `ℝ≥0∞`
carrier the reordering is available as a genuine `Tonelli` identity, but the
*collapse* of the inner `l`-sum into the coefficient `K₀·3^{−α(k−i)}` is an
inequality (the honest coefficient is `Σ_{p ≥ q−1} 3^{−αp}`, which is at most
`3^α(1−3^{−α})⁻¹3^{−αq}`, with equality only for `q ≥ 1`).

## Why `ℝ≥0∞`

Every sum here is formed in `ℝ≥0∞`, exactly as the anchor
`annular_decomposition` forms the `D₃` term.  In `ℝ≥0∞` the depth swap needs no
summability hypothesis at all: `ENNReal.tsum_comm` and
`ENNReal.tsum_le_of_sum_range_le` are unconditional.  Only the very last step —
reading the bound in `ℝ` — needs the
majorant to be finite, and that holds almost surely by the per-layer first
moments (`ae_wsumE_ne_top`), which is proved rather than assumed.

## References

* ABK26, `l.minimal.scale.sep` Step 3.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Probability
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `D₃(k)` inner object -/

/-- The outer scales `l ≤ k`, enumerated by the depth `k − l ∈ ℕ`. -/
def lowerScaleEquiv (k : ℤ) : ℕ ≃ {n : ℤ // n ≤ k} where
  toFun p := ⟨k - (p : ℤ), by omega⟩
  invFun n := (k - n.1).toNat
  left_inv p := by
    show (k - (k - (p : ℤ))).toNat = p
    omega
  right_inv n := by
    refine Subtype.ext ?_
    show k - (((k - n.1).toNat : ℕ) : ℤ) = n.1
    have hn := n.2
    omega

/-- **The inner object of `D₃(k)`**, formed in `ℝ≥0∞` at the `ℓ¹` reading of the
anchor's `D₃` term. -/
def hessInnerE (M : ABKModel d) (alpha : ℝ) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    ℝ≥0∞ :=
  ∑' n : {n : ℤ // n ≤ k},
    ENNReal.ofReal (stepThreeWt alpha (k - n.1)) *
      ∑ i ∈ Finset.Icc (n.1 - 1) k, ENNReal.ofReal (scoreG1b M k i omega)

/-- The real-valued inner object; at the divergent samples this is `0`, which only
strengthens every upper-tail statement about it. -/
def hessInner (M : ABKModel d) (alpha : ℝ) (k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  (hessInnerE M alpha k omega).toReal

/-- The lattice maximum at the layer `k − q`, enumerated downwards from the outer
cube `k`. -/
def hessDown (M : ABKModel d) (k : ℤ) (q : ℕ) (omega : Cutoff.CutoffSample d) : ℝ :=
  scoreG1b M k (k - (q : ℤ)) omega

theorem hessDown_nonneg (M : ABKModel d) (k : ℤ) (q : ℕ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ hessDown M k q omega :=
  scoreG1b_nonneg M k (k - (q : ℤ)) omega

/-- **The layer block at depth `p`**: the finite inner sum of the manuscript's
display, enumerated downwards from `k`. -/
def hessBlock (M : ABKModel d) (k : ℤ) (p : ℕ) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑ q ∈ Finset.range (p + 2), hessDown M k q omega

/-- The downward enumeration of the inner `i`-range. -/
private theorem sum_Icc_eq_sum_range_down (k : ℤ) (p : ℕ) (f : ℤ → ℝ≥0∞) :
    ∑ i ∈ Finset.Icc (k - (p : ℤ) - 1) k, f i =
      ∑ q ∈ Finset.range (p + 2), f (k - (q : ℤ)) := by
  refine (Finset.sum_nbij' (fun q : ℕ => k - (q : ℤ)) (fun i : ℤ => (k - i).toNat)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro q hq
    simp only [Finset.mem_range] at hq
    simp only [Finset.mem_Icc]
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [Finset.mem_range]
    omega
  · intro q hq
    simp only [Finset.mem_range] at hq
    show (k - (k - (q : ℤ))).toNat = q
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    show k - (((k - i).toNat : ℕ) : ℤ) = i
    omega
  · intro q _
    rfl

/-- The inner object as a `SeriesTail` weighted series over the depth. -/
theorem hessInnerE_eq_wsumE (M : ABKModel d) (alpha : ℝ) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    hessInnerE M alpha k omega =
      wsumE (fun p => hessBlock M k p) (stepThreeWeight alpha) omega := by
  rw [hessInnerE, ← (lowerScaleEquiv k).tsum_eq
      (fun n : {n : ℤ // n ≤ k} =>
        ENNReal.ofReal (stepThreeWt alpha (k - n.1)) *
          ∑ i ∈ Finset.Icc (n.1 - 1) k, ENNReal.ofReal (scoreG1b M k i omega)),
    wsumE]
  refine tsum_congr fun p => ?_
  have hwt : stepThreeWt alpha (k - (k - (p : ℤ))) = stepThreeWeight alpha p := by
    have hz : k - (k - (p : ℤ)) = (p : ℤ) := by ring
    rw [stepThreeWt, stepThreeWeight, hz]
    norm_num
  show ENNReal.ofReal (stepThreeWt alpha (k - (k - (p : ℤ)))) *
      ∑ i ∈ Finset.Icc (k - (p : ℤ) - 1) k, ENNReal.ofReal (scoreG1b M k i omega) = _
  rw [hwt, sum_Icc_eq_sum_range_down k p (fun i => ENNReal.ofReal (scoreG1b M k i omega)),
    hessBlock, ENNReal.ofReal_mul (stepThreeWeight_nonneg alpha p),
    ENNReal.ofReal_sum_of_nonneg (fun q _ => hessDown_nonneg M k q omega)]
  rfl

/-! ## 2. The depth-collapse coefficient -/

/-- **The honest depth coefficient**: the total weight the manuscript's inner
`l`-sum puts on the layer at depth `q` is at most `3^α(1−3^{−α})⁻¹` times the
layer's own weight.  This is a finite-range statement, uniform in the
truncation level `N`. -/
private theorem sum_range_ite_weight_le {alpha : ℝ} (halpha : 0 < alpha) (N q : ℕ) :
    ∑ p ∈ Finset.range N, (if q < p + 2 then stepThreeWeight alpha p else 0) ≤
      (3 : ℝ) ^ alpha * geomTailConst alpha * stepThreeWeight alpha q := by
  classical
  rw [← Finset.sum_filter]
  set A : Finset ℕ := (Finset.range N).filter fun p => q < p + 2 with hAdef
  have hkey : ∀ p ∈ A, stepThreeWeight alpha p =
      ((3 : ℝ) ^ alpha * stepThreeWeight alpha q) * stepThreeWeight alpha (p + 1 - q) := by
    intro p hp
    simp only [hAdef, Finset.mem_filter] at hp
    have hq : q ≤ p + 1 := by omega
    have hcast : ((p + 1 - q : ℕ) : ℝ) = (p : ℝ) + 1 - (q : ℝ) := by
      have hz : ((p + 1 - q : ℕ) : ℤ) = (p : ℤ) + 1 - (q : ℤ) := by omega
      exact_mod_cast hz
    rw [stepThreeWeight, stepThreeWeight, stepThreeWeight, hcast,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun p : ℕ => p + 1 - q) (A : Set ℕ) := by
    intro p hp p' hp' h
    rw [Finset.mem_coe, hAdef, Finset.mem_filter] at hp hp'
    have h' : p + 1 - q = p' + 1 - q := h
    omega
  have himage : ∑ p ∈ A, stepThreeWeight alpha (p + 1 - q) =
      ∑ t ∈ A.image (fun p => p + 1 - q), stepThreeWeight alpha t :=
    (Finset.sum_image hinj).symm
  have hgeo : ∑ t ∈ A.image (fun p => p + 1 - q), stepThreeWeight alpha t ≤
      geomTailConst alpha := sum_threePow_neg_le halpha _
  have hc0 : 0 ≤ (3 : ℝ) ^ alpha * stepThreeWeight alpha q :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (stepThreeWeight_nonneg alpha q)
  calc ((3 : ℝ) ^ alpha * stepThreeWeight alpha q) *
        ∑ p ∈ A, stepThreeWeight alpha (p + 1 - q)
      ≤ ((3 : ℝ) ^ alpha * stepThreeWeight alpha q) * geomTailConst alpha := by
        rw [himage]
        exact mul_le_mul_of_nonneg_left hgeo hc0
    _ = (3 : ℝ) ^ alpha * geomTailConst alpha * stepThreeWeight alpha q := by ring

/-- The `ℝ≥0∞` form of the depth coefficient, at the full depth series. -/
private theorem tsum_ite_weight_le {alpha : ℝ} (halpha : 0 < alpha) (q : ℕ) :
    ∑' p : ℕ, (if q < p + 2 then ENNReal.ofReal (stepThreeWeight alpha p) else 0) ≤
      ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha * stepThreeWeight alpha q) := by
  classical
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have hpush : ∀ p : ℕ,
      (if q < p + 2 then ENNReal.ofReal (stepThreeWeight alpha p) else 0)
        = ENNReal.ofReal (if q < p + 2 then stepThreeWeight alpha p else 0) := by
    intro p
    by_cases hp : q < p + 2
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp, ENNReal.ofReal_zero]
  rw [Finset.sum_congr rfl fun p _ => hpush p,
    ← ENNReal.ofReal_sum_of_nonneg
      (fun p _ => by
        by_cases hp : q < p + 2
        · rw [ite_eq_left hp]
          exact stepThreeWeight_nonneg alpha p
        · rw [ite_eq_right hp])]
  exact ENNReal.ofReal_le_ofReal (sum_range_ite_weight_le halpha N q)

/-! ## 3. The depth swap -/

/-- **The depth swap.**  The manuscript's inner double sum is at most
`K₀ = 3^α(1−3^{−α})⁻¹` times the single geometrically weighted sum of the lattice
maxima, at every sample point, unconditionally. -/
theorem hessInnerE_le_swap (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    hessInnerE M alpha k omega ≤
      ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha) *
        wsumE (fun q => hessDown M k q) (stepThreeWeight alpha) omega := by
  classical
  have hK0 : (0 : ℝ) ≤ (3 : ℝ) ^ alpha * geomTailConst alpha :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (geomTailConst_pos halpha).le
  -- Step A: write the inner object as a double `ℝ≥0∞` series
  have hA : hessInnerE M alpha k omega =
      ∑' p : ℕ, ∑' q : ℕ,
        (if q < p + 2 then
            ENNReal.ofReal (stepThreeWeight alpha p) * ENNReal.ofReal (hessDown M k q omega)
          else 0) := by
    rw [hessInnerE_eq_wsumE, wsumE]
    refine tsum_congr fun p => ?_
    have hzero : ∀ q : ℕ, q ∉ Finset.range (p + 2) →
        (if q < p + 2 then
            ENNReal.ofReal (stepThreeWeight alpha p) *
              ENNReal.ofReal (hessDown M k q omega) else 0) = 0 := by
      intro q hq
      simp only [Finset.mem_range, not_lt] at hq
      rw [ite_eq_right (by omega)]
    rw [tsum_eq_sum hzero, hessBlock, ENNReal.ofReal_mul (stepThreeWeight_nonneg alpha p),
      ENNReal.ofReal_sum_of_nonneg (fun q _ => hessDown_nonneg M k q omega),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_range] at hq
    rw [ite_eq_left hq]
  -- Step B: swap the two series and bound the total coefficient of each layer
  rw [hA, ENNReal.tsum_comm, wsumE, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun q => ?_
  have hpull : ∑' p : ℕ,
        (if q < p + 2 then
            ENNReal.ofReal (stepThreeWeight alpha p) *
              ENNReal.ofReal (hessDown M k q omega) else 0)
      = (∑' p : ℕ, (if q < p + 2 then ENNReal.ofReal (stepThreeWeight alpha p) else 0)) *
          ENNReal.ofReal (hessDown M k q omega) := by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun p => ?_
    by_cases hp : q < p + 2
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp, zero_mul]
  rw [hpull]
  have hstep : (∑' p : ℕ, (if q < p + 2 then ENNReal.ofReal (stepThreeWeight alpha p) else 0)) *
        ENNReal.ofReal (hessDown M k q omega)
      ≤ ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha * stepThreeWeight alpha q) *
        ENNReal.ofReal (hessDown M k q omega) :=
    mul_le_mul' (tsum_ite_weight_le halpha q) le_rfl
  refine le_trans hstep ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg hK0 (stepThreeWeight_nonneg alpha q)),
    ← ENNReal.ofReal_mul hK0]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-! ## 4. The window split -/

/-- The `q`-series of one outer cube, split at the window's lower end: the layers
`i ≥ n` are the in-window channel's summands and the layers `i ≤ n−1` are the
below-window channel's. -/
private theorem tsum_split_window (M : ABKModel d) (alpha : ℝ) {n k : ℤ} (hnk : n ≤ k)
    (omega : Cutoff.CutoffSample d) :
    ∑' q : ℕ, ENNReal.ofReal (stepThreeWeight alpha q * hessDown M k q omega)
      = (∑ i ∈ Finset.Icc n k,
            ENNReal.ofReal (stepThreeWt alpha (k - i) * scoreG1b M k i omega))
        + ∑' r : ℕ,
            ENNReal.ofReal (stepThreeWeight alpha ((k - n).toNat + 1 + r) *
              scoreG1b M k (n - 1 - (r : ℤ)) omega) := by
  classical
  set f : ℕ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (stepThreeWeight alpha q * hessDown M k q omega) with hfdef
  set Nk : ℕ := (k - n).toNat + 1 with hNk
  have hsplit : (∑ q ∈ Finset.range Nk, f q) + ∑' r : ℕ, f (r + Nk) = ∑' q : ℕ, f q :=
    (ENNReal.summable (f := fun r => f (r + Nk))).sum_add_tsum_nat_add'
  rw [← hsplit]
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the in-window layers, reindexed by `i = k − q`
    refine (Finset.sum_nbij' (fun i : ℤ => (k - i).toNat) (fun q : ℕ => k - (q : ℤ))
      ?_ ?_ ?_ ?_ ?_).symm
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      simp only [Finset.mem_range, hNk]
      omega
    · intro q hq
      simp only [Finset.mem_range, hNk] at hq
      simp only [Finset.mem_Icc]
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      show k - (((k - i).toNat : ℕ) : ℤ) = i
      omega
    · intro q hq
      simp only [Finset.mem_range, hNk] at hq
      show (k - (k - (q : ℤ))).toNat = q
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      have hz : k - (((k - i).toNat : ℕ) : ℤ) = i := by omega
      have hcast : (((k - i).toNat : ℕ) : ℝ) = ((k - i : ℤ) : ℝ) := by
        have hz : (((k - i).toNat : ℕ) : ℤ) = k - i := by omega
        exact_mod_cast hz
      have hwt : stepThreeWeight alpha ((k - i).toNat) = stepThreeWt alpha (k - i) := by
        rw [stepThreeWeight, stepThreeWt, hcast]
      rw [hfdef]
      simp only [hessDown]
      rw [hz, hwt]
  · -- the below-window layers, reindexed by the depth `r`
    refine tsum_congr fun r => ?_
    have hidx : k - ((r + Nk : ℕ) : ℤ) = n - 1 - (r : ℤ) := by
      have hk : ((Nk : ℕ) : ℤ) = k - n + 1 := by
        rw [hNk]
        push_cast
        omega
      push_cast [hk]
      ring
    have hwt : stepThreeWeight alpha (r + Nk) = stepThreeWeight alpha (Nk + r) := by
      rw [Nat.add_comm]
    rw [hfdef]
    simp only [hessDown]
    rw [hidx, hwt, hNk]

/-- The below-window weight splits off the outer-cube factor. -/
private theorem weight_shift (alpha : ℝ) {n k : ℤ} (hnk : n ≤ k) (r : ℕ) :
    stepThreeWeight alpha ((k - n).toNat + 1 + r) =
      stepThreeWeight alpha (r + 1) * stepThreeWt alpha (k - n) := by
  have hcast : (((k - n).toNat + 1 + r : ℕ) : ℝ)
      = ((r + 1 : ℕ) : ℝ) + ((k - n : ℤ) : ℝ) := by
    have hz : (((k - n).toNat + 1 + r : ℕ) : ℤ) = ((r + 1 : ℕ) : ℤ) + (k - n) := by omega
    exact_mod_cast hz
  rw [stepThreeWeight, stepThreeWeight, stepThreeWt, hcast,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- Over the window `[n,m]` the manuscript's `D₃` inner objects are bounded, in
`ℝ≥0∞` and at every sample point, by `K₀ = 3^α(1−3^{−α})⁻¹` times the sum of
the two channels of `StepThreeDThree`. -/
theorem sum_hessInnerE_le (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    ∑ k ∈ Finset.Icc n m, hessInnerE M alpha k omega ≤
      ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha) *
        ((∑ i ∈ Finset.Icc n m, ENNReal.ofReal (hessWindow M alpha n m i omega)) +
          wsumE (fun r => hessHead M alpha n m r)
            (fun r => stepThreeWeight alpha (r + 1)) omega) := by
  classical
  have hper : ∀ k ∈ Finset.Icc n m, hessInnerE M alpha k omega ≤
      ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha) *
        ((∑ i ∈ Finset.Icc n k,
              ENNReal.ofReal (stepThreeWt alpha (k - i) * scoreG1b M k i omega)) +
          ∑' r : ℕ,
            ENNReal.ofReal (stepThreeWeight alpha ((k - n).toNat + 1 + r) *
              scoreG1b M k (n - 1 - (r : ℤ)) omega)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h1 := hessInnerE_le_swap M halpha k omega
    rw [wsumE, tsum_split_window M alpha hk.1 omega] at h1
    exact h1
  have hstep := Finset.sum_le_sum hper
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hstep
  refine le_trans hstep ?_
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the in-window channel, after the finite triangular swap
    have hcomm := Finset.sum_comm' (s := Finset.Icc n m) (t := fun k => Finset.Icc n k)
      (t' := Finset.Icc n m) (s' := fun i => Finset.Icc i m)
      (f := fun k i => ENNReal.ofReal (stepThreeWt alpha (k - i) * scoreG1b M k i omega))
      (by
        intro k i
        simp only [Finset.mem_Icc]
        constructor
        · intro h; exact ⟨⟨h.2.2, h.1.2⟩, ⟨h.2.1, le_trans h.2.2 h.1.2⟩⟩
        · intro h; exact ⟨⟨le_trans h.2.1 h.1.1, h.1.2⟩, ⟨h.2.1, h.1.1⟩⟩)
    rw [hcomm]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    have hmax : max n i = i := max_eq_right hi.1
    rw [hessWindow, hmax,
      ENNReal.ofReal_sum_of_nonneg (fun k _ =>
        mul_nonneg (stepThreeWt_pos alpha (k - i)).le (scoreG1b_nonneg M k i omega))]
  · -- the below-window channel, after the finite/infinite swap
    rw [wsumE, (Summable.tsum_finsetSum (fun _ (_ : _ ∈ Finset.Icc n m) =>
      ENNReal.summable)).symm]
    refine tsum_congr fun r => ?_
    have hterm : ∀ k ∈ Finset.Icc n m,
        ENNReal.ofReal (stepThreeWeight alpha ((k - n).toNat + 1 + r) *
            scoreG1b M k (n - 1 - (r : ℤ)) omega)
          = ENNReal.ofReal (stepThreeWeight alpha (r + 1) *
              (stepThreeWt alpha (k - n) * scoreG1b M k (n - 1 - (r : ℤ)) omega)) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [weight_shift alpha hk.1 r, mul_assoc]
    rw [Finset.sum_congr rfl hterm, hessHead, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg (fun k _ =>
        mul_nonneg (stepThreeWeight_nonneg alpha (r + 1))
          (mul_nonneg (stepThreeWt_pos alpha (k - n)).le
            (scoreG1b_nonneg M k (n - 1 - (r : ℤ)) omega)))]

/-! ## 5. Almost sure finiteness of the below-window channel -/

/-- The below-window channel converges almost surely, at every window.  Proved
from its per-depth first moments, which come from the per-depth `Γ₂` tails. -/
theorem ae_hessHeadSeries_finite (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha)
    {n m : ℤ} (hnm : n ≤ m) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      wsumE (fun r => hessHead M alpha n m r) (fun r => stepThreeWeight alpha (r + 1)) omega
        ≠ (⊤ : ℝ≥0∞) := by
  have hCv : 0 < hessAmp d := hessAmp_pos d
  have hmom : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hshift : ∀ r : ℕ, stepThreeWeight alpha (r + 1)
      = (3 : ℝ) ^ (-(alpha * (1 : ℝ))) * stepThreeWeight alpha r := by
    intro r
    have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    rw [stepThreeWeight, stepThreeWeight, hcast,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hsum : Summable fun r : ℕ =>
      stepThreeWeight alpha (r + 1) * (gammaMomentConst 2 * step3HeadAmp (hessAmp d) alpha r) := by
    have hbase := (summable_weight_step3HeadAmp (Cv := hessAmp d) halpha).mul_left
      ((3 : ℝ) ^ (-(alpha * (1 : ℝ))) * gammaMomentConst 2)
    refine hbase.congr fun r => ?_
    rw [hshift r, stepThreeWeight]
    ring
  refine ae_wsumE_ne_top (fun r omega => hessHead_nonneg M alpha n m r omega)
    (fun r => measurable_hessHead M alpha n m r) (fun r => ?_)
    (fun r => stepThreeWeight_nonneg alpha (r + 1)) (fun r => ?_) (fun r => ?_) hsum
  · exact integrable_of_isBigOWith_of_nonneg (step3HeadAmp_pos halpha hCv r)
      (hessHead_nonneg M alpha n m r) (measurable_hessHead M alpha n m r)
      (isBigOWith_hessHead M halpha hnm r)
  · exact mul_nonneg hmom.le (step3HeadAmp_nonneg halpha hCv.le r)
  · exact integral_le_of_isBigOWith_of_nonneg (step3HeadAmp_pos halpha hCv r)
      (hessHead_nonneg M alpha n m r) (measurable_hessHead M alpha n m r)
      (isBigOWith_hessHead M halpha hnm r)

/-- The real form of the rearrangement: almost surely, the window sum of the
manuscript's `D₃` inner objects is below `K₀` times the two channels. -/
theorem ae_sum_hessInner_le (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) {n m : ℤ}
    (hnm : n ≤ m) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∑ k ∈ Finset.Icc n m, hessInner M alpha k omega ≤
        ((3 : ℝ) ^ alpha * geomTailConst alpha) *
          ((∑ i ∈ Finset.Icc n m, hessWindow M alpha n m i omega) +
            hessHeadSeries M alpha n m omega) := by
  have hK0 : (0 : ℝ) ≤ (3 : ℝ) ^ alpha * geomTailConst alpha :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (geomTailConst_pos halpha).le
  filter_upwards [ae_hessHeadSeries_finite M halpha hnm] with omega hfin
  set A : ℝ≥0∞ := ∑ i ∈ Finset.Icc n m, ENNReal.ofReal (hessWindow M alpha n m i omega)
    with hAdef
  set B : ℝ≥0∞ := wsumE (fun r => hessHead M alpha n m r)
    (fun r => stepThreeWeight alpha (r + 1)) omega with hBdef
  have hAne : A ≠ (⊤ : ℝ≥0∞) := by
    rw [hAdef]
    refine (ENNReal.sum_lt_top.2 fun i _ => ?_).ne
    exact ENNReal.ofReal_lt_top
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha) * (A + B) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hAne, hfin⟩)
  have hle := sum_hessInnerE_le M halpha n m omega
  rw [← hAdef, ← hBdef] at hle
  have hkne : ∀ k ∈ Finset.Icc n m, hessInnerE M alpha k omega ≠ (⊤ : ℝ≥0∞) := by
    intro k hk
    refine ne_top_of_le_ne_top hRne (le_trans ?_ hle)
    exact Finset.single_le_sum (f := fun k => hessInnerE M alpha k omega)
      (fun j _ => (zero_le : (0 : ℝ≥0∞) ≤ hessInnerE M alpha j omega)) hk
  have htoReal : ∑ k ∈ Finset.Icc n m, hessInner M alpha k omega
      = (∑ k ∈ Finset.Icc n m, hessInnerE M alpha k omega).toReal := by
    rw [ENNReal.toReal_sum hkne]
    rfl
  rw [htoReal]
  refine le_trans (ENNReal.toReal_mono hRne hle) (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_add hAne hfin, hAdef,
    ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  refine congrArg (fun t : ℝ => ((3 : ℝ) ^ alpha * geomTailConst alpha) * t) ?_
  refine congrArg₂ (· + ·) ?_ rfl
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ENNReal.toReal_ofReal (hessWindow_nonneg M alpha n m i omega)

/-! ## 6. The `D₃` bound: `e.D3k.kicked` at the manuscript's own `D₃` -/

/-- **`e.D3k.kicked`**, at an arbitrary nonnegative prefactor and at the
manuscript's own `D₃` inner object.  At `pref = c⋆^{−1/2}s^{−1}γ^{1/2}` and `α
= s/4` the two output scales are, by `stepThree_det_closed` and
`stepThree_fluc_closed`,

```
deterministic : C c⋆^{−1/2}s^{−7/2}γ^{1/2}                    (the printed level)
fluctuation   : C c⋆^{−1/2}s^{−9/2}γ^{1/2}(m−n)^{−1/2}        (the E5 finding)
```

i.e. the printed display with the fluctuation exponent corrected from `s^{−7/2}`
to `s^{−9/2}`. -/
theorem exists_D3k_kicked (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) {n m : ℤ}
    (hnm : n < m) {pref : ℝ} (hpref : 0 ≤ pref) :
    ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
      (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          cesaroAvg (fun k => pref * hessInner M alpha k omega) n m ≤
            Xdet omega + Xfluc omega) ∧
        (∀ omega, Xdet omega ≤
          pref * (((3 : ℝ) ^ alpha * geomTailConst alpha) *
            (gammaMomentConst 2 * step3WindowAmp (hessAmp d) alpha))) ∧
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
          (pref * (cesaroTailEngineConst *
            (((3 : ℝ) ^ alpha * geomTailConst alpha) * step3WindowAmp (hessAmp d) alpha +
              ((3 : ℝ) ^ alpha * geomTailConst alpha) * step3TailAmp (hessAmp d) alpha)) *
            (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hnm' : n ≤ m := le_of_lt hnm
  have hK0 : (0 : ℝ) ≤ (3 : ℝ) ^ alpha * geomTailConst alpha :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (geomTailConst_pos halpha).le
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ :=
    exists_stepThree_channels_kicked M halpha hnm hK0
  refine ⟨fun omega => pref * Xdet omega, fun omega => pref * Xfluc omega, ?_, ?_, ?_⟩
  · filter_upwards [ae_sum_hessInner_le M halpha hnm'] with omega hsum
    have hcard : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm'
    have hinv : (0 : ℝ) ≤ 1 / ((m - n + 1 : ℤ) : ℝ) := by positivity
    have hstep : cesaroAvg (fun k => hessInner M alpha k omega) n m ≤
        ((3 : ℝ) ^ alpha * geomTailConst alpha) *
            cesaroAvg (fun i => hessWindow M alpha n m i omega) n m
          + (1 / (((m - n + 1 : ℤ) : ℝ))) *
              (((3 : ℝ) ^ alpha * geomTailConst alpha) * hessHeadSeries M alpha n m omega) := by
      have hmul := mul_le_mul_of_nonneg_left hsum hinv
      simp only [cesaroAvg]
      calc 1 / ((m - n + 1 : ℤ) : ℝ) * ∑ k ∈ Finset.Icc n m, hessInner M alpha k omega
          ≤ 1 / ((m - n + 1 : ℤ) : ℝ) *
              (((3 : ℝ) ^ alpha * geomTailConst alpha) *
                ((∑ i ∈ Finset.Icc n m, hessWindow M alpha n m i omega) +
                  hessHeadSeries M alpha n m omega)) := hmul
        _ = ((3 : ℝ) ^ alpha * geomTailConst alpha) *
              (1 / ((m - n + 1 : ℤ) : ℝ) *
                ∑ i ∈ Finset.Icc n m, hessWindow M alpha n m i omega)
            + 1 / ((m - n + 1 : ℤ) : ℝ) *
              (((3 : ℝ) ^ alpha * geomTailConst alpha) *
                hessHeadSeries M alpha n m omega) := by ring
    rw [cesaroAvg_const_mul]
    calc pref * cesaroAvg (fun k => hessInner M alpha k omega) n m
        ≤ pref * (Xdet omega + Xfluc omega) :=
          mul_le_mul_of_nonneg_left (le_trans hstep (hdom omega)) hpref
      _ = pref * Xdet omega + pref * Xfluc omega := by ring
  · intro omega
    exact mul_le_mul_of_nonneg_left (hdet omega) hpref
  · have h := IsBigO.const_mul hpref hfluc
    refine h.mono_scale (le_of_eq ?_)
    ring

end

end Algsuperdiff.Section4.Provider.MinimalScale
