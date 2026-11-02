/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.ProportionGoodScales
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.WindowTails
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.ZScores

/-!
# ZDensityLeg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `Z^{(2)}` leg: the bad-density random scale and its geometric tail

ABK26, §4.2.  The chain is:

1. **The `θ`-instantiation.**  The proportion anchor
   `Algsuperdiff.Frozen.Section4.proportion_of_good_scales` is consumed at `θ =
   δ`, `ep = s√δ`, `m₀ = m − j`, `Mw = j`.
2. **The centre-uniform upgrade.**  The per-centre mass is centre-independent
   by the proved translation identities (`Provider.GoodEvents`), so each centre
   of `3^{n−1}ℤ^d ∩ □_m` carries the origin's bound; the union over centres
   uses the *explicit* enumeration `Provider.Proportion.latticeCubeFinset` (the
   count `3^{d(j+2)}`) and `lt_iSup_iff`.  **Neither the cardinality bound nor
   the covering property is a hypothesis anywhere in this file**: both are
   theorems (`card_latticeCubeFinset_le`, `exists_center_of_badDensity`).
3. **The geometric closure.**  `Algsuperdiff.Probability.WindowTails` turns the
   per-window bound into the tail of `minimalScale`, at the frozen
   prefactor-tail shape `C exp(−(N−1) s⁹ c⋆² δ² /(Cγ))`.

## The `s`-exponent

The centre union bound converges **only** when the per-centre rate beats the
centre count, i.e. only when

`c⋆² s⁹ δ² / γ ≥ K(d)`  (K(d) ≈ 4 d log 3),

equivalently `γ ≤ K(d)⁻¹ c⋆² s⁹ δ²`.  The `θ`-instantiation itself (step 1)
closes at `s⁸` — see `measure_center_density_le`, whose regime hypothesis is
the printed one verbatim.  It is step 2 that needs `s⁹`.  Accordingly every
public of this file downstream of the union bound carries the regime clause at
`s⁹`, i.e. the printed clause with the single numeral `8` replaced by `9`; this
is the ONLY deviation from the printed hypotheses and it is stated at each
site.  The manuscript itself uses the matching condition at its own exponent:
it invokes `δ ≥ C s^{−7/2} c⋆^{−1} γ^{1/2}`, i.e. `γ ≤ C^{−2} c⋆² s⁷ δ²`, which
is `e.scale.sep.cond` read at the *rate* exponent `s⁷`.

## Contents

* `anchorConst` — the proportion anchor's constant, normalised to `≥ 1`, with
  `anchorConst_spec`, the anchor's own conclusion re-run at it.
* `measure_center_density_le` — **the `θ`-instantiation**: the per-centre
  bad-density mass at rate `c⋆² s⁹ δ² (j+1)/(anchorConst · γ)`, from the
  printed regime clause (`s⁸`).
* `card_centerFinset_le`, `exists_center_finset_of_badDensity` — `hcard` and
  `hcover`, as theorems.
* `zTwoConst` — the assembled constant, with its four domination lemmas.
* `measure_tail_badDensity_le` — **the `Z²` tail at the frozen prefactor-tail
  shape**.

## References

* ABK26, `p.minimal.scale.separation.sec4`.
* ABK26, `p.independence.between.scales`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Generic window arithmetic -/

/-- The window `[m − j, m]` of integers, re-indexed by `Finset.range (j+1)`. -/
private theorem sum_Icc_sub_eq_sum_range {A : Type*} [AddCommMonoid A] (f : ℤ → A) (m : ℤ)
    (j : ℕ) :
    ∑ k ∈ Finset.Icc (m - (j : ℤ)) m, f k
      = ∑ i ∈ Finset.range (j + 1), f (m - (j : ℤ) + (i : ℤ)) := by
  have hinj : Function.Injective (fun i : ℕ => m - (j : ℤ) + (i : ℤ)) := by
    intro a b hab
    have h : m - (j : ℤ) + (a : ℤ) = m - (j : ℤ) + (b : ℤ) := hab
    omega
  have hmap : Finset.Icc (m - (j : ℤ)) m
      = (Finset.range (j + 1)).map ⟨fun i : ℕ => m - (j : ℤ) + (i : ℤ), hinj⟩ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h0, hn⟩
      exact ⟨(k - (m - (j : ℤ))).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hmap, Finset.sum_map]
  rfl

/-- The `ℝ`-valued indicator of a set at `1` takes only the values `1` and
`0`. -/
private theorem indicator_one_eq_or {Omega : Type*} (G : Set Omega) (omega : Omega) :
    Set.indicator G (fun _ => (1 : ℝ)) omega = 1 ∨
      Set.indicator G (fun _ => (1 : ℝ)) omega = 0 := by
  by_cases homega : omega ∈ G
  · exact Or.inl (Set.indicator_of_mem homega _)
  · exact Or.inr (Set.indicator_of_notMem homega _)

/-- The `ℝ≥0∞`-valued indicator of the *complement* is the `ofReal` of
`1 − (the ℝ-valued indicator)`. -/
private theorem indicator_compl_eq_ofReal {Omega : Type*} (G : Set Omega) (omega : Omega) :
    Set.indicator Gᶜ (fun _ => (1 : ℝ≥0∞)) omega
      = ENNReal.ofReal (1 - Set.indicator G (fun _ => (1 : ℝ)) omega) := by
  by_cases homega : omega ∈ G
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 homega),
      Set.indicator_of_mem homega, sub_self, ENNReal.ofReal_zero]
  · rw [Set.indicator_of_mem homega, Set.indicator_of_notMem homega, sub_zero,
      ENNReal.ofReal_one]

/-- The window count of bad scales, as an `ofReal`. -/
private theorem sum_indicator_compl_eq_ofReal {Omega : Type*} (G : ℕ → Set Omega)
    (omega : Omega) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), Set.indicator (G i)ᶜ (fun _ => (1 : ℝ≥0∞)) omega
      = ENNReal.ofReal (((j : ℝ) + 1) -
          ∑ i ∈ Finset.range (j + 1), Set.indicator (G i) (fun _ => (1 : ℝ)) omega) := by
  have hnn : ∀ i ∈ Finset.range (j + 1),
      (0 : ℝ) ≤ 1 - Set.indicator (G i) (fun _ => (1 : ℝ)) omega := by
    intro i _
    rcases indicator_one_eq_or (G i) omega with h | h <;> rw [h] <;> norm_num
  have hstep : ∑ i ∈ Finset.range (j + 1), Set.indicator (G i)ᶜ (fun _ => (1 : ℝ≥0∞)) omega
      = ∑ i ∈ Finset.range (j + 1),
          ENNReal.ofReal (1 - Set.indicator (G i) (fun _ => (1 : ℝ)) omega) :=
    Finset.sum_congr rfl fun i _ => indicator_compl_eq_ofReal (G i) omega
  have hsum : ∑ i ∈ Finset.range (j + 1),
        (1 - Set.indicator (G i) (fun _ => (1 : ℝ)) omega)
      = ((j : ℝ) + 1) -
        ∑ i ∈ Finset.range (j + 1), Set.indicator (G i) (fun _ => (1 : ℝ)) omega := by
    rw [Finset.sum_sub_distrib (fun _ => (1 : ℝ))
      (fun i => Set.indicator (G i) (fun _ => (1 : ℝ)) omega), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hstep, ← ENNReal.ofReal_sum_of_nonneg hnn, hsum]

/-- The scalar rearrangement behind the bad-density-to-good-proportion
conversion. -/
private theorem avg_le_of_lt_aux {g x delta : ℝ} (hx : 0 < x)
    (h : delta < x⁻¹ * (x - g)) : x⁻¹ * g ≤ 1 - delta := by
  have hkey : x⁻¹ * (x - g) = 1 - x⁻¹ * g := by
    rw [mul_sub, inv_mul_cancel₀ (ne_of_gt hx)]
  rw [hkey] at h
  linarith only [h]

/-- **The bad-density threshold, converted to the anchor's good-proportion
threshold.**  If the `ℝ≥0∞`-valued Cesàro average of the *complement*
indicators exceeds `ENNReal.ofReal delta`, then the `ℝ`-valued Cesàro average of the
indicators is at most `1 − delta`.  The two are complementary window counts, so
the implication is exact; no measurability and no finiteness is used. -/
private theorem avg_good_le_of_avg_bad_lt {Omega : Type*} {delta : ℝ}
    (hdelta : 0 ≤ delta) (j : ℕ) (G : ℕ → Set Omega) (omega : Omega)
    (h : ENNReal.ofReal delta < ((j : ℝ≥0∞) + 1)⁻¹ *
      ∑ i ∈ Finset.range (j + 1), Set.indicator (G i)ᶜ (fun _ => (1 : ℝ≥0∞)) omega) :
    (1 / ((j : ℝ) + 1)) *
        ∑ i ∈ Finset.range (j + 1), Set.indicator (G i) (fun _ => (1 : ℝ)) omega
      ≤ 1 - delta := by
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hcast : ((j : ℝ≥0∞) + 1) = ENNReal.ofReal ((j : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [sum_indicator_compl_eq_ofReal, hcast, ← ENNReal.ofReal_inv_of_pos hjpos,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hjpos)),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hdelta] at h
  rw [one_div]
  exact avg_le_of_lt_aux hjpos h

/-! ## 2. The proportion anchor's constant -/

/-- **The proportion anchor's constant, normalised to be at least `1`.** The
anchor's statement is monotone in its constant (both parameter clauses tighten
and the delivered rate weakens as the constant grows), so the normalisation
costs nothing — see `anchorConst_spec`. -/
noncomputable def anchorConst (d : ℕ) : ℝ :=
  max 1 (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose

theorem one_le_anchorConst (d : ℕ) : 1 ≤ anchorConst d := le_max_left _ _

theorem anchorConst_pos (d : ℕ) : 0 < anchorConst d :=
  lt_of_lt_of_le zero_lt_one (one_le_anchorConst d)

/-- **`p.independence.between.scales`, re-run at `anchorConst d`.**  This is the
anchor's own conclusion; the only change is that the constant is `anchorConst d
≥ 1`. -/
theorem anchorConst_spec (d : ℕ) (M : ABKModel d) (s ep theta : ℝ)
    (hsr : s ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hepr : ep ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hthr : theta ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgam : M.gamma ≤ (anchorConst d)⁻¹ *
      min (Disorder.cstar M ^ (10 : ℕ))
        (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)))
    (hwin : 8 * M.gamma ≤ s)
    (hlev : anchorConst d * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) *
      ep⁻¹ ^ (2 : ℕ) * M.gamma ≤ theta)
    (m0 : ℤ) (Mw : ℕ) (hs : 0 < s) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega |
          (1 / ((Mw : ℝ) + 1)) *
              ∑ k ∈ Finset.range (Mw + 1),
                (Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Support.cgEllipLowerConstant d) (m0 + (k : ℤ)) 0 ⟨s, hs⟩ ep).indicator
                  (fun _ => (1 : ℝ)) omega ≤
            1 - theta} ≤
      ENNReal.ofReal
        (6 *
          Real.exp
            (-(Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta *
                  ((Mw : ℝ) + 1)) /
              (anchorConst d * M.gamma))) := by
  obtain ⟨hC0pos, hspec⟩ :=
    (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose_spec
  have hle : (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose
      ≤ anchorConst d := le_max_right _ _
  have hcs0 : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs0 : (0 : ℝ) < s := hsr.1
  have hep0 : (0 : ℝ) < ep := hepr.1
  -- the regime clause at the smaller constant
  have hmin0 : (0 : ℝ) ≤ min (Disorder.cstar M ^ (10 : ℕ))
      (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)) :=
    le_min (pow_nonneg hcs0.le 10)
      (mul_nonneg (mul_nonneg (pow_nonneg hcs0.le 2) (pow_nonneg hs0.le 5))
        (pow_nonneg hep0.le 2))
  have hgam' : M.gamma ≤
      (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose⁻¹ *
        min (Disorder.cstar M ^ (10 : ℕ))
          (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)) :=
    le_trans hgam
      (mul_le_mul_of_nonneg_right (inv_anti₀ hC0pos hle) hmin0)
  -- the level clause at the smaller constant
  have hA0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) *
      M.gamma :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 hcs0.le) 2)
      (pow_nonneg (inv_nonneg.2 hs0.le) 6)) (pow_nonneg (inv_nonneg.2 hep0.le) 2)) hgam0.le
  have hlev' : (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose *
      (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) * M.gamma ≤ theta := by
    calc (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose *
          (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) * M.gamma
        = (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose *
            ((Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) * M.gamma) := by
          ring
      _ ≤ anchorConst d *
            ((Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) * M.gamma) :=
          mul_le_mul_of_nonneg_right hle hA0
      _ = anchorConst d * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) *
            ep⁻¹ ^ (2 : ℕ) * M.gamma := by ring
      _ ≤ theta := hlev
  refine le_trans (hspec M s ep theta hsr hepr hthr hgam' hwin hlev' m0 Mw hs) ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
  have hnum0 : (0 : ℝ) ≤ Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta *
      ((Mw : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hcs0.le 2)
      (pow_nonneg hs0.le 7)) (pow_nonneg hep0.le 2)) hthr.1.le) (by positivity)
  have hden : (0 : ℝ) <
      (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose * M.gamma :=
    mul_pos hC0pos hgam0
  have hdenle : (Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose * M.gamma
      ≤ anchorConst d * M.gamma := mul_le_mul_of_nonneg_right hle hgam0.le
  have hkey : (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta *
        ((Mw : ℝ) + 1)) / (anchorConst d * M.gamma)
      ≤ (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta *
        ((Mw : ℝ) + 1)) /
        ((Algsuperdiff.Frozen.Section4.proportion_of_good_scales d).choose * M.gamma) :=
    div_le_div_of_nonneg_left hnum0 hden hdenle
  rw [neg_div, neg_div]
  linarith only [hkey]

/-! ## 3. The `θ`-instantiation: the per-centre bad-density mass -/

/-- **The per-centre bad-density mass is centre-independent.**  Both halves of the
stationarity gap are proved: the law-level invariance of
`Cutoff.translateCutoffSample` and the pointwise observable identity.  This is
`Provider.GoodEvents.measure_lt_mul_sum_indicator_compl_goodEventAt` read at
the two centres `y` and `y'`. -/
theorem measure_center_density_gt_eq (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (y y' : Vec d) (n m : ℤ) (t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < centerDensityScore M s delta hs y n m omega}
      = (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < centerDensityScore M s delta hs y' n m omega} := by
  have h1 := GoodEvents.measure_lt_mul_sum_indicator_compl_goodEventAt M
    (Support.cgEllipLowerConstant d) y ⟨s, hs⟩ (s * Real.sqrt delta) n m
    ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹) t
  have h2 := GoodEvents.measure_lt_mul_sum_indicator_compl_goodEventAt M
    (Support.cgEllipLowerConstant d) y' ⟨s, hs⟩ (s * Real.sqrt delta) n m
    ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹) t
  exact h1.trans h2.symm

/-- **The bad-density event at the origin sits inside the anchor's event.**  The
`ℝ≥0∞`-valued Cesàro average of the complement indicators exceeding
`ofReal delta` forces the anchor's `ℝ`-valued good-proportion to be at most
`1 − delta`, at base scale `m − j` and window length `j`. -/
theorem center_density_gt_subset_anchor (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (hdelta : 0 ≤ delta) (m : ℤ) (j : ℕ) :
    {omega | ENNReal.ofReal delta <
        centerDensityScore M s delta hs 0 (m - (j : ℤ)) m omega} ⊆
      {omega |
        (1 / ((j : ℝ) + 1)) *
            ∑ i ∈ Finset.range (j + 1),
              (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
                    (m - (j : ℤ) + (i : ℤ)) 0 ⟨s, hs⟩ (s * Real.sqrt delta)).indicator
                (fun _ => (1 : ℝ)) omega ≤
          1 - delta} := by
  intro omega homega
  simp only [Set.mem_ofPred_eq, centerDensityScore, toNat_sub_sub] at homega
  rw [sum_Icc_sub_eq_sum_range] at homega
  exact avg_good_le_of_avg_bad_lt hdelta j
    (fun i => Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
      (m - (j : ℤ) + (i : ℤ)) 0 ⟨s, hs⟩ (s * Real.sqrt delta)) omega homega

/-- **The `θ`-instantiation.**  The proportion anchor at
`θ = δ`, `ep = s√δ`, `m₀ = m − j`, `Mw = j`, transported to an arbitrary
centre.  The delivered rate is `c⋆² s⁹ δ² (j+1)/(anchorConst · γ)`: the
anchor's `s⁷ ep² θ` **is** `s⁹ δ²` at this instantiation, which is exactly the
`s⁹` the frozen tail asserts.

The regime hypothesis is the **printed** clause, verbatim (exponent `s⁸`): this
step closes at `s⁸`.  (The union bound over centres does not — see the module
docstring.) -/
theorem measure_center_density_le (C : ℝ) (hC1 : 1 ≤ C) (hCa : anchorConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (y : Vec d) (m : ℤ) (j : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | ENNReal.ofReal delta <
          centerDensityScore M s delta hs y (m - (j : ℤ)) m omega} ≤
      ENNReal.ofReal
        (6 *
          Real.exp
            (-(Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) * ((j : ℝ) + 1)) /
              (anchorConst d * M.gamma))) := by
  have hCa1 : 1 ≤ anchorConst d := one_le_anchorConst d
  have hCa0 : (0 : ℝ) < anchorConst d := anchorConst_pos d
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hsqpos : (0 : ℝ) < Real.sqrt delta := Real.sqrt_pos.2 hd0
  have hsqle : Real.sqrt delta ≤ 1 := Real.sqrt_le_one.2 (by linarith only [hd2])
  have hep2 : (s * Real.sqrt delta) ^ (2 : ℕ) = s ^ (2 : ℕ) * delta := by
    rw [mul_pow, Real.sq_sqrt hd0.le]
  have hep0 : (0 : ℝ) < s * Real.sqrt delta := mul_pos hs hsqpos
  have hepr : s * Real.sqrt delta ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    refine ⟨hep0, ?_⟩
    have h := mul_le_mul_of_nonneg_left hsqle hs.le
    rw [mul_one] at h
    linarith only [h, hs4]
  have hsr : s ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨hs, by linarith only [hs4]⟩
  have hthr : delta ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨hd0, hd2⟩
  -- the anchor's regime clause
  have hgam2 : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)) :=
    le_trans hgam
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg (inv_nonneg.2 hC0.le) 10))
  have hCinv1 : C⁻¹ ≤ 1 := by
    rw [← one_div, div_le_one hC0]
    exact hC1
  have hCinv : C⁻¹ ^ (10 : ℕ) ≤ (anchorConst d)⁻¹ := by
    refine le_trans ?_ (inv_anti₀ hCa0 hCa)
    calc C⁻¹ ^ (10 : ℕ) ≤ C⁻¹ ^ (1 : ℕ) :=
          pow_le_pow_of_le_one (inv_nonneg.2 hC0.le) hCinv1 (by norm_num)
      _ = C⁻¹ := pow_one _
  have hminle : min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ))
      ≤ min (Disorder.cstar M ^ (10 : ℕ))
        (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * (s * Real.sqrt delta) ^ (2 : ℕ)) := by
    refine min_le_min (le_refl _) ?_
    rw [hep2]
    have hds : delta * s ≤ 1 := by
      have h1 : delta * s ≤ (1 / 2 : ℝ) * s := mul_le_mul_of_nonneg_right hd2 hs.le
      have h2 : (1 / 2 : ℝ) * s ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hs4 (by norm_num)
      linarith only [h1, h2]
    have hmul : delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)
        = (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * (s ^ (2 : ℕ) * delta)) * (delta * s) := by
      ring
    rw [hmul]
    have hbase : (0 : ℝ) ≤ Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * (s ^ (2 : ℕ) * delta) :=
      mul_nonneg (mul_nonneg (pow_nonneg hcs0.le 2) (pow_nonneg hs.le 5))
        (mul_nonneg (pow_nonneg hs.le 2) hd0.le)
    have h := mul_le_mul_of_nonneg_left hds hbase
    rw [mul_one] at h
    exact h
  have hmin0 : (0 : ℝ) ≤ min (Disorder.cstar M ^ (10 : ℕ))
      (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)) :=
    le_min (pow_nonneg hcs0.le 10)
      (mul_nonneg (mul_nonneg (pow_nonneg hd0.le 2) (pow_nonneg hcs0.le 2))
        (pow_nonneg hs.le 8))
  have hgamA : M.gamma ≤ (anchorConst d)⁻¹ *
      min (Disorder.cstar M ^ (10 : ℕ))
        (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * (s * Real.sqrt delta) ^ (2 : ℕ)) := by
    refine le_trans hgam (le_trans (mul_le_mul_of_nonneg_right hCinv hmin0) ?_)
    exact mul_le_mul_of_nonneg_left hminle (inv_nonneg.2 hCa0.le)
  -- the anchor's level clause
  have hXpos : (0 : ℝ) < Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * (s ^ (2 : ℕ) * delta) :=
    mul_pos (mul_pos (pow_pos hcs0 2) (pow_pos hs 6)) (mul_pos (pow_pos hs 2) hd0)
  have hpow : anchorConst d * C⁻¹ ^ (10 : ℕ) ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hC0 10)]
    calc anchorConst d ≤ C := hCa
      _ = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (10 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hlev : anchorConst d * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) *
      (s * Real.sqrt delta)⁻¹ ^ (2 : ℕ) * M.gamma ≤ delta := by
    rw [inv_pow, inv_pow, inv_pow, hep2]
    have heq : anchorConst d * (Disorder.cstar M ^ (2 : ℕ))⁻¹ * (s ^ (6 : ℕ))⁻¹ *
          (s ^ (2 : ℕ) * delta)⁻¹ * M.gamma
        = (anchorConst d * M.gamma) /
          (Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * (s ^ (2 : ℕ) * delta)) := by
      rw [div_eq_mul_inv, mul_inv, mul_inv]
      ring
    rw [heq, div_le_iff₀ hXpos]
    have hnn : (0 : ℝ) ≤ delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ) :=
      mul_nonneg (mul_nonneg (pow_nonneg hd0.le 2) (pow_nonneg hcs0.le 2)) (pow_nonneg hs.le 8)
    calc anchorConst d * M.gamma
        ≤ anchorConst d *
            (C⁻¹ ^ (10 : ℕ) * (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ))) :=
          mul_le_mul_of_nonneg_left hgam2 hCa0.le
      _ = (anchorConst d * C⁻¹ ^ (10 : ℕ)) *
            (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)) := by ring
      _ ≤ 1 * (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)) :=
          mul_le_mul_of_nonneg_right hpow hnn
      _ = delta * (Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * (s ^ (2 : ℕ) * delta)) := by ring
  -- the anchor, and the exponent rewriting
  have hanch := anchorConst_spec d M s (s * Real.sqrt delta) delta hsr hepr hthr hgamA hwin
    hlev (m - (j : ℤ)) j hs
  have hnum : Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * (s * Real.sqrt delta) ^ (2 : ℕ) *
        delta * ((j : ℝ) + 1)
      = Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) * ((j : ℝ) + 1) := by
    rw [hep2]; ring
  rw [hnum] at hanch
  rw [measure_center_density_gt_eq M s delta hs y 0 (m - (j : ℤ)) m]
  exact le_trans (measure_mono (center_density_gt_subset_anchor M s delta hs hd0.le m j)) hanch

/-! ## 4. The centre enumeration: `hcard` and `hcover`, as theorems -/

/-- **The centre family of the window `[m − j, m]`**: the integer indices of
`3^{m−j−1}ℤ^d ∩ □_m`, as an explicit `Finset` (the proved enumeration of
`Provider.Proportion`). -/
def centerFinset (d : ℕ) (m : ℤ) (j : ℕ) : Finset (Fin d → ℤ) :=
  Proportion.latticeCubeFinset d (m - (j : ℤ) - 1) m

/-- The centre count of the window `[m − j, m]` is at most `3^{d(j+2)} ≤
3^{2d(j+1)}`; the exponent `2d` is the `D` of
`Algsuperdiff.Probability.count_exp_absorb_const`. -/
theorem card_centerFinset_le (d : ℕ) (m : ℤ) (j : ℕ) :
    ((centerFinset d m j).card : ℝ) ≤ (3 : ℝ) ^ (2 * d * (j + 1)) := by
  have hidx : (m - (m - (j : ℤ) - 1)).toNat = j + 1 := by
    have h : m - (m - (j : ℤ) - 1) = (j : ℤ) + 1 := by ring
    rw [h]
    omega
  have hbase : (centerFinset d m j).card ≤ 3 ^ (d * ((j + 1) + 1)) := by
    have h := Proportion.card_latticeCubeFinset_le d (j := m - (j : ℤ) - 1) (outer := m)
    rw [hidx] at h
    exact h
  have hstep : d * ((j + 1) + 1) ≤ 2 * d * (j + 1) := by
    have h3 : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (Nat.succ_pos j)
    calc d * ((j + 1) + 1) = d * (j + 1) + d := by ring
      _ ≤ d * (j + 1) + d * (j + 1) := Nat.add_le_add_left h3 _
      _ = 2 * d * (j + 1) := by ring
  have hcardnat : (centerFinset d m j).card ≤ 3 ^ (2 * d * (j + 1)) :=
    le_trans hbase (Nat.pow_le_pow_right (by norm_num) hstep)
  calc ((centerFinset d m j).card : ℝ) ≤ ((3 ^ (2 * d * (j + 1)) : ℕ) : ℝ) :=
        Nat.cast_le.2 hcardnat
    _ = (3 : ℝ) ^ (2 * d * (j + 1)) := by push_cast; ring

/-- A bad density window is witnessed by a centre of the explicit enumeration; the
mechanism is `lt_iSup_iff` in `ℝ≥0∞`, so no finiteness and no positivity of `δ`
is used. -/
theorem exists_center_finset_of_badDensity (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (m : ℤ) (j : ℕ) (omega : Cutoff.CutoffSample d)
    (h : badDensity M s delta hs m j omega) :
    ∃ z ∈ centerFinset d m j,
      ENNReal.ofReal delta <
        centerDensityScore M s delta hs (Support.triadicLatticePoint (m - (j : ℤ) - 1) z)
          (m - (j : ℤ)) m omega := by
  obtain ⟨z, hzmem, hz⟩ := exists_center_of_badDensity M s delta hs m j h
  refine ⟨z, ?_, hz⟩
  exact (Proportion.mem_latticeCubeFinset_iff (by omega : m - (j : ℤ) - 1 ≤ m)).2 hzmem

/-! ## 5. The assembled constant -/

/-- **The `Z²` leg's constant.**  Three floor duties, all functions of `d` alone:
`2 · anchorConst d` (halving the anchor's rate, which is what pays for the centre
count), `2 · 3^{2d}` (the union-bound prefactor against the geometric-summation
constant `(1 − e^{−c₀})⁻¹`), and `log 6 + 4 d log 3` (the anchor's per-window
prefactor `6`, and the absorption `2d log 3 + c₀ ≤ c₁`). -/
noncomputable def zTwoConst (d : ℕ) : ℝ :=
  max (2 * anchorConst d)
    (max (2 * (3 : ℝ) ^ (2 * d)) (Real.log 6 + 4 * (d : ℝ) * Real.log 3))

theorem two_mul_anchorConst_le_zTwoConst (d : ℕ) : 2 * anchorConst d ≤ zTwoConst d :=
  le_max_left _ _

theorem two_mul_three_pow_le_zTwoConst (d : ℕ) : 2 * (3 : ℝ) ^ (2 * d) ≤ zTwoConst d :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem log_six_add_le_zTwoConst (d : ℕ) :
    Real.log 6 + 4 * (d : ℝ) * Real.log 3 ≤ zTwoConst d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem one_le_zTwoConst (d : ℕ) : 1 ≤ zTwoConst d := by
  refine le_trans ?_ (two_mul_anchorConst_le_zTwoConst d)
  have h := one_le_anchorConst d
  linarith only [h]

theorem anchorConst_le_zTwoConst (d : ℕ) : anchorConst d ≤ zTwoConst d := by
  refine le_trans ?_ (two_mul_anchorConst_le_zTwoConst d)
  have h := anchorConst_pos d
  linarith only [h]

theorem zTwoConst_pos (d : ℕ) : 0 < zTwoConst d :=
  lt_of_lt_of_le zero_lt_one (one_le_zTwoConst d)

/-! ## 6. The `Z²` tail at the frozen prefactor-tail shape -/

/-- **The geometric tail of the bad-density random scale, at the frozen
prefactor-tail shape**

`P[N ≤ Z²] ≤ C exp(−(N−1) s⁹ c⋆² δ² /(C γ))`.

The route: the `θ`-instantiation `measure_center_density_le` per centre, the
explicit centre count `card_centerFinset_le` and cover
`exists_center_finset_of_badDensity` (both theorems — neither is a binder), then
`Algsuperdiff.Probability.windowScale_tail_const_of_center_tails`, whose
`windowTailConst (2d) c₀` prefactor is absorbed by the `(N−1)` shift of the
frozen display.

**Deviation from the printed hypothesis.**  The regime clause below is
`e.scale.sep.cond` with the single numeral `8` replaced by `9` (`… s ^ (9 :
ℕ)`).  It is *forced*: the centre union bound needs the per-centre rate `c⋆² s⁹
δ²/(C_a γ)` to exceed `2d log 3 + c₀`, i.e. it needs `γ ≤ K(d)⁻¹ c⋆² s⁹ δ²`,
and the printed `s⁸` clause is weaker by a factor `s`, which is a free
parameter with `s ↓ 8γ` and hence not absorbable into `C(d)`.  The
`θ`-instantiation itself closes at the printed `s⁸` — see
`measure_center_density_le`. -/
theorem measure_tail_badDensity_le (C : ℝ) (hC : zTwoConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (N : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badDensity M s delta hs m) omega} ≤
      ENNReal.ofReal
        (C *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))) := by
  classical
  have hCa1 : 1 ≤ anchorConst d := one_le_anchorConst d
  have hCa0 : (0 : ℝ) < anchorConst d := anchorConst_pos d
  have hC1 : 1 ≤ C := le_trans (one_le_zTwoConst d) hC
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hCaC : anchorConst d ≤ C := le_trans (anchorConst_le_zTwoConst d) hC
  have h2CaC : 2 * anchorConst d ≤ C := le_trans (two_mul_anchorConst_le_zTwoConst d) hC
  have h3dC : 2 * (3 : ℝ) ^ (2 * d) ≤ C := le_trans (two_mul_three_pow_le_zTwoConst d) hC
  have hlogC : Real.log 6 + 4 * (d : ℝ) * Real.log 3 ≤ C :=
    le_trans (log_six_add_le_zTwoConst d) hC
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h4nn : (0 : ℝ) ≤ 4 * (d : ℝ) * Real.log 3 := mul_nonneg (by positivity) hlog3
  have hCagam : (0 : ℝ) < anchorConst d * M.gamma := mul_pos hCa0 hgam0
  have hCgam : (0 : ℝ) < C * M.gamma := mul_pos hC0 hgam0
  have hnumpos : (0 : ℝ) <
      Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) :=
    mul_pos (mul_pos (pow_pos hcs0 2) (pow_pos hs 9)) (pow_pos hd0 2)
  set A : ℝ :=
    Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) / (anchorConst d * M.gamma)
    with hAdef
  set c0 : ℝ :=
    Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) / (C * M.gamma) with hc0def
  -- the `s⁹` regime clause, in product form
  have hgam2 : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) :=
    le_trans hgam
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg (inv_nonneg.2 hC0.le) 10))
  have hcancelC : (C : ℝ) ^ (10 : ℕ) * C⁻¹ ^ (10 : ℕ) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hC0), one_pow]
  have hX : C ^ (10 : ℕ) * M.gamma ≤
      Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) := by
    calc C ^ (10 : ℕ) * M.gamma
        ≤ C ^ (10 : ℕ) *
            (C⁻¹ ^ (10 : ℕ) *
              (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ))) :=
          mul_le_mul_of_nonneg_left hgam2 (pow_nonneg hC0.le 10)
      _ = (C ^ (10 : ℕ) * C⁻¹ ^ (10 : ℕ)) *
            (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by ring
      _ = delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) := by
          rw [hcancelC, one_mul]
      _ = Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) := by ring
  -- the two rate lower bounds
  have hrates := Probability.rates_ge_of_large_power hC1 hCa0 hCaC hgam0 hX
  have hAlow : C ≤ A := hrates.1
  have hc0low : 1 ≤ c0 := hrates.2
  have hc0pos : (0 : ℝ) < c0 := lt_of_lt_of_le zero_lt_one hc0low
  have h2c0A : 2 * c0 ≤ A := by
    have hstep : 2 * c0 =
        (2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ))) / (C * M.gamma) := by
      rw [hc0def]; ring
    rw [hstep, hAdef, div_le_div_iff₀ hCgam hCagam]
    have h := mul_le_mul_of_nonneg_left h2CaC
      (mul_nonneg hnumpos.le hgam0.le)
    linarith only [h]
  -- the absorption and the per-window prefactor
  have h4d : 4 * (d : ℝ) * Real.log 3 ≤ A := by
    have hlog6 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    linarith only [hlogC, hAlow, hlog6]
  have hcast2d : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
  have habsorb : ((2 * d : ℕ) : ℝ) * Real.log 3 + c0 ≤ A := by
    rw [hcast2d]
    linarith only [h4d, h2c0A]
  have hAlog6 : Real.log 6 ≤ A := by linarith only [hlogC, hAlow, h4nn]
  have hexpA : (6 : ℝ) ≤ Real.exp A := by
    rw [show (6 : ℝ) = Real.exp (Real.log 6) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_le_exp.2 hAlog6
  -- the printed regime clause, from the `s⁹` one
  have hs9le8 : s ^ (9 : ℕ) ≤ s ^ (8 : ℕ) :=
    pow_le_pow_of_le_one hs.le (by linarith only [hs4]) (by norm_num)
  have hgam8 : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (8 : ℕ)) := by
    refine le_trans hgam (mul_le_mul_of_nonneg_left (min_le_min (le_refl _) ?_)
      (pow_nonneg (inv_nonneg.2 hC0.le) 10))
    exact mul_le_mul_of_nonneg_left hs9le8
      (mul_nonneg (pow_nonneg hd0.le 2) (pow_nonneg hcs0.le 2))
  -- the per-centre tails, at the `n`-proportional rate
  have hcenter : ∀ j : ℕ, 1 ≤ j → ∀ z ∈ centerFinset d m j,
      ((Cutoff.cutoffSampleLaw M).toMeasure).real
          {omega | ENNReal.ofReal delta <
            centerDensityScore M s delta hs
              (Support.triadicLatticePoint (m - (j : ℤ) - 1) z) (m - (j : ℤ)) m omega} ≤
        Real.exp (-A * (j : ℝ)) := by
    intro j _ z _
    have hb := measure_center_density_le C hC1 hCaC M s delta hs hs4 hd0 hd2 hgam8 hwin
      (Support.triadicLatticePoint (m - (j : ℤ) - 1) z) m j
    have hrw : -(Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) * delta ^ (2 : ℕ) * ((j : ℝ) + 1)) /
          (anchorConst d * M.gamma)
        = -A * ((j : ℝ) + 1) := by
      rw [hAdef]; ring
    rw [hrw] at hb
    have hreal : ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          centerDensityScore M s delta hs
            (Support.triadicLatticePoint (m - (j : ℤ) - 1) z) (m - (j : ℤ)) m omega}
        ≤ 6 * Real.exp (-A * ((j : ℝ) + 1)) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      rwa [ENNReal.toReal_ofReal (by positivity), ← measureReal_def] at h
    refine le_trans hreal ?_
    have hsplit : Real.exp (-A * ((j : ℝ) + 1))
        = Real.exp (-A * (j : ℝ)) * Real.exp (-A) := by
      rw [← Real.exp_add]; congr 1; ring
    have hcancel : Real.exp A * Real.exp (-A) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hsplit]
    calc (6 : ℝ) * (Real.exp (-A * (j : ℝ)) * Real.exp (-A))
        ≤ Real.exp A * (Real.exp (-A * (j : ℝ)) * Real.exp (-A)) :=
          mul_le_mul_of_nonneg_right hexpA (by positivity)
      _ = (Real.exp A * Real.exp (-A)) * Real.exp (-A * (j : ℝ)) := by ring
      _ = Real.exp (-A * (j : ℝ)) := by rw [hcancel, one_mul]
  -- the geometric closure
  have htail := Probability.windowScale_tail_const_of_center_tails
    ((Cutoff.cutoffSampleLaw M).toMeasure) (D := 2 * d) (badDensity M s delta hs m)
    (centerFinset d m)
    (fun z j omega => ENNReal.ofReal delta <
      centerDensityScore M s delta hs (Support.triadicLatticePoint (m - (j : ℤ) - 1) z)
        (m - (j : ℤ)) m omega)
    hc0pos (fun j => card_centerFinset_le d m j) habsorb
    (fun j omega h => exists_center_finset_of_badDensity M s delta hs m j omega h)
    hcenter N
  -- the prefactor, absorbed by the `(N − 1)` shift
  have hfrozen : -c0 * ((N : ℝ) - 1)
      = -(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
        (C * M.gamma) := by
    rw [hc0def]; ring
  have hpref : Probability.windowTailConst (2 * d) c0 * Real.exp (-c0 * (N : ℝ))
      ≤ C *
        Real.exp
          (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
            (C * M.gamma)) := by
    rw [← hfrozen]
    exact Probability.windowTailConst_mul_exp_le_shift (2 * d) hc0low h3dC (N : ℝ)
  have hmeas : (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badDensity M s delta hs m) omega}
      = ENNReal.ofReal (((Cutoff.cutoffSampleLaw M).toMeasure).real
          {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badDensity M s delta hs m) omega}) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hmeas]
  exact ENNReal.ofReal_le_ofReal (le_trans htail hpref)

end

end Algsuperdiff.Section4.Provider.MinimalScale
