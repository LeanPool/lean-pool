/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.TailGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.HighMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.JointGridDepthMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport

/-!
# SharpTailProbability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Almost-sure sharp shell rates at every crossover scale

The two `Γ₂` shell estimates are grouped by square boxes in `ℤ × ℤ`.  We
square the normalized gauges, turning `Γ₂` into `Γ₁`; the graded finite-envelope
lemma then pays one linear factor for the row entropy.  The original cube
maximum already costs a square root of that row size.  Taking the square root
of the resulting envelope therefore gives exactly the first power of
`2 + |n| + |ell|`, with no additional power beyond that linear crossover
weight.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A dimension-only scale large enough for both one-shell `Γ₂` estimates. -/
def sharpTailOrliczConst (d : ℕ) : ℝ :=
  Real.exp 1 * gaussianMaximumDimConst d +
    Stream.shellW1InfConst d

theorem sharpTailOrliczConst_pos (d : ℕ) : 0 < sharpTailOrliczConst d := by
  unfold sharpTailOrliczConst
  exact add_pos (mul_pos (Real.exp_pos _) (gaussianMaximumDimConst_pos d))
    (Stream.shellW1InfConst_pos d)

/-- The value gauge divided by its exact shell amplitude. -/
def sharpValueRatio (gamma : ℝ) (n ell : ℤ) (omega : CutoffSample d) : ℝ :=
  localCubeControl ell (omega.1 n) / Real.rpow 3 (gamma * (n : ℝ))

/-- The derivative gauge divided by its exact shell amplitude. -/
def sharpGradientRatio (gamma : ℝ) (n ell : ℤ) (omega : CutoffSample d) : ℝ :=
  sharpGradientGauge ell n omega / Real.rpow 3 ((gamma - 1) * (n : ℝ))

private theorem sharpValueRatio_nonneg (gamma : ℝ) (n ell : ℤ)
    (omega : CutoffSample d) : 0 ≤ sharpValueRatio gamma n ell omega :=
  div_nonneg (localCubeControl_nonneg _ _) (Real.rpow_nonneg (by norm_num) _)

private theorem sharpGradientRatio_nonneg (gamma : ℝ) (n ell : ℤ)
    (omega : CutoffSample d) : 0 ≤ sharpGradientRatio gamma n ell omega :=
  div_nonneg (sharpGradientGauge_nonneg _ _ _) (Real.rpow_nonneg (by norm_num) _)

private theorem measurable_sharpValueRatio (gamma : ℝ) (n ell : ℤ) :
    Measurable (sharpValueRatio (d := d) gamma n ell) :=
  ((measurable_localCubeControl ell).comp
    ((measurable_pi_apply n).comp measurable_subtype_coe)).div_const _

private theorem measurable_sharpGradientRatio (gamma : ℝ) (n ell : ℤ) :
    Measurable (sharpGradientRatio (d := d) gamma n ell) :=
  (measurable_sharpGradientGauge ell n).div_const _

private theorem sqrt_value_cost_le_weight (n ell : ℤ) :
    Real.sqrt (1 + max ((ell : ℝ) - (n : ℝ)) 0) ≤
      Real.sqrt (sharpTailWeight n ell) := by
  refine Real.sqrt_le_sqrt ?_
  have hn : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hell : (ell.natAbs : ℝ) = |(ell : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hsub : (ell : ℝ) - (n : ℝ) ≤ |(ell : ℝ)| + |(n : ℝ)| :=
    (le_abs_self ((ell : ℝ) - (n : ℝ))).trans (abs_sub _ _)
  have hmax : max ((ell : ℝ) - (n : ℝ)) 0 ≤ |(ell : ℝ)| + |(n : ℝ)| :=
    max_le hsub (add_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [sharpTailWeight, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, hn, hell]
  linarith only [hmax]

private theorem sqrt_gradient_cost_le_weight (n ell : ℤ) :
    Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) ≤
      Real.sqrt (sharpTailWeight n ell) := by
  refine Real.sqrt_le_sqrt ?_
  have hn : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hell : (ell.natAbs : ℝ) = |(ell : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hsub : (ell : ℝ) - (n : ℝ) ≤ |(ell : ℝ)| + |(n : ℝ)| :=
    (le_abs_self ((ell : ℝ) - (n : ℝ))).trans (abs_sub _ _)
  have hmax : max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ)) ≤
      2 + |(n : ℝ)| + |(ell : ℝ)| := by
    rw [Int.cast_sub, Int.cast_one, max_le_iff]
    constructor <;> linarith only [hsub, abs_nonneg (n : ℝ), abs_nonneg (ell : ℝ)]
  rw [sharpTailWeight, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, hn, hell]
  exact hmax

/-- The value ratio has a common `Γ₂` scale bounded by the square root of the
integer crossover weight. -/
theorem isBigOWith_gammaSigma_sharpValueRatio (M : ABKModel d) (n ell : ℤ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (sharpValueRatio M.gamma n ell)
      (sharpTailOrliczConst d * Real.sqrt (sharpTailWeight n ell)) := by
  have hraw := Stream.isBigOWith_cutoffSampleLaw_comp_val
    (isBigOWith_gammaSigma_localCubeControl_lowerShell M n ell 0)
  have hrate : 0 < Real.rpow 3 (M.gamma * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hscaled := hraw.const_mul (inv_nonneg.mpr hrate.le)
  have hratio : (fun omega : CutoffSample d =>
      (Real.rpow 3 (M.gamma * (n : ℝ)))⁻¹ *
        localCubeControl ell (omega.1 (n - (0 : ℕ)))) =
      sharpValueRatio M.gamma n ell := by
    funext omega
    simp only [Nat.cast_zero, sub_zero, sharpValueRatio, div_eq_mul_inv, mul_comm]
  rw [hratio] at hscaled
  have hcost := sqrt_value_cost_le_weight n ell
  have hdim : Real.exp 1 * gaussianMaximumDimConst d ≤ sharpTailOrliczConst d := by
    unfold sharpTailOrliczConst
    exact le_add_of_nonneg_right (Stream.shellW1InfConst_pos d).le
  have hsqrt0 : 0 ≤ Real.sqrt (1 + max ((ell : ℝ) - (n : ℝ)) 0) :=
    Real.sqrt_nonneg _
  have hscale :
      (Real.rpow 3 (M.gamma * (n : ℝ)))⁻¹ *
          cutoffGammaMajorant d M.gamma n ell 0 =
        Real.exp 1 * gaussianMaximumDimConst d *
          Real.sqrt (1 + max ((ell : ℝ) - (n : ℝ)) 0) := by
    unfold cutoffGammaMajorant expectedCubeMajorant cubeMajorant
    norm_num
    field_simp
  rw [hscale] at hscaled
  refine hscaled.mono_scale ?_
  calc
    Real.exp 1 * gaussianMaximumDimConst d *
        Real.sqrt (1 + max ((ell : ℝ) - (n : ℝ)) 0) ≤
      sharpTailOrliczConst d *
        Real.sqrt (1 + max ((ell : ℝ) - (n : ℝ)) 0) :=
      mul_le_mul_of_nonneg_right hdim hsqrt0
    _ ≤ sharpTailOrliczConst d * Real.sqrt (sharpTailWeight n ell) :=
      mul_le_mul_of_nonneg_left hcost (sharpTailOrliczConst_pos d).le

/-- The derivative ratio has the same common `Γ₂` scale. -/
theorem isBigOWith_gammaSigma_sharpGradientRatio (M : ABKModel d) (n ell : ℤ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (sharpGradientRatio M.gamma n ell)
      (sharpTailOrliczConst d * Real.sqrt (sharpTailWeight n ell)) := by
  have hrawShell := Stream.isBigOWith_gammaSigma_largeCubeDerivGauge
    (M := M) (l := ell) (n := n - 1) (k := n) (by omega)
  have hraw := Stream.isBigOWith_cutoffSampleLaw_comp_val hrawShell
  have hthree : 0 < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hrate : 0 < Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hscaled := (hraw.const_mul hthree.le).const_mul (inv_nonneg.mpr hrate.le)
  have hratio : (fun omega : CutoffSample d =>
      (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))⁻¹ *
        ((3 : ℝ) ^ (-n) * Stream.largeCubeDerivGauge ell n (omega.1 n))) =
      sharpGradientRatio M.gamma n ell := by
    funext omega
    simp only [sharpGradientRatio, sharpGradientGauge, div_eq_mul_inv, mul_comm]
  rw [hratio] at hscaled
  have hcost := sqrt_gradient_cost_le_weight n ell
  have hdim : Stream.shellW1InfConst d ≤ sharpTailOrliczConst d := by
    unfold sharpTailOrliczConst
    exact le_add_of_nonneg_left
      (mul_nonneg (Real.exp_pos _).le (gaussianMaximumDimConst_pos d).le)
  have hsqrt0 : 0 ≤ Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) :=
    Real.sqrt_nonneg _
  have hscale :
      (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))⁻¹ *
          ((3 : ℝ) ^ (-n) *
            (Stream.shellW1InfConst d *
              Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) *
              (3 : ℝ) ^ (M.gamma * (n : ℝ)))) =
        Stream.shellW1InfConst d *
          Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) := by
    have hpow : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (M.gamma * (n : ℝ)) =
        Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (-n),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    calc
      (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))⁻¹ *
          ((3 : ℝ) ^ (-n) *
            (Stream.shellW1InfConst d *
              Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) *
              Real.rpow 3 (M.gamma * (n : ℝ)))) =
        (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))⁻¹ *
          (((3 : ℝ) ^ (-n) * Real.rpow 3 (M.gamma * (n : ℝ))) *
            (Stream.shellW1InfConst d *
              Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))))) := by ring
      _ = (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))⁻¹ *
          (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) *
            (Stream.shellW1InfConst d *
              Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))))) := by
        exact congrArg (fun z =>
          (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))⁻¹ *
            (z * (Stream.shellW1InfConst d *
              Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ)))))) hpow
      _ = _ := by field_simp
  rw [hscale] at hscaled
  refine hscaled.mono_scale ?_
  calc
    Stream.shellW1InfConst d *
        Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) ≤
      sharpTailOrliczConst d *
        Real.sqrt (max 1 ((ell : ℝ) - ((n - 1 : ℤ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hdim hsqrt0
    _ ≤ sharpTailOrliczConst d * Real.sqrt (sharpTailWeight n ell) :=
      mul_le_mul_of_nonneg_left hcost (sharpTailOrliczConst_pos d).le

/-! ## The joint square-box envelope -/

/-- Both gauges over the square `[-k,k]²`; `false` is the value leg and
`true` is the derivative leg. -/
def sharpTailRow (k : ℕ) : Finset (Bool × (ℤ × ℤ)) :=
  Finset.univ.product
    (Finset.Icc (-(k : ℤ)) (k : ℤ) |>.product
      (Finset.Icc (-(k : ℤ)) (k : ℤ)))

/-- The squared normalized observable used to turn the `Γ₂` inputs into a
`Γ₁` row. -/
def sharpTailSquaredObservable (gamma : ℝ) (_k : ℕ)
    (i : Bool × (ℤ × ℤ)) (omega : CutoffSample d) : ℝ :=
  if i.1 then sharpGradientRatio gamma i.2.1 i.2.2 omega ^ (2 : ℕ)
  else sharpValueRatio gamma i.2.1 i.2.2 omega ^ (2 : ℕ)

/-- A common deterministic `Γ₁` scale for the squared observables in row `k`. -/
def sharpTailSquaredScale (d k : ℕ) : ℝ :=
  (sharpTailOrliczConst d * Real.sqrt (2 + 2 * (k : ℝ))) ^ (2 : ℕ)

private theorem sharpTailSquaredScale_pos (d k : ℕ) :
    0 < sharpTailSquaredScale d k := by
  unfold sharpTailSquaredScale
  exact pow_pos (mul_pos (sharpTailOrliczConst_pos d)
    (Real.sqrt_pos.2 (by positivity))) _

private theorem sharpTailWeight_le_rowScale {k : ℕ} {n ell : ℤ}
    (hn : n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ))
    (hell : ell ∈ Finset.Icc (-(k : ℤ)) (k : ℤ)) :
    sharpTailWeight n ell ≤ 2 + 2 * (k : ℝ) := by
  have hnabs : n.natAbs ≤ k := by
    simp only [Finset.mem_Icc] at hn
    omega
  have hellabs : ell.natAbs ≤ k := by
    simp only [Finset.mem_Icc] at hell
    omega
  unfold sharpTailWeight
  have hnat : 2 + n.natAbs + ell.natAbs ≤ 2 + 2 * k := by omega
  exact_mod_cast hnat

private theorem measurable_sharpTailSquaredObservable (M : ABKModel d)
    (k : ℕ) (i : Bool × (ℤ × ℤ)) :
    Measurable (sharpTailSquaredObservable (d := d) M.gamma k i) := by
  unfold sharpTailSquaredObservable
  split
  · exact (measurable_sharpGradientRatio M.gamma i.2.1 i.2.2).pow_const _
  · exact (measurable_sharpValueRatio M.gamma i.2.1 i.2.2).pow_const _

private theorem isBigOWith_gammaSigma_one_sharpTailSquaredObservable
    (M : ABKModel d) (k : ℕ) (i : Bool × (ℤ × ℤ))
    (hi : i ∈ sharpTailRow k) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (sharpTailSquaredObservable M.gamma k i) (sharpTailSquaredScale d k) := by
  have hi' := Finset.mem_product.mp hi
  have hnell := Finset.mem_product.mp hi'.2
  have hweight := sharpTailWeight_le_rowScale hnell.1 hnell.2
  have hsqrt := Real.sqrt_le_sqrt hweight
  have hscale : sharpTailOrliczConst d * Real.sqrt (sharpTailWeight i.2.1 i.2.2) ≤
      sharpTailOrliczConst d * Real.sqrt (2 + 2 * (k : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt (sharpTailOrliczConst_pos d).le
  unfold sharpTailSquaredObservable
  split
  · have htail := isBigOWith_gammaSigma_sharpGradientRatio M i.2.1 i.2.2
    have hsquare := isBigOWith_gammaSigma_rpow
      (μ := (cutoffSampleLaw M).toMeasure) (X := sharpGradientRatio M.gamma i.2.1 i.2.2)
      (A := sharpTailOrliczConst d * Real.sqrt (sharpTailWeight i.2.1 i.2.2))
      (σ := 2) (p := 2) (by norm_num)
      (mul_nonneg (sharpTailOrliczConst_pos d).le (Real.sqrt_nonneg _))
      (sharpGradientRatio_nonneg M.gamma i.2.1 i.2.2) htail
    have hscalePow := Real.rpow_le_rpow
      (mul_nonneg (sharpTailOrliczConst_pos d).le (Real.sqrt_nonneg _))
      hscale (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_two,
      sharpTailSquaredScale] using hsquare.mono_scale hscalePow
  · have htail := isBigOWith_gammaSigma_sharpValueRatio M i.2.1 i.2.2
    have hsquare := isBigOWith_gammaSigma_rpow
      (μ := (cutoffSampleLaw M).toMeasure) (X := sharpValueRatio M.gamma i.2.1 i.2.2)
      (A := sharpTailOrliczConst d * Real.sqrt (sharpTailWeight i.2.1 i.2.2))
      (σ := 2) (p := 2) (by norm_num)
      (mul_nonneg (sharpTailOrliczConst_pos d).le (Real.sqrt_nonneg _))
      (sharpValueRatio_nonneg M.gamma i.2.1 i.2.2) htail
    have hscalePow := Real.rpow_le_rpow
      (mul_nonneg (sharpTailOrliczConst_pos d).le (Real.sqrt_nonneg _))
      hscale (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_two,
      sharpTailSquaredScale] using hsquare.mono_scale hscalePow

private theorem card_sharpTailRow_le_exp (k : ℕ) :
    ((sharpTailRow k).card : ℝ) ≤ Real.exp (8 * ((k : ℝ) + 1)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hquad := Real.quadratic_le_exp_of_nonneg
    (x := 8 * ((k : ℝ) + 1)) (by positivity)
  have hcard : ((sharpTailRow k).card : ℝ) =
      2 * (2 * (k : ℝ) + 1) ^ (2 : ℕ) := by
    simp [sharpTailRow]
    norm_cast
    simp only [Int.toNat_natCast]
    ring
  rw [hcard]
  exact le_trans (by nlinarith only [hk0, sq_nonneg ((k : ℝ) + 1)]) hquad

/-- The explicit joint envelope whose finiteness supplies one sample constant
for every shell/cube pair and both gauges. -/
def sharpTailEnvelope (M : ABKModel d) : CutoffSample d → ℝ :=
  CoarseEllipticity.gradedFiniteEnvelope sharpTailRow
    (sharpTailSquaredObservable M.gamma) (sharpTailSquaredScale d) 8

theorem ae_sharpTailEnvelope_bound (M : ABKModel d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, ∀ k i, i ∈ sharpTailRow k →
      sharpTailSquaredObservable M.gamma k i omega ≤
        CoarseEllipticity.gradedFiniteEnvelopeScale 8 (sharpTailSquaredScale d) k *
          sharpTailEnvelope M omega := by
  exact (CoarseEllipticity.gradedFiniteEnvelope_spec sharpTailRow
    (sharpTailSquaredObservable M.gamma) (sharpTailSquaredScale d)
    (growth := 8) (by norm_num) (sharpTailSquaredScale_pos d)
    card_sharpTailRow_le_exp
    (fun k i _ => measurable_sharpTailSquaredObservable M k i)
    (isBigOWith_gammaSigma_one_sharpTailSquaredObservable M)).2.2.2

private theorem int_mem_square_at_natAbs_add (n ell : ℤ) :
    n ∈ Finset.Icc (-((n.natAbs + ell.natAbs : ℕ) : ℤ))
        ((n.natAbs + ell.natAbs : ℕ) : ℤ) ∧
      ell ∈ Finset.Icc (-((n.natAbs + ell.natAbs : ℕ) : ℤ))
        ((n.natAbs + ell.natAbs : ℕ) : ℤ) := by
  simp only [Finset.mem_Icc]
  constructor <;> omega

/-- The joint envelope implies the sharp two-sided bounds with polynomial
power one. -/
theorem sharpTailBounded_of_envelope (M : ABKModel d) (omega : CutoffSample d)
    (homega : ∀ k i, i ∈ sharpTailRow k →
      sharpTailSquaredObservable M.gamma k i omega ≤
        CoarseEllipticity.gradedFiniteEnvelopeScale 8 (sharpTailSquaredScale d) k *
          sharpTailEnvelope M omega) :
    ∃ C : ℕ, SharpTailBounded M.gamma C omega := by
  let E : ℝ := max 1 (sharpTailEnvelope M omega)
  let A : ℝ := Real.sqrt
    (2 * CoarseEllipticity.jointDepthEntropyConst 8 *
      sharpTailOrliczConst d ^ (2 : ℕ) * E)
  have hE : sharpTailEnvelope M omega ≤ E := le_max_right _ _
  have hE0 : 0 ≤ E := le_trans zero_le_one (le_max_left _ _)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  obtain ⟨C, hC⟩ := exists_nat_ge A
  refine ⟨C, fun n ell => ?_⟩
  let k : ℕ := n.natAbs + ell.natAbs
  have hmem := int_mem_square_at_natAbs_add n ell
  have hiValue : (false, (n, ell)) ∈ sharpTailRow k := by
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr hmem⟩
  have hiGrad : (true, (n, ell)) ∈ sharpTailRow k := by
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr hmem⟩
  have hvalueSq := homega k (false, (n, ell)) hiValue
  have hgradSq := homega k (true, (n, ell)) hiGrad
  simp only [sharpTailSquaredObservable, Bool.false_eq_true, ↓reduceIte] at hvalueSq
  simp only [sharpTailSquaredObservable, ↓reduceIte] at hgradSq
  have hkWeight : (k : ℝ) + 1 ≤ sharpTailWeight n ell := by
    dsimp [k]
    unfold sharpTailWeight
    push_cast
    linarith only [show (0 : ℝ) ≤ 1 by norm_num]
  have hrow : 2 + 2 * (k : ℝ) = 2 * ((k : ℝ) + 1) := by ring
  have hscaleEq :
      CoarseEllipticity.gradedFiniteEnvelopeScale 8 (sharpTailSquaredScale d) k =
        2 * CoarseEllipticity.jointDepthEntropyConst 8 *
          sharpTailOrliczConst d ^ (2 : ℕ) * ((k : ℝ) + 1) ^ (2 : ℕ) := by
    unfold CoarseEllipticity.gradedFiniteEnvelopeScale sharpTailSquaredScale
    rw [hrow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2 * ((k : ℝ) + 1))]
    ring
  rw [hscaleEq] at hvalueSq hgradSq
  have hbase0 : 0 ≤ 2 * CoarseEllipticity.jointDepthEntropyConst 8 *
      sharpTailOrliczConst d ^ (2 : ℕ) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (CoarseEllipticity.jointDepthEntropyConst_pos
        (by norm_num : (0 : ℝ) ≤ 8)).le)
      (sq_nonneg _)
  have hscaleE :
      2 * CoarseEllipticity.jointDepthEntropyConst 8 *
          sharpTailOrliczConst d ^ (2 : ℕ) * ((k : ℝ) + 1) ^ (2 : ℕ) *
            sharpTailEnvelope M omega ≤
        A ^ (2 : ℕ) * sharpTailWeight n ell ^ (2 : ℕ) := by
    have hAeq : A ^ (2 : ℕ) =
        2 * CoarseEllipticity.jointDepthEntropyConst 8 *
          sharpTailOrliczConst d ^ (2 : ℕ) * E := by
      dsimp [A]
      rw [Real.sq_sqrt]
      exact mul_nonneg hbase0 hE0
    rw [hAeq]
    calc
      2 * CoarseEllipticity.jointDepthEntropyConst 8 *
            sharpTailOrliczConst d ^ (2 : ℕ) * ((k : ℝ) + 1) ^ (2 : ℕ) *
          sharpTailEnvelope M omega ≤
        2 * CoarseEllipticity.jointDepthEntropyConst 8 *
            sharpTailOrliczConst d ^ (2 : ℕ) * ((k : ℝ) + 1) ^ (2 : ℕ) * E :=
          mul_le_mul_of_nonneg_left hE
            (mul_nonneg hbase0 (sq_nonneg ((k : ℝ) + 1)))
      _ ≤ 2 * CoarseEllipticity.jointDepthEntropyConst 8 *
            sharpTailOrliczConst d ^ (2 : ℕ) * sharpTailWeight n ell ^ (2 : ℕ) * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) + 1) hkWeight 2) hbase0)
            hE0
      _ = (2 * CoarseEllipticity.jointDepthEntropyConst 8 *
            sharpTailOrliczConst d ^ (2 : ℕ) * E) *
          sharpTailWeight n ell ^ (2 : ℕ) := by ring
  have hvalueRatio : sharpValueRatio M.gamma n ell omega ≤
      (C : ℝ) * sharpTailWeight n ell := by
    rw [← sq_le_sq₀ (sharpValueRatio_nonneg _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg C) (sharpTailWeight_pos n ell).le)]
    exact hvalueSq.trans <| hscaleE.trans <| by
      simpa only [mul_pow] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0 hC 2)
          (sq_nonneg (sharpTailWeight n ell))
  have hgradRatio : sharpGradientRatio M.gamma n ell omega ≤
      (C : ℝ) * sharpTailWeight n ell := by
    rw [← sq_le_sq₀ (sharpGradientRatio_nonneg _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg C) (sharpTailWeight_pos n ell).le)]
    exact hgradSq.trans <| hscaleE.trans <| by
      simpa only [mul_pow] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0 hC 2)
          (sq_nonneg (sharpTailWeight n ell))
  constructor
  · have hrate := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
      (M.gamma * (n : ℝ))
    have hmul := (div_le_iff₀ hrate).1 hvalueRatio
    calc
      localCubeControl ell (omega.1 n) ≤
          ((C : ℝ) * sharpTailWeight n ell) *
            Real.rpow 3 (M.gamma * (n : ℝ)) := hmul
      _ = (C : ℝ) * Real.rpow 3 (M.gamma * (n : ℝ)) *
          sharpTailWeight n ell := by ring
  · have hrate := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
      ((M.gamma - 1) * (n : ℝ))
    have hmul := (div_le_iff₀ hrate).1 hgradRatio
    calc
      sharpGradientGauge ell n omega ≤
          ((C : ℝ) * sharpTailWeight n ell) *
            Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := hmul
      _ = (C : ℝ) * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) *
          sharpTailWeight n ell := by ring

/-- The sharp all-crossover shell event has full measure. -/
theorem ae_sharpTailGood (M : ABKModel d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, SharpTailGood M.gamma omega := by
  filter_upwards [ae_sharpTailEnvelope_bound M] with omega homega
  exact sharpTailBounded_of_envelope M omega homega

end

end Algsuperdiff.Section5.Field
