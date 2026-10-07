/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Fourier algebra for the vector potential

These coordinate identities encode the curl-inverse-Laplacian symbol in
`eq:J-vector-potential`.
-/

public section

open scoped FourierTransform ENNReal BoundedContinuousFunction SchwartzMap
open MeasureTheory
open Filter
open scoped Topology



namespace CKN

noncomputable section

/-- Complex-valued Euclidean three-vectors used as Fourier transform values. -/
abbrev FourierVec3 := PiLp 2 (fun _ : Fin 3 => ℂ)

/-- A real spatial field, viewed on the Euclidean spatial carrier with
complex-valued vector components. -/
@[expose]
def complexifyVec3 (a : CKN.Foundation.Parabolic.Vec3 → CKN.Foundation.Parabolic.Vec3) :
    CKN.Foundation.Parabolic.L2Vec3 → FourierVec3 :=
  fun x => WithLp.toLp 2 (fun i => (a (WithLp.ofLp x) i : ℂ))

/-- Complexification preserves square integrability on the Euclidean spatial
carrier. -/
theorem complexifyVec3_memLp
    {a : CKN.Foundation.Parabolic.Vec3 → CKN.Foundation.Parabolic.Vec3}
    (ha : MeasureTheory.MemLp a (2 : ℝ≥0∞) volume) :
    MeasureTheory.MemLp (complexifyVec3 a) (2 : ℝ≥0∞) volume := by
  apply MeasureTheory.MemLp.of_eval_piLp
  intro i
  have hcoord : MeasureTheory.MemLp (fun x : CKN.Foundation.Parabolic.Vec3 => a x i)
      (2 : ℝ≥0∞) volume := ha.eval i
  have hcoordE : MeasureTheory.MemLp
      (fun x : CKN.Foundation.Parabolic.L2Vec3 => a (WithLp.ofLp x) i)
      (2 : ℝ≥0∞) volume :=
    hcoord.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  have hcomplex := Complex.isometry_ofReal.lipschitzWith.comp_memLp Complex.ofReal_zero hcoordE
  simpa [complexifyVec3, Function.comp_def] using hcomplex















/-- The coordinate of a frequency vector when it is regarded as a point of
the native Euclidean spatial carrier. -/
@[expose]
def frequencyL2Coord (i : Fin 3) : CKN.Foundation.Parabolic.L2Vec3 →L[ℝ] ℝ :=
  PiLp.proj 2 (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) i

/-- A frequency coordinate rescaled by a positive regularization length. -/
@[expose]
def regularizedFrequencyCoord (δ : ℝ) (i : Fin 3)
    (ξ : CKN.Foundation.Parabolic.L2Vec3) : ℝ :=
  δ⁻¹ * frequencyL2Coord i ξ

/-- The regularized inverse of `1 + |ξ/δ|²` used to remove the singularity at
zero frequency from the potential multiplier. -/
@[expose]
def regularizedFrequencyWeight (δ : ℝ)
    (ξ : CKN.Foundation.Parabolic.L2Vec3) : ℝ :=
  (1 + ‖(δ⁻¹ : ℝ) • ξ‖ ^ 2) ^ (-1 : ℝ)

/-- An entry of the regularized curl-inverse-Laplacian multiplier. -/
@[expose]
def regularizedPotentialEntry (δ : ℝ) (i : Fin 3)
    (ξ : CKN.Foundation.Parabolic.L2Vec3) : ℂ :=
  (Complex.I / (2 * Real.pi * δ)) *
    (regularizedFrequencyCoord δ i ξ : ℂ) *
    (regularizedFrequencyWeight δ ξ : ℂ)

/-- The regularized frequency weight is a smooth multiplier of temperate
growth. -/
@[fun_prop]
theorem regularizedFrequencyWeight_hasTemperateGrowth (δ : ℝ) :
    (regularizedFrequencyWeight δ).HasTemperateGrowth := by
  change (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
    (1 + ‖(δ⁻¹ : ℝ) • ξ‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth
  have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow
    CKN.Foundation.Parabolic.L2Vec3 (-1 : ℝ)
  have hscale : (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
      (δ⁻¹ : ℝ) • ξ).HasTemperateGrowth := by fun_prop
  exact h.comp hscale

/-- Each rescaled frequency coordinate has temperate growth. -/
@[fun_prop]
theorem regularizedFrequencyCoord_hasTemperateGrowth (δ : ℝ) (i : Fin 3) :
    (regularizedFrequencyCoord δ i).HasTemperateGrowth := by
  change (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
    δ⁻¹ * frequencyL2Coord i ξ).HasTemperateGrowth
  have hcoord : (fun ξ => frequencyL2Coord i ξ).HasTemperateGrowth :=
    _root_.ContinuousLinearMap.hasTemperateGrowth (frequencyL2Coord i)
  exact (Function.HasTemperateGrowth.const δ⁻¹).mul hcoord

/-- The regularized potential multiplier entry is of temperate growth, so it
acts on tempered distributions. -/
theorem regularizedPotentialEntry_hasTemperateGrowth (δ : ℝ) (i : Fin 3) :
    (regularizedPotentialEntry δ i).HasTemperateGrowth := by
  change (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
    (Complex.I / (2 * Real.pi * δ)) *
      Complex.ofReal (regularizedFrequencyCoord δ i ξ) *
      Complex.ofReal (regularizedFrequencyWeight δ ξ)).HasTemperateGrowth
  have hconstant : (fun _ : CKN.Foundation.Parabolic.L2Vec3 =>
      Complex.I / (2 * Real.pi * δ)).HasTemperateGrowth :=
    Function.HasTemperateGrowth.const _
  have hcoord : (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
      Complex.ofReal (regularizedFrequencyCoord δ i ξ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      (regularizedFrequencyCoord_hasTemperateGrowth δ i)
  have hweight : (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
      Complex.ofReal (regularizedFrequencyWeight δ ξ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      (regularizedFrequencyWeight_hasTemperateGrowth δ)
  exact (hconstant.mul hcoord).mul hweight

/-- A coordinate of a vector in the Euclidean `L²` product norm is bounded
by the full vector norm. -/
theorem frequencyL2Coord_abs_le (ξ : CKN.Foundation.Parabolic.L2Vec3) (i : Fin 3) :
    |frequencyL2Coord i ξ| ≤ ‖ξ‖ := by
  change |ξ.ofLp i| ≤ ‖ξ‖
  have hcoordSq : (ξ.ofLp i) ^ 2 ≤ ∑ j : Fin 3, (ξ.ofLp j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (ξ.ofLp j)) (Finset.mem_univ i)
  have hroot : √((ξ.ofLp i) ^ 2) ≤ √(∑ j : Fin 3, (ξ.ofLp j) ^ 2) :=
    Real.sqrt_le_sqrt hcoordSq
  have hcoord : √((ξ.ofLp i) ^ 2) = |ξ.ofLp i| := Real.sqrt_sq_eq_abs _
  have hnorm : ‖ξ‖ = √(∑ j : Fin 3, (ξ.ofLp j) ^ 2) := by
    rw [PiLp.norm_eq_sum (p := (2 : ENNReal)) (by norm_num) ξ]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  rw [← hcoord, hnorm]
  exact hroot

/-- The scaled coordinate is the corresponding coordinate of the scaled
frequency vector. -/
theorem regularizedFrequencyCoord_eq_scaled
    (δ : ℝ) (i : Fin 3) (ξ : CKN.Foundation.Parabolic.L2Vec3) :
    regularizedFrequencyCoord δ i ξ =
      frequencyL2Coord i ((δ⁻¹ : ℝ) • ξ) := by
  simp [regularizedFrequencyCoord, frequencyL2Coord, PiLp.proj_apply]

/-- The first-order regularized symbol is bounded by the input frequency
vector. -/
theorem regularizedFrequencyCoord_mul_weight_abs_le_one
    (δ : ℝ) (ξ : CKN.Foundation.Parabolic.L2Vec3) (i : Fin 3) :
    |regularizedFrequencyCoord δ i ξ * regularizedFrequencyWeight δ ξ| ≤ 1 := by
  let η : CKN.Foundation.Parabolic.L2Vec3 := (δ⁻¹ : ℝ) • ξ
  have hcoord : |frequencyL2Coord i η| ≤ ‖η‖ := frequencyL2Coord_abs_le η i
  have hη : 0 ≤ ‖η‖ := norm_nonneg η
  have hweight : regularizedFrequencyWeight δ ξ = 1 / (1 + ‖η‖ ^ 2) := by
    rw [regularizedFrequencyWeight, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖η‖ ^ 2)]
    simp [η, Real.rpow_one]
  rw [regularizedFrequencyCoord_eq_scaled, hweight, abs_mul, abs_div, abs_one,
    abs_of_pos (by positivity : 0 < 1 + ‖η‖ ^ 2)]
  have hineq : ‖η‖ ≤ 1 + ‖η‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖η‖ - (1 / 2 : ℝ))]
  calc
    |frequencyL2Coord i η| * (1 / (1 + ‖η‖ ^ 2)) =
        |frequencyL2Coord i η| / (1 + ‖η‖ ^ 2) := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 (hcoord.trans hineq)

/-- The second-order regularized scalar multipliers are bounded by one. -/
theorem regularizedFrequencyCoordProduct_mul_weight_abs_le_one
    (δ : ℝ) (ξ : CKN.Foundation.Parabolic.L2Vec3) (i j : Fin 3) :
    |regularizedFrequencyCoord δ i ξ * regularizedFrequencyCoord δ j ξ *
      regularizedFrequencyWeight δ ξ| ≤ 1 := by
  let η : CKN.Foundation.Parabolic.L2Vec3 := (δ⁻¹ : ℝ) • ξ
  have hi : |frequencyL2Coord i η| ≤ ‖η‖ := frequencyL2Coord_abs_le η i
  have hj : |frequencyL2Coord j η| ≤ ‖η‖ := frequencyL2Coord_abs_le η j
  have hη : 0 ≤ ‖η‖ := norm_nonneg η
  have hweight : regularizedFrequencyWeight δ ξ = 1 / (1 + ‖η‖ ^ 2) := by
    rw [regularizedFrequencyWeight, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖η‖ ^ 2)]
    simp [η, Real.rpow_one]
  rw [regularizedFrequencyCoord_eq_scaled, regularizedFrequencyCoord_eq_scaled,
    hweight, abs_mul, abs_mul, abs_div, abs_one,
    abs_of_pos (by positivity : 0 < 1 + ‖η‖ ^ 2)]
  have hprod : |frequencyL2Coord i η| * |frequencyL2Coord j η| ≤ ‖η‖ ^ 2 := by
    calc
      |frequencyL2Coord i η| * |frequencyL2Coord j η| ≤ ‖η‖ * ‖η‖ :=
        mul_le_mul hi hj (abs_nonneg _) hη
      _ = ‖η‖ ^ 2 := by ring
  calc
    |frequencyL2Coord i η| * |frequencyL2Coord j η| *
        (1 / (1 + ‖η‖ ^ 2)) =
        (|frequencyL2Coord i η| * |frequencyL2Coord j η|) /
          (1 + ‖η‖ ^ 2) := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 (by
      calc
        |frequencyL2Coord i η| * |frequencyL2Coord j η| ≤ ‖η‖ ^ 2 := hprod
        _ ≤ 1 + ‖η‖ ^ 2 := by nlinarith only [sq_nonneg (‖η‖ - (1 / 2 : ℝ))])

/-- The regularized vector-potential multiplier is bounded for each fixed
positive regularization length. -/
theorem regularizedPotentialEntry_norm_le
    (δ : ℝ) (hδ : 0 < δ) (ξ : CKN.Foundation.Parabolic.L2Vec3) (i : Fin 3) :
    ‖regularizedPotentialEntry δ i ξ‖ ≤ 1 / (2 * Real.pi * δ) := by
  have hconst : 0 < 2 * Real.pi * δ := by positivity
  have hcoord := regularizedFrequencyCoord_mul_weight_abs_le_one δ ξ i
  have hdenom :
      ‖(2 : ℂ) * (Real.pi : ℂ) * (δ : ℂ)‖ = 2 * Real.pi * δ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hδ]
  have hweight : 0 ≤ regularizedFrequencyWeight δ ξ := by
    exact Real.rpow_nonneg (by positivity) _
  have hnormcoord :
      ‖(regularizedFrequencyCoord δ i ξ : ℂ)‖ =
        |regularizedFrequencyCoord δ i ξ| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hnormweight :
      ‖(regularizedFrequencyWeight δ ξ : ℂ)‖ = regularizedFrequencyWeight δ ξ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hweight]
  rw [regularizedPotentialEntry, norm_mul, norm_mul, Complex.norm_div, Complex.norm_I,
    hdenom, hnormcoord, hnormweight]
  calc
    (1 / (2 * Real.pi * δ)) * |regularizedFrequencyCoord δ i ξ| *
        regularizedFrequencyWeight δ ξ ≤
      (1 / (2 * Real.pi * δ)) * 1 := by
      calc
        _ = (1 / (2 * Real.pi * δ)) *
            (|regularizedFrequencyCoord δ i ξ| * regularizedFrequencyWeight δ ξ) := by ring
        _ = (1 / (2 * Real.pi * δ)) *
            |regularizedFrequencyCoord δ i ξ * regularizedFrequencyWeight δ ξ| := by
              rw [abs_mul, abs_of_nonneg hweight]
        _ ≤ (1 / (2 * Real.pi * δ)) * 1 :=
          mul_le_mul_of_nonneg_left hcoord (by positivity)
    _ = 1 / (2 * Real.pi * δ) := by ring

/-- A first-derivative multiplier entry for the regularized vector
potential. -/
@[expose]
def regularizedDerivativeEntry (δ : ℝ) (k j : Fin 3)
    (ξ : CKN.Foundation.Parabolic.L2Vec3) : ℂ :=
  -Complex.ofReal (regularizedFrequencyCoord δ k ξ *
    regularizedFrequencyCoord δ j ξ * regularizedFrequencyWeight δ ξ)

/-- The first-derivative multiplier is of temperate growth. -/
theorem regularizedDerivativeEntry_hasTemperateGrowth
    (δ : ℝ) (k j : Fin 3) :
    (regularizedDerivativeEntry δ k j).HasTemperateGrowth := by
  change (fun ξ : CKN.Foundation.Parabolic.L2Vec3 =>
    -Complex.ofReal (regularizedFrequencyCoord δ k ξ *
      regularizedFrequencyCoord δ j ξ * regularizedFrequencyWeight δ ξ)).HasTemperateGrowth
  fun_prop

/-- The first-derivative multiplier entry is bounded by one. -/
theorem regularizedDerivativeEntry_norm_le
    (δ : ℝ) (k j : Fin 3) (ξ : CKN.Foundation.Parabolic.L2Vec3) :
    ‖regularizedDerivativeEntry δ k j ξ‖ ≤ 1 := by
  rw [regularizedDerivativeEntry, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have h := regularizedFrequencyCoordProduct_mul_weight_abs_le_one δ ξ k j
  simpa [abs_mul, mul_assoc] using h

/-- Multiplying a potential symbol by the Fourier derivative symbol gives
the bounded first-derivative entry. -/
theorem regularizedDerivativeEntry_eq_frequency_mul_potential
    (δ : ℝ) (hδ : 0 < δ) (ξ : CKN.Foundation.Parabolic.L2Vec3)
    (k j : Fin 3) :
    regularizedDerivativeEntry δ k j ξ =
      (2 * Real.pi : ℂ) * Complex.I *
        Complex.ofReal (frequencyL2Coord k ξ) * regularizedPotentialEntry δ j ξ := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hden : ((2 * Real.pi * δ : ℝ) : ℂ) ≠ 0 := by
    have hdenR : 2 * Real.pi * δ ≠ 0 := by positivity
    exact_mod_cast hdenR
  rw [regularizedDerivativeEntry, regularizedPotentialEntry]
  simp only [regularizedFrequencyCoord, frequencyL2Coord, PiLp.proj_apply]
  push_cast
  field_simp [hδc, hden]
  rw [Complex.I_sq]
  ring

/-- A bounded temperate complex multiplier belongs to `L∞`. -/
theorem boundedComplexMultiplier_memLp
    (g : CKN.Foundation.Parabolic.L2Vec3 → ℂ)
    (hg : Function.HasTemperateGrowth g) {C : ℝ}
    (hbound : ∀ ξ, ‖g ξ‖ ≤ C) :
    MeasureTheory.MemLp g (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3) := by
  let g' : CKN.Foundation.Parabolic.L2Vec3 →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous C hbound
  exact g'.memLp_top

/-- Multiplication by a bounded Fourier symbol on scalar `L²`. -/
@[expose]
noncomputable def fourierMultiplyScalarL2
    (g : CKN.Foundation.Parabolic.L2Vec3 → ℂ)
    (hg : MeasureTheory.MemLp g (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3))
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2 :=
  hg.toLp g • f


private theorem fourierMultiplyScalarL2_norm_le_ae
    {g : CKN.Foundation.Parabolic.L2Vec3 → ℂ}
    (hg : MeasureTheory.MemLp g (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3))
    (hbound : ∀ ξ, ‖g ξ‖ ≤ 1)
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    ∀ᵐ ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3),
      ‖fourierMultiplyScalarL2 g hg f ξ‖ ≤ ‖f ξ‖ := by
  filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (r := 2) (hg.toLp g) f,
    hg.coeFn_toLp] with ξ hprod hmult
  change ‖(hg.toLp g • f) ξ‖ ≤ ‖f ξ‖
  rw [hprod]
  change ‖(hg.toLp g ξ) • f ξ‖ ≤ ‖f ξ‖
  rw [hmult, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hbound ξ)

private theorem fourierMultiplierSequence_tendsto_ae
    {g : ℕ → CKN.Foundation.Parabolic.L2Vec3 → ℂ}
    (hg : ∀ n, MeasureTheory.MemLp (g n) (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3))
    (hpoint : ∀ᵐ ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3),
      Tendsto (fun n => g n ξ) atTop (𝓝 0))
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    ∀ᵐ ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3),
      Tendsto (fun n => fourierMultiplyScalarL2 (g n) (hg n) f ξ) atTop (𝓝 0) := by
  have hrep (n : ℕ) : ∀ᵐ ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3),
      fourierMultiplyScalarL2 (g n) (hg n) f ξ = g n ξ * f ξ := by
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (r := 2) ((hg n).toLp (g n)) f,
      (hg n).coeFn_toLp] with ξ hprod hmult
    change (((hg n).toLp (g n) • f) ξ) = _
    rw [hprod]
    change (((hg n).toLp (g n) ξ) • f ξ) = _
    rw [hmult, smul_eq_mul]
  filter_upwards [hpoint, ae_all_iff.2 hrep] with ξ hξ heq
  have hmultiply : Tendsto (fun n => g n ξ * f ξ) atTop (𝓝 0) := by
    simpa using hξ.mul_const (f ξ)
  exact hmultiply.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

/-- A uniformly bounded sequence of Fourier multipliers that converges
almost everywhere to zero converges strongly to zero on each square-integrable input. -/
theorem fourierMultiplyScalarL2_tendsto_zero_of_tendsto_ae
    {g : ℕ → CKN.Foundation.Parabolic.L2Vec3 → ℂ}
    (hg : ∀ n, MeasureTheory.MemLp (g n) (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3))
    (hbound : ∀ n ξ, ‖g n ξ‖ ≤ 1)
    (hpoint : ∀ᵐ ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3),
      Tendsto (fun n => g n ξ) atTop (𝓝 0))
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    Tendsto (fun n => MeasureTheory.eLpNorm
      (fourierMultiplyScalarL2 (g n) (hg n) f) 2
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3)) atTop (𝓝 0) := by
  let u : ℕ → CKN.Foundation.Parabolic.L2Vec3 → ℂ :=
    fun n ξ => fourierMultiplyScalarL2 (g n) (hg n) f ξ
  let F : ℕ → CKN.Foundation.Parabolic.L2Vec3 → ℝ≥0∞ :=
    fun n ξ => ‖u n ξ‖ₑ ^ (2 : ℝ)
  let B : CKN.Foundation.Parabolic.L2Vec3 → ℝ≥0∞ :=
    fun ξ => ‖f ξ‖ₑ ^ (2 : ℝ)
  have hf : MeasureTheory.MemLp (f : CKN.Foundation.Parabolic.L2Vec3 → ℂ) 2
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3) := MeasureTheory.Lp.memLp f
  have hB : MeasureTheory.Integrable B (volume : Measure CKN.Foundation.Parabolic.L2Vec3) := by
    rw [← MeasureTheory.memLp_one_iff_integrable]
    simpa [B, ENNReal.toReal_ofNat] using
      hf.enorm_rpow (by norm_num) (by norm_num)
  have hfinite : (∫⁻ ξ, B ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3)) ≠ ∞ := by
    have h := (MeasureTheory.hasFiniteIntegral_iff_enorm).mp hB.hasFiniteIntegral
    exact ne_of_lt (by simpa [B, enorm_eq_self] using h)
  have hmeas (n : ℕ) : AEMeasurable (F n)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3) := by
    have hu : AEStronglyMeasurable (u n)
        (volume : Measure CKN.Foundation.Parabolic.L2Vec3) :=
      (MeasureTheory.Lp.memLp (fourierMultiplyScalarL2 (g n) (hg n) f)).aestronglyMeasurable
    change AEMeasurable (fun ξ => ‖u n ξ‖ₑ ^ (2 : ℝ)) _
    exact (ENNReal.continuous_rpow_const.comp_aestronglyMeasurable hu.enorm.aestronglyMeasurable)
      |>.aemeasurable
  have hdom (n : ℕ) : F n ≤ᵐ[volume] B := by
    filter_upwards [fourierMultiplyScalarL2_norm_le_ae (hg n) (hbound n) f] with ξ hξ
    exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr hξ) (by norm_num)
  have hseq := fourierMultiplierSequence_tendsto_ae hg hpoint f
  have hlimit : ∀ᵐ ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3),
      Tendsto (fun n => F n ξ) atTop (𝓝 0) := by
    filter_upwards [hseq] with ξ hξ
    have hnorm : Tendsto (fun n => ‖u n ξ‖ₑ) atTop (𝓝 0) := by
      change Tendsto ((fun z : ℂ => ‖z‖ₑ) ∘
        (fun n => fourierMultiplyScalarL2 (g n) (hg n) f ξ)) atTop (𝓝 0)
      simpa using (continuous_enorm.tendsto (0 : ℂ)).comp hξ
    have hpow :=
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞)
    have hpow' := hpow.comp hnorm
    have hpow'' : Tendsto (fun n => ‖u n ξ‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
      change Tendsto ((fun z : ℝ≥0∞ => z ^ (2 : ℝ)) ∘
        (fun n => ‖u n ξ‖ₑ)) atTop (𝓝 0)
      simpa using hpow'
    simpa [F] using hpow''
  have hIntegral := MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    B hmeas hdom hfinite hlimit
  have hIntegralZero : Tendsto
      (fun n => ∫⁻ ξ, F n ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3))
      atTop (𝓝 0) := by
    simpa using hIntegral
  have hRoot : Tendsto
      (fun n => (∫⁻ ξ, F n ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3)) ^
        (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa using hIntegralZero.ennrpow_const (1 / 2 : ℝ)
  have hformula (n : ℕ) :
      MeasureTheory.eLpNorm (fourierMultiplyScalarL2 (g n) (hg n) f) 2
        (volume : Measure CKN.Foundation.Parabolic.L2Vec3) =
        (∫⁻ ξ, F n ξ ∂(volume : Measure CKN.Foundation.Parabolic.L2Vec3)) ^
          (1 / 2 : ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      ((MeasureTheory.Lp.memLp (fourierMultiplyScalarL2 (g n) (hg n) f)).aestronglyMeasurable)]
    congr 1
  exact hRoot.congr' (Filter.Eventually.of_forall fun n => (hformula n).symm)


/-- The same multiplier identity when the `L∞` membership is supplied
directly. -/
theorem fourierMultiplyScalarL2_toTemperedDistribution_of_memLp
    (g : CKN.Foundation.Parabolic.L2Vec3 → ℂ)
    (hg : Function.HasTemperateGrowth g)
    (hmem : MeasureTheory.MemLp g (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3))
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    (fourierMultiplyScalarL2 g hmem f :
      𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ g
        (f : 𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : ENNReal.HolderTriple (⊤ : ℝ≥0∞) 2 2 := ⟨by simp⟩
  have hmul := MeasureTheory.Lp.toTemperedDistribution_smul_eq
    (p := (⊤ : ℝ≥0∞)) (q := 2) (r := 2) hg hmem f
  simpa [fourierMultiplyScalarL2] using hmul

/-- The inverse Fourier transform of an `L²` multiplier is the corresponding
tempered-distribution Fourier multiplier. -/
theorem inverseFourier_fourierMultiplyScalarL2_eq_fourierMultiplierCLM
    (g : CKN.Foundation.Parabolic.L2Vec3 → ℂ)
    (hg : Function.HasTemperateGrowth g)
    (hmem : MeasureTheory.MemLp g (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3))
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    ((𝓕⁻ (fourierMultiplyScalarL2 g hmem (𝓕 f)) :
      MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2
        (volume : Measure CKN.Foundation.Parabolic.L2Vec3)) :
      𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ g
        (f : 𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ)) := by
  rw [TemperedDistribution.fourierMultiplierCLM_apply]
  rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq]
  apply congrArg (fun d : 𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ) => 𝓕⁻ d)
  calc
    (fourierMultiplyScalarL2 g hmem (𝓕 f) :
        𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ g
        ((𝓕 f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2
          (volume : Measure CKN.Foundation.Parabolic.L2Vec3)) :
          𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ)) :=
      fourierMultiplyScalarL2_toTemperedDistribution_of_memLp g hg hmem (𝓕 f)
    _ = TemperedDistribution.smulLeftCLM ℂ g
        (𝓕 (f : 𝓢'(CKN.Foundation.Parabolic.L2Vec3, ℂ))) := by
      rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq f]

/-- The regularized potential coefficient is an `L∞` Fourier multiplier. -/
theorem regularizedPotentialEntry_memLp
    (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) :
    MeasureTheory.MemLp (regularizedPotentialEntry δ i) (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3) :=
  boundedComplexMultiplier_memLp (regularizedPotentialEntry δ i)
    (regularizedPotentialEntry_hasTemperateGrowth δ i)
    (C := 1 / (2 * Real.pi * δ))
    (fun ξ => regularizedPotentialEntry_norm_le δ hδ ξ i)

/-- Each first-derivative symbol entry is an `L∞` Fourier multiplier. -/
theorem regularizedDerivativeEntry_memLp
    (δ : ℝ) (k j : Fin 3) :
    MeasureTheory.MemLp (regularizedDerivativeEntry δ k j) (⊤ : ℝ≥0∞)
      (volume : Measure CKN.Foundation.Parabolic.L2Vec3) :=
  boundedComplexMultiplier_memLp (regularizedDerivativeEntry δ k j)
    (regularizedDerivativeEntry_hasTemperateGrowth δ k j)
    (C := 1)
    (fun ξ => regularizedDerivativeEntry_norm_le δ k j ξ)

/-- Applying a bounded first-derivative symbol to a scalar frequency
component. -/
@[expose]
noncomputable def regularizedDerivativeEntryApply
    (δ : ℝ) (k j : Fin 3)
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2 :=
  fourierMultiplyScalarL2 (regularizedDerivativeEntry δ k j)
    (regularizedDerivativeEntry_memLp δ k j) f

/-- Applying a regularized potential coefficient to one scalar frequency
component. -/
@[expose]
noncomputable def regularizedPotentialEntryApply
    (δ : ℝ) (hδ : 0 < δ) (i : Fin 3)
    (f : MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2 :=
  fourierMultiplyScalarL2 (regularizedPotentialEntry δ i)
    (regularizedPotentialEntry_memLp δ hδ i) f

/-- The three component formulas for the regularized Fourier vector
potential. -/
@[expose]
noncomputable def regularizedPotentialFourierComponent
    (δ : ℝ) (hδ : 0 < δ) (i : Fin 3)
    (f : Fin 3 → MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2 :=
  if _hi : i = 0 then
    regularizedPotentialEntryApply δ hδ 1 (f 2) -
      regularizedPotentialEntryApply δ hδ 2 (f 1)
  else if _hi : i = 1 then
    regularizedPotentialEntryApply δ hδ 2 (f 0) -
      regularizedPotentialEntryApply δ hδ 0 (f 2)
  else
    regularizedPotentialEntryApply δ hδ 0 (f 1) -
      regularizedPotentialEntryApply δ hδ 1 (f 0)

/-- The spatial `L²` regularized vector potential, obtained by inverse
Fourier transformation of its three component multipliers. -/
@[expose]
noncomputable def regularizedPotentialL2Component
    (δ : ℝ) (hδ : 0 < δ) (i : Fin 3)
    (f : Fin 3 → MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2) :
    MeasureTheory.Lp (α := CKN.Foundation.Parabolic.L2Vec3) ℂ 2 :=
  𝓕⁻ (regularizedPotentialFourierComponent δ hδ i f)

end

end CKN
