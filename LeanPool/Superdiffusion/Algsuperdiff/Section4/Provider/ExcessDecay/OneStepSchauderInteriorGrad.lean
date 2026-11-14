/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderReproducing
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# OneStepSchauderInteriorGrad

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Differentiating the reproducing convolution; the `L²`/`L¹` bookkeeping

* **The pointwise gradient half.**  Differentiating the reproducing
  convolution once moves the derivative onto the kernel:
  `∇w(x₀) = ((∇K_ε) ⋆ w)(x₀)`, hence
  `‖∇w(x₀)‖ ≤ ‖∇K_ε‖_∞ · ∫_{B(x₀,2ε)} |w|`.
* **The `L²` half.**  The Cauchy–Schwarz upgrade `(∫_s |f|)²
  ≤ |s| · ∫_s f²` (`sq_setIntegral_abs_le`) and the measure-preserving transfer
  of the CoarseGraining `meanSquareDeviationOn` on `euclideanBall` to the
  volume-normalized `L²` deviation on the Mathlib metric ball
  (`meanSquareDeviationOn_euclideanBall_eq`).
-/

-- ==== interior gradient estimate ====
open scoped Real Convolution Topology Laplacian
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Constant-subtraction stays harmonic -/

/-- A constant function is harmonic in a neighbourhood of any set. -/
theorem harmonicOnNhd_const (c : ℝ) (s : Set 𝔼) : HarmonicOnNhd (fun _ : 𝔼 => c) s := by
  intro x _
  refine ⟨contDiffAt_const, ?_⟩
  have hΔ : Δ (fun _ : 𝔼 => c) = 0 := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun _ : 𝔼 => c)]
    funext y
    simp [iteratedFDeriv_const_of_ne (n := 2) (by norm_num)]
  rw [hΔ]

/-- A harmonic function minus a constant is harmonic. -/
theorem harmonicOnNhd_sub_const {v : 𝔼 → ℝ} {s : Set 𝔼} (hv : HarmonicOnNhd v s) (c : ℝ) :
    HarmonicOnNhd (fun y => v y - c) s := by
  have hfun : (fun y : 𝔼 => v y - c) = v + fun _ => (-c) := by funext y; simp [sub_eq_add_neg]
  rw [hfun]
  exact hv.add (harmonicOnNhd_const (-c) s)

/-! ### The core estimate -/

/-! ### The interior gradient bound -/

end
end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== interior gradient estimate, `L²` form ====
open scoped Real Convolution Topology
open MeasureTheory Metric Set InnerProductSpace
open HCPolySupport (Vec euclideanBall volumeAverage)
open HCPolySupport.Book.Ch01 (meanSquareDeviationOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### A sup bound for the unit-kernel gradient -/

/-! ### The core `L¹` gradient bound -/

/-! ### Cauchy–Schwarz on the ball -/

/-- **Cauchy–Schwarz on a finite-measure set.**  `(∫_s |f|)² ≤ vol(s) · ∫_s f²`
for `f` a.e.-bounded on
`s`.  Applied with `s` a ball and `f = w`. -/
theorem sq_setIntegral_abs_le (s : Set 𝔼) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    {f : 𝔼 → ℝ} {Mf : ℝ} (hf : AEStronglyMeasurable f (volume.restrict s))
    (hfb : ∀ᵐ y ∂(volume.restrict s), |f y| ≤ Mf) :
    (∫ y in s, |f y| ∂volume) ^ 2 ≤ (volume s).toReal * ∫ y in s, (f y) ^ 2 ∂volume := by
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμ.lt_top⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hmem_f : MemLp (fun y => |f y|) (ENNReal.ofReal 2) (volume.restrict s) :=
    MemLp.of_bound (continuous_abs.comp_aestronglyMeasurable hf) Mf (by
      filter_upwards [hfb] with y hy; rwa [Real.norm_eq_abs, abs_abs])
  have hmem_1 : MemLp (fun _ : 𝔼 => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict s) := memLp_const 1
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun y => abs_nonneg (f y)))
    (Filter.Eventually.of_forall (fun _ => (zero_le_one : (0 : ℝ) ≤ 1))) hmem_f hmem_1
  have e1 : ∫ y in s, |f y| * (1 : ℝ) ∂volume = ∫ y in s, |f y| ∂volume := by simp
  have e2 : ∫ _y in s, ((1 : ℝ)) ^ (2 : ℝ) ∂volume = (volume s).toReal := by
    simp only [Real.one_rpow, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have e3 : ∫ y in s, |f y| ^ (2 : ℝ) ∂volume = ∫ y in s, (f y) ^ 2 ∂volume := by
    refine setIntegral_congr_fun hs (fun y _ => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e3, e2] at hCS
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have hf2nonneg : 0 ≤ ∫ y in s, (f y) ^ 2 ∂volume := setIntegral_nonneg hs (fun y _ => sq_nonneg _)
  have habs_nonneg : 0 ≤ ∫ y in s, |f y| ∂volume := setIntegral_nonneg hs (fun y _ => abs_nonneg _)
  calc (∫ y in s, |f y| ∂volume) ^ 2
      ≤ (Real.sqrt (∫ y in s, (f y) ^ 2 ∂volume) * Real.sqrt (volume s).toReal) ^ 2 :=
        pow_le_pow_left₀ habs_nonneg hCS 2
    _ = (volume s).toReal * ∫ y in s, (f y) ^ 2 ∂volume := by
        rw [mul_pow, Real.sq_sqrt hf2nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]; ring

/-! ### The measure-preserving coordinate transfer -/

/-- `toEuc = toLp 2` is volume preserving (it is the identity on underlying data). -/
theorem measurePreserving_toEuc (d : ℕ) :
    MeasurePreserving (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) volume volume :=
  PiLp.volume_preserving_toLp (Fin d)

theorem measurableEmbedding_toEuc (d : ℕ) :
    MeasurableEmbedding (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) :=
  (toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toHomeomorph.measurableEmbedding

theorem preimage_ball_toEuc (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    toEuc ⁻¹' (Metric.ball x r) = euclideanBall (toEuc.symm x) r := by
  ext a
  rw [Set.mem_preimage, show x = toEuc (toEuc.symm x) from (toEuc.apply_symm_apply x).symm]
  exact mem_euclideanBall_toEuc_iff a (toEuc.symm x) hr

/-- **Transfer of the mean-square deviation.**  The CoarseGraining volume-averaged
mean-square deviation on the explicit `euclideanBall`, of `u ∘ toEuc`, equals
the volume-normalized `L²` deviation of `u` on the mathlib metric ball, via the
measure-preserving identification `toEuc`. -/
theorem meanSquareDeviationOn_euclideanBall_eq (u : 𝔼 → ℝ) (x : 𝔼) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c
      = (volume (Metric.ball x r)).toReal⁻¹ * ∫ z in Metric.ball x r, (u z - c) ^ 2 ∂volume := by
  have hpre : toEuc ⁻¹' (Metric.ball x r) = euclideanBall (toEuc.symm x) r :=
    preimage_ball_toEuc x hr
  have hvol : volume (euclideanBall (toEuc.symm x) r) = volume (Metric.ball x r) := by
    rw [← hpre, (measurePreserving_toEuc d).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  have hint : ∫ y in euclideanBall (toEuc.symm x) r, ((u ∘ toEuc) y - c) ^ 2 ∂volume
      = ∫ z in Metric.ball x r, (u z - c) ^ 2 ∂volume := by
    rw [← hpre]
    exact (measurePreserving_toEuc d).setIntegral_preimage_emb (measurableEmbedding_toEuc d)
      (fun z => (u z - c) ^ 2) (Metric.ball x r)
  simp only [meanSquareDeviationOn, volumeAverage]
  rw [hvol, hint]

/-! ### The interior gradient estimate, `L²`-deviation shape (native) -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

