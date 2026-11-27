/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Mixed derivative control of the actual six-dimensional kernel transform

The carrier is the real Hilbert product, with its actual Euclidean volume.
The two factors of the frequency weight arise from the first derivatives
in each variable and their mixed derivatives. All integrals are genuine
Schwartz integrals; no kernel-operator or source-norm estimate is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap FourierTransform LineDeriv

section MixedPlancherel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem norm_sq_fourier_lineDeriv (K : SchwartzMap V ℂ) (v ξ : V) :
    ‖(𝓕 (∂_{v} K)) ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (inner ℝ ξ v) ^ 2 * ‖(𝓕 K) ξ‖ ^ 2 := by
  have hv : Function.HasTemperateGrowth (inner ℝ · v) :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hv,
    norm_smul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow, sq_abs]
  ring

/-- Mixed kernel frequency weight. -/
def mixedKernelFrequencyWeight (u : ι → V) (v : κ → V) (ξ : V) : ℝ :=
  (1 + (2 * Real.pi) ^ 2 * ∑ i, (inner ℝ ξ (u i)) ^ 2) *
    (1 + (2 * Real.pi) ^ 2 * ∑ j, (inner ℝ ξ (v j)) ^ 2)

/-- Mixed kernel derivative energy. -/
def mixedKernelDerivativeEnergy (u : ι → V) (v : κ → V)
    (K : SchwartzMap V ℂ) : ℝ :=
  (∫ x, ‖K x‖ ^ 2) + (∑ i, ∫ x, ‖(∂_{u i} K) x‖ ^ 2) +
    (∑ j, ∫ x, ‖(∂_{v j} K) x‖ ^ 2) +
      ∑ i, ∑ j, ∫ x, ‖(∂_{u i} (∂_{v j} K)) x‖ ^ 2

theorem mixedKernelFrequencyWeight_mul_norm_sq (u : ι → V) (v : κ → V)
    (K : SchwartzMap V ℂ) (ξ : V) :
    mixedKernelFrequencyWeight u v ξ * ‖(𝓕 K) ξ‖ ^ 2 =
      ‖(𝓕 K) ξ‖ ^ 2 + (∑ i, ‖(𝓕 (∂_{u i} K)) ξ‖ ^ 2) +
        (∑ j, ‖(𝓕 (∂_{v j} K)) ξ‖ ^ 2) +
          ∑ i, ∑ j, ‖(𝓕 (∂_{u i} (∂_{v j} K))) ξ‖ ^ 2 := by
  simp only [mixedKernelFrequencyWeight, norm_sq_fourier_lineDeriv]
  have hleft : (∑ i, (2 * Real.pi) ^ 2 * (inner ℝ ξ (u i)) ^ 2 * ‖(𝓕 K) ξ‖ ^ 2) =
      (2 * Real.pi) ^ 2 * (∑ i, (inner ℝ ξ (u i)) ^ 2) * ‖(𝓕 K) ξ‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hright : (∑ j, (2 * Real.pi) ^ 2 * (inner ℝ ξ (v j)) ^ 2 * ‖(𝓕 K) ξ‖ ^ 2) =
      (2 * Real.pi) ^ 2 * (∑ j, (inner ℝ ξ (v j)) ^ 2) * ‖(𝓕 K) ξ‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hboth : (∑ i, ∑ j, (2 * Real.pi) ^ 2 * (inner ℝ ξ (u i)) ^ 2 *
      ((2 * Real.pi) ^ 2 * (inner ℝ ξ (v j)) ^ 2 * ‖(𝓕 K) ξ‖ ^ 2)) =
      (2 * Real.pi) ^ 4 * (∑ i, (inner ℝ ξ (u i)) ^ 2) *
        (∑ j, (inner ℝ ξ (v j)) ^ 2) * ‖(𝓕 K) ξ‖ ^ 2 := by
    calc
      _ = ∑ i, ∑ j, ((2 * Real.pi) ^ 4 * ‖(𝓕 K) ξ‖ ^ 2) *
          ((inner ℝ ξ (u i)) ^ 2 * (inner ℝ ξ (v j)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ((2 * Real.pi) ^ 4 * ‖(𝓕 K) ξ‖ ^ 2) *
          (∑ i, ∑ j, (inner ℝ ξ (u i)) ^ 2 * (inner ℝ ξ (v j)) ^ 2) := by
        simp only [Finset.mul_sum]
      _ = _ := by rw [← Finset.sum_mul_sum]; ring
  rw [hleft, hright, hboth]
  ring

theorem integrable_mixedKernelFrequencyWeight (u : ι → V) (v : κ → V)
    (K : SchwartzMap V ℂ) :
    Integrable (fun ξ => mixedKernelFrequencyWeight u v ξ * ‖(𝓕 K) ξ‖ ^ 2) := by
  have hi (L : SchwartzMap V ℂ) : Integrable (fun ξ => ‖(𝓕 L) ξ‖ ^ 2) :=
    ((𝓕 L).memLp 2).norm.integrable_sq
  simp_rw [mixedKernelFrequencyWeight_mul_norm_sq]
  exact (((hi K).add (integrable_finsetSum _ (fun i _ => hi (∂_{u i} K)))).add
    (integrable_finsetSum _ (fun j _ => hi (∂_{v j} K)))).add
      (integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => hi (∂_{u i} (∂_{v j} K)))))

/-- Separate scalar integral linearity from the large Schwartz operator terms. -/
private theorem integral_four_families
    (a : V → ℝ) (b : ι → V → ℝ) (c : κ → V → ℝ) (d : ι → κ → V → ℝ)
    (ha : Integrable a) (hb : ∀ i, Integrable (b i))
    (hc : ∀ j, Integrable (c j)) (hd : ∀ i j, Integrable (d i j)) :
    (∫ x, a x + (∑ i, b i x) + (∑ j, c j x) + ∑ i, ∑ j, d i j x) =
      (∫ x, a x) + (∑ i, ∫ x, b i x) + (∑ j, ∫ x, c j x) +
        ∑ i, ∑ j, ∫ x, d i j x := by
  have hbs := integrable_finsetSum Finset.univ (fun i _ => hb i)
  have hcs := integrable_finsetSum Finset.univ (fun j _ => hc j)
  have hds := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hd i j))
  have hsplit : (∫ x, a x + (∑ i, b i x) + (∑ j, c j x) + ∑ i, ∑ j, d i j x) =
      ((∫ x, a x) + (∫ x, ∑ i, b i x)) + (∫ x, ∑ j, c j x) +
        ∫ x, ∑ i, ∑ j, d i j x := by
    calc
      _ = (∫ x, a x + (∑ i, b i x) + ∑ j, c j x) +
          ∫ x, ∑ i, ∑ j, d i j x := integral_add ((ha.add hbs).add hcs) hds
      _ = ((∫ x, a x + ∑ i, b i x) + (∫ x, ∑ j, c j x)) +
          ∫ x, ∑ i, ∑ j, d i j x :=
        congrArg (fun z : ℝ => z + ∫ x, ∑ i, ∑ j, d i j x)
          (integral_add (ha.add hbs) hcs)
      _ = _ := congrArg (fun z : ℝ => z + (∫ x, ∑ j, c j x) +
        ∫ x, ∑ i, ∑ j, d i j x) (integral_add ha hbs)
  have hbint : (∫ x, ∑ i, b i x) = ∑ i, ∫ x, b i x :=
    integral_finsetSum _ (fun i _ => hb i)
  have hcint : (∫ x, ∑ j, c j x) = ∑ j, ∫ x, c j x :=
    integral_finsetSum _ (fun j _ => hc j)
  have hdint : (∫ x, ∑ i, ∑ j, d i j x) = ∑ i, ∑ j, ∫ x, d i j x := by
    calc
      _ = ∑ i, ∫ x, ∑ j, d i j x :=
        integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hd i j))
      _ = _ := Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hd i j))
  rw [hsplit, hbint, hcint, hdint]

/-- Exact weighted Plancherel, with the normalization of the actual Mathlib
Fourier transform displayed in the weight. -/
theorem integral_mixedKernelFrequencyWeight (u : ι → V) (v : κ → V)
    (K : SchwartzMap V ℂ) :
    (∫ ξ, mixedKernelFrequencyWeight u v ξ * ‖(𝓕 K) ξ‖ ^ 2) =
      mixedKernelDerivativeEnergy u v K := by
  have hi (L : SchwartzMap V ℂ) : Integrable (fun ξ => ‖(𝓕 L) ξ‖ ^ 2) :=
    ((𝓕 L).memLp 2).norm.integrable_sq
  calc
    _ = ∫ ξ, ‖(𝓕 K) ξ‖ ^ 2 + (∑ i, ‖(𝓕 (∂_{u i} K)) ξ‖ ^ 2) +
        (∑ j, ‖(𝓕 (∂_{v j} K)) ξ‖ ^ 2) +
          ∑ i, ∑ j, ‖(𝓕 (∂_{u i} (∂_{v j} K))) ξ‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (mixedKernelFrequencyWeight_mul_norm_sq u v K)
    _ = (∫ ξ, ‖(𝓕 K) ξ‖ ^ 2) + (∑ i, ∫ ξ, ‖(𝓕 (∂_{u i} K)) ξ‖ ^ 2) +
        (∑ j, ∫ ξ, ‖(𝓕 (∂_{v j} K)) ξ‖ ^ 2) +
          ∑ i, ∑ j, ∫ ξ, ‖(𝓕 (∂_{u i} (∂_{v j} K))) ξ‖ ^ 2 :=
      integral_four_families _ _ _ _ (hi K) (fun i => hi (∂_{u i} K))
        (fun j => hi (∂_{v j} K)) (fun i j => hi (∂_{u i} (∂_{v j} K)))
    _ = _ := by
      simp only [SchwartzMap.integral_norm_sq_fourier, mixedKernelDerivativeEnergy]


end MixedPlancherel

/-- The actual real six-dimensional Euclidean space, not the max-norm product. -/
abbrev JointKernelSpace := WithLp 2
  (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))

/-- Joint kernel left direction defined as `WithLp.toLp 2 (EuclideanSpace.basisFun (Fin 3) ℝ i,
0)`. -/
def jointKernelLeftDirection (i : Fin 3) : JointKernelSpace :=
  WithLp.toLp 2 (EuclideanSpace.basisFun (Fin 3) ℝ i, 0)

/-- Joint kernel right direction defined as `WithLp.toLp 2 (0, EuclideanSpace.basisFun (Fin 3) ℝ
i)`. -/
def jointKernelRightDirection (i : Fin 3) : JointKernelSpace :=
  WithLp.toLp 2 (0, EuclideanSpace.basisFun (Fin 3) ℝ i)

theorem jointKernelFrequencyWeight_eq (ξ : JointKernelSpace) :
    mixedKernelFrequencyWeight jointKernelLeftDirection jointKernelRightDirection ξ =
      (1 + (2 * Real.pi) ^ 2 * ‖ξ.fst‖ ^ 2) *
        (1 + (2 * Real.pi) ^ 2 * ‖ξ.snd‖ ^ 2) := by
  simp only [mixedKernelFrequencyWeight, jointKernelLeftDirection,
    jointKernelRightDirection, WithLp.prod_inner_apply,
    inner_zero_right, add_zero, zero_add]
  rw [(EuclideanSpace.basisFun (Fin 3) ℝ).sum_sq_inner_left,
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_sq_inner_left]
  rfl

/-- Joint kernel derivative energy defined as `mixedKernelDerivativeEnergy jointKernelLeftDirection
jointKernelRightDirection K`. -/
def jointKernelDerivativeEnergy (K : SchwartzMap JointKernelSpace ℂ) : ℝ :=
  mixedKernelDerivativeEnergy jointKernelLeftDirection jointKernelRightDirection K

theorem jointKernelDerivativeEnergy_nonneg (K : SchwartzMap JointKernelSpace ℂ) :
    0 ≤ jointKernelDerivativeEnergy K := by
  unfold jointKernelDerivativeEnergy mixedKernelDerivativeEnergy
  positivity

/-- The sixteen actual position-space L² terms control the full polynomial
frequency weight on the original six-dimensional Hilbert carrier. -/
theorem integral_jointKernel_frequency_weight (K : SchwartzMap JointKernelSpace ℂ) :
    (∫ ξ : JointKernelSpace,
      (1 + (2 * Real.pi) ^ 2 * ‖ξ.fst‖ ^ 2) *
        (1 + (2 * Real.pi) ^ 2 * ‖ξ.snd‖ ^ 2) * ‖(𝓕 K) ξ‖ ^ 2) =
      jointKernelDerivativeEnergy K := by
  simpa only [jointKernelFrequencyWeight_eq, jointKernelDerivativeEnergy] using
    integral_mixedKernelFrequencyWeight jointKernelLeftDirection jointKernelRightDirection K

theorem integrable_jointKernel_frequency_weight (K : SchwartzMap JointKernelSpace ℂ) :
    Integrable (fun ξ : JointKernelSpace =>
      (1 + (2 * Real.pi) ^ 2 * ‖ξ.fst‖ ^ 2) *
        (1 + (2 * Real.pi) ^ 2 * ‖ξ.snd‖ ^ 2) * ‖(𝓕 K) ξ‖ ^ 2) := by
  simpa only [jointKernelFrequencyWeight_eq] using
    integrable_mixedKernelFrequencyWeight jointKernelLeftDirection jointKernelRightDirection K

end VacuumBellSeparation
