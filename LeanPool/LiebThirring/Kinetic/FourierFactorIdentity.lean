/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.FourierFactorTensor
public import LeanPool.LiebThirring.Kinetic.FourierFactorCurrying
public import LeanPool.LiebThirring.Fourier.TensorDensity
public import LeanPool.LiebThirring.Kinetic.CurryingExchange

/-!
# Full and partial Fourier factorization

Outer Fourier transform acts on the spatial factor of a curried tensor.

Rest-coordinate Fourier transforms act on the remaining factor of a tensor.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal NNReal

namespace LiebThirring

/-- Outer Fourier transform acts on the spatial factor of a curried tensor. -/
theorem fourier_tensorInsertion {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (v : RestState i q) :
    𝓕 (tensorInsertion (H := RestState i q) f v) =
      tensorInsertion (H := RestState i q) (𝓕 f) v := by
  change 𝓕 ((tensorInsertionBilinear v).compLp f) =
    (tensorInsertionBilinear v).compLp (𝓕 f)
  exact Fourier.fourier_compLp _ f

/-- Rest-coordinate Fourier transforms act on the remaining factor of a tensor. -/
theorem restFourier_tensorInsertion {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (v : RestState i q) :
    (restFourierLinearIsometryEquiv (q := q) i).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (tensorInsertion (H := RestState i q) f v) =
        tensorInsertion (H := RestState i q) f (𝓕 v) := by
  exact piLpCongrRight_compLp_tensorInsertion
    (Lp.fourierTransformₗᵢ (OtherConfiguration i)
      (EuclideanSpace ℂ (OtherSpinLabels i q))) f v

/-- The full/partial factorization on the smooth tensor core. -/
theorem oneParticleCurrying_fourier_insertion_toLp {N q : ℕ} (i : Fin N)
    (f : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (v : 𝓢(OtherConfiguration i, EuclideanSpace ℂ (OtherSpinLabels i q))) :
    oneParticleCurrying i (𝓕 (oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume))) =
      (restFourierLinearIsometryEquiv (q := q)
        i).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (𝓕 (oneParticleCurrying i (oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume)))) :=
          by
  let V := (restFourierLinearIsometryEquiv (q := q) i).toContinuousLinearEquiv.toContinuousLinearMap
  have hleft := congrArg (oneParticleCurrying i) (fourier_oneParticleInsertion_toLp i f v)
  have hcore := oneParticleCurrying_insertion i ((𝓕 f : 𝓢(Position, EuclideanSpace ℂ (Fin q))).toLp
    2 volume)
    ((𝓕 v : 𝓢(OtherConfiguration i, EuclideanSpace ℂ (OtherSpinLabels i q))).toLp 2 volume)
  have hright := congrArg (fun z => V.compLp (𝓕 z))
    (oneParticleCurrying_insertion i (f.toLp 2 volume) (v.toLp 2 volume))
  have hout := fourier_tensorInsertion i (f.toLp 2 volume) (v.toLp 2 volume)
  have hrest := restFourier_tensorInsertion i (𝓕 (f.toLp 2 volume)) (v.toLp 2 volume)
  have heq := congrArg₂ (fun a b => tensorInsertion (H := RestState i q) a b)
    (SchwartzMap.toLp_fourier_eq f) (SchwartzMap.toLp_fourier_eq v)
  exact (hleft.trans hcore).trans
    (heq.symm.trans (hrest.symm.trans ((congrArg V.compLp hout).symm.trans hright.symm)))

/-- Exact unweighted Fourier factorization factorization as an equality of L² classes. -/
theorem oneParticleCurrying_fourier {N q : ℕ} (i : Fin N) (ψ : State N q) :
    oneParticleCurrying i (𝓕 ψ) =
      (restFourierLinearIsometryEquiv (q := q)
        i).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (𝓕 (oneParticleCurrying i ψ)) := by
  let C := (oneParticleCurryingLinearIsometryEquiv (q := q)
    i).toContinuousLinearEquiv.toContinuousLinearMap
  let V := (restFourierLinearIsometryEquiv (q := q) i).toContinuousLinearEquiv.toContinuousLinearMap
  let A : State N q →L[ℂ] Lp (OneParticleFiber i q) 2 volume :=
    C.comp (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N
      q)).toContinuousLinearEquiv.toContinuousLinearMap
  let B : State N q →L[ℂ] Lp (OneParticleFiber i q) 2 volume :=
    (V.compLpL 2 volume).comp
      ((Lp.fourierTransformₗᵢ Position (OneParticleFiber i
        q)).toContinuousLinearEquiv.toContinuousLinearMap.comp C)
  have heq : A = B := by
    apply continuousLinearMap_ext_oneParticleInsertion_schwartz i
    intro f v
    exact oneParticleCurrying_fourier_insertion_toLp i f v
  exact congrArg (fun T : State N q →L[ℂ] Lp (OneParticleFiber i q) 2 volume => T ψ) heq

/-- Currying the full Fourier transform and partial Fourier have identical fiber norms a.e. -/
theorem norm_oneParticleCurrying_fourier_ae {N q : ℕ} (i : Fin N) (ψ : State N q) :
    ∀ᵐ ξ : Position,
      ‖oneParticleCurrying i (𝓕 ψ) ξ‖₊ = ‖(𝓕 (oneParticleCurrying i ψ) : Lp (OneParticleFiber i q)
        2 volume) ξ‖₊ := by
  rw [oneParticleCurrying_fourier]
  filter_upwards [(restFourierLinearIsometryEquiv (q := q)
    i).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (𝓕 (oneParticleCurrying i ψ))] with ξ hξ
  rw [hξ]
  exact (restFourierLinearIsometryEquiv i).nnnorm_map _

/-- The particle energy equals the partial Fourier kinetic integral, including infinite energy. -/
theorem particleFourierEnergy_eq_partialFourier {N q : ℕ} (i : Fin N) (ψ : State N q) :
    particleFourierEnergy ψ i = ∫⁻ ξ : Position,
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
        (‖(Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (oneParticleCurrying i ψ)) ξ‖₊ :
          ℝ≥0∞) ^ 2 := by
  rw [particleFourierEnergy_eq_currying_fullFourier]
  apply lintegral_congr_ae
  filter_upwards [norm_oneParticleCurrying_fourier_ae i ψ] with ξ hξ
  rw [hξ]
  rfl

end LiebThirring
end
