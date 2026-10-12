/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.RealFormCurrying
public import LeanPool.LiebThirring.Kinetic.FourierFactorIdentity

/-! # Full-spin one-particle L² slices

Spatial currying without spin regrouping gives the slices on which the
one-body Hardy estimate is applied. Spin regrouping is an isometry, so the
partial Fourier weighted norm is exactly the landed particle Fourier energy.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.Assembly

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- Spatial currying with the complete spin amplitude retained in each slice. -/
@[expose] noncomputable def realFormParticleCurrying {N q : ℕ} (i : Fin N)
    (ψ : State N q) :
    Lp (Lp (SpinAmplitudes N q) 2 (volume : Measure (OtherConfiguration i))) 2
      (volume : Measure Position) :=
  l2Curry (l2PullbackEquiv (E := SpinAmplitudes N q)
    (insertionMeasurableEquiv i) (measurePreserving_insertion i) ψ)

/-- The full-spin curried representative is the inserted state. -/
theorem realFormParticleCurrying_ae {N q : ℕ} (i : Fin N) (ψ : State N q) :
    ∀ᵐ x : Position, ∀ᵐ y : OtherConfiguration i,
      realFormParticleCurrying i ψ x y = ψ (insertParticle i x y) := by
  let f := l2PullbackEquiv (E := SpinAmplitudes N q)
    (insertionMeasurableEquiv i) (measurePreserving_insertion i) ψ
  filter_upwards [l2Curry_ae f, Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (insertionMeasurableEquiv i) (measurePreserving_insertion i) ψ)] with x hx ht
  filter_upwards [hx, ht] with y hxy hty
  exact hxy.trans (hty.trans (congrArg ψ (insertionMeasurableEquiv_apply i (x, y))))

/-- Spatial currying preserves the original L² norm. -/
theorem realFormParticleCurrying_norm {N q : ℕ} (i : Fin N) (ψ : State N q) :
    ‖realFormParticleCurrying i ψ‖ = ‖ψ‖ := by
  rw [realFormParticleCurrying, l2Curry_norm, LinearIsometryEquiv.norm_map]

/-- Regroup the complete spin slice into the landed one-particle fiber. -/
@[expose] noncomputable def realFormSpinRegrouping {N q : ℕ} (i : Fin N) :
    Lp (SpinAmplitudes N q) 2 (volume : Measure (OtherConfiguration i)) ≃ₗᵢ[ℂ]
      OneParticleFiber i q :=
  (l2TargetEquiv (volume : Measure (OtherConfiguration i))
    (spinCurryingLinearIsometryEquiv (q := q) i)).trans
    (finiteLpPiLpEquiv (volume : Measure (OtherConfiguration i))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)))

/-- The representative formula for spin regrouping. -/
theorem realFormSpinRegrouping_ae {N q : ℕ} (i : Fin N)
    (v : Lp (SpinAmplitudes N q) 2 (volume : Measure (OtherConfiguration i)))
    (s : Fin q) :
    ∀ᵐ y : OtherConfiguration i, ∀ t : OtherSpinLabels i q,
      realFormSpinRegrouping i v s y t = v y (insertSpin i s t) := by
  filter_upwards [finiteLpPiLpEquiv_apply_ae
    (volume : Measure (OtherConfiguration i))
    (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q))
    (l2TargetEquiv (volume : Measure (OtherConfiguration i))
      (spinCurryingLinearIsometryEquiv (q := q) i) v) s,
    l2TargetEquiv_ae (volume : Measure (OtherConfiguration i))
      (spinCurryingLinearIsometryEquiv (q := q) i) v] with y hy ht
  intro t
  change finiteLpPiLpEquiv (volume : Measure (OtherConfiguration i))
    (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q))
    (l2TargetEquiv (volume : Measure (OtherConfiguration i))
      (spinCurryingLinearIsometryEquiv (q := q) i) v) s y t = _
  rw [hy, ht]
  rfl

/-- Full-spin currying and the currying currying differ only by a target isometry. -/
theorem realFormSpinRegrouping_compLp {N q : ℕ} (i : Fin N) (ψ : State N q) :
    (realFormSpinRegrouping (q := q) i).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (realFormParticleCurrying i ψ) = oneParticleCurrying i ψ := by
  apply Lp.ext
  filter_upwards [(realFormSpinRegrouping (q := q)
    i).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (realFormParticleCurrying i ψ), realFormParticleCurrying_ae i ψ,
    oneParticleCurrying_ae i ψ] with x ht hx hc
  rw [ht]
  apply PiLp.ext
  intro s
  apply Lp.ext
  filter_upwards [realFormSpinRegrouping_ae i (realFormParticleCurrying i ψ x) s,
    hx, hc s] with y hty hxy hcy
  ext t
  change realFormSpinRegrouping i (realFormParticleCurrying i ψ x) s y t =
    oneParticleCurrying i ψ x s y t
  rw [hty t, hxy, hcy t]

/-- Spin regrouping commutes with the spatial partial Fourier transform. -/
theorem realFormParticleCurrying_fourier_regrouping {N q : ℕ} (i : Fin N) (ψ : State N q) :
    (realFormSpinRegrouping (q := q) i).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (𝓕 (realFormParticleCurrying i ψ)) = 𝓕 (oneParticleCurrying i ψ) := by
  rw [← Fourier.fourier_compLp, realFormSpinRegrouping_compLp]

/-- Partial Fourier kinetic mass of the full-spin slices is the particle energy. -/
theorem realFormParticleCurrying_fourier_energy {N q : ℕ} (i : Fin N) (ψ : State N q) :
    (∫⁻ ξ : Position, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
      (‖(𝓕 (realFormParticleCurrying i ψ) :
        Lp (Lp (SpinAmplitudes N q) 2 (volume : Measure (OtherConfiguration i))) 2 volume) ξ‖₊ :
          ℝ≥0∞) ^ 2) =
      particleFourierEnergy ψ i := by
  have h := realFormTargetIsometry_weighted_norm_sq (realFormSpinRegrouping (q := q) i)
    (𝓕 (realFormParticleCurrying i ψ))
    (fun ξ : Position => ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2)
  rw [realFormParticleCurrying_fourier_regrouping] at h
  exact h.symm.trans (particleFourierEnergy_eq_partialFourier i ψ).symm

/-- In the opposite order, each remaining-coordinate slice is the original
state as a function of the selected particle position. -/
theorem realFormParticleSlices_ae {N q : ℕ} (i : Fin N) (ψ : State N q) :
    ∀ᵐ y : OtherConfiguration i, ∀ᵐ x : Position,
      realFormSwapCurrying (realFormParticleCurrying i ψ) y x =
        ψ (insertParticle i x y) := by
  let f := l2PullbackEquiv (E := SpinAmplitudes N q)
    (insertionMeasurableEquiv i) (measurePreserving_insertion i) ψ
  have hinv : (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
      (ν := (volume : Measure (OtherConfiguration i))) (E := SpinAmplitudes N q)).symm
      (realFormParticleCurrying i ψ) = f :=
    (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
      (ν := (volume : Measure (OtherConfiguration i))) (E := SpinAmplitudes N q)).symm_apply_apply f
  have hS := realFormSwapCurrying_ae_uncurry (realFormParticleCurrying i ψ)
  rw [hinv] at hS
  have hA := l2PullbackEquiv_ae (insertionMeasurableEquiv i)
    (measurePreserving_insertion i) ψ
  have hback := (Measure.measurePreserving_swap
    (μ := (volume : Measure (OtherConfiguration i))) (ν := (volume : Measure
      Position))).quasiMeasurePreserving.ae hA
  filter_upwards [hS, Measure.ae_ae_of_ae_prod hback] with y hy ht
  filter_upwards [hy, ht] with x hx htx
  exact hx.trans (htx.trans (congrArg ψ (insertionMeasurableEquiv_apply i (x, y))))

end LiebThirring.Assembly
end
