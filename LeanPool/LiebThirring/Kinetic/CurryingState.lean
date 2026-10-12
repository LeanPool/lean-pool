/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.Currying
public import LeanPool.LiebThirring.Kinetic.CurryingFinite
public import LeanPool.LiebThirring.Kinetic.CurryingProductSurjective
public import LeanPool.LiebThirring.Kinetic.CurryingTransport

/-!
# Currying on the state carriers

The one-particle currying isometry on the spatial and spin carriers.

The full currying complex linear isometric equivalence, with the original state as its source
and the literal one-particle fiber as its target.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The full currying complex linear isometric equivalence, with the original state
as its source and the literal one-particle fiber as its target. -/
@[expose] noncomputable def oneParticleCurryingLinearIsometryEquiv {N q : ℕ} (i : Fin N) :
    State N q ≃ₗᵢ[ℂ] Lp (OneParticleFiber i q) 2 (volume : Measure Position) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let A := l2PullbackEquiv (E := SpinAmplitudes N q)
    (insertionMeasurableEquiv i) (measurePreserving_insertion i)
  let B := l2TargetEquiv (volume : Measure (Position × OtherConfiguration i))
    (spinCurryingLinearIsometryEquiv (q := q) i)
  let C := l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
    (ν := (volume : Measure (OtherConfiguration i)))
    (E := PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)))
  let D := l2TargetEquiv (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherConfiguration i))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)))
  exact ((A.trans B).trans C).trans D

/-- The one-particle currying isometry on the spatial and spin carriers. -/
@[expose] noncomputable def oneParticleCurrying {N q : ℕ} (i : Fin N) :
    State N q →ₗᵢ[ℂ] Lp (OneParticleFiber i q) 2 (volume : Measure Position) :=
  (oneParticleCurryingLinearIsometryEquiv i).toLinearIsometry

/-- The currying representative identity, on one common full-measure outer set. -/
theorem oneParticleCurrying_ae {N q : ℕ} (i : Fin N) (ψ : State N q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ y : OtherConfiguration i,
      ∀ t : OtherSpinLabels i q,
        oneParticleCurrying i ψ x s y t =
          ψ (insertParticle i x y) (insertSpin i s t) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let A := l2PullbackEquiv (E := SpinAmplitudes N q)
    (insertionMeasurableEquiv i) (measurePreserving_insertion i)
  let B := l2TargetEquiv (volume : Measure (Position × OtherConfiguration i))
    (spinCurryingLinearIsometryEquiv (q := q) i)
  let h := B (A ψ)
  let D := l2TargetEquiv (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherConfiguration i))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)))
  have hA := Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (insertionMeasurableEquiv i) (measurePreserving_insertion i) ψ)
  have hB := Measure.ae_ae_of_ae_prod (l2TargetEquiv_ae
    (volume : Measure (Position × OtherConfiguration i))
    (spinCurryingLinearIsometryEquiv (q := q) i) (A ψ))
  change ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ y : OtherConfiguration i,
    ∀ t : OtherSpinLabels i q,
      D (l2Curry h) x s y t = ψ (insertParticle i x y) (insertSpin i s t)
  filter_upwards [l2TargetEquiv_ae (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherConfiguration i))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q))) (l2Curry h),
    l2Curry_ae h, hA, hB] with x hx hc ha hb
  intro s
  rw [hx]
  filter_upwards [finiteLpPiLpEquiv_apply_ae (volume : Measure (OtherConfiguration i))
    (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)) (l2Curry h x) s,
    hc, ha, hb] with y hy hcy hay hby
  intro t
  rw [hy, hcy, hby, hay]
  exact congrArg (fun u : SpinAmplitudes N q => u (insertSpin i s t))
    (congrArg ψ (insertionMeasurableEquiv_apply i (x, y)))

end LiebThirring

end
