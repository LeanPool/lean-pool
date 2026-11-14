/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionRestEncoding
public import LeanPool.LiebThirring.Kinetic.PauliLiftCurrying

/-! # Currying a second particle from a remaining state

The two equivalences here identify either one-particle remaining carrier with
the same ordered second-factor space used by pair currying.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal

namespace LiebThirring

/-- The second one-particle factor over the ordered pair-rest state. -/
noncomputable abbrev RestFactorState {N : ℕ} (i j : Fin N) (q : ℕ) : Type :=
  Lp (PiLp 2 (fun _ : Fin q => PairRestState i j q)) 2
    (volume : Measure Position)

/-- Split particle `j` from a state on the coordinates complementary to `i`. -/
@[expose] noncomputable def restCurryingLeftLinearIsometryEquiv {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) : RestState i q ≃ₗᵢ[ℂ] RestFactorState i j q := by
  let A := l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels i q))
    (restLeftInsertionMeasurableEquiv i j hij) (measurePreserving_restLeftInsertion i j hij)
  let B := l2TargetEquiv (volume : Measure (Position × OtherPairConfiguration i j))
    (restLeftSpinCurryingEquiv (q := q) i j hij)
  let C := l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
    (ν := (volume : Measure (OtherPairConfiguration i j)))
    (E := PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  let D := l2TargetEquiv (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  exact ((A.trans B).trans C).trans D

/-- Split particle `i` from a state on the coordinates complementary to `j`,
using the same ordered pair-rest carrier as the left equivalence. -/
@[expose] noncomputable def restCurryingRightLinearIsometryEquiv {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) : RestState j q ≃ₗᵢ[ℂ] RestFactorState i j q := by
  let A := l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels j q))
    (restRightInsertionMeasurableEquiv i j hij) (measurePreserving_restRightInsertion i j hij)
  let B := l2TargetEquiv (volume : Measure (Position × OtherPairConfiguration i j))
    (restRightSpinCurryingEquiv (q := q) i j hij)
  let C := l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
    (ν := (volume : Measure (OtherPairConfiguration i j)))
    (E := PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  let D := l2TargetEquiv (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  exact ((A.trans B).trans C).trans D

/-- Literal representative of left remaining-state currying. -/
theorem restCurryingLeftLinearIsometryEquiv_apply_ae {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) (v : RestState i q) :
    ∀ᵐ z : Position, ∀ r : Fin q, ∀ᵐ y : OtherPairConfiguration i j,
      ∀ t : OtherPairSpinLabels i j q,
        restCurryingLeftLinearIsometryEquiv i j hij v z r y t =
          v (insertOtherParticleLeft i j z y) (insertOtherSpinLeft i j r t) := by
  let A := l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels i q))
    (restLeftInsertionMeasurableEquiv i j hij) (measurePreserving_restLeftInsertion i j hij)
  let B := l2TargetEquiv (volume : Measure (Position × OtherPairConfiguration i j))
    (restLeftSpinCurryingEquiv (q := q) i j hij)
  let h := B (A v)
  let D := l2TargetEquiv (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  have hA := Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (restLeftInsertionMeasurableEquiv i j hij) (measurePreserving_restLeftInsertion i j hij) v)
  have hB := Measure.ae_ae_of_ae_prod (l2TargetEquiv_ae
    (volume : Measure (Position × OtherPairConfiguration i j))
    (restLeftSpinCurryingEquiv (q := q) i j hij) (A v))
  change ∀ᵐ z : Position, ∀ r : Fin q, ∀ᵐ y : OtherPairConfiguration i j,
    ∀ t : OtherPairSpinLabels i j q,
      D (l2Curry h) z r y t =
        v (insertOtherParticleLeft i j z y) (insertOtherSpinLeft i j r t)
  filter_upwards [l2TargetEquiv_ae (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q))) (l2Curry h),
    l2Curry_ae h, hA, hB] with z hz hc ha hb
  intro r
  rw [hz]
  filter_upwards [finiteLpPiLpEquiv_apply_ae (volume : Measure (OtherPairConfiguration i j))
    (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)) (l2Curry h z) r,
    hc, ha, hb] with y hy hcy hay hby
  intro t
  rw [hy, hcy, hby, hay]
  exact congrArg (fun u : EuclideanSpace ℂ (OtherSpinLabels i q) =>
    u (insertOtherSpinLeft i j r t))
      (congrArg v (restLeftInsertionMeasurableEquiv_apply i j hij (z, y)))

/-- Literal representative of right remaining-state currying. -/
theorem restCurryingRightLinearIsometryEquiv_apply_ae {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) (v : RestState j q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ y : OtherPairConfiguration i j,
      ∀ t : OtherPairSpinLabels i j q,
        restCurryingRightLinearIsometryEquiv i j hij v x s y t =
          v (insertOtherParticleRight i j x y) (insertOtherSpinRight i j s t) := by
  let A := l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels j q))
    (restRightInsertionMeasurableEquiv i j hij) (measurePreserving_restRightInsertion i j hij)
  let B := l2TargetEquiv (volume : Measure (Position × OtherPairConfiguration i j))
    (restRightSpinCurryingEquiv (q := q) i j hij)
  let h := B (A v)
  let D := l2TargetEquiv (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  have hA := Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (restRightInsertionMeasurableEquiv i j hij) (measurePreserving_restRightInsertion i j hij) v)
  have hB := Measure.ae_ae_of_ae_prod (l2TargetEquiv_ae
    (volume : Measure (Position × OtherPairConfiguration i j))
    (restRightSpinCurryingEquiv (q := q) i j hij) (A v))
  change ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ y : OtherPairConfiguration i j,
    ∀ t : OtherPairSpinLabels i j q,
      D (l2Curry h) x s y t =
        v (insertOtherParticleRight i j x y) (insertOtherSpinRight i j s t)
  filter_upwards [l2TargetEquiv_ae (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q))) (l2Curry h),
    l2Curry_ae h, hA, hB] with x hx hc ha hb
  intro s
  rw [hx]
  filter_upwards [finiteLpPiLpEquiv_apply_ae (volume : Measure (OtherPairConfiguration i j))
    (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)) (l2Curry h x) s,
    hc, ha, hb] with y hy hcy hay hby
  intro t
  rw [hy, hcy, hby, hay]
  exact congrArg (fun u : EuclideanSpace ℂ (OtherSpinLabels j q) =>
    u (insertOtherSpinRight i j s t))
      (congrArg v (restRightInsertionMeasurableEquiv_apply i j hij (x, y)))

end LiebThirring

end
