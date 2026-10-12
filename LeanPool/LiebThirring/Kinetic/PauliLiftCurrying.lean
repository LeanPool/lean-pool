/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.PauliLiftEncoding
public import LeanPool.LiebThirring.Kinetic.CurryingState

/-! # Two-particle currying

An ordered two-coordinate version of the state currying equivalence.  Its
parenthesization exposes the first one-particle factor and then the second.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal

namespace LiebThirring

instance pairProductVolumeIsSeparable {N : ℕ} (i j : Fin N) :
    IsSeparable (volume : Measure (Position × OtherPairConfiguration i j)) :=
  isSeparable_of_sigmaFinite _

/-- The Hilbert space of spatial and spin coordinates remaining after two
distinct particles are removed. -/
noncomputable abbrev PairRestState {N : ℕ} (i j : Fin N) (q : ℕ) : Type :=
  Lp (EuclideanSpace ℂ (OtherPairSpinLabels i j q)) 2
    (volume : Measure (OtherPairConfiguration i j))

/-- The ordered two-coordinate curried state carrier. -/
noncomputable abbrev PairCurriedState {N : ℕ} (i j : Fin N) (q : ℕ) : Type :=
  Lp (PiLp 2 (fun _ : Fin q =>
    Lp (PiLp 2 (fun _ : Fin q => PairRestState i j q)) 2
      (volume : Measure Position))) 2 (volume : Measure Position)

instance pairSpinRestSecondCountableTopology {N : ℕ} (i j : Fin N) (q : ℕ) :
    SecondCountableTopology
      (Lp (PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q))) 2
        (volume : Measure (OtherPairConfiguration i j))) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

instance pairNestedSpinSecondCountableTopology {N : ℕ} (i j : Fin N) (q : ℕ) :
    SecondCountableTopology
      (Lp (PiLp 2 (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
        EuclideanSpace ℂ (OtherPairSpinLabels i j q)))) 2
        (volume : Measure (Position × OtherPairConfiguration i j))) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- Curry the inner position and distribute both finite spin coordinates. -/
@[expose] noncomputable def innerPairCurryingEquiv {N q : ℕ}
    (i j : Fin N) :
    Lp (PiLp 2 (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
      EuclideanSpace ℂ (OtherPairSpinLabels i j q)))) 2
        (volume : Measure (Position × OtherPairConfiguration i j)) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : Fin q =>
        Lp (PiLp 2 (fun _ : Fin q => PairRestState i j q)) 2
          (volume : Measure Position)) := by
  let D := finiteLpPiLpEquiv
    (volume : Measure (Position × OtherPairConfiguration i j))
    (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
      EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  let E (s : Fin q) :=
    (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
      (ν := (volume : Measure (OtherPairConfiguration i j)))
      (E := PiLp 2 (fun _ : Fin q =>
        EuclideanSpace ℂ (OtherPairSpinLabels i j q)))).trans
    (l2TargetEquiv (volume : Measure Position)
      (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
        (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q))))
  exact D.trans (LinearIsometryEquiv.piLpCongrRight 2 (𝕜 := ℂ) E)

/-- Representative formula for the inner half of ordered pair currying. -/
theorem innerPairCurryingEquiv_ae {N q : ℕ} (i j : Fin N)
    (h : Lp (PiLp 2 (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
      EuclideanSpace ℂ (OtherPairSpinLabels i j q)))) 2
        (volume : Measure (Position × OtherPairConfiguration i j))) :
    ∀ s : Fin q, ∀ᵐ z : Position, ∀ r : Fin q,
      ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
        innerPairCurryingEquiv i j h s z r y t = h (z, y) s r t := by
  let D := finiteLpPiLpEquiv
    (volume : Measure (Position × OtherPairConfiguration i j))
    (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
      EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
  intro s
  have hD := Measure.ae_ae_of_ae_prod (finiteLpPiLpEquiv_apply_ae
    (μ := (volume : Measure (Position × OtherPairConfiguration i j)))
    (E := fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
      EuclideanSpace ℂ (OtherPairSpinLabels i j q))) h s)
  change ∀ᵐ z : Position, ∀ r : Fin q,
    ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
      l2TargetEquiv (volume : Measure Position)
        (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
          (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
        (l2CurryLinearIsometryEquiv (D h s)) z r y t = h (z, y) s r t
  filter_upwards [l2TargetEquiv_ae (volume : Measure Position)
    (finiteLpPiLpEquiv (volume : Measure (OtherPairConfiguration i j))
      (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)))
    (l2CurryLinearIsometryEquiv (D h s)),
    l2CurryLinearIsometryEquiv_apply_ae (D h s), hD] with z hz hc hDz
  intro r
  rw [hz]
  filter_upwards [finiteLpPiLpEquiv_apply_ae
    (μ := (volume : Measure (OtherPairConfiguration i j)))
    (E := fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q))
    (l2CurryLinearIsometryEquiv (D h s) z) r, hc, hDz] with y hy hcy hDy
  intro t
  rw [hy, hcy, hDy]

/-- The state carrier after separating two spatial coordinates, before spin regrouping. -/
noncomputable abbrev PairRawState {N q : ℕ} (i j : Fin N) : Type :=
  Lp (SpinAmplitudes N q) 2
    (volume : Measure (Position × (Position × OtherPairConfiguration i j)))

/-- The state carrier after separating and regrouping the two selected spins. -/
noncomputable abbrev PairSpinState {N q : ℕ} (i j : Fin N) : Type :=
  Lp (PiLp 2 (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
    EuclideanSpace ℂ (OtherPairSpinLabels i j q)))) 2
      (volume : Measure (Position × (Position × OtherPairConfiguration i j)))

/-- The state carrier after currying the first selected spatial coordinate. -/
noncomputable abbrev PairOuterState {N q : ℕ} (i j : Fin N) : Type :=
  Lp (Lp (PiLp 2 (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
    EuclideanSpace ℂ (OtherPairSpinLabels i j q)))) 2
      (volume : Measure (Position × OtherPairConfiguration i j))) 2
    (volume : Measure Position)

/-- Pull states back along the measure-preserving two-particle coordinate insertion. -/
noncomputable def pairPullbackEquiv {N q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    State N q ≃ₗᵢ[ℂ] PairRawState (q := q) i j :=
  l2PullbackEquiv (E := SpinAmplitudes N q)
    (pairInsertionMeasurableEquiv i j hij) (measurePreserving_pairInsertion i j hij)

theorem pairPullbackEquiv_apply_ae {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State N q) :
    pairPullbackEquiv i j hij ψ =ᵐ[volume]
      fun w => ψ (pairInsertionMeasurableEquiv i j hij w) := by
  exact l2PullbackEquiv_ae (E := SpinAmplitudes N q)
    (pairInsertionMeasurableEquiv i j hij) (measurePreserving_pairInsertion i j hij) ψ

/-- Regroup the two selected spin coordinates in the pulled-back state. -/
noncomputable def pairSpinTargetEquiv {N q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    PairRawState (q := q) i j ≃ₗᵢ[ℂ] PairSpinState (q := q) i j :=
  l2TargetEquiv (volume : Measure (Position × (Position × OtherPairConfiguration i j)))
    (spinPairCurryingLinearIsometryEquiv (q := q) i j hij)

theorem pairSpinTargetEquiv_apply_ae {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : PairRawState (q := q) i j) :
    pairSpinTargetEquiv i j hij a =ᵐ[volume]
      fun w => spinPairCurryingLinearIsometryEquiv i j hij (a w) := by
  exact l2TargetEquiv_ae
    (volume : Measure (Position × (Position × OtherPairConfiguration i j)))
    (spinPairCurryingLinearIsometryEquiv (q := q) i j hij) a

/-- Curry the first selected spatial coordinate in the spin-regrouped state. -/
noncomputable def pairOuterCurryEquiv {N q : ℕ} (i j : Fin N) :
    PairSpinState (q := q) i j ≃ₗᵢ[ℂ] PairOuterState (q := q) i j :=
  l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
    (ν := (volume : Measure (Position × OtherPairConfiguration i j)))
    (E := PiLp 2 (fun _ : Fin q => PiLp 2 (fun _ : Fin q =>
      EuclideanSpace ℂ (OtherPairSpinLabels i j q))))

theorem pairOuterCurryEquiv_apply_ae {N q : ℕ} (i j : Fin N)
    (h : PairSpinState (q := q) i j) :
    ∀ᵐ x : Position, ∀ᵐ w : Position × OtherPairConfiguration i j,
      pairOuterCurryEquiv i j h x w = h (x, w) := by
  exact l2CurryLinearIsometryEquiv_apply_ae h

/-- Curry the inner spatial coordinate and distribute its finite-spin factors. -/
noncomputable def pairInnerTargetEquiv {N q : ℕ} (i j : Fin N) :=
  l2TargetEquiv (volume : Measure Position) (innerPairCurryingEquiv (q := q) i j)

theorem pairInnerTargetEquiv_apply_ae {N q : ℕ} (i j : Fin N)
    (c : PairOuterState (q := q) i j) :
    pairInnerTargetEquiv i j c =ᵐ[volume]
      fun x => innerPairCurryingEquiv i j (c x) := by
  exact l2TargetEquiv_ae (volume : Measure Position)
    (innerPairCurryingEquiv (q := q) i j) c

/-- The ordered two-particle currying equivalence on the state carrier. -/
noncomputable def pairCurryingLinearIsometryEquiv {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) : State N q ≃ₗᵢ[ℂ] PairCurriedState i j q :=
  (((pairPullbackEquiv (q := q) i j hij).trans (pairSpinTargetEquiv i j hij)).trans
    (pairOuterCurryEquiv i j)).trans (pairInnerTargetEquiv i j)

/-- The ordered pair currying has the literal two-particle representative. -/
theorem pairCurryingLinearIsometryEquiv_apply_ae {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) (ψ : State N q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ z : Position, ∀ r : Fin q,
      ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
        pairCurryingLinearIsometryEquiv i j hij ψ x s z r y t =
          ψ (insertParticlePair i j x z y) (insertSpinPair i j s r t) := by
  let a : PairRawState (q := q) i j := pairPullbackEquiv i j hij ψ
  let h : PairSpinState (q := q) i j := pairSpinTargetEquiv i j hij a
  let c : PairOuterState (q := q) i j := pairOuterCurryEquiv i j h
  change ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ z : Position, ∀ r : Fin q,
    ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
      pairInnerTargetEquiv i j c x s z r y t =
        ψ (insertParticlePair i j x z y) (insertSpinPair i j s r t)
  have ha := Measure.ae_ae_of_ae_prod (pairPullbackEquiv_apply_ae i j hij ψ)
  have hh := Measure.ae_ae_of_ae_prod (pairSpinTargetEquiv_apply_ae i j hij a)
  filter_upwards [pairInnerTargetEquiv_apply_ae i j c,
    pairOuterCurryEquiv_apply_ae i j h, ha, hh] with x hinner hc hax hhx
  intro s
  rw [hinner]
  have hc' := Measure.ae_ae_of_ae_prod hc
  have hax' := Measure.ae_ae_of_ae_prod hax
  have hhx' := Measure.ae_ae_of_ae_prod hhx
  filter_upwards [innerPairCurryingEquiv_ae i j (c x) s, hc', hax', hhx']
    with z hz hcz haz hhz
  intro r
  filter_upwards [hz r, hcz, haz, hhz] with y hzy hczy hay hhy
  intro t
  rw [hzy t, hczy]
  rw [hhy]
  change a (x, (z, y)) (insertSpinPair i j s r t) = _
  rw [hay]
  exact congrArg (fun u : SpinAmplitudes N q => u (insertSpinPair i j s r t))
    (congrArg ψ (pairInsertionMeasurableEquiv_apply i j hij (x, z, y)))

end LiebThirring

end
