/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionRestCurrying
public import LeanPool.LiebThirring.Kinetic.ContractionState
public import LeanPool.LiebThirring.Kinetic.ContractionFactors

/-! # Intertwining concrete coordinate insertion with pair factors

Pair currying sends insertion in the first or second selected particle to the
corresponding abstract tensor-factor insertion.
-/

public section

open MeasureTheory WithLp

namespace LiebThirring

private theorem eventually_forall_finite {α β : Type*} [Finite α]
    {l : Filter β} {p : α → β → Prop} (h : ∀ a, ∀ᶠ b in l, p a b) :
    ∀ᶠ b in l, ∀ a, p a b := by
  classical
  let := Fintype.ofFinite α
  have hu : ∀ᶠ b in l, ∀ a ∈ Finset.univ, p a b :=
    (Finset.eventually_all Finset.univ).2 fun a _ => h a
  simpa using hu

/-- Reassociate ordered pair coordinates so that insertion in coordinate `j`
is expressed in its native one-particle splitting. -/
noncomputable def pairToRightRestMeasurableEquiv {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    (Position × (Position × OtherPairConfiguration i j)) ≃ᵐ
      (Position × OtherConfiguration j) :=
  MeasurableEquiv.prodAssoc.symm |>.trans
    ((MeasurableEquiv.prodComm (α := Position) (β := Position)).prodCongr
      (MeasurableEquiv.refl (OtherPairConfiguration i j))) |>.trans
    MeasurableEquiv.prodAssoc |>.trans
    ((MeasurableEquiv.refl Position).prodCongr
      (restRightInsertionMeasurableEquiv i j hij))

theorem pairToRightRestMeasurableEquiv_apply {N : ℕ}
    (i j : Fin N) (hij : i ≠ j)
    (w : Position × (Position × OtherPairConfiguration i j)) :
    pairToRightRestMeasurableEquiv i j hij w =
      (w.2.1, insertOtherParticleRight i j w.1 w.2.2) := by
  change (w.2.1, restRightInsertionMeasurableEquiv i j hij (w.1, w.2.2)) = _
  rw [restRightInsertionMeasurableEquiv_apply]

theorem measurePreserving_pairToRightRest {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (pairToRightRestMeasurableEquiv i j hij) volume volume := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Position × (Position × OtherPairConfiguration i j) →
          (Position × Position) × OtherPairConfiguration i j) volume volume :=
    volume_preserving_prodAssoc.symm
  have h2 : MeasurePreserving
      ((MeasurableEquiv.prodComm (α := Position) (β := Position)).prodCongr
        (MeasurableEquiv.refl (OtherPairConfiguration i j))) volume volume :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (Position × Position) × OtherPairConfiguration i j →
          Position × (Position × OtherPairConfiguration i j)) volume volume :=
    volume_preserving_prodAssoc
  have h4 : MeasurePreserving
      ((MeasurableEquiv.refl Position).prodCongr
        (restRightInsertionMeasurableEquiv i j hij)) volume volume :=
    (MeasurePreserving.id volume).prod (measurePreserving_restRightInsertion i j hij)
  exact ((h1.trans h2).trans h3).trans h4

/-- Pair currying transports concrete insertion in coordinate `i` to insertion
in the first abstract tensor factor. -/
theorem pairCurrying_oneParticleInsertion_left {N q : ℕ} (i j : Fin N)
    (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : RestState i q) :
    pairCurryingLinearIsometryEquiv i j hij (oneParticleInsertion i f v) =
      firstFactorInsertion (H := PairRestState i j q) f
        (restCurryingLeftLinearIsometryEquiv i j hij v) := by
  apply Lp.ext
  filter_upwards [pairCurryingLinearIsometryEquiv_apply_ae i j hij
      (oneParticleInsertion i f v),
    tensorInsertion_apply_ae (H := RestFactorState i j q) f
      (restCurryingLeftLinearIsometryEquiv i j hij v),
    oneParticleInsertion_ae i f v] with x hp ht hi
  apply PiLp.ext
  intro s
  apply Lp.ext
  have hi' := Measure.ae_ae_of_ae_prod
    ((measurePreserving_restLeftInsertion i j hij).quasiMeasurePreserving.ae (hi s))
  have hs := Lp.coeFn_smul (f x s) (restCurryingLeftLinearIsometryEquiv i j hij v)
  filter_upwards [hp s, hi', restCurryingLeftLinearIsometryEquiv_apply_ae i j hij v, hs]
    with z hpz hiz hrz hsz
  apply PiLp.ext
  intro r
  apply Lp.ext
  have hs' := Lp.coeFn_smul (f x s)
    (restCurryingLeftLinearIsometryEquiv i j hij v z r)
  filter_upwards [hpz r, hiz, hrz r, hs'] with y hpy hiy hry hsy
  ext t
  change pairCurryingLinearIsometryEquiv i j hij (oneParticleInsertion i f v) x s z r y t =
    firstFactorInsertion (H := PairRestState i j q) f
      (restCurryingLeftLinearIsometryEquiv i j hij v) x s z r y t
  rw [hpy t]
  rw [show firstFactorInsertion (H := PairRestState i j q) f
      (restCurryingLeftLinearIsometryEquiv i j hij v) x s z r y t =
      (f x s • restCurryingLeftLinearIsometryEquiv i j hij v) z r y t by
    rw [firstFactorInsertion, ht s]]
  rw [hsz]
  simp only [Pi.smul_apply, PiLp.smul_apply]
  rw [hsy]
  change oneParticleInsertion i f v (insertParticlePair i j x z y)
      (insertSpinPair i j s r t) =
    f x s * restCurryingLeftLinearIsometryEquiv i j hij v z r y t
  rw [hry t]
  have hiPair := hiy (insertOtherSpinLeft i j r t)
  rw [restLeftInsertionMeasurableEquiv_apply,
    insertParticle_insertOtherParticleLeft, insertSpin_insertOtherSpinLeft] at hiPair
  exact hiPair

/-- Pair currying transports concrete insertion in coordinate `j` to insertion
in the second abstract tensor factor. -/
theorem pairCurrying_oneParticleInsertion_right {N q : ℕ} (i j : Fin N)
    (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : RestState j q) :
    pairCurryingLinearIsometryEquiv i j hij (oneParticleInsertion j f v) =
      secondFactorInsertion (H := PairRestState i j q) f
        (restCurryingRightLinearIsometryEquiv i j hij v) := by
  have hi := oneParticleInsertion_ae j f v
  have hpull (r s : Fin q) (t : OtherPairSpinLabels i j q) :
      ∀ᵐ x : Position, ∀ᵐ z : Position, ∀ᵐ y : OtherPairConfiguration i j,
        oneParticleInsertion j f v (insertParticlePair i j x z y)
            (insertSpinPair i j s r t) =
          f z r * v (insertOtherParticleRight i j x y)
            (insertOtherSpinRight i j s t) := by
    have hnested : ∀ᵐ z : Position, ∀ᵐ y : OtherConfiguration j,
        oneParticleInsertion j f v (insertParticle j z y)
            (insertSpin j r (insertOtherSpinRight i j s t)) =
          f z r * v y (insertOtherSpinRight i j s t) := by
      filter_upwards [hi] with z hz
      exact (hz r).mono fun y hy => hy (insertOtherSpinRight i j s t)
    have hmeas : MeasurableSet {w : Position × OtherConfiguration j |
        oneParticleInsertion j f v (insertParticle j w.1 w.2)
            (insertSpin j r (insertOtherSpinRight i j s t)) =
          f w.1 r * v w.2 (insertOtherSpinRight i j s t)} := by
      let pState := PiLp.proj (𝕜 := ℂ) 2
        (fun _ : SpinLabels N q => ℂ) (insertSpin j r (insertOtherSpinRight i j s t))
      let pF := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q => ℂ) r
      let pV := PiLp.proj (𝕜 := ℂ) 2
        (fun _ : OtherSpinLabels j q => ℂ) (insertOtherSpinRight i j s t)
      have hleft : StronglyMeasurable (fun w : Position × OtherConfiguration j =>
          oneParticleInsertion j f v (insertParticle j w.1 w.2)
            (insertSpin j r (insertOtherSpinRight i j s t))) :=
        pState.continuous.comp_stronglyMeasurable
          ((Lp.stronglyMeasurable (oneParticleInsertion j f v)).comp_measurable
            (measurePreserving_insertParticle j).measurable)
      have hright : StronglyMeasurable (fun w : Position × OtherConfiguration j =>
          f w.1 r * v w.2 (insertOtherSpinRight i j s t)) :=
        ((pF.continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable f)).comp_measurable
          measurable_fst).mul
        ((pV.continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable v)).comp_measurable
          measurable_snd)
      exact hleft.measurableSet_eq_fun hright
    have hprod := (Measure.ae_prod_iff_ae_ae hmeas).2 hnested
    have hback := (measurePreserving_pairToRightRest i j hij).quasiMeasurePreserving.ae hprod
    have houter := Measure.ae_ae_of_ae_prod hback
    filter_upwards [houter] with x hx
    have hx' := Measure.ae_ae_of_ae_prod hx
    filter_upwards [hx'] with z hz
    filter_upwards [hz] with y hy
    rw [pairToRightRestMeasurableEquiv_apply] at hy
    simpa only [insertParticle_insertOtherParticleRight i j hij,
      insertSpin_insertOtherSpinRight i j hij] using hy
  have hpullRS (r s : Fin q) : ∀ᵐ x : Position, ∀ᵐ z : Position,
      ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
          oneParticleInsertion j f v (insertParticlePair i j x z y)
              (insertSpinPair i j s r t) =
            f z r * v (insertOtherParticleRight i j x y)
              (insertOtherSpinRight i j s t) := by
    have h₁ := eventually_forall_finite (fun t => hpull r s t)
    filter_upwards [h₁] with x hx
    have h₂ := eventually_forall_finite hx
    filter_upwards [h₂] with z hz
    exact eventually_forall_finite hz
  have hpullAll : ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ z : Position,
      ∀ᵐ y : OtherPairConfiguration i j, ∀ r : Fin q,
        ∀ t : OtherPairSpinLabels i j q,
          oneParticleInsertion j f v (insertParticlePair i j x z y)
              (insertSpinPair i j s r t) =
            f z r * v (insertOtherParticleRight i j x y)
              (insertOtherSpinRight i j s t) := by
    have hrs (s : Fin q) : ∀ᵐ x : Position, ∀ᵐ z : Position,
        ∀ᵐ y : OtherPairConfiguration i j, ∀ r : Fin q,
          ∀ t : OtherPairSpinLabels i j q,
            oneParticleInsertion j f v (insertParticlePair i j x z y)
                (insertSpinPair i j s r t) =
              f z r * v (insertOtherParticleRight i j x y)
                (insertOtherSpinRight i j s t) := by
      have h₁ := eventually_forall_finite (fun r => hpullRS r s)
      filter_upwards [h₁] with x hx
      have h₂ := eventually_forall_finite hx
      filter_upwards [h₂] with z hz
      exact eventually_forall_finite hz
    have h := eventually_forall_finite hrs
    filter_upwards [h] with x hx
    exact hx
  apply Lp.ext
  filter_upwards [pairCurryingLinearIsometryEquiv_apply_ae i j hij
      (oneParticleInsertion j f v),
    tensorTargetLift_apply_ae (ι := Fin q)
      (tensorInsertion (H := PairRestState i j q) f)
      (restCurryingRightLinearIsometryEquiv i j hij v),
    restCurryingRightLinearIsometryEquiv_apply_ae i j hij v,
    hpullAll] with x hp hl hrx hix
  apply PiLp.ext
  intro s
  apply Lp.ext
  filter_upwards [hp s,
    tensorInsertion_apply_ae (H := PairRestState i j q) f
      (restCurryingRightLinearIsometryEquiv i j hij v x s), hix s] with z hpz ht hiz
  apply PiLp.ext
  intro r
  apply Lp.ext
  have hs := Lp.coeFn_smul (f z r) (restCurryingRightLinearIsometryEquiv i j hij v x s)
  filter_upwards [hpz r, hrx s, hs, hiz] with y hpy hry hsy hiy
  ext t
  change pairCurryingLinearIsometryEquiv i j hij (oneParticleInsertion j f v) x s z r y t =
    secondFactorInsertion (H := PairRestState i j q) f
      (restCurryingRightLinearIsometryEquiv i j hij v) x s z r y t
  rw [hpy t]
  rw [show secondFactorInsertion (H := PairRestState i j q) f
      (restCurryingRightLinearIsometryEquiv i j hij v) x s =
      tensorInsertion (H := PairRestState i j q) f
        (restCurryingRightLinearIsometryEquiv i j hij v x s) by
    rw [secondFactorInsertion, hl s]]
  rw [ht r]
  rw [hsy]
  simp only [Pi.smul_apply, PiLp.smul_apply]
  change oneParticleInsertion j f v (insertParticlePair i j x z y)
      (insertSpinPair i j s r t) =
    f z r * restCurryingRightLinearIsometryEquiv i j hij v x s y t
  rw [hry t, hiy r t]

end LiebThirring

end
