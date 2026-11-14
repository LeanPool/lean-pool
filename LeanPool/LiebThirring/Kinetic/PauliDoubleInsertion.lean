/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionFactors
public import LeanPool.LiebThirring.Kinetic.PauliLiftCurrying
public import LeanPool.LiebThirring.Kinetic.FourierFactor

/-!
# Two-particle insertion on the state carrier

Insert the same one-particle vector in two distinct coordinates.

The two-particle insertion has its literal nested product representative.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal InnerProduct

namespace LiebThirring

/-- Insert the same one-particle vector in two distinct coordinates. -/
noncomputable def doubleParticleInsertion {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    PairRestState i j q →L[ℂ] State N q :=
  let C : PairCurriedState i j q ≃L[ℂ] State N q :=
    (pairCurryingLinearIsometryEquiv (q := q) i j hij).symm.toContinuousLinearEquiv
  C.toContinuousLinearMap.comp (doubleFactorInsertion (H := PairRestState i j q) f)

/-- The two-particle insertion has its literal nested product representative. -/
theorem doubleParticleInsertion_apply_ae {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : PairRestState i j q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ z : Position, ∀ r : Fin q,
      ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
        doubleParticleInsertion i j hij f v
            (insertParticlePair i j x z y) (insertSpinPair i j s r t) =
          f x s * f z r * v y t := by
  have hc := pairCurryingLinearIsometryEquiv_apply_ae i j hij
    (doubleParticleInsertion i j hij f v)
  have hout := tensorInsertion_apply_ae (H :=
    FirstFactorSpace (Fin q) Position (PairRestState i j q) (volume : Measure Position))
    f (tensorInsertion (H := PairRestState i j q) f v)
  have hin := tensorInsertion_apply_ae (H := PairRestState i j q) f v
  have heq : pairCurryingLinearIsometryEquiv (q := q) i j hij
      (doubleParticleInsertion i j hij f v) =
      doubleFactorInsertion (H := PairRestState i j q) f v := by
    change pairCurryingLinearIsometryEquiv (q := q) i j hij
      ((pairCurryingLinearIsometryEquiv (q := q) i j hij).symm
        (doubleFactorInsertion (H := PairRestState i j q) f v)) = _
    exact (pairCurryingLinearIsometryEquiv (q := q) i j hij).apply_symm_apply _
  filter_upwards [hc, hout] with x hcx hox
  intro s
  filter_upwards [hcx s, hin,
    Lp.coeFn_smul (f x s) (tensorInsertion (H := PairRestState i j q) f v)]
      with z hcz hiz hsmz
  intro r
  filter_upwards [hcz r,
    Lp.coeFn_smul (f x s) (f z r • v), Lp.coeFn_smul (f z r) v]
      with y hczy hsm hsmv
  intro t
  rw [← hczy t, heq]
  change ((tensorInsertion (H := FirstFactorSpace (Fin q) Position
    (PairRestState i j q) (volume : Measure Position)) f
      (tensorInsertion (H := PairRestState i j q) f v)) x s) z r y t = _
  rw [hox s, hsmz]
  change ((f x s) • ((tensorInsertion (H := PairRestState i j q) f v) z r)) y t = _
  rw [hiz r, hsm]
  change f x s * ((f z r • v) y t) = _
  rw [hsmv]
  change f x s * (f z r * v y t) = _
  ring

private theorem doubleParticleInsertion_apply_swap_ae {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : PairRestState i j q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ z : Position, ∀ r : Fin q,
      ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
        doubleParticleInsertion i j hij f v
            (insertParticlePair i j z x y) (insertSpinPair i j r s t) =
          f z r * f x s * v y t := by
  let μp : Measure Position := volume
  let μr : Measure (OtherPairConfiguration i j) := volume
  let mtranspose : MeasurePreserving
      (fun w : Position × (Position × OtherPairConfiguration i j) =>
        (w.2.1, (w.1, w.2.2))) (μp.prod (μp.prod μr)) (μp.prod (μp.prod μr)) := by
    let massoc₁ : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
        Position × (Position × OtherPairConfiguration i j) →
          (Position × Position) × OtherPairConfiguration i j)
        (μp.prod (μp.prod μr)) ((μp.prod μp).prod μr) :=
      (measurePreserving_prodAssoc μp μp μr).symm MeasurableEquiv.prodAssoc
    let mswap : MeasurePreserving (Prod.map Prod.swap id)
        ((μp.prod μp).prod μr) ((μp.prod μp).prod μr) :=
      MeasurePreserving.prod Measure.measurePreserving_swap (MeasurePreserving.id μr)
    let massoc₂ : MeasurePreserving MeasurableEquiv.prodAssoc
        ((μp.prod μp).prod μr) (μp.prod (μp.prod μr)) :=
      measurePreserving_prodAssoc μp μp μr
    exact massoc₂.comp (mswap.comp massoc₁)
  have hbase := doubleParticleInsertion_apply_ae i j hij f v
  have hswap (s : Fin q) (r : Fin q) (t : OtherPairSpinLabels i j q) :
      ∀ᵐ x : Position, ∀ᵐ z : Position, ∀ᵐ y : OtherPairConfiguration i j,
        doubleParticleInsertion i j hij f v
            (insertParticlePair i j z x y) (insertSpinPair i j r s t) =
          f z r * f x s * v y t := by
    let P := fun w : Position × (Position × OtherPairConfiguration i j) =>
      doubleParticleInsertion i j hij f v
          (insertParticlePair i j w.1 w.2.1 w.2.2) (insertSpinPair i j r s t) =
        f w.1 r * f w.2.1 s * v w.2.2 t
    have hP : MeasurableSet {w | P w} := by
      apply measurableSet_setOfPred.mpr
      have hins : Measurable (fun w : Position × (Position × OtherPairConfiguration i j) =>
          insertParticlePair i j w.1 w.2.1 w.2.2) := by
        convert (pairInsertionMeasurableEquiv i j hij).measurable using 1
        funext w
        exact (pairInsertionMeasurableEquiv_apply i j hij w).symm
      have hl : StronglyMeasurable (fun w : Position ×
          (Position × OtherPairConfiguration i j) =>
          doubleParticleInsertion i j hij f v
            (insertParticlePair i j w.1 w.2.1 w.2.2) (insertSpinPair i j r s t)) :=
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : SpinLabels N q => ℂ)
          (insertSpinPair i j r s t)).continuous.comp_stronglyMeasurable
            ((Lp.stronglyMeasurable (doubleParticleInsertion i j hij f v)).comp_measurable hins)
      exact Measurable.eq hl.measurable (by fun_prop)
    have hnested : ∀ᵐ x : Position, ∀ᵐ z : Position,
        ∀ᵐ y : OtherPairConfiguration i j, P (x, (z, y)) := by
      filter_upwards [hbase] with x hx
      filter_upwards [hx r] with z hz
      filter_upwards [hz s] with y hy
      exact hy t
    have hjoint : ∀ᵐ w ∂μp.prod (μp.prod μr), P w := by
      apply (Measure.ae_prod_iff_ae_ae hP).2
      filter_upwards [hnested] with x hx
      apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {w | P (x, w)} from by
        change MeasurableSet ((fun w => (x, w)) ⁻¹' {w | P w})
        exact hP.preimage (by fun_prop))).2 hx
    have htrans := mtranspose.quasiMeasurePreserving.ae hjoint
    have htrans' : ∀ᵐ x : Position, ∀ᵐ z : Position,
        ∀ᵐ y : OtherPairConfiguration i j, P (z, (x, y)) := by
      have hP' : MeasurableSet {w : Position ×
          (Position × OtherPairConfiguration i j) | P (w.2.1, (w.1, w.2.2))} :=
        hP.preimage mtranspose.measurable
      have := (Measure.ae_prod_iff_ae_ae hP').1 htrans
      filter_upwards [this] with x hx
      exact (Measure.ae_prod_iff_ae_ae
        (show MeasurableSet {w : Position × OtherPairConfiguration i j |
            P (w.1, (x, w.2))} from by
          change MeasurableSet ((fun w => (x, w)) ⁻¹'
            {w : Position × (Position × OtherPairConfiguration i j) |
              P (w.2.1, (w.1, w.2.2))})
          exact hP'.preimage (by fun_prop))).1 hx
    simpa only [P] using htrans'
  have hall : ∀ᵐ x : Position, ∀ s : Fin q, ∀ r : Fin q,
      ∀ t : OtherPairSpinLabels i j q, ∀ᵐ z : Position,
        ∀ᵐ y : OtherPairConfiguration i j,
          doubleParticleInsertion i j hij f v
              (insertParticlePair i j z x y) (insertSpinPair i j r s t) =
            f z r * f x s * v y t :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun r => ae_all_iff.mpr fun t => hswap s r t
  filter_upwards [hall] with x hx
  intro s
  have hzr : ∀ᵐ z : Position, ∀ r : Fin q, ∀ t : OtherPairSpinLabels i j q,
      ∀ᵐ y : OtherPairConfiguration i j,
        doubleParticleInsertion i j hij f v
            (insertParticlePair i j z x y) (insertSpinPair i j r s t) =
          f z r * f x s * v y t :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun t => hx s r t
  filter_upwards [hzr] with z hz
  intro r
  have hyt : ∀ᵐ y : OtherPairConfiguration i j, ∀ t : OtherPairSpinLabels i j q,
      doubleParticleInsertion i j hij f v
          (insertParticlePair i j z x y) (insertSpinPair i j r s t) =
        f z r * f x s * v y t := ae_all_iff.mpr fun t => hz r t
  exact hyt

/-- Exchanging the two inserted coordinates fixes the double insertion. -/
theorem simultaneousPermutation_doubleParticleInsertion {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : PairRestState i j q) :
    simultaneousPermutation (Equiv.swap i j)
        (doubleParticleInsertion i j hij f v) =
      doubleParticleInsertion i j hij f v := by
  apply (pairCurryingLinearIsometryEquiv (q := q) i j hij).injective
  apply Lp.ext
  have hp := Measure.ae_ae_of_ae_prod
    ((measurePreserving_pairInsertion i j hij).quasiMeasurePreserving.ae
      (simultaneousPermutation_apply_ae (Equiv.swap i j)
        (doubleParticleInsertion i j hij f v)))
  filter_upwards [pairCurryingLinearIsometryEquiv_apply_ae i j hij
      (simultaneousPermutation (Equiv.swap i j) (doubleParticleInsertion i j hij f v)),
    pairCurryingLinearIsometryEquiv_apply_ae i j hij
      (doubleParticleInsertion i j hij f v), hp,
    doubleParticleInsertion_apply_ae i j hij f v,
    doubleParticleInsertion_apply_swap_ae i j hij f v] with x hl hr hp hD hDswap
  apply PiLp.ext
  intro s
  apply Lp.ext
  have hp' := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hl s, hr s, hp', hD s, hDswap s] with z hlz hrz hpz hDz hDswapz
  apply PiLp.ext
  intro r
  apply Lp.ext
  filter_upwards [hlz r, hrz r, hpz, hDz r, hDswapz r]
    with y hly hry hpy hDy hDswapy
  ext t
  rw [hly t, hry t, ← pairInsertionMeasurableEquiv_apply i j hij (x, (z, y)),
    hpy, pairInsertionMeasurableEquiv_apply,
    permutePositions_swap_insertParticlePair i j hij,
    permuteSpins_swap_insertSpinPair i j hij, hDy t]
  rw [hDswapy t]
  ring

end LiebThirring

end
