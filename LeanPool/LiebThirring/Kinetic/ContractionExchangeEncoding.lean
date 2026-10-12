/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionState
public import LeanPool.LiebThirring.Kinetic.CurryingExchange

/-! # Remaining-coordinate transport under particle exchange

The transposition between two particle labels bijects their complementary
spatial and spin labels. This is the concrete unitary needed to compare
one-particle contractions in different coordinates.
-/

public section

open MeasureTheory WithLp

namespace LiebThirring

/-- Exchange bijects the indices complementary to its two distinguished labels. -/
@[expose] def restExchangeIndexEquiv {N : ℕ} (i j : Fin N) :
    {k : Fin N // k ≠ i} ≃ {k : Fin N // k ≠ j} where
  toFun k := ⟨Equiv.swap i j k, by
    intro h
    have := (Equiv.swap_apply_eq_iff.mp h)
    simp only [Equiv.swap_apply_right] at this
    exact k.property this⟩
  invFun k := ⟨Equiv.swap i j k, by
    intro h
    have := (Equiv.swap_apply_eq_iff.mp h)
    simp only [Equiv.swap_apply_left] at this
    exact k.property this⟩
  left_inv k := by ext; simp
  right_inv k := by ext; simp

/-- Spatial exchange on the remaining coordinates. -/
@[expose] noncomputable def restExchangeSpatial {N : ℕ} (i j : Fin N) :
    OtherConfiguration j ≃ₗᵢ[ℝ] OtherConfiguration i :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((restExchangeIndexEquiv i j).symm.prodCongr (Equiv.refl (Fin 3)))

/-- Spin exchange on the remaining labels. -/
@[expose] def restExchangeSpins {N q : ℕ} (i j : Fin N) :
    OtherSpinLabels i q ≃ OtherSpinLabels j q :=
  Equiv.piCongrLeft (fun _ : {k : Fin N // k ≠ j} => Fin q)
    (restExchangeIndexEquiv i j)

/-- Spin-amplitude transport on the remaining labels. -/
@[expose] noncomputable def restExchangeAmplitudes {N q : ℕ} (i j : Fin N) :
    EuclideanSpace ℂ (OtherSpinLabels i q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (OtherSpinLabels j q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (restExchangeSpins i j)

/-- The remaining-state unitary induced by particle exchange. -/
@[expose] noncomputable def restExchange {N q : ℕ} (i j : Fin N) :
    RestState i q ≃ₗᵢ[ℂ] RestState j q :=
  (l2PullbackEquiv (restExchangeSpatial i j).toHomeomorph.toMeasurableEquiv
    (restExchangeSpatial i j).measurePreserving).trans
    (l2TargetEquiv (volume : Measure (OtherConfiguration j)) (restExchangeAmplitudes i j))

/-- Remaining spatial exchange intertwines the two insertion maps. -/
theorem permutePositions_swap_insertParticle {N : ℕ} (i j : Fin N)
    (x : Position) (y : OtherConfiguration j) :
    permutePositions (Equiv.swap i j) (insertParticle j x y) =
      insertParticle i x (restExchangeSpatial i j y) := by
  ext ka
  rcases ka with ⟨k, a⟩
  change (if h : Equiv.swap i j k = j then x a else y (⟨Equiv.swap i j k, h⟩, a)) =
    (if h : k = i then x a else restExchangeSpatial i j y (⟨k, h⟩, a))
  by_cases hk : k = i
  · subst k
    simp
  have hs : Equiv.swap i j k ≠ j := by
    intro h
    exact hk (by simpa only [Equiv.swap_apply_right] using (Equiv.swap_apply_eq_iff.mp h))
  simp only [hk, hs, ↓reduceDIte]
  rfl

/-- Remaining spin exchange intertwines the two spin insertions. -/
theorem permuteSpins_swap_insertSpin {N q : ℕ} (i j : Fin N) (s : Fin q)
    (t : OtherSpinLabels j q) :
    permuteSpins (Equiv.swap i j) (insertSpin j s t) =
      insertSpin i s ((restExchangeSpins i j).symm t) := by
  funext k
  change (if h : Equiv.swap i j k = j then s else t ⟨Equiv.swap i j k, h⟩) =
    (if h : k = i then s else (restExchangeSpins i j).symm t ⟨k, h⟩)
  by_cases hk : k = i
  · subst k
    simp
  have hs : Equiv.swap i j k ≠ j := by
    intro h
    exact hk (by simpa only [Equiv.swap_apply_right] using (Equiv.swap_apply_eq_iff.mp h))
  simp only [hk, hs, ↓reduceDIte]
  rfl

/-- Exact representative of the remaining-state exchange unitary. -/
theorem restExchange_ae {N q : ℕ} (i j : Fin N) (v : RestState i q) :
    ∀ᵐ y : OtherConfiguration j, ∀ t : OtherSpinLabels j q,
      restExchange i j v y t =
        v (restExchangeSpatial i j y) ((restExchangeSpins i j).symm t) := by
  let A := l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels i q))
    (restExchangeSpatial i j).toHomeomorph.toMeasurableEquiv
    (restExchangeSpatial i j).measurePreserving
  filter_upwards [l2PullbackEquiv_ae
    (restExchangeSpatial i j).toHomeomorph.toMeasurableEquiv
    (restExchangeSpatial i j).measurePreserving v,
    l2TargetEquiv_ae (volume : Measure (OtherConfiguration j))
      (restExchangeAmplitudes i j) (A v)] with y ha hb
  intro t
  change l2TargetEquiv (volume : Measure (OtherConfiguration j))
    (restExchangeAmplitudes i j) (A v) y t = _
  rw [hb, ha]
  rfl

/-- Simultaneous particle permutation packaged as a unitary on `State`. -/
@[expose] noncomputable def statePermutationLinearIsometryEquiv {N q : ℕ}
    (σ : Equiv.Perm (Fin N)) : State N q ≃ₗᵢ[ℂ] State N q :=
  (l2PullbackEquiv (permutationLinearIsometryEquiv σ).toHomeomorph.toMeasurableEquiv
    (permutationLinearIsometryEquiv σ).measurePreserving).trans
      (l2TargetEquiv (volume : Measure (Configuration N)) (spinPermutationLinearIsometryEquiv σ))

@[simp] theorem statePermutationLinearIsometryEquiv_apply {N q : ℕ}
    (σ : Equiv.Perm (Fin N)) (ψ : State N q) :
    statePermutationLinearIsometryEquiv σ ψ = simultaneousPermutation σ ψ := rfl

end LiebThirring

end
