/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.Insertion
public import LeanPool.LiebThirring.Kinetic.Encoding
public import LeanPool.LiebThirring.Kinetic.Permutation

/-! # Two-particle coordinate encoding

The coordinate splitting used to compare rank-one lifts in two distinct
particle coordinates.  The order of the two displayed particles is retained;
simultaneous exchange therefore acts by swapping those two entries and fixes
the remaining configuration.
-/

@[expose] public section

open MeasureTheory WithLp

namespace LiebThirring

/-- Partition the full spatial index into two selected particles and all
remaining coordinates. -/
def pairInsertionIndexEquiv {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (Fin N × Fin 3) ≃ (Fin 3 ⊕ (Fin 3 ⊕ ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3))) where
  toFun ka := if hi : ka.1 = i then Sum.inl ka.2 else if hj : ka.1 = j then
    Sum.inr (Sum.inl ka.2) else Sum.inr (Sum.inr (⟨ka.1, hi, hj⟩, ka.2))
  invFun := Sum.elim (fun a => (i, a))
    (Sum.elim (fun a => (j, a)) (fun ka => (ka.1.val, ka.2)))
  left_inv ka := by
    rcases ka with ⟨k, a⟩
    dsimp
    by_cases hi : k = i
    · simp [hi]
    by_cases hj : k = j
    · simp [hj, hij.symm]
    · simp [hi, hj]
  right_inv u := by
    rcases u with a | u
    · simp
    · rcases u with a | ka
      · simp [hij.symm]
      · simp [ka.1.property.1, ka.1.property.2]

/-- Spatial coordinates other than two specified distinct particles. -/
abbrev OtherPairConfiguration {N : ℕ} (i j : Fin N) :=
  EuclideanSpace ℝ ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3)

/-- Spin labels other than two specified distinct particles. -/
abbrev OtherPairSpinLabels {N : ℕ} (i j : Fin N) (q : ℕ) :=
  {k : Fin N // k ≠ i ∧ k ≠ j} → Fin q

/-- Insert two distinct spatial particle coordinates. -/
def insertParticlePair {N : ℕ} (i j : Fin N) (x z : Position)
    (y : OtherPairConfiguration i j) : Configuration N :=
  toLp 2 (fun ka => if hi : ka.1 = i then x ka.2 else
    if hj : ka.1 = j then z ka.2 else y (⟨ka.1, hi, hj⟩, ka.2))

/-- Insert two distinct spin coordinates. -/
def insertSpinPair {N q : ℕ} (i j : Fin N) (s r : Fin q)
    (t : OtherPairSpinLabels i j q) : SpinLabels N q :=
  fun k => if hi : k = i then s else if hj : k = j then r else t ⟨k, hi, hj⟩

/-- The measurable coordinate equivalence associated with ordered insertion
of two distinct particles. -/
noncomputable def pairInsertionMeasurableEquiv {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (Position × (Position × OtherPairConfiguration i j)) ≃ᵐ Configuration N :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr
    ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr
      (MeasurableEquiv.toLp 2
        (({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) → ℝ)).symm)).trans
  (((MeasurableEquiv.refl (Fin 3 → ℝ)).prodCongr
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕
        ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) => ℝ)).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ (Fin 3 ⊕
      ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3)) => ℝ)).symm.trans
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin 3 => ℝ)
        (pairInsertionIndexEquiv i j hij).symm).trans (MeasurableEquiv.toLp 2 _))))

theorem pairInsertionMeasurableEquiv_apply {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : Position × (Position × OtherPairConfiguration i j)) :
    pairInsertionMeasurableEquiv i j hij z = insertParticlePair i j z.1 z.2.1 z.2.2 := by
  ext ka
  rcases ka with ⟨k, a⟩
  by_cases hi : k = i
  · simp [pairInsertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.prodCongr,
    pairInsertionIndexEquiv, insertParticlePair, hi]
  by_cases hj : k = j
  · simp [pairInsertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.prodCongr,
    pairInsertionIndexEquiv, insertParticlePair, hj, hij.symm]
  · simp [pairInsertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.prodCongr,
    pairInsertionIndexEquiv, insertParticlePair, hi, hj]

/-- Ordered insertion of two distinct particles preserves product volume. -/
theorem measurePreserving_pairInsertion {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (pairInsertionMeasurableEquiv i j hij) volume volume := by
  exact ((PiLp.volume_preserving_ofLp (Fin 3)).prod
    ((PiLp.volume_preserving_ofLp (Fin 3)).prod
      (PiLp.volume_preserving_ofLp ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3)))).trans
    (((MeasurePreserving.id (volume : Measure (Fin 3 → ℝ))).prod
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 3 ⊕
        ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) => ℝ))).trans
      ((volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 3 ⊕ (Fin 3 ⊕
        ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3)) => ℝ)).trans
        ((volume_measurePreserving_piCongrLeft _ (pairInsertionIndexEquiv i j hij).symm).trans
          (PiLp.volume_preserving_toLp (Fin N × Fin 3)))))

/-- Split a spin assignment into two selected labels and the remaining labels. -/
def spinPairInsertionEquiv {N q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (Fin q × (Fin q × OtherPairSpinLabels i j q)) ≃ SpinLabels N q where
  toFun z := insertSpinPair i j z.1 z.2.1 z.2.2
  invFun t := (t i, t j, fun k => t k.val)
  left_inv z := by
    rcases z with ⟨s, r, t⟩
    apply Prod.ext
    · simp [insertSpinPair]
    · apply Prod.ext
      · simp [insertSpinPair, hij.symm]
      · funext k
        simp [insertSpinPair, k.property.1, k.property.2]
  right_inv t := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [insertSpinPair]
    by_cases hkj : k = j
    · subst k
      simp [insertSpinPair, hij.symm]
    · simp [insertSpinPair, hki, hkj]

/-- Regroup finite spin amplitudes into two selected spin factors. -/
noncomputable def spinPairCurryingLinearIsometryEquiv {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    SpinAmplitudes N q ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Fin q =>
      PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q))) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (spinPairInsertionEquiv i j hij).symm).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sigmaEquivProd (Fin q)
        (Fin q × OtherPairSpinLabels i j q)).symm).trans
      ((LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : Fin q) (_ : Fin q × OtherPairSpinLabels i j q) => ℂ)).trans
        (LinearIsometryEquiv.piLpCongrRight 2 (𝕜 := ℂ)
          (fun _ : Fin q => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (Equiv.sigmaEquivProd (Fin q) (OtherPairSpinLabels i j q)).symm).trans
            (LinearIsometryEquiv.piLpCurry ℂ 2
              (fun (_ : Fin q) (_ : OtherPairSpinLabels i j q) => ℂ))))))

/-- Swapping the two displayed spatial entries is simultaneous particle exchange. -/
theorem permutePositions_swap_insertParticlePair {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x z : Position) (y : OtherPairConfiguration i j) :
    permutePositions (Equiv.swap i j) (insertParticlePair i j x z y) =
      insertParticlePair i j z x y := by
  ext ka
  rcases ka with ⟨k, a⟩
  simp only [permutePositions, insertParticlePair]
  by_cases hki : k = i
  · subst k
    simp [hij.symm]
  by_cases hkj : k = j
  · subst k
    simp [hki]
  simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

/-- Swapping the two displayed spin entries is simultaneous particle exchange. -/
theorem permuteSpins_swap_insertSpinPair {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (s r : Fin q) (t : OtherPairSpinLabels i j q) :
    permuteSpins (Equiv.swap i j) (insertSpinPair i j s r t) =
      insertSpinPair i j r s t := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [permuteSpins, insertSpinPair, hij.symm]
  by_cases hkj : k = j
  · subst k
    simp [permuteSpins, insertSpinPair, hki]
  simp [permuteSpins, insertSpinPair, Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

end LiebThirring

end
