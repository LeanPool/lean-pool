/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.PauliLiftEncoding

/-! # Splitting a second particle from a remaining-coordinate carrier

These ordered encodings split particle `j` from the coordinates complementary
to `i`, or particle `i` from those complementary to `j`, while using the same
ordered pair-rest carrier in both cases.
-/

@[expose] public section

open MeasureTheory WithLp

namespace LiebThirring

/-- Split the coordinate `j` from the spatial indices complementary to `i`. -/
def restLeftIndexEquiv {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ({k : Fin N // k ≠ i} × Fin 3) ≃
      (Fin 3 ⊕ ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3)) where
  toFun ka := if h : ka.1.val = j then Sum.inl ka.2 else
    Sum.inr (⟨ka.1.val, ka.1.property, h⟩, ka.2)
  invFun := Sum.elim (fun a => (⟨j, hij.symm⟩, a))
    (fun ka => (⟨ka.1.val, ka.1.property.1⟩, ka.2))
  left_inv ka := by
    rcases ka with ⟨k, a⟩
    by_cases h : k.val = j
    · simp only [h, ↓reduceDIte]
      change (⟨j, hij.symm⟩, a) = (k, a)
      apply Prod.ext
      · apply Subtype.ext
        exact h.symm
      · rfl
    · simp only [h, ↓reduceDIte]
      change (⟨k.val, k.property⟩, a) = (k, a)
      rfl
  right_inv u := by
    rcases u with a | ka
    · simp
    · simp [ka.1.property.2]

/-- Split the coordinate `i` from the spatial indices complementary to `j`. -/
def restRightIndexEquiv {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ({k : Fin N // k ≠ j} × Fin 3) ≃
      (Fin 3 ⊕ ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3)) where
  toFun ka := if h : ka.1.val = i then Sum.inl ka.2 else
    Sum.inr (⟨ka.1.val, h, ka.1.property⟩, ka.2)
  invFun := Sum.elim (fun a => (⟨i, hij⟩, a))
    (fun ka => (⟨ka.1.val, ka.1.property.2⟩, ka.2))
  left_inv ka := by
    rcases ka with ⟨k, a⟩
    by_cases h : k.val = i
    · simp only [h, ↓reduceDIte]
      change (⟨i, hij⟩, a) = (k, a)
      apply Prod.ext
      · apply Subtype.ext
        exact h.symm
      · rfl
    · simp only [h, ↓reduceDIte]
      change (⟨k.val, k.property⟩, a) = (k, a)
      rfl
  right_inv u := by
    rcases u with a | ka
    · simp
    · simp [ka.1.property.1]

/-- Insert particle `j` into the spatial coordinates complementary to `i`. -/
def insertOtherParticleLeft {N : ℕ} (i j : Fin N) (z : Position)
    (y : OtherPairConfiguration i j) : OtherConfiguration i :=
  toLp 2 (fun ka => if h : ka.1.val = j then z ka.2 else
    y (⟨ka.1.val, ka.1.property, h⟩, ka.2))

/-- Insert particle `i` into the spatial coordinates complementary to `j`. -/
def insertOtherParticleRight {N : ℕ} (i j : Fin N) (x : Position)
    (y : OtherPairConfiguration i j) : OtherConfiguration j :=
  toLp 2 (fun ka => if h : ka.1.val = i then x ka.2 else
    y (⟨ka.1.val, h, ka.1.property⟩, ka.2))

/-- Insert spin `j` into the labels complementary to `i`. -/
def insertOtherSpinLeft {N q : ℕ} (i j : Fin N) (r : Fin q)
    (t : OtherPairSpinLabels i j q) : OtherSpinLabels i q :=
  fun k => if h : k.val = j then r else t ⟨k.val, k.property, h⟩

/-- Insert spin `i` into the labels complementary to `j`. -/
def insertOtherSpinRight {N q : ℕ} (i j : Fin N) (s : Fin q)
    (t : OtherPairSpinLabels i j q) : OtherSpinLabels j q :=
  fun k => if h : k.val = i then s else t ⟨k.val, h, k.property⟩

/-- Spatial insertion into `RestState i` as a measurable equivalence. -/
noncomputable def restLeftInsertionMeasurableEquiv {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    (Position × OtherPairConfiguration i j) ≃ᵐ OtherConfiguration i :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr
    (MeasurableEquiv.toLp 2
      (({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) → ℝ)).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕
      ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : {k : Fin N // k ≠ i} × Fin 3 => ℝ)
      (restLeftIndexEquiv i j hij).symm).trans (MeasurableEquiv.toLp 2 _)))

/-- Spatial insertion into `RestState j` as a measurable equivalence. -/
noncomputable def restRightInsertionMeasurableEquiv {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    (Position × OtherPairConfiguration i j) ≃ᵐ OtherConfiguration j :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr
    (MeasurableEquiv.toLp 2
      (({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) → ℝ)).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕
      ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : {k : Fin N // k ≠ j} × Fin 3 => ℝ)
      (restRightIndexEquiv i j hij).symm).trans (MeasurableEquiv.toLp 2 _)))

theorem restLeftInsertionMeasurableEquiv_apply {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) (w : Position × OtherPairConfiguration i j) :
    restLeftInsertionMeasurableEquiv i j hij w = insertOtherParticleLeft i j w.1 w.2 := by
  ext ka
  simp [restLeftInsertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, restLeftIndexEquiv, insertOtherParticleLeft]
  split <;> rfl

theorem restRightInsertionMeasurableEquiv_apply {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) (w : Position × OtherPairConfiguration i j) :
    restRightInsertionMeasurableEquiv i j hij w = insertOtherParticleRight i j w.1 w.2 := by
  ext ka
  simp [restRightInsertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, restRightIndexEquiv, insertOtherParticleRight]
  split <;> rfl

theorem measurePreserving_restLeftInsertion {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (restLeftInsertionMeasurableEquiv i j hij) volume volume := by
  exact ((PiLp.volume_preserving_ofLp (Fin 3)).prod
    (PiLp.volume_preserving_ofLp ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3))).trans
    ((volume_measurePreserving_sumPiEquivProdPi_symm _).trans
      ((volume_measurePreserving_piCongrLeft _ (restLeftIndexEquiv i j hij).symm).trans
        (PiLp.volume_preserving_toLp ({k : Fin N // k ≠ i} × Fin 3))))

theorem measurePreserving_restRightInsertion {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (restRightInsertionMeasurableEquiv i j hij) volume volume := by
  exact ((PiLp.volume_preserving_ofLp (Fin 3)).prod
    (PiLp.volume_preserving_ofLp ({k : Fin N // k ≠ i ∧ k ≠ j} × Fin 3))).trans
    ((volume_measurePreserving_sumPiEquivProdPi_symm _).trans
      ((volume_measurePreserving_piCongrLeft _ (restRightIndexEquiv i j hij).symm).trans
        (PiLp.volume_preserving_toLp ({k : Fin N // k ≠ j} × Fin 3))))

/-- Split remaining spin labels in the left orientation. -/
def restLeftSpinInsertionEquiv {N q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (Fin q × OtherPairSpinLabels i j q) ≃ OtherSpinLabels i q where
  toFun w := insertOtherSpinLeft i j w.1 w.2
  invFun u := (u ⟨j, hij.symm⟩, fun k => u ⟨k.val, k.property.1⟩)
  left_inv w := by
    apply Prod.ext
    · simp [insertOtherSpinLeft]
    · funext k
      simp [insertOtherSpinLeft, k.property.2]
  right_inv u := by
    funext k
    by_cases h : k.val = j
    · subst h
      simp [insertOtherSpinLeft]
    · simp [insertOtherSpinLeft, h]

/-- Split remaining spin labels in the right orientation. -/
def restRightSpinInsertionEquiv {N q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (Fin q × OtherPairSpinLabels i j q) ≃ OtherSpinLabels j q where
  toFun w := insertOtherSpinRight i j w.1 w.2
  invFun u := (u ⟨i, hij⟩, fun k => u ⟨k.val, k.property.2⟩)
  left_inv w := by
    apply Prod.ext
    · simp [insertOtherSpinRight]
    · funext k
      simp [insertOtherSpinRight, k.property.1]
  right_inv u := by
    funext k
    by_cases h : k.val = i
    · subst h
      simp [insertOtherSpinRight]
    · simp [insertOtherSpinRight, h]

/-- Split off the left selected spin from the remaining spin assignment. -/
noncomputable def restLeftSpinCurryingEquiv {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    EuclideanSpace ℂ (OtherSpinLabels i q) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (restLeftSpinInsertionEquiv i j hij).symm).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sigmaEquivProd (Fin q) (OtherPairSpinLabels i j q)).symm).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : Fin q) (_ : OtherPairSpinLabels i j q) => ℂ)))

/-- Split off the right selected spin from the remaining spin assignment. -/
noncomputable def restRightSpinCurryingEquiv {N q : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    EuclideanSpace ℂ (OtherSpinLabels j q) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherPairSpinLabels i j q)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (restRightSpinInsertionEquiv i j hij).symm).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sigmaEquivProd (Fin q) (OtherPairSpinLabels i j q)).symm).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : Fin q) (_ : OtherPairSpinLabels i j q) => ℂ)))

theorem insertParticle_insertOtherParticleLeft {N : ℕ} (i j : Fin N)
    (x z : Position) (y : OtherPairConfiguration i j) :
    insertParticle i x (insertOtherParticleLeft i j z y) =
      insertParticlePair i j x z y := by
  ext ka
  rcases ka with ⟨k, a⟩
  change (if hi : k = i then x a else if hj : k = j then z a else
    y (⟨k, hi, hj⟩, a)) =
      if hi : k = i then x a else if hj : k = j then z a else y (⟨k, hi, hj⟩, a)
  rfl

theorem insertParticle_insertOtherParticleRight {N : ℕ} (i j : Fin N)
    (hij : i ≠ j) (x z : Position) (y : OtherPairConfiguration i j) :
    insertParticle j z (insertOtherParticleRight i j x y) =
      insertParticlePair i j x z y := by
  ext ka
  rcases ka with ⟨k, a⟩
  by_cases hj : k = j
  · subst k
    simp [insertParticle, insertParticlePair, hij.symm]
  by_cases hi : k = i
  · subst k
    simp [insertParticle, insertParticlePair, insertOtherParticleRight, hij]
  · simp [insertParticle, insertParticlePair, insertOtherParticleRight, hi, hj]

theorem insertSpin_insertOtherSpinLeft {N q : ℕ} (i j : Fin N)
    (s r : Fin q) (t : OtherPairSpinLabels i j q) :
    insertSpin i s (insertOtherSpinLeft i j r t) = insertSpinPair i j s r t := by
  funext k
  change (if hi : k = i then s else if hj : k = j then r else t ⟨k, hi, hj⟩) =
    if hi : k = i then s else if hj : k = j then r else t ⟨k, hi, hj⟩
  rfl

theorem insertSpin_insertOtherSpinRight {N q : ℕ} (i j : Fin N)
    (hij : i ≠ j) (s r : Fin q) (t : OtherPairSpinLabels i j q) :
    insertSpin j r (insertOtherSpinRight i j s t) = insertSpinPair i j s r t := by
  funext k
  by_cases hj : k = j
  · subst k
    simp [insertSpin, insertSpinPair, hij.symm]
  by_cases hi : k = i
  · subst k
    simp [insertSpin, insertSpinPair, insertOtherSpinRight, hij]
  · simp [insertSpin, insertSpinPair, insertOtherSpinRight, hi, hj]

end LiebThirring

end
