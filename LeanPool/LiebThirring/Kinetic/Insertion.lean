/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Defs.Configuration
/-!
# Particle insertion and product volume

Partition spatial coordinates into particle `i` and the other particles.

Coordinate insertion as an equivalence of measurable spaces.
-/
public section
open MeasureTheory WithLp
namespace LiebThirring

/-- Partition spatial coordinates into particle `i` and the other particles. -/
@[expose] def insertionIndexEquiv {N : ℕ} (i : Fin N) :
    (Fin N × Fin 3) ≃ (Fin 3 ⊕ ({j : Fin N // j ≠ i} × Fin 3)) where
  toFun ja := if h : ja.1 = i then Sum.inl ja.2 else Sum.inr (⟨ja.1, h⟩, ja.2)
  invFun := Sum.elim (fun a => (i, a)) (fun ja => (ja.1.val, ja.2))
  left_inv := by
    rintro ⟨j, a⟩
    dsimp
    split <;> simp_all
  right_inv ja := by cases ja with
    | inl a => simp
    | inr ja => simp [ja.1.property]

/-- Coordinate insertion as an equivalence of measurable spaces. -/
@[expose] noncomputable def insertionMeasurableEquiv {N : ℕ} (i : Fin N) :
    (Position × OtherConfiguration i) ≃ᵐ Configuration N :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr
    (MeasurableEquiv.toLp 2 (({j : Fin N // j ≠ i} × Fin 3) → ℝ)).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕
      ({j : Fin N // j ≠ i} × Fin 3) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin 3 => ℝ)
      (insertionIndexEquiv i).symm).trans (MeasurableEquiv.toLp 2 _)))

theorem insertionMeasurableEquiv_apply {N : ℕ} (i : Fin N)
    (z : Position × OtherConfiguration i) :
    insertionMeasurableEquiv i z = insertParticle i z.1 z.2 := by
  ext ja
  simp [insertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, insertionIndexEquiv, insertParticle]
  split <;> rfl

theorem measurePreserving_insertion {N : ℕ} (i : Fin N) :
    MeasurePreserving (insertionMeasurableEquiv i) volume volume := by
  exact ((PiLp.volume_preserving_ofLp (Fin 3)).prod
    (PiLp.volume_preserving_ofLp ({j : Fin N // j ≠ i} × Fin 3))).trans
    ((volume_measurePreserving_sumPiEquivProdPi_symm _).trans
      ((volume_measurePreserving_piCongrLeft _ (insertionIndexEquiv i).symm).trans
        (PiLp.volume_preserving_toLp (Fin N × Fin 3))))

theorem measurePreserving_insertParticle {N : ℕ} (i : Fin N) :
    MeasurePreserving (fun z : Position × OtherConfiguration i =>
      insertParticle i z.1 z.2) volume volume := by
  simpa only [← insertionMeasurableEquiv_apply] using measurePreserving_insertion i

@[simp] theorem particlePosition_insertParticle {N : ℕ} (i : Fin N)
    (x : Position) (y : OtherConfiguration i) :
    particlePosition (insertParticle i x y) i = x := by
  ext a
  simp [particlePosition, insertParticle]

end LiebThirring
end
