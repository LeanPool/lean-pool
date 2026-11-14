/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.State

/-!
# Coordinate norms and singled-out spin encoding

The configuration norm is the sum of particle squared norms (coordinate norms).

The amplitude norm is the sum of squared scalar spin amplitudes (coordinate norms).
-/

public section

open MeasureTheory WithLp

namespace LiebThirring

/-- Spins of all particles other than the selected particle. -/
abbrev OtherSpinLabels {N : ℕ} (i : Fin N) (q : ℕ) :=
  {j : Fin N // j ≠ i} → Fin q

/-- Insert the selected spin into a configuration of the remaining spins. -/
@[expose] def insertSpin {N q : ℕ} (i : Fin N) (s : Fin q)
    (t : OtherSpinLabels i q) : SpinLabels N q :=
  fun j => if h : j = i then s else t ⟨j, h⟩

@[simp] theorem insertSpin_self {N q : ℕ} (i : Fin N) (s : Fin q)
    (t : OtherSpinLabels i q) : insertSpin i s t i = s := by
  simp [insertSpin]

@[simp] theorem insertSpin_other {N q : ℕ} (i : Fin N) (s : Fin q)
    (t : OtherSpinLabels i q) (j : {j : Fin N // j ≠ i}) :
    insertSpin i s t j.val = t j := by
  simp only [insertSpin, dite_eq_right j.property]

/-- Split a spin assignment into the selected spin and the remaining spins. -/
@[expose] def spinInsertionEquiv {N q : ℕ} (i : Fin N) :
    (Fin q × OtherSpinLabels i q) ≃ SpinLabels N q where
  toFun z := insertSpin i z.1 z.2
  invFun t := (t i, fun j => t j.val)
  left_inv z := by
    apply Prod.ext
    · exact insertSpin_self i z.1 z.2
    · funext j
      exact insertSpin_other i z.1 z.2 j
  right_inv t := by
    funext j
    dsimp [insertSpin]
    split
    · rename_i h
      exact congrArg t h.symm
    · rfl

/-- Spin regrouping as a complex linear isometry, before spatial currying. -/
@[expose] noncomputable def spinCurryingLinearIsometryEquiv {N q : ℕ} (i : Fin N) :
    SpinAmplitudes N q ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (spinInsertionEquiv i).symm).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sigmaEquivProd (Fin q) (OtherSpinLabels i q)).symm).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : Fin q) (_ : OtherSpinLabels i q) => ℂ)))

@[simp] theorem spinCurryingLinearIsometryEquiv_apply {N q : ℕ} (i : Fin N)
    (u : SpinAmplitudes N q) (s : Fin q) (t : OtherSpinLabels i q) :
    spinCurryingLinearIsometryEquiv i u s t = u (insertSpin i s t) := rfl

end LiebThirring

end
