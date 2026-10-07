/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTrace
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial

/-!
# Cutoff data for Gaussian unique continuation

The first and second weak derivative fields of a cut off vector field are
written component first and spatial derivative indices afterward.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The product of spatial, final-time, and initial-time cutoffs. -/
@[expose] def ucCutoffScalar (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ := θ z.1 * η z.2 * χ z.2

/-- The cut off vector field of `lem:uc-gaussian`. -/
@[expose] def ucCutoffField (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (v : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => ucCutoffScalar θ η χ z • v z

/-- The first spatial derivative data of a cut off field. -/
@[expose] def ucCutoffDw (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (v : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i j => ucCutoffScalar θ η χ z * Dw z i j +
    v z i * spatialPartial (ucCutoffScalar θ η χ) j z

/-- The second spatial derivative data of a cut off field. -/
@[expose] def ucCutoffD2 (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (v : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (z : ParabolicPoint) : Fin 3 → Fin 3 → Vec3 :=
  fun i j k => ucCutoffScalar θ η χ z * D2w z i j k +
    spatialPartial (ucCutoffScalar θ η χ) k z * Dw z i j +
    spatialPartial (ucCutoffScalar θ η χ) j z * Dw z i k +
    v z i * spatialSecondPartial (ucCutoffScalar θ η χ) j k z

/-- The time derivative data of a cut off field. -/
@[expose] def ucCutoffDt (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (v : ParabolicPoint → Vec3) (Dtw : ParabolicPoint → Vec3)
    (z : ParabolicPoint) : Vec3 :=
  fun i => ucCutoffScalar θ η χ z * Dtw z i +
    v z i * timePartial (ucCutoffScalar θ η χ) z

/-- The heat operator acting on the cut off field, expressed through the
specified weak derivative data. -/
@[expose] def ucCutoffHeat (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (v : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  fun i => ucCutoffScalar θ η χ z * ucWeakHeatVector D2w Dtw z i +
    (timePartial (ucCutoffScalar θ η χ) z +
      ∑ j : Fin 3, spatialSecondPartial (ucCutoffScalar θ η χ) j j z) * v z i +
    2 * ∑ j : Fin 3,
      spatialPartial (ucCutoffScalar θ η χ) j z * Dw z i j

/-- The product expansion agrees componentwise with the weak heat operator. -/
theorem ucCutoffHeat_eq_weakHeat
    (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (v : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    ucCutoffHeat θ η χ v Dw D2w Dtw z =
      ucWeakHeatVector (ucCutoffD2 θ η χ v Dw D2w)
        (ucCutoffDt θ η χ v Dtw) z := by
  funext i
  simp only [ucCutoffHeat, ucWeakHeatVector, ucCutoffD2, ucCutoffDt]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end ESS
