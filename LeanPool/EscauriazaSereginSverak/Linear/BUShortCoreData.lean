/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCoreRegion

/-!
# Weak data on the cutoff plateau

On the open plateau, the cutoff field and its specified weak derivatives
agree with the shifted source field.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The complete cutoff weak data agree with the shifted field on the
open plateau of `lem:bu-small-time`. -/
theorem bu_short_cutoff_data_eq_on_core
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    {z : ParabolicPoint}
    (hz : parabolicHomeomorph z ∈ buShortCoreRegion scale R ε) :
    buCutField (buShortFullCutoff scale R hR ε) v z = v z ∧
    buCutDw (buShortFullCutoff scale R hR ε) v Dv z = Dv z ∧
    buCutD2 (buShortFullCutoff scale R hR ε) v Dv D2v z = D2v z ∧
    buCutDt (buShortFullCutoff scale R hR ε) v Dtv z = Dtv z := by
  let κ := buShortFullCutoff scale R hR ε
  have hκ : buCutScalar κ z = 1 :=
    buShortFullCutoff_eq_one_on_core scale R ε hscale hscale1 hR hε hz
  dsimp [κ] at hκ
  obtain ⟨hsp, hsp2, ht⟩ :=
    buShortFullCutoff_derivatives_zero_on_core scale R ε
      hscale hscale1 hR hε hz
  constructor
  · funext i
    simp only [buCutField, Pi.smul_apply, smul_eq_mul, hκ, one_mul]
  constructor
  · funext i j
    simp only [buCutDw, hκ, hsp j, mul_zero, add_zero, one_mul]
  constructor
  · funext i j k
    simp only [buCutD2, hκ, hsp j, hsp k, hsp2 j k,
      mul_zero, add_zero, one_mul, zero_mul]
  · funext i
    simp only [buCutDt, hκ, ht, mul_zero, add_zero, one_mul]

end ESS
