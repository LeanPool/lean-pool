/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureOperator
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Pairings of the force pressure with fixed test functions

For a fixed function ψ ∈ L^{6/5}, the pairing f ↦ ∫ p_f ψ of the slice
force pressure of `lem:force-pressure` is a bounded linear functional on
spatial L². By the Riesz representation theorem it is the pairing with one
fixed L² field, which is what makes the force pressure measurable in time.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem forcePressure_integrable_mul {ψ : Vec3 → ℝ}
    (hψ : MemLp ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume) (v : RealVectorL2) :
    Integrable (fun x => forcePressureSlice v x * ψ x) volume := by
  have := holderTriple_six_ofReal_sixFifths
  exact (forcePressureSlice_memLp v).integrable_mul hψ

theorem forcePressure_pairing_bound {ψ : Vec3 → ℝ}
    (hψ : MemLp ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume) (v : RealVectorL2) :
    ‖∫ x, forcePressureSlice v x * ψ x‖ ≤
      ((gagliardoNirenbergSobolevConstant *
        eLpNorm ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume).toReal * 2) * ‖v‖ := by
  have := holderTriple_six_ofReal_sixFifths
  set C := gagliardoNirenbergSobolevConstant
  set A := eLpNorm ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume
  have hCtop : C ≠ ⊤ := gagliardoNirenbergSobolevConstant_ne_top
  have hAtop : A ≠ ⊤ := hψ.eLpNorm_lt_top.ne
  have hholder : eLpNorm (fun x => forcePressureSlice v x * ψ x) 1 volume ≤
      eLpNorm (forcePressureSlice v) 6 volume * A := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 6)
      (q := ENNReal.ofReal (6 / 5 : ℝ)) (r := 1)
      (fun a b : ℝ => a * b) 1 continuous_mul
      (forcePressureSlice_memLp v).aestronglyMeasurable hψ.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
  have hgrad : eLpNorm (forcePressureGradientL2 v) 2 volume ≤ ENNReal.ofReal (2 * ‖v‖) := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (forcePressureGradientL2_norm_le v)
  have hmain : ‖∫ x, forcePressureSlice v x * ψ x‖ₑ ≤
      (C * A) * ENNReal.ofReal (2 * ‖v‖) := by
    calc
      ‖∫ x, forcePressureSlice v x * ψ x‖ₑ ≤
          ∫⁻ x, ‖forcePressureSlice v x * ψ x‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => forcePressureSlice v x * ψ x) 1 volume :=
          (eLpNorm_one_eq_lintegral_enorm
            (forcePressure_integrable_mul hψ v).aestronglyMeasurable).symm
      _ ≤ eLpNorm (forcePressureSlice v) 6 volume * A := hholder
      _ ≤ (C * eLpNorm (forcePressureGradientL2 v) 2 volume) * A := by
          gcongr
          exact forcePressureSlice_eLpNorm_le v
      _ ≤ (C * ENNReal.ofReal (2 * ‖v‖)) * A := by gcongr
      _ = (C * A) * ENNReal.ofReal (2 * ‖v‖) := by ring
  have hfin : (C * A) * ENNReal.ofReal (2 * ‖v‖) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hCtop hAtop) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfin hmain
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  calc
    ‖∫ x, forcePressureSlice v x * ψ x‖ ≤ (C * A).toReal * (2 * ‖v‖) := hreal
    _ = ((C * A).toReal * 2) * ‖v‖ := by ring

/-- The pairing of the slice force pressure with a fixed L^{6/5} function,
as a bounded linear functional on spatial L². -/
@[expose]
def forcePressurePairing (ψ : Vec3 → ℝ)
    (hψ : MemLp ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    StrongDual ℝ RealVectorL2 :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x, forcePressureSlice v x * ψ x
      map_add' := by
        intro v w
        have h := forcePressureSlice_linearCombination_ae 1 1 v w
        simp only [one_smul, one_mul] at h
        rw [← integral_add (forcePressure_integrable_mul hψ v)
          (forcePressure_integrable_mul hψ w)]
        apply integral_congr_ae
        filter_upwards [h] with x hx
        rw [hx]
        ring
      map_smul' := by
        intro c v
        have h := forcePressureSlice_linearCombination_ae c 0 v v
        simp only [zero_smul, add_zero, zero_mul] at h
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [h] with x hx
        rw [hx]
        ring }
    ((gagliardoNirenbergSobolevConstant *
      eLpNorm ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume).toReal * 2)
    (forcePressure_pairing_bound hψ)

/-- The Riesz representative of the pairing functional of the slice force
pressure. -/
@[expose]
def forcePressurePairingField (ψ : Vec3 → ℝ)
    (hψ : MemLp ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume) : RealVectorL2 :=
  (InnerProductSpace.toDual ℝ RealVectorL2).symm (forcePressurePairing ψ hψ)

/-- The pairing of the slice force pressure with a fixed L^{6/5} function
is the L² pairing of the input field with the Riesz representative. -/
theorem integral_forcePressureSlice_mul_eq (ψ : Vec3 → ℝ)
    (hψ : MemLp ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume) (v : RealVectorL2) :
    ∫ x, forcePressureSlice v x * ψ x =
      ∫ x : Vec3, ∑ i : Fin 3,
        realVectorL2Representative (forcePressurePairingField ψ hψ) x i *
          realVectorL2Representative v x i := by
  rw [← inner_eq_integral_realVectorL2Representative, forcePressurePairingField,
    InnerProductSpace.toDual_symm_apply]
  rfl

end CKN.Leray
