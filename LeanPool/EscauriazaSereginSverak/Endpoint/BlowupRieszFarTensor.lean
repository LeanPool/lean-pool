/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszLinear
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTensorConvergence

/-!
# Blowup Riesz Far Tensor

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A whole-space space-time `L³` velocity has an `L^(3/2)` quadratic
tensor, the input to the canonical Riesz pressure. -/
theorem blowup_velocity_tensor_memLp
    (v : Vec3 × ℝ → Vec3) (hv : MemLp v 3 volume) :
    ∀ i j : Fin 3,
      MemLp (fun z : Vec3 × ℝ => v z i * v z j)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthree : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
  have : (3 : ℝ≥0∞).HolderTriple 3 (3 / 2 : ℝ≥0∞) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [hcoeff, hthree] using h.ennrealOfReal
  have hcomp (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => v z i) 3 volume :=
    hv.of_le ((continuous_apply i).comp_aestronglyMeasurable
      hv.aestronglyMeasurable)
      (Eventually.of_forall fun z => norm_le_pi_norm (v z) i)
  intro i j
  rw [hcoeff]
  exact (hcomp i).mul (hcomp j)

/-- The tensor of an `L³` velocity, truncated to an exterior spatial region
and a time interval, belongs to whole-space space-time `L^(3/2)`. -/
theorem blowup_exterior_velocity_tensor_memLp
    (v : Vec3 × ℝ → Vec3) (L a b : ℝ)
    (hv : MemLp v 3
      ((volume : Measure (Vec3 × ℝ)).restrict
        ((CKN.euclideanBall 0 L)ᶜ ×ˢ Ioo a b))) :
    ∀ i j : Fin 3,
      MemLp (((CKN.euclideanBall 0 L)ᶜ ×ˢ Ioo a b).indicator
        (fun z : Vec3 × ℝ => v z i * v z j))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  let C : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ Ioo a b
  have hC : MeasurableSet C :=
    (CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod measurableSet_Ioo
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthree : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
  have : (3 : ℝ≥0∞).HolderTriple 3 (3 / 2 : ℝ≥0∞) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [hcoeff, hthree] using h.ennrealOfReal
  have hcomp (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => v z i) 3
      (volume.restrict C) :=
    hv.of_le ((continuous_apply i).comp_aestronglyMeasurable
      hv.aestronglyMeasurable)
      (Eventually.of_forall fun z => norm_le_pi_norm (v z) i)
  intro i j
  rw [hcoeff]
  change MemLp (C.indicator (fun z => v z i * v z j))
    (3 / 2 : ℝ≥0∞) volume
  rw [memLp_indicator_iff_restrict hC]
  exact (hcomp i).mul (hcomp j)

/-- The exterior tensor slice has `L^(3/2)` norm at most the square of the
whole-space `L³` velocity-slice bound. -/
theorem blowup_exterior_velocity_tensor_slice_bound
    (v : Vec3 × ℝ → Vec3) (L a b : ℝ)
    (N : ℝ≥0∞) (hN : N < ⊤)
    (hv : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      MemLp (fun x : Vec3 => v (x,t)) 3 volume ∧
      eLpNorm (fun x : Vec3 => v (x,t)) 3 volume ≤ N) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      ∀ i j : Fin 3,
        lpNorm (fun x : Vec3 =>
          (((CKN.euclideanBall 0 L)ᶜ ×ˢ Ioo a b).indicator
            (fun z : Vec3 × ℝ => v z i * v z j)) (x,t))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ N.toReal ^ 2 := by
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hC : MeasurableSet (CKN.euclideanBall (0 : Vec3) L)ᶜ :=
    (CKN.isOpen_euclideanBall 0 L).measurableSet.compl
  filter_upwards [hv, self_mem_ae_restrict measurableSet_Ioo] with t ht htJ i j
  let w : Vec3 → Vec3 := fun x => v (x,t)
  have hi : AEStronglyMeasurable (fun x : Vec3 => w x i) volume :=
    (continuous_apply i).comp_aestronglyMeasurable ht.1.aestronglyMeasurable
  have hj : AEStronglyMeasurable (fun x : Vec3 => w x j) volume :=
    (continuous_apply j).comp_aestronglyMeasurable ht.1.aestronglyMeasurable
  have hmul : eLpNorm (fun x : Vec3 => w x i * w x j)
      (3 / 2 : ℝ≥0∞) volume ≤
      eLpNorm (fun x : Vec3 => w x i) 3 volume *
        eLpNorm (fun x : Vec3 => w x j) 3 volume :=
    by
      simpa only [hcoeff, show ENNReal.ofReal (3 : ℝ) =
        (3 : ℝ≥0∞) by norm_num] using
          (CKN.Foundation.Measure.eLpNorm_mul_le_three_three hi hj)
  have hcompI : eLpNorm (fun x : Vec3 => w x i) 3 volume ≤ N :=
    (blowup_component_eLpNorm_le volume 3 w
      ht.1.aestronglyMeasurable i).trans ht.2
  have hcompJ : eLpNorm (fun x : Vec3 => w x j) 3 volume ≤ N :=
    (blowup_component_eLpNorm_le volume 3 w
      ht.1.aestronglyMeasurable j).trans ht.2
  have hslice : (fun x : Vec3 =>
      (((CKN.euclideanBall 0 L)ᶜ ×ˢ Ioo a b).indicator
        (fun z : Vec3 × ℝ => v z i * v z j)) (x,t)) =
      (CKN.euclideanBall 0 L)ᶜ.indicator (fun x : Vec3 => w x i * w x j) := by
    funext x
    by_cases hx : x ∈ (CKN.euclideanBall 0 L)ᶜ
    · simp [Set.indicator_of_mem, hx, htJ, w]
    · simp [Set.indicator_of_notMem, hx, w]
  rw [hslice, hcoeff]
  have hbound : eLpNorm
      ((CKN.euclideanBall 0 L)ᶜ.indicator (fun x : Vec3 => w x i * w x j))
      (3 / 2 : ℝ≥0∞) volume ≤ N * N := by
    calc
      _ ≤ eLpNorm (fun x : Vec3 => w x i * w x j)
          (3 / 2 : ℝ≥0∞) volume :=
        eLpNorm_indicator_le _ hC
      _ ≤ eLpNorm (fun x : Vec3 => w x i) 3 volume *
          eLpNorm (fun x : Vec3 => w x j) 3 volume := hmul
      _ ≤ N * N := by gcongr
  have hNmul : N * N < ⊤ := ENNReal.mul_lt_top hN hN
  change (eLpNorm _ (3 / 2 : ℝ≥0∞) volume).toReal ≤ N.toReal ^ 2
  calc
    (eLpNorm _ (3 / 2 : ℝ≥0∞) volume).toReal ≤ (N * N).toReal :=
      ENNReal.toReal_mono hNmul.ne hbound
    _ = N.toReal ^ 2 := by rw [ENNReal.toReal_mul]; ring

end ESS
