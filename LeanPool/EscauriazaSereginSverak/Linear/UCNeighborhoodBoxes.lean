/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCFlatnessFromBoxes

/-!
# Neighborhood geometry for Gaussian boxes

Small local cylinders and every geometric covering box remain inside a
fixed cylinder around their common spatial center.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Local cylinders, geometric slabs, and nearby Gaussian boxes stay inside
a fixed positive-time neighborhood. -/
theorem uc_neighborhood_boxes_subset
    (x : Vec3) (L S r : ℝ) (hL : 0 < L) (hS : 0 < S)
    (hr : 0 < r) (hrL : r < L / 4)
    (hrS : r < Real.sqrt (S / 2)) (n : ℕ) :
    let U := spaceTimeSet (vec3Ball x L) (Ioo 0 S)
    spaceTimeSet (vec3Ball x r) (Ioo 0 (r ^ 2)) ⊆ U ∧
    spaceTimeSet (vec3Ball x r)
      (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
        (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) ⊆ U ∧
    ∀ c ∈ vec3Ball x (2 * r),
      spaceTimeSet
        (vec3Ball c (Real.sqrt
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) ⊆ U := by
  dsimp
  let t : ℝ := (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hr2S : 2 * r ^ 2 < S := by
    have hS2 : 0 ≤ S / 2 := by linarith only [hS]
    have hsq := (sq_lt_sq₀ hr.le (Real.sqrt_nonneg _)).mpr hrS
    rw [Real.sq_sqrt hS2] at hsq
    linarith only [hsq]
  have htbound : 2 * t ≤ 2 * r ^ 2 := by
    have hp : (3 / 4 : ℝ) ^ n ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg r)
    dsimp [t]
    nlinarith only [hmul, sq_nonneg r]
  have hroot : Real.sqrt (2 * t) < 2 * r := by
    apply (Real.sqrt_lt' (by linarith only [hr])).mpr
    have hbound : 2 * t < (2 * r) ^ 2 := by
      nlinarith only [htbound, sq_pos_of_pos hr]
    exact hbound
  have hrL' : r < L := by linarith only [hrL, hL]
  have h4rL : 4 * r < L := by linarith only [hrL]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ⟨(vec3Ball_mono hrL'.le) hz.1,
      ⟨hz.2.1, hz.2.2.trans (by linarith only [hr2S, sq_nonneg r])⟩⟩
  · intro z hz
    exact ⟨(vec3Ball_mono hrL'.le) hz.1,
      ⟨ht.trans hz.2.1, hz.2.2.trans_le htbound |>.trans hr2S⟩⟩
  · intro c hc z hz
    have hcx : vec3EuclideanNorm (c - x) < 2 * r :=
      (mem_vec3Ball).mp hc
    have hzc : vec3EuclideanNorm (z.1 - c) < Real.sqrt (2 * t) :=
      (mem_vec3Ball).mp hz.1
    have htri := vec3EuclideanNorm_add_le (z.1 - c) (c - x)
    have heq : z.1 - c + (c - x) = z.1 - x := by abel
    rw [heq] at htri
    constructor
    · apply (mem_vec3Ball).mpr
      linarith only [htri, hzc, hcx, hroot, h4rL]
    · exact ⟨ht.trans hz.2.1, hz.2.2.trans_le htbound |>.trans hr2S⟩

/-- An integrable neighborhood supplies the local integrability hypotheses
for Gaussian box propagation. -/
theorem uc_gaussian_neighborhood_flatness
    (F : Finset Vec3)
    (hF : ∀ y ∈ closure (vec3Ball 0 1),
      ∃ c ∈ F, y ∈ vec3Ball c (1 / 2))
    (hFpos : 0 < F.card)
    (x : Vec3) (R T L S δ A b : ℝ)
    (hL : 0 < L) (hS : 0 < S)
    (hδ : 0 < δ) (hδL : δ ≤ L / 4)
    (hδS : δ ≤ Real.sqrt (S / 2))
    (hA : 0 ≤ A) (hb : 0 < b)
    (w : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x L) (Ioo 0 S)) volume)
    (hbox : ∀ r : ℝ, 0 < r → r < δ → ∀ n : ℕ,
      ∀ c ∈ vec3Ball x (2 * r),
      (∫ z in spaceTimeSet
        (vec3Ball c (Real.sqrt
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))),
        vec3EuclideanNorm (w z) ^ 2) ≤
          A * Real.exp (-(b /
            ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) :
    UCIntegralFlatness x R T w := by
  apply uc_box_decay_implies_integral_flatness F hF hFpos x R T δ A b
    hδ hA hb w
  · intro r hr hrδ
    have hgeom := uc_neighborhood_boxes_subset x L S r hL hS hr
      (hrδ.trans_le hδL) (hrδ.trans_le hδS) 0
    exact hInt.mono_set hgeom.1
  · intro r hr hrδ n
    have hgeom := uc_neighborhood_boxes_subset x L S r hL hS hr
      (hrδ.trans_le hδL) (hrδ.trans_le hδS) n
    exact hInt.mono_set hgeom.2.1
  · intro r hr hrδ n c hc
    have hgeom := uc_neighborhood_boxes_subset x L S r hL hS hr
      (hrδ.trans_le hδL) (hrδ.trans_le hδS) n
    exact hInt.mono_set (hgeom.2.2 c hc)
  · exact hbox

end ESS
