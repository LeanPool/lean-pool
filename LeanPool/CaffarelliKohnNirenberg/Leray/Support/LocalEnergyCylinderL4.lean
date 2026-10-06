/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyL4
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! The next result is the time integration of the slice estimate. Its time-energy hypothesis
is exactly the sliced form of the space-time L² energy bound and is derived from that bound in
the E1 wrapper. -/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CKN

private theorem parabolic_memLp_of_product_restrict
    {E : Type} [TopologicalSpace E] [ContinuousENorm E]
    {C : Set Vec3} {J : Set ℝ} (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (f : ParabolicPoint → E)
    (hf : MemLp (fun z : Vec3 × ℝ => f (parabolicHomeomorph.symm z)) 4
      ((volume : Measure (Vec3 × ℝ)).restrict (C ×ˢ J))) :
    MemLp f 4 (volume.restrict (spaceTimeSet C J)) := by
  have hprodMeas : MeasurableSet (C ×ˢ J) := hC.prod hJ
  have hpre : parabolicHomeomorph ⁻¹' (C ×ˢ J) = spaceTimeSet C J := by
    ext z
    rfl
  have hmp := parabolicHomeomorph_measurePreserving.restrict_preimage hprodMeas
  rw [hpre] at hmp
  have h := hf.comp_measurePreserving hmp
  change MemLp (fun z : ParabolicPoint =>
    f (parabolicHomeomorph.symm (parabolicHomeomorph z))) 4
    (volume.restrict (spaceTimeSet C J)) at h
  have hEqFun : (fun z : ParabolicPoint =>
      f (parabolicHomeomorph.symm (parabolicHomeomorph z))) = f := by
    funext z
    rfl
  rw [hEqFun] at h
  exact h

private theorem h1_slice_representation_of_product_data
    {V U B : Set Vec3} {J : Set ℝ}
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hVB : V ⊆ B)
    (u : Vec3 × ℝ → Vec3) (Du : Vec3 × ℝ → Fin 3 → Vec3)
    (i : Fin 3)
    (hU : AEStronglyMeasurable u
      ((volume.restrict U).prod (volume.restrict J)))
    (hDu : AEStronglyMeasurable Du
      ((volume.restrict U).prod (volume.restrict J)))
    (hUsq : Integrable (fun z => (‖u z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict U).prod (volume.restrict J)))
    (hDusq : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict U).prod (volume.restrict J)))
    (hgrad : ∀ᵐ t ∂(volume.restrict J), ∀ j : Fin 3,
      HasWeakGradientOn B (fun x => u (x, t) j) (fun x => Du (x, t) j)) :
    ∀ᵐ t ∂(volume.restrict J), ∃ v : H1Function V,
      (fun x => u (x, t) i) =ᵐ[volume.restrict V] v.toFun ∧
      (fun x => Du (x, t) i) =ᵐ[volume.restrict V] v.grad := by
  filter_upwards [hU.prodMk_right, hDu.prodMk_right,
    hUsq.prod_left_ae, hDusq.prod_left_ae, hgrad] with t hUmeas hDumeas hUsq_t hDusq_t hgrad_t
  have hUslice : MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict U) :=
    (memLp_two_iff_integrable_sq_norm hUmeas).2 hUsq_t
  have hDuslice : MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict U) :=
    (memLp_two_iff_integrable_sq_norm hDumeas).2 hDusq_t
  have hUsliceV : MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict V) :=
    hUslice.mono_measure (Measure.restrict_mono_set volume hVU)
  have hDusliceV : MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict V) :=
    hDuslice.mono_measure (Measure.restrict_mono_set volume hVU)
  refine ⟨⟨fun x => u (x, t) i, fun x => Du (x, t) i, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa [MemL2On, MemLpOn, volumeOn] using (memLp_pi_iff.mp hUsliceV) i
  · intro j
    simpa [GradMemLpOn, MemL2On, MemLpOn, volumeOn] using
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDusliceV) i)) j
  · exact (hgrad_t i).restrict hVopen hVB
  · rfl
  · rfl

private theorem componentEnergy_finite_on_product_ball
    {U B : Set Vec3} {J : Set ℝ} (hUB : U ⊆ B)
    (u : Vec3 × ℝ → Vec3) (Du : Vec3 × ℝ → Fin 3 → Vec3) (i : Fin 3)
    (μx : Measure Vec3) (μt : Measure ℝ)
    (hmeasure : μx.prod μt =
      (volume : Measure (Vec3 × ℝ)).restrict (U ×ˢ J))
    (henergy : (∫⁻ z in B ×ˢ J,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure (Vec3 × ℝ))) < ⊤) :
    (∫⁻ z, ‖u z i‖ₑ ^ (2 : ℝ) + ‖Du z i‖ₑ ^ (2 : ℝ)
      ∂(μx.prod μt)) < ⊤ := by
  have hfull : (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)
      ∂(μx.prod μt)) < ⊤ := by
    have hset : (∫⁻ z in U ×ˢ J,
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure (Vec3 × ℝ))) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono_set (Set.prod_mono hUB le_rfl)) henergy
    rw [hmeasure]
    exact hset
  refine lt_of_le_of_lt ?_ hfull
  apply lintegral_mono
  intro z
  apply add_le_add
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_le_pi_norm (u z) i)) (by norm_num)
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_le_pi_norm (Du z) i)) (by norm_num)

private theorem ennreal_add_sq_bound (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℝ) ≤ 4 * (a ^ (2 : ℝ) + b ^ (2 : ℝ)) := by
  have hadd : a + b ≤ 2 * max a b := by
    calc
      a + b ≤ max a b + max a b := add_le_add (le_max_left a b) (le_max_right a b)
      _ = 2 * max a b := by simp [two_mul]
  have hpow := ENNReal.rpow_le_rpow hadd (by norm_num : 0 ≤ (2 : ℝ))
  have hmax : (max a b) ^ (2 : ℝ) ≤ a ^ (2 : ℝ) + b ^ (2 : ℝ) := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab]
      exact le_add_left le_rfl
    · rw [max_eq_left hba]
      exact le_add_right le_rfl
  calc
    (a + b) ^ (2 : ℝ) ≤ (2 * max a b) ^ (2 : ℝ) := hpow
    _ = 4 * (max a b) ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    _ ≤ _ := by gcongr

private theorem ennreal_interp_integrand_bound (A c a b d : ℝ≥0∞) :
    A ^ (2 : ℝ) * (c * (b + a * d)) ^ (2 : ℝ) ≤
      (4 * A ^ (2 : ℝ) * c ^ (2 : ℝ) * max 1 (a ^ (2 : ℝ))) *
        (b ^ (2 : ℝ) + d ^ (2 : ℝ)) := by
  have hadd := ennreal_add_sq_bound b (a * d)
  have hscale : (a * d) ^ (2 : ℝ) = a ^ (2 : ℝ) * d ^ (2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg a d (by norm_num)
  calc
    A ^ (2 : ℝ) * (c * (b + a * d)) ^ (2 : ℝ) =
        A ^ (2 : ℝ) * c ^ (2 : ℝ) * (b + a * d) ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg c (b + a * d) (by norm_num : 0 ≤ (2 : ℝ))]
          ac_rfl
    _ ≤ A ^ (2 : ℝ) * c ^ (2 : ℝ) *
          (4 * (b ^ (2 : ℝ) + (a * d) ^ (2 : ℝ))) := by gcongr
    _ ≤ A ^ (2 : ℝ) * c ^ (2 : ℝ) *
          (4 * (max 1 (a ^ (2 : ℝ)) * (b ^ (2 : ℝ) + d ^ (2 : ℝ)))) := by
          gcongr
          rw [hscale]
          have ha : a ^ (2 : ℝ) ≤ max 1 (a ^ (2 : ℝ)) := le_max_right _ _
          have hone : 1 ≤ max 1 (a ^ (2 : ℝ)) := le_max_left _ _
          calc
            b ^ (2 : ℝ) + a ^ (2 : ℝ) * d ^ (2 : ℝ) ≤
                max 1 (a ^ (2 : ℝ)) * b ^ (2 : ℝ) +
                  max 1 (a ^ (2 : ℝ)) * d ^ (2 : ℝ) := by
              exact add_le_add (le_mul_of_one_le_left' hone)
                (mul_le_mul_of_nonneg_right ha bot_le)
            _ = max 1 (a ^ (2 : ℝ)) * (b ^ (2 : ℝ) + d ^ (2 : ℝ)) := by ring
    _ = _ := by ring

private theorem eLpNorm_four_pow_eq_lintegral {α E : Type} [MeasurableSpace α]
    [TopologicalSpace E] [ContinuousENorm E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 4 μ ^ (4 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_mul]
  norm_num

private theorem eLpNorm_two_pow_eq_lintegral {α E : Type} [MeasurableSpace α]
    [TopologicalSpace E] [ContinuousENorm E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_mul]
  norm_num

/-- The cube of the `L³` seminorm is the integral of the cubed extended norm. -/
theorem eLpNorm_three_pow_eq_lintegral {α E : Type} [MeasurableSpace α]
    [TopologicalSpace E] [ContinuousENorm E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 3 μ ^ (3 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (3 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_mul]
  norm_num

/-- Tonelli identifies the time integral of the squared spatial L² norm with the
space-time squared norm. -/
theorem scalarTimeL2Energy_eq {E : Type} [TopologicalSpace E] [ContinuousENorm E]
    {J : Set ℝ} {x₀ : Vec3} {r : ℝ}
    (f : Vec3 × ℝ → E)
    (hf : AEStronglyMeasurable f
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J))) :
    (∫⁻ t, eLpNorm (fun x : Vec3 => f (x, t)) 2
      (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) ∂(volume.restrict J)) =
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) := by
  let μx := volume.restrict (euclideanBall x₀ r)
  let μt := volume.restrict J
  have hslice := hf.prodMk_right
  have hpow : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ) =
        ∫⁻ x, ‖f (x, t)‖ₑ ^ (2 : ℝ) ∂μx := by
    filter_upwards [hslice] with t ht
    exact eLpNorm_two_pow_eq_lintegral ht
  have hmeas : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ (2 : ℝ))
      (μx.prod μt) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf.enorm
  calc
    (∫⁻ t, eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ) ∂μt) =
        ∫⁻ t, ∫⁻ x, ‖f (x, t)‖ₑ ^ (2 : ℝ) ∂μx ∂μt :=
          lintegral_congr_ae hpow
    _ = ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(μx.prod μt) :=
          (lintegral_prod_symm _ hmeas).symm

/-- Almost every H¹ slice with a uniform L³ bound obeys the quantitative L⁴ interpolation
estimate used in `lem:lei-L4` of the Escauriaza–Seregin–Šverák manuscript. -/
theorem scalarSliceL4_bound_ae {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    (hr : 0 < r) (f : Vec3 × ℝ → ℝ) (g : Vec3 × ℝ → Vec3) {A : ℝ≥0∞}
    (hA : A < ⊤)
    (h3 : ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x : Vec3 => f (x, t)) 3 (volume.restrict (euclideanBall x₀ r)) ≤ A)
    (hSlice : ∀ᵐ t ∂(volume.restrict J), ∃ v : H1Function (euclideanBall x₀ r),
      (fun x => f (x, t)) =ᵐ[volume.restrict (euclideanBall x₀ r)] v.toFun ∧
      (fun x => g (x, t)) =ᵐ[volume.restrict (euclideanBall x₀ r)] v.grad) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x : Vec3 => f (x, t)) 4 (volume.restrict (euclideanBall x₀ r)) ∧
      eLpNorm (fun x : Vec3 => f (x, t)) 4 (volume.restrict (euclideanBall x₀ r)) ^ (4 : ℝ) ≤
        A ^ (2 : ℝ) *
          (ENNReal.ofReal sobolevPoincareFaithfulC5 *
            (eLpNorm (fun x : Vec3 => g (x, t)) 2 (volume.restrict (euclideanBall x₀ r)) +
              (ENNReal.ofReal r)⁻¹ *
                eLpNorm (fun x : Vec3 => f (x, t)) 2
                  (volume.restrict (euclideanBall x₀ r)))) ^ (2 : ℝ) := by
  filter_upwards [h3, hSlice] with t h3t ⟨v, hf, hg⟩
  have h3mem : MemLp (fun x : Vec3 => f (x, t)) 3
      (volume.restrict (euclideanBall x₀ r)) := by
    rw [memLp_iff]
    exact lt_of_le_of_lt h3t hA
  have h3v : MemLp v.toFun 3 (volume.restrict (euclideanBall x₀ r)) := by
    rw [memLp_iff]
    rw [← eLpNorm_congr_ae hf]
    exact (memLp_iff.mp h3mem)
  have hbound := scalarH1L4_bound hr v h3v
  have hfour : MemLp (fun x : Vec3 => f (x, t)) 4
      (volume.restrict (euclideanBall x₀ r)) := by
    rw [memLp_iff]
    rw [eLpNorm_congr_ae hf]
    exact hbound.1.eLpNorm_lt_top
  refine ⟨hfour, ?_⟩
  have hf4 : eLpNorm (fun x : Vec3 => f (x, t)) 4
      (volume.restrict (euclideanBall x₀ r)) = eLpNorm v.toFun 4
        (volume.restrict (euclideanBall x₀ r)) := eLpNorm_congr_ae hf
  have hf3 : eLpNorm (fun x : Vec3 => f (x, t)) 3
      (volume.restrict (euclideanBall x₀ r)) = eLpNorm v.toFun 3
        (volume.restrict (euclideanBall x₀ r)) := eLpNorm_congr_ae hf
  have hg2 : eLpNorm (fun x : Vec3 => g (x, t)) 2
      (volume.restrict (euclideanBall x₀ r)) = eLpNorm v.grad 2
        (volume.restrict (euclideanBall x₀ r)) := eLpNorm_congr_ae hg
  have hf2 : eLpNorm (fun x : Vec3 => f (x, t)) 2
      (volume.restrict (euclideanBall x₀ r)) = eLpNorm v.toFun 2
        (volume.restrict (euclideanBall x₀ r)) := eLpNorm_congr_ae hf
  calc
    eLpNorm (fun x : Vec3 => f (x, t)) 4
        (volume.restrict (euclideanBall x₀ r)) ^ (4 : ℝ) =
      eLpNorm v.toFun 4 (volume.restrict (euclideanBall x₀ r)) ^ (4 : ℝ) := by rw [hf4]
    _ ≤
      eLpNorm v.toFun 3 (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) *
        (ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (eLpNorm v.grad 2 (volume.restrict (euclideanBall x₀ r)) +
            (ENNReal.ofReal r)⁻¹ * eLpNorm v.toFun 2
              (volume.restrict (euclideanBall x₀ r)))) ^ (2 : ℝ) := hbound.2
    _ = eLpNorm (fun x : Vec3 => f (x, t)) 3
          (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) *
        (ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (eLpNorm (fun x : Vec3 => g (x, t)) 2 (volume.restrict (euclideanBall x₀ r)) +
            (ENNReal.ofReal r)⁻¹ * eLpNorm (fun x : Vec3 => f (x, t)) 2
              (volume.restrict (euclideanBall x₀ r)))) ^ (2 : ℝ) := by rw [← hf3, ← hg2, ← hf2]
    _ ≤ A ^ (2 : ℝ) *
        (ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (eLpNorm (fun x : Vec3 => g (x, t)) 2 (volume.restrict (euclideanBall x₀ r)) +
            (ENNReal.ofReal r)⁻¹ * eLpNorm (fun x : Vec3 => f (x, t)) 2
              (volume.restrict (euclideanBall x₀ r)))) ^ (2 : ℝ) := by
      gcongr



/-- A uniform spatial L³ bound and finite time-integrated L² energy imply the cylinder L⁴ bound. -/
theorem scalarCylinderL4_of_sliceBounds {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    (hr : 0 < r) (f : Vec3 × ℝ → ℝ) (g : Vec3 × ℝ → Vec3)
    (hf : AEStronglyMeasurable f
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)))
    (hA : essSup
      (fun t : ℝ => eLpNorm (fun x : Vec3 => f (x, t)) 3
        (volume.restrict (euclideanBall x₀ r))) (volume.restrict J) < ⊤)
    (henergy : (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => f (x, t)) 2 (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) +
        eLpNorm (fun x : Vec3 => g (x, t)) 2
          (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)) < ⊤)
    (hSlice : ∀ᵐ t ∂(volume.restrict J), ∃ v : H1Function (euclideanBall x₀ r),
      (fun x => f (x, t)) =ᵐ[volume.restrict (euclideanBall x₀ r)] v.toFun ∧
      (fun x => g (x, t)) =ᵐ[volume.restrict (euclideanBall x₀ r)] v.grad) :
    MemLp f 4 ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) := by
  let μx := volume.restrict (euclideanBall x₀ r)
  let μt := volume.restrict J
  let A := essSup (fun t : ℝ => eLpNorm (fun x : Vec3 => f (x, t)) 3 μx) μt
  let a := (ENNReal.ofReal r)⁻¹
  let c := ENNReal.ofReal sobolevPoincareFaithfulC5
  let K := 4 * A ^ (2 : ℝ) * c ^ (2 : ℝ) * max 1 (a ^ (2 : ℝ))
  have hA_top : A < ⊤ := by simpa [A, μx, μt] using hA
  have hAtime : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => f (x, t)) 3 μx ≤ A := by
    exact ENNReal.ae_le_essSup (fun t : ℝ => eLpNorm (fun x : Vec3 => f (x, t)) 3 μx)
  have hslice4 := scalarSliceL4_bound_ae (x₀ := x₀) hr f g hA_top hAtime hSlice
  have hK_top : K < ⊤ := by
    dsimp [K]
    have hA2 : A ^ (2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA_top.ne
    have hc : c < ⊤ := by simp [c]
    have hc2 : c ^ (2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hc.ne
    have ha : a < ⊤ := by
      dsimp [a]
      exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hr)
    have ha2 : a ^ (2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) ha.ne
    have hm : max 1 (a ^ (2 : ℝ)) < ⊤ := max_lt (by simp) ha2
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hA2) hc2) hm
  have htime : (∫⁻ t,
      eLpNorm (fun x : Vec3 => f (x, t)) 4 μx ^ (4 : ℝ) ∂μt) < ⊤ := by
    have hmono : ∀ᵐ t ∂μt,
        eLpNorm (fun x : Vec3 => f (x, t)) 4 μx ^ (4 : ℝ) ≤
          K * (eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ) +
            eLpNorm (fun x : Vec3 => g (x, t)) 2 μx ^ (2 : ℝ)) := by
      filter_upwards [hslice4] with t ht
      calc
        _ ≤ A ^ (2 : ℝ) * (c * (eLpNorm (fun x : Vec3 => g (x, t)) 2 μx +
            a * eLpNorm (fun x : Vec3 => f (x, t)) 2 μx)) ^ (2 : ℝ) := by simpa [a, c] using ht.2
        _ ≤ K * (eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ) +
            eLpNorm (fun x : Vec3 => g (x, t)) 2 μx ^ (2 : ℝ)) := by
              simpa [K, add_comm] using ennreal_interp_integrand_bound A c a
                (eLpNorm (fun x : Vec3 => g (x, t)) 2 μx)
                (eLpNorm (fun x : Vec3 => f (x, t)) 2 μx)
    have hle := lintegral_mono_ae hmono
    have hscale := lintegral_const_mul' (μ := μt) K
      (fun t => eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ) +
        eLpNorm (fun x : Vec3 => g (x, t)) 2 μx ^ (2 : ℝ)) hK_top.ne
    have henergy' : (∫⁻ t,
        eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ) +
          eLpNorm (fun x : Vec3 => g (x, t)) 2 μx ^ (2 : ℝ) ∂μt) < ⊤ := by
      simpa [μx, μt] using henergy
    rw [hscale] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top hK_top henergy')
  have hf4meas : AEMeasurable (fun z : ParabolicPoint => ‖f z‖ₑ ^ (4 : ℝ))
      (μx.prod μt) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf.enorm
  have hprodEq : (∫⁻ z, ‖f z‖ₑ ^ (4 : ℝ) ∂(μx.prod μt)) =
      ∫⁻ t, ∫⁻ x, ‖f (x, t)‖ₑ ^ (4 : ℝ) ∂μx ∂μt := by
    have hf4meas' : AEMeasurable (fun z : ParabolicPoint => ‖f z‖ₑ ^ (4 : ℝ))
        (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
          (euclideanBall x₀ r ×ˢ J)) := by
      rw [← Measure.prod_restrict]
      exact hf4meas
    rw [show μx.prod μt =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (euclideanBall x₀ r ×ˢ J) by
          simp [μx, μt, Measure.prod_restrict]]
    simpa [μx, μt] using setLIntegral_prod_symm
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
      (s := euclideanBall x₀ r) (t := J) (f := fun z : Vec3 × ℝ => ‖f z‖ₑ ^ (4 : ℝ)) hf4meas'
  have hinner_bound : ∀ᵐ t ∂μt,
      (∫⁻ x, ‖f (x, t)‖ₑ ^ (4 : ℝ) ∂μx) ≤
        eLpNorm (fun x : Vec3 => f (x, t)) 4 μx ^ (4 : ℝ) := by
    filter_upwards [hslice4] with t ht
    rw [eLpNorm_four_pow_eq_lintegral ht.1.aestronglyMeasurable]
  have hprod_top : (∫⁻ z, ‖f z‖ₑ ^ (4 : ℝ) ∂(μx.prod μt)) < ⊤ := by
    rw [hprodEq]
    have hle := lintegral_mono_ae hinner_bound
    exact lt_of_le_of_lt hle htime
  change MemLp f 4 (μx.prod μt)
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hprod_top.ne

/-- The cylinder estimate needs only the local space-time L² energy: Tonelli turns it into the
time-integrated slice energy used by `scalarCylinderL4_of_sliceBounds`. -/
theorem scalarCylinderL4_of_jointEnergy {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    (hr : 0 < r) (f : Vec3 × ℝ → ℝ) (g : Vec3 × ℝ → Vec3)
    (hf : AEStronglyMeasurable f
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)))
    (hg : AEStronglyMeasurable g
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)))
    (hA : essSup
      (fun t : ℝ => eLpNorm (fun x : Vec3 => f (x, t)) 3
        (volume.restrict (euclideanBall x₀ r))) (volume.restrict J) < ⊤)
    (henergy : (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) + ‖g z‖ₑ ^ (2 : ℝ)
      ∂((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J))) < ⊤)
    (hSlice : ∀ᵐ t ∂(volume.restrict J), ∃ v : H1Function (euclideanBall x₀ r),
      (fun x => f (x, t)) =ᵐ[volume.restrict (euclideanBall x₀ r)] v.toFun ∧
      (fun x => g (x, t)) =ᵐ[volume.restrict (euclideanBall x₀ r)] v.grad) :
    MemLp f 4 ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) := by
  have hf2meas : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ (2 : ℝ))
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf.enorm
  have hg2meas : AEMeasurable (fun z : Vec3 × ℝ => ‖g z‖ₑ ^ (2 : ℝ))
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hg.enorm
  have hsum_eq : (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) + ‖g z‖ₑ ^ (2 : ℝ)
      ∂((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J))) =
      (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J))) +
      (∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J))) := by
    rw [lintegral_add_left' hf2meas _]
  have henergyParts := ENNReal.add_lt_top.mp (hsum_eq ▸ henergy)
  have htimef := scalarTimeL2Energy_eq (J := J) (x₀ := x₀) (r := r) f hf
  have htimeg := scalarTimeL2Energy_eq (J := J) (x₀ := x₀) (r := r) g hg
  have htimefTop : (∫⁻ t, eLpNorm (fun x : Vec3 => f (x, t)) 2
      (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)
      ∂(volume.restrict J)) < ⊤ := by
    rw [htimef]
    exact henergyParts.1
  have htimegTop : (∫⁻ t, eLpNorm (fun x : Vec3 => g (x, t)) 2
      (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)
      ∂(volume.restrict J)) < ⊤ := by
    rw [htimeg]
    exact henergyParts.2
  let μx := volume.restrict (euclideanBall x₀ r)
  let μt := volume.restrict J
  have hf2timeMeas : AEMeasurable
      (fun t => eLpNorm (fun x : Vec3 => f (x, t)) 2 μx ^ (2 : ℝ)) μt := by
    rcases hf2meas.prod_swap.lintegral_prod_right' with ⟨m, hm, hmeq⟩
    refine ⟨m, hm, ?_⟩
    filter_upwards [hmeq, hf.prodMk_right] with t hmEq ht
    exact (eLpNorm_two_pow_eq_lintegral ht).trans hmEq
  have hg2timeMeas : AEMeasurable
      (fun t => eLpNorm (fun x : Vec3 => g (x, t)) 2 μx ^ (2 : ℝ)) μt := by
    rcases hg2meas.prod_swap.lintegral_prod_right' with ⟨m, hm, hmeq⟩
    refine ⟨m, hm, ?_⟩
    filter_upwards [hmeq, hg.prodMk_right] with t hmEq ht
    exact (eLpNorm_two_pow_eq_lintegral ht).trans hmEq
  have htime : (∫⁻ t, eLpNorm (fun x : Vec3 => f (x, t)) 2
      μx ^ (2 : ℝ) +
        eLpNorm (fun x : Vec3 => g (x, t)) 2
          μx ^ (2 : ℝ) ∂μt) < ⊤ := by
    rw [lintegral_add_left' hf2timeMeas _]
    exact ENNReal.add_lt_top.mpr ⟨htimefTop, htimegTop⟩
  change (∫⁻ t, eLpNorm (fun x : Vec3 => f (x, t)) 2
      (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) +
        eLpNorm (fun x : Vec3 => g (x, t)) 2
          (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)
          ∂(volume.restrict J)) < ⊤ at htime
  exact scalarCylinderL4_of_sliceBounds hr f g hf hA htime hSlice

/-! ### The E1 cylinder estimate -/

/-- Each velocity component is in space-time `L⁴` on a smaller ball cylinder under the
energy, `L∞ₜL³ₓ`, and slice-gradient hypotheses of `thm:ess-local` of the
Escauriaza–Seregin–Šverák manuscript. -/
theorem velocityComponent_memLp_four_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {i : Fin 3} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ j : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) j) (fun x => Du (x, t) j)) :
    MemLp (fun z : ParabolicPoint => u z i) 4
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0))) := by
  let J : Set ℝ := Ioo (-1) 0
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let μx : Measure Vec3 := volume.restrict (euclideanBall (0 : Vec3) r)
  let μt : Measure ℝ := volume.restrict J
  let μx₁ : Measure Vec3 := volume.restrict B
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  have hmeasureBase : μx₁.prod μt =
      (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  have hmeasureSmall : μx.prod μt =
      (volume : Measure (Vec3 × ℝ)).restrict
        (euclideanBall (0 : Vec3) r ×ˢ J) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  have hball : euclideanBall (0 : Vec3) r ⊆ B := by
    intro x hx
    rw [euclideanBall_eq_vec3Ball (x₀ := (0 : Vec3)) (r := r) hr] at hx
    exact mem_vec3Ball.mpr ((mem_vec3Ball.mp hx).trans_le hr1)
  have hbaseSetMeas : MeasurableSet (spaceTimeSet B J) := by
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod
      (measurableSet_Ioo)
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet B J = B ×ˢ J := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hbaseSetMeas
  rw [hpre] at hmp
  have hbaseU : AEStronglyMeasurable uP (μx₁.prod μt) := by
    rw [hmeasureBase]
    exact hu.comp_measurePreserving hmp
  have hbaseDu : AEStronglyMeasurable DuP (μx₁.prod μt) := by
    rw [hmeasureBase]
    exact hDu.comp_measurePreserving hmp
  have henergyTrans :
      (∫⁻ z, ‖uP z‖ₑ ^ (2 : ℝ) + ‖DuP z‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J))) =
      (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure ParabolicPoint).restrict (spaceTimeSet B J))) := by
    simpa [uP, DuP] using hmp.lintegral_comp_emb
      parabolicHomeomorph.symm.measurableEmbedding
      (fun z : ParabolicPoint => ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ))
  have henergyProduct : (∫⁻ z, ‖uP z‖ₑ ^ (2 : ℝ) + ‖DuP z‖ₑ ^ (2 : ℝ)
      ∂((volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J))) < ⊤ := by
    rw [henergyTrans]
    simpa [B, J, spaceTimeSet] using henergy
  have hsmallU : AEStronglyMeasurable uP (μx.prod μt) := by
    exact hbaseU.mono_measure
      (Measure.prod_mono (Measure.restrict_mono hball le_rfl) le_rfl)
  have hsmallDu : AEStronglyMeasurable DuP (μx.prod μt) := by
    exact hbaseDu.mono_measure
      (Measure.prod_mono (Measure.restrict_mono hball le_rfl) le_rfl)
  have henergyProductSet : (∫⁻ z in B ×ˢ J,
      ‖uP z‖ₑ ^ (2 : ℝ) + ‖DuP z‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := henergyProduct
  have hbaseU2int : (∫⁻ z in B ×ˢ J,
      ‖uP z‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    refine lt_of_le_of_lt ?_ henergyProductSet
    apply lintegral_mono
    intro z
    exact le_add_right le_rfl
  have hbaseDu2int : (∫⁻ z in B ×ˢ J,
      ‖DuP z‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    refine lt_of_le_of_lt ?_ henergyProductSet
    apply lintegral_mono
    intro z
    exact le_add_left le_rfl
  have hsmallU2int : (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂(μx.prod μt)) < ⊤ := by
    have hsub : euclideanBall (0 : Vec3) r ×ˢ J ⊆ B ×ˢ J :=
      Set.prod_mono hball le_rfl
    have hset : (∫⁻ z in euclideanBall (0 : Vec3) r ×ˢ J,
        ‖uP z‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ))) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono_set hsub) hbaseU2int
    rw [hmeasureSmall]
    exact hset
  have hsmallDu2int : (∫⁻ z, ‖Du z‖ₑ ^ (2 : ℝ) ∂(μx.prod μt)) < ⊤ := by
    have hsub : euclideanBall (0 : Vec3) r ×ˢ J ⊆ B ×ˢ J :=
      Set.prod_mono hball le_rfl
    have hset : (∫⁻ z in euclideanBall (0 : Vec3) r ×ˢ J,
        ‖DuP z‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ))) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono_set hsub) hbaseDu2int
    rw [hmeasureSmall]
    exact hset
  have hsmallU2 : MemLp uP 2 (μx.prod μt) := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) hsmallU]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hsmallU2int.ne
  have hsmallDu2 : MemLp DuP 2 (μx.prod μt) := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) hsmallDu]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hsmallDu2int.ne
  have hsmallUsq : Integrable (fun z => (‖uP z‖ : ℝ) ^ (2 : ℕ)) (μx.prod μt) :=
    (memLp_two_iff_integrable_sq_norm hsmallU).mp hsmallU2
  have hsmallDusq : Integrable (fun z => (‖DuP z‖ : ℝ) ^ (2 : ℕ)) (μx.prod μt) :=
    (memLp_two_iff_integrable_sq_norm hsmallDu).mp hsmallDu2
  have hL3P : essSup (fun t : ℝ => ∫⁻ x in B,
      ENNReal.ofReal (vec3EuclideanNorm (uP (x, t))) ^ (3 : ℝ)) μt < ⊤ := by
    simpa [uP, B, J, parabolicHomeomorph_symm_apply] using hL3
  have htimeL3 : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => uP (x, t) i) 3 μx ≤
        (essSup (fun s : ℝ => ∫⁻ x in B,
          ENNReal.ofReal (vec3EuclideanNorm (uP (x, s))) ^ (3 : ℝ)) μt) ^ (1 / 3 : ℝ) := by
    have hsup := ENNReal.ae_le_essSup (μ := μt)
      (fun s : ℝ => ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (uP (x, s))) ^ (3 : ℝ))
    filter_upwards [hsup, hsmallU.prodMk_right,
      hsmallUsq.prod_left_ae] with t hsup_t hsliceMeas hsliceSq
    have hcomponent (x : Vec3) : ‖uP (x, t) i‖ₑ ≤
        ENNReal.ofReal (vec3EuclideanNorm (uP (x, t))) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (abs_apply_le_vec3EuclideanNorm _ _)
    have hInt : (∫⁻ x in euclideanBall (0 : Vec3) r,
        ‖uP (x, t) i‖ₑ ^ (3 : ℝ)) ≤
        ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (uP (x, t))) ^ (3 : ℝ) := by
      calc
        _ ≤ ∫⁻ x in euclideanBall (0 : Vec3) r,
            ENNReal.ofReal (vec3EuclideanNorm (uP (x, t))) ^ (3 : ℝ) := by
              apply lintegral_mono
              intro x
              exact ENNReal.rpow_le_rpow (hcomponent x) (by norm_num)
        _ ≤ _ := lintegral_mono_set hball
    have hsliceAE : AEStronglyMeasurable (fun x : Vec3 => uP (x, t) i) μx := by
      have hvec : MemLp (fun x : Vec3 => uP (x, t)) 2 μx :=
        (memLp_two_iff_integrable_sq_norm hsliceMeas).2 hsliceSq
      exact ((memLp_pi_iff.mp hvec) i).aestronglyMeasurable
    have hformula := eLpNorm_three_pow_eq_lintegral
      (μ := μx) (f := fun x : Vec3 => uP (x, t) i) hsliceAE
    have hrootEq : eLpNorm (fun x : Vec3 => uP (x, t) i) 3 μx =
        (∫⁻ x in euclideanBall (0 : Vec3) r,
          ‖uP (x, t) i‖ₑ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
      calc
        _ = (eLpNorm (fun x : Vec3 => uP (x, t) i) 3 μx ^ (3 : ℝ)) ^
            (1 / 3 : ℝ) := by
              rw [← ENNReal.rpow_mul]
              norm_num
        _ = _ := congrArg (fun a : ℝ≥0∞ => a ^ (1 / 3 : ℝ)) hformula
    calc
      _ = (∫⁻ x in euclideanBall (0 : Vec3) r,
          ‖uP (x, t) i‖ₑ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := hrootEq
      _ ≤ (∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (uP (x, t))) ^ (3 : ℝ)) ^
          (1 / 3 : ℝ) := ENNReal.rpow_le_rpow hInt (by norm_num)
      _ ≤ _ := ENNReal.rpow_le_rpow hsup_t (by norm_num)
  have hSlice : ∀ᵐ t ∂μt, ∃ v : H1Function (euclideanBall (0 : Vec3) r),
      (fun x => uP (x, t) i) =ᵐ[μx] v.toFun ∧
      (fun x => DuP (x, t) i) =ᵐ[μx] v.grad := by
    have hgradProduct : ∀ᵐ t ∂μt, ∀ j : Fin 3,
        HasWeakGradientOn B (fun x => uP (x, t) j) (fun x => DuP (x, t) j) := by
      filter_upwards [hgrad] with t hgrad_t
      intro j
      simpa [uP, DuP, parabolicHomeomorph_symm_apply] using hgrad_t j
    have hSlice0 := h1_slice_representation_of_product_data
      (V := euclideanBall (0 : Vec3) r) (B := B)
      (isOpen_euclideanBall (0 : Vec3) r) le_rfl hball uP DuP i
      hsmallU hsmallDu hsmallUsq hsmallDusq hgradProduct
    filter_upwards [hSlice0] with t ht
    rcases ht with ⟨v, hv, hg⟩
    exact ⟨v, hv, hg⟩
  have hcomponentEnergy := componentEnergy_finite_on_product_ball
    hball uP DuP i μx μt hmeasureSmall henergyProductSet
  have hA : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => uP (x, t) i) 3 μx ≤
        (essSup (fun s : ℝ => ∫⁻ x in B,
          ENNReal.ofReal (vec3EuclideanNorm (uP (x, s))) ^ (3 : ℝ)) μt) ^ (1 / 3 : ℝ) := by
    exact htimeL3
  have hcomp4 := scalarCylinderL4_of_jointEnergy hr (fun z => uP z i)
    (fun z => DuP z i)
    ((memLp_pi_iff.mp hsmallU2 i).aestronglyMeasurable)
    ((memLp_pi_iff.mp hsmallDu2 i).aestronglyMeasurable)
    (by
      have hbound : (essSup (fun t : ℝ => eLpNorm
          (fun x : Vec3 => uP (x, t) i) 3 μx) μt) < ⊤ := by
        exact lt_of_le_of_lt (essSup_le_of_ae_le _ hA)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hL3P.ne)
      simpa [μx, μt, J] using hbound)
    hcomponentEnergy hSlice
  have hcomp4Product : MemLp (fun z : Vec3 × ℝ => uP z i) 4
      ((volume : Measure (Vec3 × ℝ)).restrict
        (euclideanBall (0 : Vec3) r ×ˢ J)) := by
    rw [← hmeasureSmall]
    exact hcomp4
  have hcomp4Para : MemLp (fun z : ParabolicPoint => u z i) 4
      (volume.restrict (spaceTimeSet (euclideanBall (0 : Vec3) r) J)) := by
    simpa [uP] using parabolic_memLp_of_product_restrict
      (C := euclideanBall (0 : Vec3) r) (J := J)
      (isOpen_euclideanBall (0 : Vec3) r).measurableSet measurableSet_Ioo
      (fun z : ParabolicPoint => u z i) hcomp4Product
  rw [show euclideanBall (0 : Vec3) r = vec3Ball (0 : Vec3) r from
    euclideanBall_eq_vec3Ball (x₀ := (0 : Vec3)) hr] at hcomp4Para
  simpa [J] using hcomp4Para

/-- The vector velocity has space-time `L⁴` on every smaller ball cylinder under the
energy, `L∞ₜL³ₓ`, and slice-gradient hypotheses of `thm:ess-local` (ESS). -/
theorem velocity_memLp_four_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ j : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) j) (fun x => Du (x, t) j)) :
    MemLp u 4
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0))) := by
  apply memLp_pi_iff.mpr
  intro i
  exact velocityComponent_memLp_four_of_essLocalData hr hr1 hu hDu henergy hL3 hgrad

/-- The velocity has space-time `L⁴` on the full unit cylinder under the hypotheses of
`thm:ess-local` (ESS). -/
theorem velocity_memLp_four_unit_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ j : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) j) (fun x => Du (x, t) j)) :
    MemLp u 4
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) :=
  velocity_memLp_four_of_essLocalData (r := 1) (by norm_num) le_rfl
    hu hDu henergy hL3 hgrad

end CKN
