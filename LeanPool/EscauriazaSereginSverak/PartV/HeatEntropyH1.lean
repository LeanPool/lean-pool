/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropy

public section

open MeasureTheory Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

@[expose] def heatRegG_comp_h1 {η : ℝ} (hη : 0 < η)
    {h : Vec3 → Vec3} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmem : ∀ i : Fin 3, MemLp (fun x => h x i) 2 volume)
    (hderiv : ∀ i j : Fin 3,
      MemLp (fun x => fderiv ℝ h x (CKN.basisVec j) i) 2 volume)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, vec3EuclideanNorm (h x) ≤ M) :
    CKN.H1Function (Set.univ : Set Vec3) where
  toFun := fun x => heatRegG η (h x)
  grad := fun x j =>
    fderiv ℝ (fun y => heatRegG η (h y)) x (CKN.basisVec j)
  memL2 := by
    have hgfull : ContDiff ℝ (⊤ : ℕ∞) (fun x => heatRegG η (h x)) :=
      (heatRegG_contDiff hη).comp hh
    have hgdiff : ContDiff ℝ 1 (fun x => heatRegG η (h x)) :=
      hgfull.of_le (by norm_num)
    have hmeas : AEStronglyMeasurable (fun x => heatRegG η (h x)) volume :=
      hgdiff.continuous.aestronglyMeasurable
    have hqterm (i : Fin 3) :
        Integrable (fun x : Vec3 => (h x i) ^ 2) volume :=
      (memLp_two_iff_integrable_sq (hmem i).aestronglyMeasurable).1 (hmem i)
    have hq : Integrable (fun x : Vec3 => ∑ i : Fin 3, (h x i) ^ 2) volume := by
      rw [show (fun x : Vec3 => ∑ i : Fin 3, (h x i) ^ 2) =
        ∑ i : Fin 3, (fun x : Vec3 => (h x i) ^ 2) by
          funext x; rfl]
      exact integrable_finsetSum Finset.univ (fun i hi => hqterm i)
    have hmajorant : Integrable (fun x : Vec3 =>
        (27 * ((3 * η + 2 * M) / 6)) *
          ∑ i : Fin 3, (h x i) ^ 2) volume := by
      simpa only [mul_comm] using hq.const_mul (27 * ((3 * η + 2 * M) / 6))
    have hle : ∀ᵐ x : Vec3 ∂volume,
        ‖(heatRegG η (h x)) ^ 2‖ ≤
          (27 * ((3 * η + 2 * M) / 6)) *
            ∑ i : Fin 3, (h x i) ^ 2 := by
      filter_upwards [] with x
      have henergy := heatRegEnergy_le_mul_sum_sq hη hM (h x) (hbound x)
      have hG := heatRegG_sq_le_energy hη (h x)
      have hpoint : (heatRegG η (h x)) ^ 2 ≤
          (27 * ((3 * η + 2 * M) / 6)) *
            ∑ i : Fin 3, (h x i) ^ 2 := by
        calc
          (heatRegG η (h x)) ^ 2 ≤ 27 * heatRegEnergy η (h x) := hG
          _ ≤ 27 * (((3 * η + 2 * M) / 6) *
                ∑ i : Fin 3, (h x i) ^ 2) :=
            mul_le_mul_of_nonneg_left henergy (by norm_num)
          _ = (27 * ((3 * η + 2 * M) / 6)) *
                ∑ i : Fin 3, (h x i) ^ 2 := by ring
      have hleft : ‖(heatRegG η (h x)) ^ 2‖ =
          (heatRegG η (h x)) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [hleft]
      exact hpoint
    have hmem : MemLp (fun x => heatRegG η (h x)) 2 volume :=
      (memLp_two_iff_integrable_sq hmeas).2
        (hmajorant.mono' (hmeas.pow 2) hle)
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ] using hmem
  gradMemL2 := by
    intro j
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => heatRegG η (h x)) :=
      (heatRegG_contDiff hη).comp hh
    have hmeas : AEStronglyMeasurable
        (fun x : Vec3 => fderiv ℝ (fun y => heatRegG η (h y)) x
          (CKN.basisVec j)) volume := by
      have hcontinuous : Continuous (fun x : Vec3 =>
          fderiv ℝ (fun y => heatRegG η (h y)) x (CKN.basisVec j)) :=
        (hg.continuous_fderiv (by simp)).clm_apply continuous_const
      exact hcontinuous.aestronglyMeasurable
    have hsqterm (i : Fin 3) : Integrable
        (fun x : Vec3 =>
          (fderiv ℝ h x (CKN.basisVec j) i) ^ 2) volume :=
      (memLp_two_iff_integrable_sq (hderiv i j).aestronglyMeasurable).1
        (hderiv i j)
    have hsq : Integrable (fun x : Vec3 => ∑ i : Fin 3,
        (fderiv ℝ h x (CKN.basisVec j) i) ^ 2) volume := by
      rw [show (fun x : Vec3 => ∑ i : Fin 3,
          (fderiv ℝ h x (CKN.basisVec j) i) ^ 2) =
        ∑ i : Fin 3, (fun x : Vec3 =>
          (fderiv ℝ h x (CKN.basisVec j) i) ^ 2) by
            funext x; rfl]
      exact integrable_finsetSum Finset.univ (fun i hi => hsqterm i)
    have hmajorant : Integrable (fun x : Vec3 =>
        ((9 / 2 : ℝ) * M) * ∑ i : Fin 3,
          (fderiv ℝ h x (CKN.basisVec j) i) ^ 2) volume := by
      simpa only [mul_comm] using hsq.const_mul ((9 / 2 : ℝ) * M)
    have hle : ∀ᵐ x : Vec3 ∂volume,
        ‖(fderiv ℝ (fun y => heatRegG η (h y)) x
            (CKN.basisVec j)) ^ 2‖ ≤
          ((9 / 2 : ℝ) * M) * ∑ i : Fin 3,
              (fderiv ℝ h x (CKN.basisVec j) i) ^ 2 := by
      filter_upwards [] with x
      have hsumNonneg : 0 ≤ ∑ i : Fin 3,
          (fderiv ℝ h x (CKN.basisVec j) i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hroot := heatReg_root_sub_eta_le_norm hη (h x)
      have hminus : heatRegSq η (h x) ^ (1 / 2 : ℝ) - η ≤ M :=
        hroot.trans (hbound x)
      have houter := heatRegG_differentiableAt hη (h x)
      have hchain := (houter.hasFDerivAt.comp x
        ((hh.differentiable (by norm_num)).differentiableAt).hasFDerivAt).fderiv
      have hchain' := congrArg (fun D : Vec3 →L[ℝ] ℝ =>
        D (CKN.basisVec j)) hchain
      have hformula :
          fderiv ℝ (fun y => heatRegG η (h y)) x (CKN.basisVec j) =
            fderiv ℝ (heatRegG η) (h x)
              (fderiv ℝ h x (CKN.basisVec j)) := by
        change fderiv ℝ (heatRegG η ∘ h) x (CKN.basisVec j) = _
        exact hchain'
      have hpoint :
          (fderiv ℝ (fun y => heatRegG η (h y)) x (CKN.basisVec j)) ^ 2 ≤
            ((9 / 2 : ℝ) * M) * ∑ i : Fin 3,
              (fderiv ℝ h x (CKN.basisVec j) i) ^ 2 := by
        rw [hformula]
        calc
          (fderiv ℝ (heatRegG η) (h x)
              (fderiv ℝ h x (CKN.basisVec j))) ^ 2 ≤
              (9 / 2 : ℝ) *
                (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
                  ∑ i : Fin 3,
                    (fderiv ℝ h x (CKN.basisVec j) i) ^ 2 :=
            heatReg_gradient_bound hη (h x)
              (fderiv ℝ h x (CKN.basisVec j))
          _ ≤ ((9 / 2 : ℝ) * M) *
                ∑ i : Fin 3,
                  (fderiv ℝ h x (CKN.basisVec j) i) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hminus (by norm_num)) hsumNonneg
      have hleft : ‖(fderiv ℝ (fun y => heatRegG η (h y)) x
          (CKN.basisVec j)) ^ 2‖ =
          (fderiv ℝ (fun y => heatRegG η (h y)) x
            (CKN.basisVec j)) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [hleft]
      exact hpoint
    have hmem : MemLp (fun x : Vec3 =>
        fderiv ℝ (fun y => heatRegG η (h y)) x (CKN.basisVec j)) 2 volume :=
      (memLp_two_iff_integrable_sq hmeas).2
        (hmajorant.mono' (hmeas.pow 2) hle)
    simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
      CKN.volumeOn, Measure.restrict_univ] using hmem
  hasWeakGradient := by
    have hg : ContDiff ℝ 1 (fun x => heatRegG η (h x)) :=
      (heatRegG_contDiff hη).comp hh |>.of_le (by norm_num)
    simpa using
      (CKN.HasWeakGradientOn.of_contDiff
        (U := Set.univ) hg)

/-- The regularized entropy profile of smooth heat data is in whole-space `H¹`. -/
@[expose] def heatRegG_heatConv_h1 {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    CKN.H1Function (Set.univ : Set Vec3) := by
  have hvec : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have hmem (i : Fin 3) :
      MemLp (fun x : Vec3 => heatConvVec3 t b x i) 2 volume := by
    simpa [heatConvVec3] using heatConv_memLp_two_smooth (hb i) (hbc i) ht
  have hderivSmooth (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => fderiv ℝ (fun x : Vec3 => b x i) y
          (CKN.basisVec j)) := by
    have h := (hb i).contDiff_fderiv_apply (m := (⊤ : ℕ∞))
      (n := (⊤ : ℕ∞)) (by simp)
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => (y, CKN.basisVec j)) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => (fderiv ℝ (fun x : Vec3 => b x i) y)
        (CKN.basisVec j))
    exact h.comp harg
  have hderivCompact (i j : Fin 3) : HasCompactSupport
      (fun y : Vec3 => fderiv ℝ (fun x : Vec3 => b x i) y
        (CKN.basisVec j)) :=
    (hbc i).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have hderiv (i j : Fin 3) :
      MemLp (fun x : Vec3 =>
        fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j) i) 2 volume := by
    have hconv := heatConv_memLp_two_smooth (hderivSmooth i j)
      (hderivCompact i j) ht
    have heq : (fun x : Vec3 =>
        fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j) i) =
        heatConv t (fun y : Vec3 =>
          fderiv ℝ (fun z : Vec3 => b z i) y (CKN.basisVec j)) := by
      funext x
      change (fderiv ℝ (fun z : Vec3 => fun k : Fin 3 =>
        heatConv t (fun y : Vec3 => b y k) z) x
          (CKN.basisVec j)) i = _
      rw [fderiv_pi (x := x) (fun k =>
        ((heatConv_smooth_input (hb k) (hbc k) ht).differentiable
          (by norm_num)).differentiableAt)]
      simp only [ContinuousLinearMap.pi_apply]
      simpa only [heatConvVec3] using
        (heatConv_fderiv (hb i) (hbc i) ht x (CKN.basisVec j))
    rw [heq]
    exact hconv
  let C : Fin 3 → ℝ := fun i => Classical.choose
    (heatConv_abs_le_spatial_decay (hb i) (hbc i))
  have hC (i : Fin 3) : 0 ≤ C i :=
    (Classical.choose_spec
      (heatConv_abs_le_spatial_decay (hb i) (hbc i))).1
  have htail (i : Fin 3) (x : Vec3) :
    |heatConvVec3 t b x i| ≤
      C i / (1 + vec3EuclideanNorm x) ^ 3 :=
    (Classical.choose_spec
      (heatConv_abs_le_spatial_decay (hb i) (hbc i))).2 ht x
  let M : ℝ := ∑ i : Fin 3, C i
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun i _ => hC i
  have hbound (x : Vec3) : vec3EuclideanNorm (heatConvVec3 t b x) ≤ M := by
    calc
      vec3EuclideanNorm (heatConvVec3 t b x) ≤
          ∑ i : Fin 3, |heatConvVec3 t b x i| :=
        vec3EuclideanNorm_le_sum_abs _
      _ ≤ ∑ i : Fin 3, C i := by
        apply Finset.sum_le_sum
        intro i hi
        have hn : 1 ≤ 1 + vec3EuclideanNorm x := by
          linarith only [vec3EuclideanNorm_nonneg x]
        have hden : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 := by
          calc
            1 = 1 ^ 3 := by norm_num
            _ ≤ (1 + vec3EuclideanNorm x) ^ 3 := by gcongr
        have hquot : C i / (1 + vec3EuclideanNorm x) ^ 3 ≤ C i := by
          apply (div_le_iff₀ (by positivity)).2
          calc
            C i = C i * 1 := by ring
            _ ≤ C i * (1 + vec3EuclideanNorm x) ^ 3 :=
              mul_le_mul_of_nonneg_left hden (hC i)
        exact (htail i x).trans hquot
      _ = M := by rfl
  exact heatRegG_comp_h1 hη hvec hmem hderiv hM hbound

private theorem heatConvVec3_decay_constants {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ C : Fin 3 → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ {t : ℝ}, 0 < t → ∀ x i,
        |heatConvVec3 t b x i| ≤ C i / (1 + vec3EuclideanNorm x) ^ 3 := by
  let C : Fin 3 → ℝ := fun i => Classical.choose
    (heatConv_abs_le_spatial_decay (hb i) (hbc i))
  refine ⟨C, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec
      (heatConv_abs_le_spatial_decay (hb i) (hbc i))).1
  · intro t ht x i
    exact (Classical.choose_spec
      (heatConv_abs_le_spatial_decay (hb i) (hbc i))).2 ht x

/-- Smooth compact vector data have uniform positive-time spatial decay. -/
theorem heatConvVec3_norm_decay {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {t : ℝ}, 0 < t → ∀ x,
      vec3EuclideanNorm (heatConvVec3 t b x) ≤
        M / (1 + vec3EuclideanNorm x) ^ 3 := by
  obtain ⟨C, hC, htail⟩ := heatConvVec3_decay_constants hb hbc
  let M : ℝ := ∑ i : Fin 3, C i
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun i _ => hC i
  refine ⟨M, hM, ?_⟩
  intro t ht x
  calc
    vec3EuclideanNorm (heatConvVec3 t b x) ≤
        ∑ i : Fin 3, |heatConvVec3 t b x i| :=
      vec3EuclideanNorm_le_sum_abs _
    _ ≤ ∑ i : Fin 3,
          C i / (1 + vec3EuclideanNorm x) ^ 3 := by
        apply Finset.sum_le_sum
        intro i hi
        exact htail ht x i
    _ = M / (1 + vec3EuclideanNorm x) ^ 3 := by
      rw [Finset.sum_div]

/-- First spatial derivatives of smooth compact heat data have polynomial decay. -/
theorem heatConvVec3_spatialDeriv_decay_constants {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ C : Fin 3 → Fin 3 → ℝ, (∀ i j, 0 ≤ C i j) ∧
      ∀ {t : ℝ}, 0 < t → ∀ x i j,
        |CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x| ≤
          C i j / (1 + vec3EuclideanNorm x) ^ 3 := by
  have hfirstSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => b z i) y
        (CKN.basisVec j)) := by
    have h := (hb i).contDiff_fderiv_apply (m := (⊤ : ℕ∞))
      (n := (⊤ : ℕ∞)) (by simp)
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => (y, CKN.basisVec j)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => (fderiv ℝ (fun z : Vec3 => b z i) y)
        (CKN.basisVec j))
    exact h.comp harg
  have hfirstCompact (i j : Fin 3) : HasCompactSupport
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => b z i) y
        (CKN.basisVec j)) :=
    (hbc i).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  let C : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose
    (heatConv_abs_le_spatial_decay (hfirstSmooth i j) (hfirstCompact i j))
  refine ⟨C, ?_, ?_⟩
  · intro i j
    exact (Classical.choose_spec
      (heatConv_abs_le_spatial_decay (hfirstSmooth i j) (hfirstCompact i j))).1
  · intro t ht x i j
    have htail := (Classical.choose_spec
      (heatConv_abs_le_spatial_decay (hfirstSmooth i j) (hfirstCompact i j))).2 ht x
    have hEq : CKN.spatialDeriv
        (fun y : Vec3 => heatConvVec3 t b y i) j x =
        heatConv t (fun y : Vec3 => CKN.spatialDeriv (fun z => b z i) j y) x := by
      change fderiv ℝ (heatConv t (fun z : Vec3 => b z i)) x
          (CKN.basisVec j) = _
      exact heatConv_fderiv (hb i) (hbc i) ht x (CKN.basisVec j)
    rw [hEq]
    simpa [CKN.spatialDeriv] using htail

/-- Polynomial decay of order six gives an integrable whole-space majorant. -/
theorem heat_decay_six_integrable (C : ℝ) (hC : 0 ≤ C) :
    Integrable (fun x : Vec3 => C / (1 + vec3EuclideanNorm x) ^ 6) volume := by
  have hweight : Integrable
      (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    have hfin : (Module.finrank ℝ Vec3 : ℝ) < 6 := by
      rw [Module.finrank_fin_fun]
      norm_num
    exact integrable_one_add_norm (μ := volume) (E := Vec3) (r := 6) hfin
  apply hweight.const_mul C |>.mono' ?_ ?_
  · have hdenCont : Continuous
        (fun x : Vec3 => (1 + vec3EuclideanNorm x) ^ 6) := by
      exact ((continuous_const.add continuous_vec3EuclideanNorm).pow 6)
    have hdenNe (x : Vec3) :
        (1 + vec3EuclideanNorm x) ^ 6 ≠ 0 := by
      exact ne_of_gt (pow_pos (by
        have hn := vec3EuclideanNorm_nonneg x
        positivity) 6)
    exact (continuous_const.div hdenCont hdenNe).aestronglyMeasurable
  · filter_upwards [] with x
    have hden : 1 + ‖x‖ ≤ 1 + vec3EuclideanNorm x := by
      simpa only [add_comm] using
        add_le_add_right (norm_le_vec3EuclideanNorm x) (1 : ℝ)
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) hden 6
    have hquot : C / (1 + vec3EuclideanNorm x) ^ 6 ≤
        C / (1 + ‖x‖) ^ 6 :=
      div_le_div_of_nonneg_left hC (by positivity) hpow
    have hweightEq : (1 + ‖x‖) ^ (-(6 : ℝ)) =
        ((1 + ‖x‖) ^ 6)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
    have hdenV : 0 < 1 + vec3EuclideanNorm x := by
      have hn := vec3EuclideanNorm_nonneg x
      positivity
    change |C / (1 + vec3EuclideanNorm x) ^ 6| ≤
      C * (1 + ‖x‖) ^ (-(6 : ℝ))
    rw [abs_of_nonneg (div_nonneg hC (by positivity))]
    simpa [div_eq_mul_inv, hweightEq, mul_comm] using hquot

end ESS

end
