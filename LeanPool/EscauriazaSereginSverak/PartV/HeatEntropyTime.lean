/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropyH1

/-!
# Heat Entropy Time

The regularized entropy integral differentiates along a smooth heat orbit.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem heatRegEnergy_differentiableAt {η : ℝ} (hη : 0 < η)
    (v : Vec3) : DifferentiableAt ℝ (heatRegEnergy η) v := by
  unfold heatRegEnergy
  have hq := heatRegSq_differentiableAt η v
  have hthree : DifferentiableAt ℝ
      (fun z : Vec3 => heatRegSq η z ^ (3 / 2 : ℝ)) v :=
    hq.rpow_const (Or.inl (ne_of_gt (heatRegSq_pos hη v)))
  exact (hthree.const_mul _ |>.sub (hq.const_mul _)).add_const _

private theorem heatRegEnergy_comp_time_deriv {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) (x : Vec3) :
    HasDerivAt (fun s : ℝ => heatRegEnergy η (heatConvVec3 s b x))
      (∑ i : Fin 3, heatRegTest η (heatConvVec3 t b x) i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) t := by
  have hvec : HasDerivAt (fun s : ℝ => heatConvVec3 s b x)
      (fun i : Fin 3 =>
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact heatConvVec3_component_hasDerivAt_laplacianInput
      hb hbc ht x i
  have houter :=
    (heatRegEnergy_differentiableAt hη (heatConvVec3 t b x)).hasFDerivAt
  have hcomp := houter.comp_hasDerivAt t hvec
  have heq : fderiv ℝ (heatRegEnergy η) (heatConvVec3 t b x)
      (fun i : Fin 3 =>
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) =
      ∑ i : Fin 3, heatRegTest η (heatConvVec3 t b x) i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x := by
    rw [heatRegEnergy_fderiv hη]
    symm
    exact heatRegTest_pairing (heatConvVec3 t b x)
      (fun i : Fin 3 =>
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x)
  rw [← heq]
  exact hcomp

private theorem heatConvVec3_contDiff
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 s b) := by
  rw [contDiff_pi]
  intro i
  simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) hs

private theorem heatRegEnergy_decay_bound
    {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) (v : Vec3 → Vec3)
    (htailBound : ∀ x, vec3EuclideanNorm (v x) ≤ M / (1 + vec3EuclideanNorm x) ^ 3) :
    ∀ x, heatRegEnergy η (v x) ≤
      (3 * ((3 * η + 2 * M) / 6) * M ^ 2) * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
  let K : ℝ := (3 * η + 2 * M) / 6
  let CE : ℝ := 3 * K * M ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  have hdenpow (x : Vec3) (k : ℕ) : 1 ≤ (1 + vec3EuclideanNorm x) ^ k :=
    one_le_pow₀ (by linarith only [vec3EuclideanNorm_nonneg x])
  have hdenNorm (x : Vec3) : 1 + ‖x‖ ≤ 1 + vec3EuclideanNorm x := by
    simpa only [add_comm] using add_le_add_right (norm_le_vec3EuclideanNorm x) (1 : ℝ)
  have henergyBound (x : Vec3) :
      heatRegEnergy η (v x) ≤
        CE / (1 + vec3EuclideanNorm x) ^ 6 := by
    have htail := htailBound x
    have hsq : (vec3EuclideanNorm (v x)) ^ 2 ≤
        (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) htail 2
    have hsum : (∑ i : Fin 3, (v x i) ^ 2) =
        (vec3EuclideanNorm (v x)) ^ 2 := by
      unfold vec3EuclideanNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have hpoint := heatRegEnergy_le_mul_sum_sq hη hM
      (v x) (by
        have hdenone := hdenpow x 3
        have hquot : M / (1 + vec3EuclideanNorm x) ^ 3 ≤ M := by
          apply (div_le_iff₀ (by positivity)).2
          calc
            M = M * 1 := by ring
            _ ≤ M * (1 + vec3EuclideanNorm x) ^ 3 :=
              mul_le_mul_of_nonneg_left hdenone hM
        exact htail.trans hquot)
    have hKform : ((3 * η + 2 * M) / 6) = K := rfl
    calc
      heatRegEnergy η (v x) ≤
          ((3 * η + 2 * M) / 6) *
            ∑ i : Fin 3, (v x i) ^ 2 := hpoint
      _ = K * (vec3EuclideanNorm (v x)) ^ 2 := by
        rw [hsum, hKform]
      _ ≤ K * (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hK
      _ ≤ CE / (1 + vec3EuclideanNorm x) ^ 6 := by
        have hcoeff : K * M ^ 2 ≤ CE := by
          dsimp [CE]
          nlinarith only [hK, sq_nonneg M]
        calc
          K * (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 =
              K * (M ^ 2 / (1 + vec3EuclideanNorm x) ^ 6) := by
                rw [div_pow, ← pow_mul]
          _ = K * M ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 := by ring
          _ ≤ CE / (1 + vec3EuclideanNorm x) ^ 6 :=
            div_le_div_of_nonneg_right hcoeff (by positivity)
  have henergyWeight (x : Vec3) :
      heatRegEnergy η (v x) ≤
        CE * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
    calc
      heatRegEnergy η (v x) ≤
          CE / (1 + vec3EuclideanNorm x) ^ 6 := henergyBound x
      _ ≤ CE / (1 + ‖x‖) ^ 6 := by
        exact div_le_div_of_nonneg_left hCE (by positivity)
          (pow_le_pow_left₀ (by positivity) (hdenNorm x) 6)
      _ = CE * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
        rw [Real.rpow_ofNat]
  exact henergyWeight

/-- The regularized entropy integral differentiates along a smooth heat orbit. -/
theorem heatRegEnergy_integral_hasDerivAt {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    HasDerivAt (fun s : ℝ =>
      ∫ x : Vec3, heatRegEnergy η (heatConvVec3 s b x))
      (∫ x : Vec3, ∑ i : Fin 3,
        heatRegTest η (heatConvVec3 t b x) i *
          heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) t := by
  have hLap (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => CKN.spatialLaplacian (fun y => b y i) x) :=
    CKN.contDiff_spatialLaplacian_smooth (hb i)
  have hLapC (i : Fin 3) : HasCompactSupport
      (fun x => CKN.spatialLaplacian (fun y => b y i) x) :=
    CKN.hasCompactSupport_spatialLaplacian (hbc i)
  let bLap : Vec3 → Vec3 := fun x i =>
    CKN.spatialLaplacian (fun y => b y i) x
  have hbLap (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => bLap x i) := hLap i
  have hbcLap (i : Fin 3) : HasCompactSupport (fun x => bLap x i) := hLapC i
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_norm_decay hb hbc
  obtain ⟨N, hN, hNtail⟩ := heatConvVec3_norm_decay hbLap hbcLap
  let F : ℝ → Vec3 → ℝ := fun s x =>
    heatRegEnergy η (heatConvVec3 s b x)
  let F' : ℝ → Vec3 → ℝ := fun s x =>
    ∑ i : Fin 3, heatRegTest η (heatConvVec3 s b x) i *
      heatConvVec3 s bLap x i
  let S : Set ℝ := Set.Ioo (t / 2) (2 * t)
  have hS : S ∈ nhds t := by
    have hmem : t ∈ Set.Ioo (t / 2) (2 * t) := by
      constructor <;> linarith only [ht]
    simpa [S] using isOpen_Ioo.mem_nhds hmem
  have hSpos {s : ℝ} (hs : s ∈ S) : 0 < s := by
    dsimp [S] at hs
    linarith only [hs.1, ht]
  have hprofile (s : ℝ) (hs : 0 < s) := heatConvVec3_contDiff hb hbc hs
  have hprofileLap (s : ℝ) (hs : 0 < s) := heatConvVec3_contDiff hbLap hbcLap hs
  have hFmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [hS] with s hs
    have hcont : Continuous (F s) := by
      change Continuous (fun x : Vec3 => heatRegEnergy η (heatConvVec3 s b x))
      exact ((heatRegEnergy_contDiff hη).comp (hprofile s (hSpos hs))).continuous
    exact hcont.aestronglyMeasurable
  have hden (x : Vec3) : 1 ≤ 1 + vec3EuclideanNorm x := by
    linarith only [vec3EuclideanNorm_nonneg x]
  have hdenpow (x : Vec3) (k : ℕ) :
      1 ≤ (1 + vec3EuclideanNorm x) ^ k := by
    exact one_le_pow₀ (hden x)
  have hdenNorm (x : Vec3) : 1 + ‖x‖ ≤ 1 + vec3EuclideanNorm x := by
    simpa only [add_comm] using
      add_le_add_right (norm_le_vec3EuclideanNorm x) (1 : ℝ)
  have hfin : (Module.finrank ℝ Vec3 : ℝ) < 6 := by
    rw [Module.finrank_fin_fun]
    norm_num
  have hweight : Integrable
      (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    exact integrable_one_add_norm (μ := volume) (E := Vec3) (r := 6) hfin
  let K : ℝ := (3 * η + 2 * M) / 6
  let CE : ℝ := 3 * K * M ^ 2
  have henergyWeight := heatRegEnergy_decay_bound hη hM (heatConvVec3 t b) (hMtail ht)
  have henergyMajorant : Integrable
      (fun x : Vec3 => CE * (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    simpa only [mul_comm] using hweight.const_mul CE
  have hFint : Integrable (F t) volume := by
    apply henergyMajorant.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((heatRegEnergy_contDiff hη).comp (hprofile t ht)).continuous).aestronglyMeasurable
    · have hnonneg := heatRegEnergy_nonneg hη (heatConvVec3 t b x)
      rw [show F t x = heatRegEnergy η (heatConvVec3 t b x) by rfl,
        Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact henergyWeight x
  let B : ℝ := 3 * M ^ 2 * N
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFprimeBound (x : Vec3) {s : ℝ} (hs : s ∈ S) :
      ‖F' s x‖ ≤ B * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
    have hspos := hSpos hs
    have htailH := hMtail hspos x
    have htailL := hNtail hspos x
    have hD : 1 ≤ (1 + vec3EuclideanNorm x) := hden x
    have hD3 : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 := hdenpow x 3
    have hD6 : 1 ≤ (1 + vec3EuclideanNorm x) ^ 6 := hdenpow x 6
    have htest (i : Fin 3) :
        |heatRegTest η (heatConvVec3 s b x) i| ≤
          (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 := by
      rw [heatRegTest, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr
          (heatReg_root_ge_eta hη (heatConvVec3 s b x)))]
      have hroot := heatReg_root_sub_eta_le_norm hη (heatConvVec3 s b x)
      have hcoord := abs_apply_le_vec3EuclideanNorm
        (heatConvVec3 s b x) i
      calc
        (heatRegSq η (heatConvVec3 s b x) ^ (1 / 2 : ℝ) - η) *
            |heatConvVec3 s b x i| ≤
          vec3EuclideanNorm (heatConvVec3 s b x) ^ 2 := by
            calc
              _ ≤ vec3EuclideanNorm (heatConvVec3 s b x) *
                    vec3EuclideanNorm (heatConvVec3 s b x) :=
                (mul_le_mul_of_nonneg_right hroot (abs_nonneg _)).trans
                  (mul_le_mul_of_nonneg_left hcoord
                    (vec3EuclideanNorm_nonneg _))
              _ = _ := by ring
        _ ≤ (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
          pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) htailH 2
    have hlap (i : Fin 3) :
        |heatConvVec3 s bLap x i| ≤ N := by
      calc
        |heatConvVec3 s bLap x i| ≤
            vec3EuclideanNorm (heatConvVec3 s bLap x) :=
          abs_apply_le_vec3EuclideanNorm _ _
        _ ≤ N / (1 + vec3EuclideanNorm x) ^ 3 := htailL
        _ ≤ N := by
          apply (div_le_iff₀ (by positivity)).2
          calc
            N = N * 1 := by ring
            _ ≤ N * (1 + vec3EuclideanNorm x) ^ 3 :=
              mul_le_mul_of_nonneg_left hD3 hN
    have hterm (i : Fin 3) :
        |heatRegTest η (heatConvVec3 s b x) i *
            heatConvVec3 s bLap x i| ≤
          M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6 := by
      rw [abs_mul]
      calc
        |heatRegTest η (heatConvVec3 s b x) i| *
            |heatConvVec3 s bLap x i| ≤
          (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 * N :=
            mul_le_mul_of_nonneg_right (htest i) (abs_nonneg _)
              |>.trans (mul_le_mul_of_nonneg_left (hlap i)
                (sq_nonneg (M / (1 + vec3EuclideanNorm x) ^ 3)))
        _ = M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6 := by
          rw [div_pow, ← pow_mul]
          ring
    have hsum : |∑ i : Fin 3,
        heatRegTest η (heatConvVec3 s b x) i *
          heatConvVec3 s bLap x i| ≤
        3 * (M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6) := by
      calc
        |∑ i : Fin 3,
            heatRegTest η (heatConvVec3 s b x) i *
              heatConvVec3 s bLap x i| ≤
          ∑ i : Fin 3, |heatRegTest η (heatConvVec3 s b x) i *
            heatConvVec3 s bLap x i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, M ^ 2 * N /
            (1 + vec3EuclideanNorm x) ^ 6 := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i
        _ = 3 * (M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6) := by
          simp
    have hcompare :
        3 * (M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6) ≤
          B / (1 + ‖x‖) ^ 6 := by
      dsimp [B]
      have hquot : M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6 ≤
          M ^ 2 * N / (1 + ‖x‖) ^ 6 :=
        div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg M) hN)
          (by positivity)
          (pow_le_pow_left₀ (by positivity) (hdenNorm x) 6)
      calc
        3 * (M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6) ≤
            3 * (M ^ 2 * N / (1 + ‖x‖) ^ 6) :=
          mul_le_mul_of_nonneg_left hquot (by norm_num)
        _ = 3 * M ^ 2 * N / (1 + ‖x‖) ^ 6 := by ring
    have hweightEq : (1 + ‖x‖) ^ (-(6 : ℝ)) =
        ((1 + ‖x‖) ^ 6)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_num
    calc
      ‖F' s x‖ = |∑ i : Fin 3,
          heatRegTest η (heatConvVec3 s b x) i *
            heatConvVec3 s bLap x i| := by
              change ‖∑ i : Fin 3,
                heatRegTest η (heatConvVec3 s b x) i *
                  heatConvVec3 s bLap x i‖ = _
              rw [Real.norm_eq_abs]
      _ ≤ 3 * (M ^ 2 * N / (1 + vec3EuclideanNorm x) ^ 6) := hsum
      _ ≤ B / (1 + ‖x‖) ^ 6 := hcompare
      _ = B * (1 + ‖x‖) ^ (-(6 : ℝ)) := by rw [hweightEq]; ring
  have hFprimeMajorant : Integrable
      (fun x : Vec3 => B * (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    simpa only [mul_comm] using hweight.const_mul B
  have hFprimeMeas : AEStronglyMeasurable (F' t) volume := by
    have hH := hprofile t ht
    have hL := hprofileLap t ht
    have hT := (heatRegTest_contDiff hη).comp hH
    have hcontinuous : Continuous (F' t) := by
      change Continuous (fun x : Vec3 =>
        ∑ i : Fin 3, heatRegTest η (heatConvVec3 t b x) i *
          heatConvVec3 t bLap x i)
      apply continuous_finsetSum
      intro i hi
      exact ((continuous_apply i).comp hT.continuous).mul
        ((continuous_apply i).comp hL.continuous)
    exact hcontinuous.aestronglyMeasurable
  have hbound : ∀ᵐ x : Vec3 ∂volume, ∀ s ∈ S,
      ‖F' s x‖ ≤ B * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
    exact Filter.Eventually.of_forall fun x s hs => hFprimeBound x hs
  have hdiff : ∀ᵐ x : Vec3 ∂volume, ∀ s ∈ S,
      HasDerivAt (F · x) (F' s x) s := by
    exact Filter.Eventually.of_forall fun x s hs => by
      have hpoint := heatRegEnergy_comp_time_deriv hb hbc
        (hSpos hs) hη x
      simpa [F, F', heatConvVec3, bLap] using hpoint
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') hS hFmeas hFint hFprimeMeas hbound
    hFprimeMajorant hdiff
  simpa [F, F', bLap, heatConvVec3] using hmain.2

private theorem heatRegTest_component_differentiableAt {η : ℝ}
    (hη : 0 < η) (v : Vec3) (i : Fin 3) :
    DifferentiableAt ℝ (fun z : Vec3 => heatRegTest η z i) v := by
  unfold heatRegTest
  have hq := heatRegSq_differentiableAt η v
  have hroot : DifferentiableAt ℝ
      (fun z : Vec3 => heatRegSq η z ^ (1 / 2 : ℝ)) v :=
    hq.rpow_const (Or.inl (ne_of_gt (heatRegSq_pos hη v)))
  exact hroot.sub_const η |>.mul (differentiableAt_apply i v)

private theorem heatRegEnergy_comp_fderiv {η : ℝ} (hη : 0 < η)
    {h : Vec3 → Vec3} {x v : Vec3} (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (fun y => heatRegEnergy η (h y)) x v =
      (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
        heatRegDot (h x) (fderiv ℝ h x v) := by
  change fderiv ℝ (heatRegEnergy η ∘ h) x v = _
  have houter := (heatRegEnergy_differentiableAt hη (h x)).hasFDerivAt
  have hcomp := houter.comp x hh.hasFDerivAt
  have hv := congrArg (fun D : Vec3 →L[ℝ] ℝ => D v) hcomp.fderiv
  calc
    fderiv ℝ (heatRegEnergy η ∘ h) x v =
        (fderiv ℝ (heatRegEnergy η) (h x) ∘SL fderiv ℝ h x) v := hv
    _ = fderiv ℝ (heatRegEnergy η) (h x) (fderiv ℝ h x v) := rfl
    _ = (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
          heatRegDot (h x) (fderiv ℝ h x v) := by
            rw [heatRegEnergy_fderiv hη]

/-- The spatial derivative of the regularized entropy test along a smooth field. -/
theorem heatRegTest_comp_fderiv {η : ℝ} (hη : 0 < η)
    {h : Vec3 → Vec3} {x v : Vec3} (hh : DifferentiableAt ℝ h x)
    (i : Fin 3) :
    fderiv ℝ (fun y => heatRegTest η (h y) i) x v =
    (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
          (fderiv ℝ h x v) i +
        heatRegSq η (h x) ^ (-(1 / 2 : ℝ)) *
          heatRegDot (h x) (fderiv ℝ h x v) * (h x) i := by
  change fderiv ℝ ((fun z : Vec3 => heatRegTest η z i) ∘ h) x v = _
  have houter :=
    (heatRegTest_component_differentiableAt hη (h x) i).hasFDerivAt
  have hcomp := houter.comp x hh.hasFDerivAt
  have hv := congrArg (fun D : Vec3 →L[ℝ] ℝ => D v) hcomp.fderiv
  calc
    fderiv ℝ ((fun z : Vec3 => heatRegTest η z i) ∘ h) x v =
        (fderiv ℝ (fun z : Vec3 => heatRegTest η z i) (h x) ∘SL
          fderiv ℝ h x) v := hv
    _ = fderiv ℝ (fun z : Vec3 => heatRegTest η z i) (h x)
          (fderiv ℝ h x v) := rfl
    _ = (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
          (fderiv ℝ h x v) i +
        heatRegSq η (h x) ^ (-(1 / 2 : ℝ)) *
          heatRegDot (h x) (fderiv ℝ h x v) * (h x) i := by
            rw [heatRegTest_fderiv hη]

/-- The regularized entropy-test derivative has nonnegative pairing with the
directional derivative of a smooth vector field. -/
theorem heatRegTest_comp_dissipation_nonneg {η : ℝ} (hη : 0 < η)
    {h : Vec3 → Vec3} {x v : Vec3} (hh : DifferentiableAt ℝ h x) :
    0 ≤ ∑ i : Fin 3,
      fderiv ℝ (fun y : Vec3 => heatRegTest η (h y) i) x v *
        (fderiv ℝ h x v) i := by
  let w : Vec3 := fderiv ℝ h x v
  have hterm (i : Fin 3) :
      fderiv ℝ (fun y : Vec3 => heatRegTest η (h y) i) x v =
        fderiv ℝ (fun z : Vec3 => heatRegTest η z i) (h x) w := by
    rw [heatRegTest_comp_fderiv hη hh i, ← heatRegTest_fderiv hη]
  have hlower := heatRegTest_dissipation_lower hη (h x) w
  have hweighted : 0 ≤
      (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
        ∑ i : Fin 3, w i ^ 2 := by
    exact mul_nonneg (sub_nonneg.mpr (heatReg_root_ge_eta hη (h x)))
      (Finset.sum_nonneg fun i _ => sq_nonneg (w i))
  calc
    0 ≤ (heatRegSq η (h x) ^ (1 / 2 : ℝ) - η) *
        ∑ i : Fin 3, w i ^ 2 := hweighted
    _ ≤ ∑ i : Fin 3,
          fderiv ℝ (fun z : Vec3 => heatRegTest η z i) (h x) w * w i := hlower
    _ = ∑ i : Fin 3,
        fderiv ℝ (fun y : Vec3 => heatRegTest η (h y) i) x v *
          (fderiv ℝ h x v) i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hterm i]

/-- A pointwise derivative bound for the regularized entropy test on bounded
vectors and directions. -/
theorem heatRegTest_fderiv_abs_bound {η M D : ℝ} (hη : 0 < η)
    (hM : 0 ≤ M) (hD : 0 ≤ D) {v w : Vec3}
    (hv : vec3EuclideanNorm v ≤ M)
    (hw : ∀ i : Fin 3, |w i| ≤ D) (i : Fin 3) :
    |fderiv ℝ (fun z : Vec3 => heatRegTest η z i) v w| ≤
      M * D + (3 * M ^ 2 * D) / η := by
  have hroot := heatReg_root_ge_eta hη v
  have hminus : 0 ≤ heatRegSq η v ^ (1 / 2 : ℝ) - η :=
    sub_nonneg.mpr hroot
  have hminusBound : heatRegSq η v ^ (1 / 2 : ℝ) - η ≤ M := by
    exact (heatReg_root_sub_eta_le_norm hη v).trans hv
  have hvcoord (k : Fin 3) : |v k| ≤ M :=
    (abs_apply_le_vec3EuclideanNorm v k).trans hv
  have hdot : |heatRegDot v w| ≤ 3 * M * D := by
    calc
      |heatRegDot v w| ≤ ∑ k : Fin 3, |v k * w k| := by
        unfold heatRegDot
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, M * D := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (hvcoord k) (hw k) (abs_nonneg _) hM
      _ = 3 * M * D := by simp; ring
  have hrootInv :
      |heatRegSq η v ^ (-(1 / 2 : ℝ))| ≤ η⁻¹ := by
    rw [heatReg_inv_rpow_half hη v,
      abs_of_nonneg (inv_nonneg.mpr
        (Real.rpow_nonneg (le_of_lt (heatRegSq_pos hη v)) _))]
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos
      (heatRegSq_pos hη v) _) hη).2
    exact hroot
  have hform := heatRegTest_fderiv hη v w i
  rw [hform]
  have hfirst :
      |(heatRegSq η v ^ (1 / 2 : ℝ) - η) * w i| ≤ M * D := by
    rw [abs_mul, abs_of_nonneg hminus]
    exact mul_le_mul hminusBound (hw i) (abs_nonneg _) hM
  have hsecond :
      |heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v w * v i| ≤
        (3 * M ^ 2 * D) / η := by
    rw [abs_mul, abs_mul]
    calc
      |heatRegSq η v ^ (-(1 / 2 : ℝ))| *
          |heatRegDot v w| * |v i| ≤ η⁻¹ * (3 * M * D) * M := by
        exact mul_le_mul (mul_le_mul hrootInv hdot (abs_nonneg _) (by positivity))
          (hvcoord i) (by positivity) (by positivity)
      _ = (3 * M ^ 2 * D) / η := by
        field_simp [ne_of_gt hη]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

end ESS

end
