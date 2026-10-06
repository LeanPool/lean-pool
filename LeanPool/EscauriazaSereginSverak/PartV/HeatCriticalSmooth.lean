/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropyTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Heat Critical Smooth

A continuous function with sixth-order polynomial decay is integrable on
the whole space, as used in `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- A continuous function with sixth-order polynomial decay is integrable on
the whole space, as used in `lem:pv-heat-critical`. -/
theorem heat_integrable_of_decay_six {f : Vec3 → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C / (1 + vec3EuclideanNorm x) ^ 6) :
    Integrable f volume := by
  exact (heat_decay_six_integrable C hC).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact hbound x)

private theorem heat_product_decay_six_integrable {f g : Vec3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfdecay : ∀ x, |f x| ≤ A / (1 + vec3EuclideanNorm x) ^ 6)
    (hgdecay : ∀ x, |g x| ≤ B / (1 + vec3EuclideanNorm x) ^ 3) :
    Integrable (fun x => f x * g x) volume := by
  apply heat_integrable_of_decay_six (hf.mul hg) (mul_nonneg hA hB)
  intro x
  change |f x * g x| ≤ A * B / (1 + vec3EuclideanNorm x) ^ 6
  rw [abs_mul]
  have hden : 0 < 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    positivity
  have hone : 1 ≤ 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    linarith only [hn]
  have hden3 : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 := one_le_pow₀ hone
  have hgBound : |g x| ≤ B := by
    exact (hgdecay x).trans (by
      apply (div_le_iff₀ (pow_pos hden 3)).2
      calc
        B = B * 1 := by ring
        _ ≤ B * (1 + vec3EuclideanNorm x) ^ 3 :=
          mul_le_mul_of_nonneg_left hden3 hB)
  calc
    |f x| * |g x| ≤
        (A / (1 + vec3EuclideanNorm x) ^ 6) * B :=
      mul_le_mul (hfdecay x) hgBound (abs_nonneg _)
        (div_nonneg hA (pow_nonneg (le_of_lt hden) 6))
    _ = A * B / (1 + vec3EuclideanNorm x) ^ 6 := by ring

/-- Whole-space integration by parts against the spatial Laplacian for smooth
functions with integrable products, as used in `lem:pv-heat-critical`. -/
theorem integral_scalar_spatialLaplacian_ibp
    {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfg : ∀ j : Fin 3, Integrable (fun x : Vec3 =>
      f x * CKN.spatialDeriv g j x) volume)
    (hfg' : ∀ j : Fin 3, Integrable (fun x : Vec3 =>
      f x * CKN.spatialDeriv (fun y => CKN.spatialDeriv g j y) j x) volume)
    (hf'g : ∀ j : Fin 3, Integrable (fun x : Vec3 =>
      CKN.spatialDeriv f j x * CKN.spatialDeriv g j x) volume) :
    ∫ x : Vec3, f x * CKN.spatialLaplacian g x =
      -∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv f j x * CKN.spatialDeriv g j x := by
  have hsum (j : Fin 3) : Integrable (fun x : Vec3 =>
      f x * CKN.spatialDeriv (fun y => CKN.spatialDeriv g j y) j x) volume :=
    hfg' j
  have hpoint (j : Fin 3) : ∀ x ∈ tsupport
      (fun y : Vec3 => CKN.spatialDeriv g j y), DifferentiableAt ℝ f x :=
    fun x _ => hf.differentiable (by simp) x
  have hpoint' (j : Fin 3) : ∀ x ∈ tsupport f,
      DifferentiableAt ℝ (fun y : Vec3 => CKN.spatialDeriv g j y) x := by
    intro x _
    exact (CKN.contDiff_spatialDeriv_smooth hg j).differentiable (by simp) x
  have hibp (j : Fin 3) :
      ∫ x : Vec3, f x * CKN.spatialDeriv
          (fun y => CKN.spatialDeriv g j y) j x =
        -∫ x : Vec3, CKN.spatialDeriv f j x *
          CKN.spatialDeriv g j x := by
    convert (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (hf'g j) (hfg' j) (hfg j) (hpoint j) (hpoint' j)) using 1 <;> rfl
  change ∫ x : Vec3, f x *
      (∑ j : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv g j) j x) = _
  have hmul : (fun x : Vec3 => f x *
      ∑ j : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv g j) j x) =
      fun x => ∑ j : Fin 3, f x *
        CKN.spatialDeriv (CKN.spatialDeriv g j) j x := by
    funext x
    rw [Finset.mul_sum]
  rw [hmul, integral_finsetSum Finset.univ (fun j hj => hsum j)]
  calc
    ∑ j : Fin 3, ∫ x : Vec3, f x *
        CKN.spatialDeriv (fun y => CKN.spatialDeriv g j y) j x =
      ∑ j : Fin 3, -(∫ x : Vec3,
        CKN.spatialDeriv f j x * CKN.spatialDeriv g j x) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hibp j
    _ = -∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv f j x * CKN.spatialDeriv g j x := by
          rw [Finset.sum_neg_distrib]

/-- First spatial derivatives of a smooth compact vector heat orbit have
cubic decay uniformly in positive time. -/
theorem heatConvVec3_firstDeriv_uniform_decay {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {t : ℝ}, 0 < t → ∀ x i j,
      |CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x| ≤
        D / (1 + vec3EuclideanNorm x) ^ 3 := by
  obtain ⟨C, hC, htail⟩ := heatConvVec3_spatialDeriv_decay_constants hb hbc
  let D : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, C i j
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC i j
  refine ⟨D, hD, ?_⟩
  intro t ht x i j
  have hCij : C i j ≤ D := by
    dsimp [D]
    exact (Finset.single_le_sum (fun k _ => hC i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ => hC k l) (Finset.mem_univ i))
  have htailij := htail ht x i j
  have hden : 0 < 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    positivity
  exact htailij.trans
    (div_le_div_of_nonneg_right hCij (pow_nonneg hden.le 3))

/-- The vector-valued heat derivative agrees componentwise with CKN's spatial
derivative, as used in `lem:pv-heat-critical`. -/
theorem heatConvVec3_fderiv_basis_apply {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) (x : Vec3) (i j : Fin 3) :
    (fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j)) i =
      CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
  change (fderiv ℝ (fun z : Vec3 => fun k : Fin 3 =>
      heatConv t (fun y => b y k) z) x (CKN.basisVec j)) i = _
  rw [fderiv_pi (x := x) (fun k =>
    ((heatConv_smooth_input (hb k) (hbc k) ht).differentiable
      (by norm_num)).differentiableAt)]
  simp only [ContinuousLinearMap.pi_apply]
  change fderiv ℝ
      (fun z : Vec3 => heatConv t (fun y : Vec3 => b y i) z)
      x (CKN.basisVec j) =
    CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x
  rfl

@[expose] def heatSpatialDerivativeInput (b : Vec3 → Vec3) (j : Fin 3) :
    Vec3 → Vec3 := fun x i => CKN.spatialDeriv (fun y => b y i) j x

private theorem heatSpatialDerivativeInput_smooth {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) (j : Fin 3) :
    ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => heatSpatialDerivativeInput b j x i) := by
  intro i
  exact CKN.contDiff_spatialDeriv_smooth (hb i) j

private theorem heatSpatialDerivativeInput_compact {b : Vec3 → Vec3}
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) (j : Fin 3) :
    ∀ i : Fin 3, HasCompactSupport
      (fun x => heatSpatialDerivativeInput b j x i) := by
  intro i
  change HasCompactSupport (fun x => (fderiv ℝ (fun y => b y i) x)
    (CKN.basisVec j))
  exact (hbc i).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)

/-- Diagonal second spatial derivatives of a smooth compact vector heat orbit
have cubic decay uniformly in positive time. -/
theorem heatConvVec3_diagSecondDeriv_uniform_decay
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ D₂ : ℝ, 0 ≤ D₂ ∧ ∀ {t : ℝ}, 0 < t → ∀ x i j,
      |CKN.spatialDeriv
        (fun y => CKN.spatialDeriv (fun z => heatConvVec3 t b z i) j y) j x| ≤
          D₂ / (1 + vec3EuclideanNorm x) ^ 3 := by
  let D₂j : Fin 3 → ℝ := fun j => Classical.choose
    (heatConvVec3_firstDeriv_uniform_decay
      (heatSpatialDerivativeInput_smooth hb j)
      (heatSpatialDerivativeInput_compact hbc j))
  have hD₂j (j : Fin 3) : 0 ≤ D₂j j :=
    (Classical.choose_spec
      (heatConvVec3_firstDeriv_uniform_decay
        (heatSpatialDerivativeInput_smooth hb j)
        (heatSpatialDerivativeInput_compact hbc j))).1
  have htail₂j (j : Fin 3) {t : ℝ} (ht : 0 < t) (x : Vec3)
      (i k : Fin 3) :
      |CKN.spatialDeriv
          (fun y => heatConvVec3 t (heatSpatialDerivativeInput b j) y i) k x| ≤
        D₂j j / (1 + vec3EuclideanNorm x) ^ 3 :=
    (Classical.choose_spec
      (heatConvVec3_firstDeriv_uniform_decay
        (heatSpatialDerivativeInput_smooth hb j)
        (heatSpatialDerivativeInput_compact hbc j))).2 ht x i k
  let D₂ : ℝ := ∑ j : Fin 3, D₂j j
  have hD₂ : 0 ≤ D₂ := by
    dsimp [D₂]
    exact Finset.sum_nonneg fun j _ => hD₂j j
  refine ⟨D₂, hD₂, ?_⟩
  intro t ht x i j
  have hEq : (fun y : Vec3 => heatConvVec3 t
      (heatSpatialDerivativeInput b j) y i) =
      fun y => CKN.spatialDeriv (fun z => heatConvVec3 t b z i) j y := by
    funext y
    change heatConv t (fun z => CKN.spatialDeriv (fun w => b w i) j z) y = _
    symm
    exact heatConv_fderiv (hb i) (hbc i) ht y (CKN.basisVec j)
  have hEq' := congrArg (fun g : Vec3 → ℝ => CKN.spatialDeriv g j x) hEq
  have htail := htail₂j j ht x i j
  have hDj : D₂j j ≤ D₂ := by
    dsimp [D₂]
    exact Finset.single_le_sum (fun k _ => hD₂j k) (Finset.mem_univ j)
  rw [← hEq']
  have hden : 0 < 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    positivity
  exact htail.trans
    (div_le_div_of_nonneg_right hDj (pow_nonneg hden.le 3))

private theorem heatRegTest_profile_decay {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {t : ℝ}, 0 < t → ∀ x i,
      |heatRegTest η (heatConvVec3 t b x) i| ≤
        A / (1 + vec3EuclideanNorm x) ^ 6 := by
  obtain ⟨M, hM, htail⟩ := heatConvVec3_norm_decay hb hbc
  let A : ℝ := M ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro t ht x i
  have hden : 0 < 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    positivity
  have hnorm := htail ht x
  calc
    |heatRegTest η (heatConvVec3 t b x) i| ≤
        vec3EuclideanNorm (heatConvVec3 t b x) ^ 2 :=
      heatRegTest_abs_le_norm_sq hη _ _
    _ ≤ (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hnorm 2
    _ = A / (1 + vec3EuclideanNorm x) ^ 6 := by
      dsimp [A]
      rw [div_pow, ← pow_mul]

private theorem heatRegTest_spatialDeriv_profile_decay {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {t : ℝ}, 0 < t → ∀ x i j,
      |CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x| ≤
          A / (1 + vec3EuclideanNorm x) ^ 6 := by
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_norm_decay hb hbc
  obtain ⟨D, hD, hDtail⟩ := heatConvVec3_firstDeriv_uniform_decay hb hbc
  let A : ℝ := M * D + (3 * M ^ 2 * D) / η
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro t ht x i j
  have hden : 0 < 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    positivity
  have hone : 1 ≤ 1 + vec3EuclideanNorm x := by
    have hn := vec3EuclideanNorm_nonneg x
    linarith only [hn]
  let W : ℝ := 1 + vec3EuclideanNorm x
  let Mx : ℝ := M / W ^ 3
  let Dx : ℝ := D / W ^ 3
  have hden3 : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 :=
    one_le_pow₀ hone
  have hbound : vec3EuclideanNorm (heatConvVec3 t b x) ≤ Mx := by
    simpa [Mx, W] using hMtail ht x
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro k
    simpa [heatConvVec3] using heatConv_smooth_input (hb k) (hbc k) ht
  have hcoord (k : Fin 3) :
      |CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x| ≤ Dx := by
    simpa [Dx, W] using hDtail ht x k j
  have hprofileDiff : DifferentiableAt ℝ (heatConvVec3 t b) x :=
    (hprofile.differentiable (by norm_num)).differentiableAt
  have hWcoord (k : Fin 3) :
      (fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j)) k =
        CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x := by
    exact heatConvVec3_fderiv_basis_apply hb hbc ht x k j
  have hW : fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j) =
      fun k => CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x := by
    funext k
    exact hWcoord k
  have hchain := heatRegTest_comp_fderiv (η := η) hη
    (h := heatConvVec3 t b) (x := x) (v := CKN.basisVec j)
    hprofileDiff i
  have hpoint := heatRegTest_fderiv_abs_bound (η := η) (M := Mx) (D := Dx) hη
    (by dsimp [Mx]; exact div_nonneg hM (pow_nonneg (le_of_lt hden) 3))
    (by dsimp [Dx]; exact div_nonneg hD (pow_nonneg (le_of_lt hden) 3))
    (v := heatConvVec3 t b x)
    (w := fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j))
    hbound (by intro k; rw [hW]; exact hcoord k) i
  have hresult : |fderiv ℝ
      (fun y : Vec3 => heatRegTest η (heatConvVec3 t b y) i) x
      (CKN.basisVec j)| ≤ Mx * Dx + (3 * Mx ^ 2 * Dx) / η := by
    rw [hchain, ← heatRegTest_fderiv hη]
    exact hpoint
  have hden6le9 : W ^ 6 ≤ W ^ 9 := by
    calc
      W ^ 6 = W ^ 6 * 1 := by ring
      _ ≤ W ^ 6 * W ^ 3 :=
        mul_le_mul_of_nonneg_left hden3 (pow_nonneg (le_of_lt hden) 6)
      _ = W ^ 9 := by rw [← pow_add]
  have hcoef : 0 ≤ 3 * M ^ 2 * D / η := by positivity
  have hscaled : Mx * Dx + (3 * Mx ^ 2 * Dx) / η ≤ A / W ^ 6 := by
    calc
      Mx * Dx + (3 * Mx ^ 2 * Dx) / η =
          M * D / W ^ 6 + (3 * M ^ 2 * D / η) / W ^ 9 := by
            dsimp [Mx, Dx, W]
            field_simp [ne_of_gt hη, ne_of_gt (pow_pos hden 3)]
      _ ≤ M * D / W ^ 6 + (3 * M ^ 2 * D / η) / W ^ 6 :=
        by
          rw [add_le_add_iff_left]
          exact div_le_div_of_nonneg_left hcoef (pow_pos hden 6) hden6le9
      _ = A / W ^ 6 := by dsimp [A]; ring
  have hrescaled :
      |fderiv ℝ (fun y : Vec3 => heatRegTest η (heatConvVec3 t b y) i) x
          (CKN.basisVec j)| ≤ A / (1 + vec3EuclideanNorm x) ^ 6 := by
    simpa [W] using hresult.trans hscaled
  simpa [CKN.spatialDeriv] using hrescaled

/-- The spatial entropy-dissipation density of a smooth heat orbit is
integrable, as used in `lem:pv-heat-critical`. -/
theorem heatRegTest_heatConv_dissipation_integrable {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    (∀ i j : Fin 3, Integrable
      (fun x : Vec3 => CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) volume) ∧
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
      CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) volume := by
  obtain ⟨D, hD, hDtail⟩ := heatConvVec3_firstDeriv_uniform_decay hb hbc
  obtain ⟨A, hA, hAtail⟩ := heatRegTest_spatialDeriv_profile_decay hb hbc hη
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have htestProfile : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => heatRegTest η (heatConvVec3 t b x)) :=
    (heatRegTest_contDiff hη).comp hprofile
  have htestSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => heatRegTest η (heatConvVec3 t b x) i) :=
    (contDiff_apply ℝ ℝ i).comp htestProfile
  have hheatSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => heatConvVec3 t b x i) :=
    (contDiff_apply ℝ ℝ i).comp hprofile
  have hterm (i j : Fin 3) : Integrable
      (fun x : Vec3 =>
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) volume := by
    apply heat_product_decay_six_integrable
      (CKN.contDiff_spatialDeriv_smooth (htestSmooth i) j).continuous
      (CKN.contDiff_spatialDeriv_smooth (hheatSmooth i) j).continuous hA hD
    · exact fun x => hAtail ht x i j
    · exact fun x => hDtail ht x i j
  refine ⟨hterm, ?_⟩
  apply integrable_finsetSum Finset.univ
  intro i hi
  exact integrable_finsetSum Finset.univ (fun j hj => hterm i j)

/-- Spatial integration by parts expresses the entropy derivative pairing as
minus the nonnegative dissipation in `lem:pv-heat-critical`. -/
theorem heatRegEnergy_integral_derivative_eq_neg_gradient
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    (∫ x : Vec3, ∑ i : Fin 3,
      heatRegTest η (heatConvVec3 t b x) i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  obtain ⟨D, hD, hDtail⟩ := heatConvVec3_firstDeriv_uniform_decay hb hbc
  obtain ⟨D₂, hD₂, hD₂tail⟩ :=
    heatConvVec3_diagSecondDeriv_uniform_decay hb hbc
  obtain ⟨A, hA, hAtail⟩ := heatRegTest_profile_decay hb hbc hη
  obtain ⟨B, hB, hBtail⟩ := heatRegTest_spatialDeriv_profile_decay hb hbc hη
  let f : Fin 3 → Vec3 → ℝ := fun i x => heatRegTest η (heatConvVec3 t b x) i
  let g : Fin 3 → Vec3 → ℝ := fun i x => heatConvVec3 t b x i
  have htestProfile : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => heatRegTest η (heatConvVec3 t b x)) :=
    (heatRegTest_contDiff hη).comp hprofile
  have hfSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f i) := by
    dsimp [f]
    exact (contDiff_apply ℝ ℝ i).comp htestProfile
  have hgSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g i) := by
    dsimp [g]
    exact (contDiff_apply ℝ ℝ i).comp hprofile
  have hfg (i j : Fin 3) : Integrable
      (fun x : Vec3 => f i x * CKN.spatialDeriv (g i) j x) volume := by
    apply heat_product_decay_six_integrable (hfSmooth i).continuous
      (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j).continuous hA hD
    · exact fun x => hAtail ht x i
    · exact fun x => hDtail ht x i j
  have hfg' (i j : Fin 3) : Integrable
      (fun x : Vec3 => f i x *
        CKN.spatialDeriv (fun y => CKN.spatialDeriv (g i) j y) j x) volume := by
    apply heat_product_decay_six_integrable (hfSmooth i).continuous
      (CKN.contDiff_spatialDeriv_smooth
        (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j) j).continuous hA hD₂
    · exact fun x => hAtail ht x i
    · exact fun x => hD₂tail ht x i j
  have hf'g (i j : Fin 3) : Integrable
      (fun x : Vec3 => CKN.spatialDeriv (f i) j x *
        CKN.spatialDeriv (g i) j x) volume := by
    apply heat_product_decay_six_integrable
      (CKN.contDiff_spatialDeriv_smooth (hfSmooth i) j).continuous
      (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j).continuous hB hD
    · exact fun x => hBtail ht x i j
    · exact fun x => hDtail ht x i j
  have hleftInt (i : Fin 3) : Integrable
      (fun x : Vec3 => f i x * CKN.spatialLaplacian (g i) x) volume := by
    have hsum : Integrable (fun x : Vec3 => ∑ j : Fin 3,
        f i x * CKN.spatialDeriv
          (fun y => CKN.spatialDeriv (g i) j y) j x) volume :=
      integrable_finsetSum Finset.univ (fun j hj => hfg' i j)
    have heq : (fun x : Vec3 => f i x * CKN.spatialLaplacian (g i) x) =
        fun x => ∑ j : Fin 3, f i x * CKN.spatialDeriv
          (fun y => CKN.spatialDeriv (g i) j y) j x := by
      funext x
      rw [CKN.spatialLaplacian, Finset.mul_sum]
    rw [heq]
    exact hsum
  have hLapEq (i : Fin 3) (x : Vec3) : CKN.spatialLaplacian (g i) x =
      heatConv t (CKN.spatialLaplacian (fun y => b y i)) x := by
    simpa [g, heatConvVec3] using
      (heatConvVec3_component_spatialLaplacian_input hb hbc ht x i)
  have hcomponentInt (i : Fin 3) : Integrable
      (fun x : Vec3 => f i x *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) volume := by
    exact (hleftInt i).congr (Filter.Eventually.of_forall fun x =>
      congrArg (fun z => f i x * z) (hLapEq i x))
  have hcomponent (i : Fin 3) :
      ∫ x : Vec3, f i x *
          heatConv t (CKN.spatialLaplacian (fun y => b y i)) x =
        -∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      congrArg (fun z => f i x * z) (hLapEq i x).symm)]
    exact integral_scalar_spatialLaplacian_ibp (hfSmooth i) (hgSmooth i)
      (fun j => hfg i j) (fun j => hfg' i j) (fun j => hf'g i j)
  have hsumInt : Integrable (fun x : Vec3 => ∑ i : Fin 3, f i x *
      heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) volume :=
    integrable_finsetSum Finset.univ (fun i hi => hcomponentInt i)
  have hsumEq := integral_finsetSum Finset.univ
    (fun i hi => hcomponentInt i)
  calc
    (∫ x : Vec3, ∑ i : Fin 3, f i x *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) =
      ∑ i : Fin 3, ∫ x : Vec3, f i x *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x := hsumEq
    _ = ∑ i : Fin 3, -∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hcomponent i
    _ = -∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x := by
            rw [Finset.sum_neg_distrib]

private theorem heatRegTest_spatialDissipation_nonneg
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) (x : Vec3) (j : Fin 3) :
    0 ≤ ∑ i : Fin 3,
      CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
      CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have hprofileDiff : DifferentiableAt ℝ (heatConvVec3 t b) x :=
    (hprofile.differentiable (by norm_num)).differentiableAt
  let w : Vec3 := fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j)
  have hpoint := heatRegTest_comp_dissipation_nonneg hη
    (v := CKN.basisVec j) hprofileDiff
  have htermEq :
      (∑ i : Fin 3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) =
      ∑ i : Fin 3,
        fderiv ℝ (fun y : Vec3 => heatRegTest η (heatConvVec3 t b y) i)
          x (CKN.basisVec j) * w i := by
    apply Finset.sum_congr rfl
    intro i hi
    change fderiv ℝ
        (fun y : Vec3 => heatRegTest η (heatConvVec3 t b y) i)
          x (CKN.basisVec j) *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x =
      fderiv ℝ
        (fun y : Vec3 => heatRegTest η (heatConvVec3 t b y) i)
          x (CKN.basisVec j) * w i
    rw [← heatConvVec3_fderiv_basis_apply hb hbc ht x i j]
  rw [htermEq]
  exact hpoint

private theorem heatRegEnergy_integral_deriv_nonpos
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    deriv (fun s : ℝ => ∫ x : Vec3,
      heatRegEnergy η (heatConvVec3 s b x)) t ≤ 0 := by
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  obtain ⟨D, hD, hDtail⟩ := heatConvVec3_firstDeriv_uniform_decay hb hbc
  obtain ⟨B, hB, hBtail⟩ := heatRegTest_spatialDeriv_profile_decay hb hbc hη
  let f : Fin 3 → Vec3 → ℝ :=
    fun i x => heatRegTest η (heatConvVec3 t b x) i
  let g : Fin 3 → Vec3 → ℝ := fun i x => heatConvVec3 t b x i
  have htestProfile : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => heatRegTest η (heatConvVec3 t b x)) :=
    (heatRegTest_contDiff hη).comp hprofile
  have hfSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f i) := by
    dsimp [f]
    exact (contDiff_apply ℝ ℝ i).comp htestProfile
  have hgSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g i) := by
    dsimp [g]
    exact (contDiff_apply ℝ ℝ i).comp hprofile
  have htermInt (i j : Fin 3) : Integrable
      (fun x : Vec3 => CKN.spatialDeriv (f i) j x *
        CKN.spatialDeriv (g i) j x) volume := by
    apply heat_product_decay_six_integrable
      (CKN.contDiff_spatialDeriv_smooth (hfSmooth i) j).continuous
      (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j).continuous hB hD
    · exact fun x => hBtail ht x i j
    · exact fun x => hDtail ht x i j
  have hsumInt (j : Fin 3) : Integrable
      (fun x : Vec3 => ∑ i : Fin 3,
        CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x) volume :=
    integrable_finsetSum Finset.univ (fun i hi => htermInt i j)
  have hsumNonneg (j : Fin 3) : 0 ≤ ∫ x : Vec3, ∑ i : Fin 3,
      CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x := by
    apply integral_nonneg
    intro x
    simpa [f, g] using
      heatRegTest_spatialDissipation_nonneg hb hbc ht hη x j
  have hswap : (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
      CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x) =
      ∑ j : Fin 3, ∫ x : Vec3, ∑ i : Fin 3,
        CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    symm
    exact integral_finsetSum Finset.univ (fun i hi => htermInt i j)
  have hsumNonneg' : 0 ≤ ∑ j : Fin 3, ∫ x : Vec3, ∑ i : Fin 3,
      CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x :=
    Finset.sum_nonneg fun j _ => hsumNonneg j
  have hderiv := heatRegEnergy_integral_hasDerivAt hb hbc ht hη
  calc
    deriv (fun s : ℝ => ∫ x : Vec3,
        heatRegEnergy η (heatConvVec3 s b x)) t =
      ∫ x : Vec3, ∑ i : Fin 3,
        heatRegTest η (heatConvVec3 t b x) i *
          heatConv t (CKN.spatialLaplacian (fun y => b y i)) x := hderiv.deriv
    _ = -∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x :=
      heatRegEnergy_integral_derivative_eq_neg_gradient hb hbc ht hη
    _ = -∑ j : Fin 3, ∫ x : Vec3, ∑ i : Fin 3,
          CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x := by
      rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv (f i) j x * CKN.spatialDeriv (g i) j x by
          rfl]
      rw [hswap]
    _ ≤ 0 := neg_nonpos.mpr hsumNonneg'

/-- The regularized entropy integral decreases on positive times, as used in
`lem:pv-heat-critical`. -/
theorem heatRegEnergy_integral_antitoneOn
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    (η : ℝ) (hη : 0 < η) :
    AntitoneOn (fun t : ℝ => ∫ x : Vec3,
      heatRegEnergy η (heatConvVec3 t b x)) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    exact (heatRegEnergy_integral_hasDerivAt hb hbc ht' hη).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    exact (heatRegEnergy_integral_hasDerivAt hb hbc ht' hη).hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    have hderiv := heatRegEnergy_integral_hasDerivAt hb hbc ht' hη
    have hnonpos := heatRegEnergy_integral_deriv_nonpos hb hbc ht' hη
    simpa only [hderiv.deriv] using hnonpos

/-- The regularized entropy integrals converge to their initial value as time
decreases to zero, as used in `lem:pv-heat-critical`. -/
theorem heatRegEnergy_integral_tendsto_initial
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun t : ℝ => ∫ x : Vec3,
      heatRegEnergy η (heatConvVec3 t b x))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhds (∫ x : Vec3, heatRegEnergy η (b x))) := by
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_norm_decay hb hbc
  let F : ℝ → Vec3 → ℝ := fun t x =>
    heatRegEnergy η (heatConvVec3 t b x)
  let F₀ : Vec3 → ℝ := fun x => heatRegEnergy η (b x)
  let K : ℝ := (3 * η + 2 * M) / 6
  let C : ℝ := K * M ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hden (x : Vec3) : 1 ≤ 1 + vec3EuclideanNorm x := by
    linarith only [vec3EuclideanNorm_nonneg x]
  have hdenpow (x : Vec3) (k : ℕ) :
      1 ≤ (1 + vec3EuclideanNorm x) ^ k :=
    one_le_pow₀ (hden x)
  have hprofile (t : ℝ) (ht : 0 < t) :
      ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have huniform (t : ℝ) (ht : 0 < t) (x : Vec3) :
    vec3EuclideanNorm (heatConvVec3 t b x) ≤ M := by
    have htail := hMtail ht x
    have hMquot : M / (1 + vec3EuclideanNorm x) ^ 3 ≤ M := by
      apply (div_le_iff₀
        (lt_of_lt_of_le zero_lt_one (hdenpow x 3))).2
      calc
        M = M * 1 := by ring
        _ ≤ M * (1 + vec3EuclideanNorm x) ^ 3 :=
          mul_le_mul_of_nonneg_left (hdenpow x 3) hM
    exact htail.trans hMquot
  have henergyBound (t : ℝ) (ht : 0 < t) (x : Vec3) :
      heatRegEnergy η (heatConvVec3 t b x) ≤
        C / (1 + vec3EuclideanNorm x) ^ 6 := by
    have htail := hMtail ht x
    have hnormSq : (vec3EuclideanNorm (heatConvVec3 t b x)) ^ 2 ≤
        (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) htail 2
    have hsum : (∑ i : Fin 3, (heatConvVec3 t b x i) ^ 2) =
        (vec3EuclideanNorm (heatConvVec3 t b x)) ^ 2 := by
      unfold vec3EuclideanNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have henergy := heatRegEnergy_le_mul_sum_sq hη hM
      (heatConvVec3 t b x) (huniform t ht x)
    calc
      heatRegEnergy η (heatConvVec3 t b x) ≤
          K * ∑ i : Fin 3, (heatConvVec3 t b x i) ^ 2 := by
            simpa [K] using henergy
      _ = K * (vec3EuclideanNorm (heatConvVec3 t b x)) ^ 2 := by rw [hsum]
      _ ≤ K * (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left hnormSq hK
      _ = C / (1 + vec3EuclideanNorm x) ^ 6 := by
        dsimp [C, K]
        rw [div_pow, ← pow_mul]
        ring
  have hmeas : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      AEStronglyMeasurable (F t) volume := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hcont : Continuous (F t) := by
      change Continuous (fun x : Vec3 =>
        heatRegEnergy η (heatConvVec3 t b x))
      exact ((heatRegEnergy_contDiff hη).comp (hprofile t htpos)).continuous
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      ∀ᵐ x : Vec3 ∂volume, ‖F t x‖ ≤
        C / (1 + vec3EuclideanNorm x) ^ 6 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [] with x
    rw [show F t x = heatRegEnergy η (heatConvVec3 t b x) by rfl,
      Real.norm_eq_abs,
      abs_of_nonneg (heatRegEnergy_nonneg hη (heatConvVec3 t b x))]
    exact henergyBound t ht x
  have hpointwise (x : Vec3) :
      Tendsto (fun t : ℝ => F t x)
        (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (F₀ x)) := by
    have hvec : Tendsto (fun t : ℝ => heatConvVec3 t b x)
        (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (b x)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simpa [heatConvVec3] using
        heatConv_tendsto_self_nhdsWithin_zero_smooth (hb i) (hbc i) x
    have hcont : ContinuousAt (heatRegEnergy η) (b x) :=
      (heatRegEnergy_contDiff hη).continuous.continuousAt
    exact hcont.tendsto.comp hvec
  have hpointwiseAE : ∀ᵐ x : Vec3 ∂volume,
      Tendsto (fun t : ℝ => F t x)
        (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (F₀ x)) :=
    Filter.Eventually.of_forall hpointwise
  have hmajorant : Integrable
      (fun x : Vec3 => C / (1 + vec3EuclideanNorm x) ^ 6) volume :=
    heat_decay_six_integrable C hC
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (fun x : Vec3 => C / (1 + vec3EuclideanNorm x) ^ 6)
    hmeas hbound hmajorant hpointwiseAE
  simpa [F, F₀] using hmain

/-- The regularized entropy of a smooth heat orbit is bounded by its initial
entropy; this is the time-integrated form used in `lem:pv-heat-critical`. -/
theorem heatRegEnergy_integral_le_initial
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    (∫ x : Vec3, heatRegEnergy η (heatConvVec3 t b x)) ≤
      ∫ x : Vec3, heatRegEnergy η (b x) := by
  let F : ℝ → ℝ := fun s => ∫ x : Vec3, heatRegEnergy η (heatConvVec3 s b x)
  have hanti := heatRegEnergy_integral_antitoneOn hb hbc η hη
  have hlim := heatRegEnergy_integral_tendsto_initial hb hbc η hη
  have hsmall : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), s < t :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  have hle : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), F t ≤ F s := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hst
    exact hanti hs ht (le_of_lt hst)
  have hconst : Tendsto (fun _ : ℝ => F t)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (F t)) :=
    tendsto_const_nhds
  have hresult := le_of_tendsto_of_tendsto hconst hlim hle
  exact hresult

end ESS

end
