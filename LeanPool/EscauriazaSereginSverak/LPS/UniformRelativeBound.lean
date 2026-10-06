/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceBound
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Convection

/-!
# Uniform Relative Bound

The coefficient in Young's inequality for the conjugate exponents
2 / (1 + θ) and 2 / (1 - θ).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_eLpNorm_interpolate_two_six
    {f : Vec3 → Vec3} {q : ℝ}
    (hq2 : 2 < q) (hq6 : q < 6) (hf : AEStronglyMeasurable f volume) :
    eLpNorm f (ENNReal.ofReal q) volume ≤
      eLpNorm f 2 volume ^ (1 - 3 * (1 / 2 - 1 / q)) *
        eLpNorm f 6 volume ^ (3 * (1 / 2 - 1 / q)) := by
  let μ : Measure Vec3 := volume
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 3 * (1 / 2 - 1 / q) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by
    rw [hθ]
    have hq0 : 0 < q := by linarith only [hq2]
    have h : 1 / q < 1 / 2 := by
      rw [div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)]
      linarith only [hq2]
    linarith only [h]
  have hθ1 : θ < 1 := by
    rw [hθ]
    have hq0 : 0 < q := by linarith only [hq2]
    have h : 1 / 6 < 1 / q := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 6) hq0]
      linarith only [hq6]
    linarith only [h]
  have hq0 : 0 < q := by linarith only [hq2]
  let P : ℝ := 2 / (1 - θ)
  let S : ℝ := 6 / θ
  have hP : 0 < P := by dsimp [P]; exact div_pos (by norm_num) (sub_pos.mpr hθ1)
  have hS : 0 < S := by dsimp [S]; exact div_pos (by norm_num) hθ0
  have hrecip : P⁻¹ + S⁻¹ = q⁻¹ := by
    dsimp [P, S]
    rw [inv_div, inv_div, hθ]
    field_simp
    ring
  have hHolder : ENNReal.HolderTriple (ENNReal.ofReal P) (ENNReal.ofReal S)
      (ENNReal.ofReal q) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos hP, ← ENNReal.ofReal_inv_of_pos hS,
      ← ENNReal.ofReal_inv_of_pos hq0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), hrecip]
  have hw : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 - θ)) μ := by
    simpa [Function.comp_def] using
      ((Real.continuous_rpow_const (q := 1 - θ) (by linarith only
        [hθ1])).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun x => ‖f x‖ ^ θ) μ := by
    simpa [Function.comp_def] using
      ((Real.continuous_rpow_const (q := θ) hθ0.le).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hprod : (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ) = fun x => ‖f x‖ := by
    funext x
    by_cases hx : ‖f x‖ = 0
    · rw [hx, Real.zero_rpow (by linarith only [hθ1]),
        Real.zero_rpow hθ0.ne', zero_mul]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx))]
      norm_num
  have hHolderNorm : eLpNorm (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ)
      (ENNReal.ofReal q) μ ≤
      eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) (ENNReal.ofReal P) μ *
        eLpNorm (fun x => ‖f x‖ ^ θ) (ENNReal.ofReal S) μ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (μ := μ) (p := ENNReal.ofReal P) (q := ENNReal.ofReal S)
      (r := ENNReal.ofReal q) (fun a b : ℝ => a * b) 1 continuous_mul hw hv
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, one_mul])
    simpa [ENNReal.smul_def, one_mul] using h
  have hwp : eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) (ENNReal.ofReal P) μ =
      eLpNorm f 2 μ ^ (1 - θ) := by
    have hraw := eLpNorm_norm_rpow f hf (q := 1 - θ) (by linarith only [hθ1])
      (p := ENNReal.ofReal P)
    have hPe : ENNReal.ofReal P * ENNReal.ofReal (1 - θ) = 2 := by
      rw [← ENNReal.ofReal_mul hP.le]
      dsimp [P]
      rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hθ1))]
      norm_num
    rw [hPe] at hraw
    simpa using hraw
  have hvs : eLpNorm (fun x => ‖f x‖ ^ θ) (ENNReal.ofReal S) μ =
      eLpNorm f 6 μ ^ θ := by
    have hraw := eLpNorm_norm_rpow f hf (q := θ) hθ0 (p := ENNReal.ofReal S)
    have hSe : ENNReal.ofReal S * ENNReal.ofReal θ = 6 := by
      rw [← ENNReal.ofReal_mul hS.le]
      dsimp [S]
      rw [div_mul_cancel₀ _ hθ0.ne']
      norm_num
    rw [hSe] at hraw
    simpa using hraw
  rw [hprod, eLpNorm_norm f hf, hwp, hvs] at hHolderNorm
  rw [← hθ]
  exact hHolderNorm

private theorem lps_holder_real_exponents {s q : ℝ}
    (hs : 3 < s) (hq : q = 2 * s / (s - 2)) :
    (s⁻¹ + q⁻¹ = (2 : ℝ)⁻¹) ∧ (2 < q ∧ q < 6) := by
  have hs2 : 0 < s - 2 := by linarith only [hs]
  constructor
  · rw [hq]
    field_simp
    ring
  · constructor
    · rw [hq]
      rw [lt_div_iff₀ hs2]
      nlinarith only [hs]
    · rw [hq]
      rw [div_lt_iff₀ hs2]
      nlinarith only [hs]

/-- The coefficient in Young's inequality for the conjugate exponents
2 / (1 + θ) and 2 / (1 - θ). -/
@[expose] def lps_power_young_coefficient (θ : ℝ) : ℝ :=
  let p : ℝ := 2 / (1 + θ)
  let q : ℝ := 2 / (1 - θ)
  let lam : ℝ := (p / 2) ^ (1 / p)
  (lam⁻¹ ^ q) / q

private theorem lps_power_young {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    A * B ^ (1 - θ) * D ^ (1 + θ) ≤
      (1 / 2 : ℝ) * D ^ 2 + lps_power_young_coefficient θ *
        A ^ (2 / (1 - θ)) * B ^ 2 := by
  let p : ℝ := 2 / (1 + θ)
  let q : ℝ := 2 / (1 - θ)
  let lam : ℝ := (p / 2) ^ (1 / p)
  let X : ℝ := lam * D ^ (1 + θ)
  let Y : ℝ := A * B ^ (1 - θ) * lam⁻¹
  let C : ℝ := (lam⁻¹ ^ q) / q
  have hp0 : 0 < p := by
    dsimp [p]
    exact div_pos (by norm_num) (by linarith only [hθ0])
  have hq0 : 0 < q := by
    dsimp [q]
    exact div_pos (by norm_num) (sub_pos.mpr hθ1)
  have hpq : p⁻¹ + q⁻¹ = 1 := by
    dsimp [p, q]
    field_simp
    ring
  have hconj : p.HolderConjugate q := ⟨by simpa using hpq, hp0, hq0⟩
  have hLam : 0 < lam := by
    dsimp [lam]
    exact Real.rpow_pos_of_pos (div_pos hp0 (by norm_num)) _
  have hLamPow : lam ^ p = p / 2 := by
    dsimp [lam]
    rw [← Real.rpow_mul (by positivity : 0 ≤ p / 2)]
    have hpow : (1 / p) * p = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  have hθp : (1 + θ) * p = 2 := by
    dsimp [p]
    field_simp [ne_of_gt (by positivity : 0 < 1 + θ)]
  have hθq : (1 - θ) * q = 2 := by
    dsimp [q]
    field_simp [ne_of_gt (sub_pos.mpr hθ1)]
  have hXnonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hYnonneg : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have hYoung := Real.young_inequality_of_nonneg hXnonneg hYnonneg hconj
  have hXpow : X ^ p / p = (1 / 2 : ℝ) * D ^ 2 := by
    dsimp [X]
    rw [Real.mul_rpow (le_of_lt hLam) (Real.rpow_nonneg hD _), hLamPow,
      ← Real.rpow_mul hD]
    rw [hθp]
    field_simp [hp0.ne']
    rw [← Real.rpow_natCast D 2]
    rfl
  have hYpow : Y ^ q / q = C * A ^ q * B ^ 2 := by
    dsimp [Y, C]
    rw [show A * B ^ (1 - θ) * lam⁻¹ = A * (B ^ (1 - θ) * lam⁻¹) by ring]
    rw [Real.mul_rpow hA (mul_nonneg (Real.rpow_nonneg hB _) (inv_nonneg.mpr hLam.le)),
      Real.mul_rpow (Real.rpow_nonneg hB _) (inv_nonneg.mpr hLam.le),
      ← Real.rpow_mul hB, hθq]
    field_simp [hq0.ne']
    rw [← Real.rpow_natCast B 2]
    rfl
  have hXY : X * Y = A * B ^ (1 - θ) * D ^ (1 + θ) := by
    dsimp [X, Y]
    field_simp [ne_of_gt hLam]
  have hYoung' : A * B ^ (1 - θ) * D ^ (1 + θ) ≤
      (1 / 2 : ℝ) * D ^ 2 + lps_power_young_coefficient θ *
        A ^ (2 / (1 - θ)) * B ^ 2 := by
    calc
      A * B ^ (1 - θ) * D ^ (1 + θ) = X * Y := hXY.symm
      _ ≤ X ^ p / p + Y ^ q / q := hYoung
      _ = (1 / 2 : ℝ) * D ^ 2 +
          lps_power_young_coefficient θ * A ^ (2 / (1 - θ)) * B ^ 2 := by
        rw [hXpow, hYpow]
        dsimp [C, lps_power_young_coefficient, p, q, lam]
  exact hYoung'

private theorem lps_vector_six_bound
    {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hH1 : ∀ _i : Fin 3, H1Function (Set.univ : Set Vec3))
    (hFun : ∀ i : Fin 3, (hH1 i).toFun = fun x => w x i)
    (hGrad : ∀ i : Fin 3, (hH1 i).grad = fun x j => Dw x i j) :
    eLpNorm w 6 volume ≤
      (6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
  let Wsum : Vec3 → ℝ := fun x => ∑ i : Fin 3, |w x i|
  have hWsumNonneg (x : Vec3) : 0 ≤ Wsum x := by
    dsimp [Wsum]
    positivity
  have hpoint (x : Vec3) : ‖w x‖ ≤ Wsum x := by
    apply (pi_norm_le_iff_of_nonneg (hWsumNonneg x)).2
    intro i
    dsimp [Wsum]
    calc
      ‖w x i‖ = |w x i| := Real.norm_eq_abs _
      _ ≤ ∑ j : Fin 3, |w x j| :=
        Finset.single_le_sum (f := fun j : Fin 3 => |w x j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hvector : eLpNorm w 6 volume ≤ eLpNorm Wsum 6 volume :=
    eLpNorm_mono_ae_real hw2.aestronglyMeasurable (Eventually.of_forall hpoint)
  have hsumEq : Wsum = ∑ i : Fin 3, (fun x : Vec3 => |w x i|) := by
    funext x
    rfl
  have hsum : eLpNorm Wsum 6 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => |w x i|) 6 volume := by
    rw [hsumEq]
    exact eLpNorm_sum_le (p := (6 : ℝ≥0∞)) (s := Finset.univ)
      (f := fun i : Fin 3 => (fun x => |w x i|)) (by norm_num)
  have hcomp (i : Fin 3) : eLpNorm (fun x => |w x i|) 6 volume ≤
      2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
    have hcoord : AEStronglyMeasurable (fun x => w x i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hw2.aestronglyMeasurable
    have habs : eLpNorm (fun x => |w x i|) 6 volume = eLpNorm (fun x => w x i) 6 volume := by
      rw [← eLpNorm_norm (fun x => w x i) hcoord]
      exact eLpNorm_congr_ae (Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
    rw [habs]
    calc
      eLpNorm (fun x => w x i) 6 volume = eLpNorm (hH1 i).toFun 6 volume := by
        rw [hFun i]
      _ ≤ gagliardoNirenbergSobolevConstant *
          eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume :=
        LPS.lps_h1_component_six (hH1 i)
      _ ≤ 2 * gagliardoNirenbergSobolevConstant *
          eLpNorm Dw 2 volume := by
        have hrowMem : MemLp (fun x => (hH1 i).grad x) 2 volume := by
          apply (memLp_pi_iff).2
          intro j
          simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
            (hH1 i).gradMemL2 j
        have hrowPoint (x : Vec3) :
            vec3EuclideanNorm ((hH1 i).grad x) ≤ 2 * ‖Dw x‖ := by
          rw [hGrad i]
          have hrow : ‖(fun j => Dw x i j : Vec3)‖ ≤ ‖Dw x‖ := norm_le_pi_norm (Dw x) i
          have hsqrt : Real.sqrt 3 ≤ 2 := by
            nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
          calc
            vec3EuclideanNorm (fun j => Dw x i j) ≤
                Real.sqrt 3 * ‖(fun j => Dw x i j : Vec3)‖ :=
              vec3EuclideanNorm_le_sqrt_three_mul_norm _
            _ ≤ Real.sqrt 3 * ‖Dw x‖ := mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg 3)
            _ ≤ 2 * ‖Dw x‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
        have hrowNormMeas : AEStronglyMeasurable
            (fun x => vec3EuclideanNorm ((hH1 i).grad x)) volume :=
          continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hrowMem.aestronglyMeasurable
        have hrowPoint' (x : Vec3) :
            ‖vec3EuclideanNorm ((hH1 i).grad x)‖ ≤ 2 * ‖‖Dw x‖‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hrowPoint x
        have hscaled := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hrowNormMeas
          (Eventually.of_forall hrowPoint') (2 : ℝ≥0∞)
        have hrowLe : eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume ≤
            2 * eLpNorm Dw 2 volume := by
          have hDwNorm : eLpNorm (fun x => ‖Dw x‖) 2 volume = eLpNorm Dw 2 volume :=
            eLpNorm_norm Dw hDw2.aestronglyMeasurable
          rw [hDwNorm] at hscaled
          norm_num at hscaled ⊢
          exact hscaled
        calc
          gagliardoNirenbergSobolevConstant *
              eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume ≤
              gagliardoNirenbergSobolevConstant * (2 * eLpNorm Dw 2 volume) := by
            gcongr
          _ = 2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by ring
  calc
    eLpNorm w 6 volume ≤ eLpNorm Wsum 6 volume := hvector
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |w x i|) 6 volume := hsum
    _ ≤ ∑ _i : Fin 3,
        2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume :=
      Finset.sum_le_sum fun i _ => hcomp i
    _ = (6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

private theorem lps_vector_spatial_q_bound
    {s : ℝ} (hs : 3 < s)
    {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i)) :
    eLpNorm w (ENNReal.ofReal (2 * s / (s - 2))) volume ≤
      ((6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant) ^ (3 / s : ℝ) *
        eLpNorm w 2 volume ^ (1 - 3 / s : ℝ) *
          eLpNorm Dw 2 volume ^ (3 / s : ℝ) := by
  let q : ℝ := 2 * s / (s - 2)
  have hq : q = 2 * s / (s - 2) := rfl
  obtain ⟨_, hq2, hq6⟩ := lps_holder_real_exponents hs hq
  let hH1 : ∀ i : Fin 3, H1Function (Set.univ : Set Vec3) := fun i =>
    { toFun := fun x => w x i
      grad := fun x => Dw x i
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          hw2.eval i
      gradMemL2 := by
        intro j
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (hDw2.eval i).eval j
      hasWeakGradient := hgrad i }
  have hL6 := lps_vector_six_bound hw2 hDw2 hH1
    (fun i => by dsimp [hH1])
    (fun i => by dsimp [hH1])
  have hinterp := lps_eLpNorm_interpolate_two_six hq2 hq6 hw2.aestronglyMeasurable
  have htheta : 3 * (1 / 2 - 1 / q) = 3 / s := by
    dsimp [q]
    field_simp
    ring
  have hbase : eLpNorm w (ENNReal.ofReal q) volume ≤
      eLpNorm w 2 volume ^ (1 - 3 / s : ℝ) *
        eLpNorm w 6 volume ^ (3 / s : ℝ) := by
    rw [htheta] at hinterp
    exact hinterp
  have hsob : eLpNorm w 6 volume ≤
      (6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := hL6
  calc
    eLpNorm w (ENNReal.ofReal q) volume ≤
        eLpNorm w 2 volume ^ (1 - 3 / s : ℝ) *
          eLpNorm w 6 volume ^ (3 / s : ℝ) := hbase
    _ ≤ eLpNorm w 2 volume ^ (1 - 3 / s : ℝ) *
          ((6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume) ^
        (3 / s : ℝ) := by
      gcongr
    _ = ((6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant) ^ (3 / s : ℝ) *
          eLpNorm w 2 volume ^ (1 - 3 / s : ℝ) *
            eLpNorm Dw 2 volume ^ (3 / s : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 3 / s)]
      ac_rfl

/-- The squared `L²` norm of a field is bounded by the integral of any integrable
pointwise majorant of its squared norm. -/
theorem lps_sq_eLpNorm_le
    {E : Type} [NormedAddCommGroup E] {w : Vec3 → E}
    (hw : MemLp w 2 volume) (S : Vec3 → ℝ)
    (hpoint : ∀ x, ‖w x‖ ^ 2 ≤ S x) (hSint : Integrable S volume) :
    (eLpNorm w 2 volume).toReal ^ 2 ≤ ∫ x : Vec3, S x := by
  have hint : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  have heq : (eLpNorm w 2 volume).toReal ^ 2 = ∫ x : Vec3, ‖w x‖ ^ 2 := by
    have hnn : 0 ≤ ∫ x : Vec3, ‖w x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
    rw [hw.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    simp only [ENNReal.toReal_ofNat]
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hinv, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
    congr 1
    funext x
    exact Real.rpow_two _
  rw [heq]
  exact integral_mono hint hSint hpoint

/-- The squared sup norm of a vector is at most the sum of squares of its entries. -/
theorem lps_norm_sq_le_sum_sq (w : Vec3) :
    ‖w‖ ^ 2 ≤ ∑ i : Fin 3, w i ^ 2 := by
  have hsum : 0 ≤ ∑ i : Fin 3, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm : ‖w‖ ≤ Real.sqrt (∑ i : Fin 3, w i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j : Fin 3 => w j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc
    ‖w‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, w i ^ 2) ^ 2 := by gcongr
    _ = ∑ i : Fin 3, w i ^ 2 := Real.sq_sqrt hsum

/-- The squared sup norm of a matrix is at most the sum of squares of its entries. -/
theorem lps_norm_sq_le_sum_sq₂ (Dw : Fin 3 → Vec3) :
    ‖Dw‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2 := by
  have hsum : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnorm : ‖Dw‖ ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    calc
      ‖Dw i‖ ^ 2 ≤ ∑ j : Fin 3, Dw i j ^ 2 := lps_norm_sq_le_sum_sq (Dw i)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2 :=
        Finset.single_le_sum (f := fun i : Fin 3 => ∑ j : Fin 3, Dw i j ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc
    ‖Dw‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2) ^ 2 := by gcongr
    _ = ∑ i : Fin 3, ∑ j : Fin 3, Dw i j ^ 2 := Real.sq_sqrt hsum

private theorem lps_triple_pointwise (u w : Vec3) (Dw : Fin 3 → Vec3) :
    |∑ i : Fin 3, u i * ∑ j : Fin 3, w j * Dw i j| ≤
      9 * (‖u‖ * ‖w‖ * ‖Dw‖) := by
  have hu (i : Fin 3) : |u i| ≤ ‖u‖ := norm_le_pi_norm u i
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := norm_le_pi_norm w j
  have hD (i j : Fin 3) : |Dw i j| ≤ ‖Dw‖ :=
    (norm_le_pi_norm (Dw i) j).trans (norm_le_pi_norm Dw i)
  calc
    |∑ i : Fin 3, u i * ∑ j : Fin 3, w j * Dw i j| ≤
        ∑ i : Fin 3, ∑ j : Fin 3, |u i| * (|w j| * |Dw i j|) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖u‖ * (‖w‖ * ‖Dw‖) := by
      gcongr with i _ j _
      · exact hu i
      · exact hw j
      · exact hD i j
    _ = 9 * (‖u‖ * ‖w‖ * ‖Dw‖) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Pointwise bound of the trilinear convection form by the Euclidean norm of the
first factor and the sup norms of the others. -/
theorem lps_triple_pointwise_euclidean (u w : Vec3) (Dw : Fin 3 → Vec3) :
    |∑ i : Fin 3, u i * ∑ j : Fin 3, w j * Dw i j| ≤
      9 * (vec3EuclideanNorm u * ‖w‖ * ‖Dw‖) := by
  have hu (i : Fin 3) : |u i| ≤ vec3EuclideanNorm u := by
    calc
      |u i| = ‖u i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖u‖ := norm_le_pi_norm u i
      _ ≤ vec3EuclideanNorm u := CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm u
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := norm_le_pi_norm w j
  have hD (i j : Fin 3) : |Dw i j| ≤ ‖Dw‖ :=
    (norm_le_pi_norm (Dw i) j).trans (norm_le_pi_norm Dw i)
  calc
    |∑ i : Fin 3, u i * ∑ j : Fin 3, w j * Dw i j| ≤
        ∑ i : Fin 3, ∑ j : Fin 3, |u i| * (|w j| * |Dw i j|) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3,
        vec3EuclideanNorm u * (‖w‖ * ‖Dw‖) := by
      gcongr with i _ j _
      · exact vec3EuclideanNorm_nonneg _
      · exact hu i
      · exact hw j
      · exact hD i j
    _ = 9 * (vec3EuclideanNorm u * ‖w‖ * ‖Dw‖) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem lps_integral_triple_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hrecip : p⁻¹ + q⁻¹ = (2 : ℝ)⁻¹)
    {u w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hu : MemLp (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume)
    (hw : MemLp w (ENNReal.ofReal q) volume)
    (hDw : MemLp Dw 2 volume) :
    ∫ x : Vec3, vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ ≤
      (eLpNorm (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume).toReal *
        (eLpNorm w (ENNReal.ofReal q) volume).toReal * (eLpNorm Dw 2 volume).toReal := by
  have H1 : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q)
      (ENNReal.ofReal 2) :=
    serrin_holder_ofReal3 hp hq (by norm_num) hrecip
  have H2 : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    simpa using (serrin_holder_ofReal3 (p := 2) (q := 2) (r := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h12mem : MemLp (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖) 2 volume := by
    change MemLp ((fun x : Vec3 => vec3EuclideanNorm (u x)) *
      (fun x : Vec3 => ‖w x‖)) 2 volume
    have H1' : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 2 := by
      simpa only [ENNReal.ofReal_ofNat] using H1
    exact MemLp.mul hu hw.norm (hpqr := H1')
  have hprodBound : eLpNorm (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume *
        eLpNorm w (ENNReal.ofReal q) volume *
        eLpNorm Dw 2 volume := by
    have h12Bound : eLpNorm (fun x : Vec3 =>
        vec3EuclideanNorm (u x) * ‖w x‖) 2 volume ≤
        eLpNorm (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume *
          eLpNorm w (ENNReal.ofReal q) volume := by
      have h12Raw := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal p) (q := ENNReal.ofReal q) (r := ENNReal.ofReal 2)
        (fun a b : ℝ => a * b) 1 continuous_mul hu.aestronglyMeasurable
        hw.aestronglyMeasurable.norm
        (Eventually.of_forall fun x => by
          change ‖vec3EuclideanNorm (u x) * ‖w x‖‖ ≤
            (1 : ℝ) * ‖vec3EuclideanNorm (u x)‖ * ‖‖w x‖‖
          rw [norm_mul]
          simp)
        (hpqr := H1)
      rw [ENNReal.ofReal_ofNat] at h12Raw
      have h12Raw' : eLpNorm (fun x : Vec3 =>
          vec3EuclideanNorm (u x) * ‖w x‖) 2 volume ≤
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume *
            eLpNorm (fun x : Vec3 => ‖w x‖) (ENNReal.ofReal q) volume := by
        simpa only [ENNReal.coe_one, Pi.mul_apply, one_mul] using h12Raw
      simpa only [eLpNorm_norm w hw.aestronglyMeasurable] using h12Raw'
    have h3 := eLpNorm_smul_le_mul_eLpNorm (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (r := (1 : ℝ≥0∞)) h12mem.aestronglyMeasurable hDw.aestronglyMeasurable.norm
    have h3' : eLpNorm (fun x : Vec3 =>
        vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume ≤
        eLpNorm (fun x => vec3EuclideanNorm (u x) * ‖w x‖) 2 volume *
          eLpNorm Dw 2 volume := by
      change eLpNorm ((fun x : Vec3 => vec3EuclideanNorm (u x) * ‖w x‖) *
        (fun x : Vec3 => ‖Dw x‖)) 1 volume ≤ _
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        eLpNorm_norm Dw hDw.aestronglyMeasurable] using h3
    calc
      _ ≤ eLpNorm (fun x => vec3EuclideanNorm (u x) * ‖w x‖) 2 volume *
          eLpNorm Dw 2 volume := h3'
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right h12Bound (by positivity)
  have hprod : Integrable (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) volume := by
    exact memLp_one_iff_integrable.mp
      (MemLp.mul (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := 1)
        h12mem hDw.norm (hpqr := H2))
  have hnonneg (x : Vec3) :
      0 ≤ vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ :=
    mul_nonneg (mul_nonneg (vec3EuclideanNorm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hfin : eLpNorm (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume *
      eLpNorm w (ENNReal.ofReal q) volume *
      eLpNorm Dw 2 volume ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hu.eLpNorm_ne_top hw.eLpNorm_ne_top)
      hDw.eLpNorm_ne_top
  have hmeas : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) volume :=
    (hu.aestronglyMeasurable.mul hw.aestronglyMeasurable.norm).mul
      hDw.aestronglyMeasurable.norm
  calc
    ∫ x : Vec3, vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ =
        (eLpNorm (fun x : Vec3 =>
          vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnonneg) hmeas,
        eLpNorm_one_eq_lintegral_enorm hmeas]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal (hnonneg x)]
    _ ≤ (eLpNorm (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal p) volume *
        eLpNorm w (ENNReal.ofReal q) volume *
        eLpNorm Dw 2 volume).toReal := ENNReal.toReal_mono hfin hprodBound
    _ = _ := by simp only [ENNReal.toReal_mul]

private theorem lps_slice_square_integrable_gradient
    {Dw : Vec3 → Fin 3 → Vec3} (hDw2 : MemLp Dw 2 volume) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) volume := by
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (memLp_two_iff_integrable_sq_norm ((hDw2.eval i).eval j).aestronglyMeasurable).mp
      ((hDw2.eval i).eval j) |>.congr (Eventually.of_forall fun x => by simp)

private theorem lps_slice_square_integrable_velocity
    {w : Vec3 → Vec3} (hw2 : MemLp w 2 volume) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, w x i ^ 2) volume := by
  exact integrable_finsetSum _ fun i _ =>
    (memLp_two_iff_integrable_sq_norm (hw2.eval i).aestronglyMeasurable).mp
      (hw2.eval i) |>.congr (Eventually.of_forall fun x => by simp)

/-- Fixed-time relative convection estimate for a finite Serrin exponent. The
coefficient is the distinguished field's spatial `L^s` norm raised to the
critical power `2s/(s-3)`, as in `lem:lps-comparison`. -/
theorem lps_slice_relative_bound_finite_uniform {s : ℝ} (hs : 3 < s)
    {u w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (huMeas : AEStronglyMeasurable u volume)
    (huS : MemLp (fun x => vec3EuclideanNorm (u x)) (ENNReal.ofReal s) volume)
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i)) :
    |∫ x : Vec3, ∑ i : Fin 3, u x i * ∑ j : Fin 3, w x j * Dw x i j| ≤
      (1 / 2 : ℝ) * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) +
        (lps_power_young_coefficient (3 / s) *
          (9 * ((6 : ℝ) * gagliardoNirenbergSobolevConstant.toReal) ^ (3 / s)) ^
            (2 * s / (s - 3))) *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x))
            (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3)) *
          (∫ x : Vec3, ∑ i : Fin 3, w x i ^ 2) := by
  let q : ℝ := 2 * s / (s - 2)
  let θ : ℝ := 3 / s
  let Cg : ℝ := ((6 : ℝ) * gagliardoNirenbergSobolevConstant.toReal) ^ θ
  let U : ℝ := (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x))
    (ENNReal.ofReal s) volume).toReal
  let W : ℝ := (eLpNorm w 2 volume).toReal
  let D : ℝ := (eLpNorm Dw 2 volume).toReal
  let N : ℝ := (eLpNorm w (ENNReal.ofReal q) volume).toReal
  have hs0 : 0 < s := by linarith only [hs]
  have hq : q = 2 * s / (s - 2) := rfl
  obtain ⟨hrecip, hq2, _⟩ := lps_holder_real_exponents hs hq
  have hq0 : 0 < q := by linarith only [hq2]
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one hs0]
    linarith only [hs]
  have hell : 2 / (1 - θ) = 2 * s / (s - 3) := by
    dsimp [θ]
    field_simp [ne_of_gt hs0]
  have hinterp := lps_vector_spatial_q_bound hs hw2 hDw2 hgrad
  have hfiniteQ :
      ((6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant) ^ (3 / s : ℝ) *
      eLpNorm w 2 volume ^ (1 - 3 / s : ℝ) *
          eLpNorm Dw 2 volume ^ (3 / s : ℝ) ≠ ⊤ := by
    have hGN : gagliardoNirenbergSobolevConstant ≠ ⊤ :=
      (Classical.choose_spec CKN.sobolev_L6_global).1
    have hW := hw2.eLpNorm_ne_top
    have hD := hDw2.eLpNorm_ne_top
    finiteness
  have hwq : MemLp w (ENNReal.ofReal q) volume := by
    change eLpNorm w (ENNReal.ofReal q) volume < ⊤
    exact lt_of_le_of_lt hinterp hfiniteQ.lt_top
  have hN : N ≤ Cg * W ^ (1 - θ) * D ^ θ := by
    have h := ENNReal.toReal_mono hfiniteQ hinterp
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofNat] at h
    change N ≤ Cg * W ^ (1 - θ) * D ^ θ at h
    exact h
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hCg0 : 0 ≤ Cg := Real.rpow_nonneg (by positivity) _
  have hqHolder : ENNReal.HolderTriple (ENNReal.ofReal s)
      (ENNReal.ofReal q) (ENNReal.ofReal 2) :=
    serrin_holder_ofReal3 (by linarith only [hs]) hq0 (by norm_num) hrecip
  have h12 : MemLp (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖) 2 volume := by
    change MemLp ((fun x : Vec3 => vec3EuclideanNorm (u x)) *
      (fun x : Vec3 => ‖w x‖)) 2 volume
    have hqHolder' : ENNReal.HolderTriple (ENNReal.ofReal s)
        (ENNReal.ofReal q) 2 := by
      simpa only [ENNReal.ofReal_ofNat] using hqHolder
    exact MemLp.mul huS hwq.norm (hpqr := hqHolder')
  have hHolder22 : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    simpa using (serrin_holder_ofReal3 (p := 2) (q := 2) (r := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hprodMem : MemLp (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) 1 volume := by
    change MemLp (((fun x : Vec3 => vec3EuclideanNorm (u x) * ‖w x‖) *
      (fun x : Vec3 => ‖Dw x‖))) 1 volume
    exact MemLp.mul h12 hDw2.norm (hpqr := hHolder22)
  have hprodInt : Integrable (fun x : Vec3 =>
      vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) volume :=
    memLp_one_iff_integrable.mp hprodMem
  have hprodBound := lps_integral_triple_le (by linarith only [hs]) hq0 hrecip huS hwq hDw2
  let B : Vec3 × (Vec3 × (Fin 3 → Vec3)) → ℝ := fun z =>
    ∑ i : Fin 3, z.1 i * ∑ j : Fin 3, z.2.1 j * z.2.2 i j
  have hBcont : Continuous B := by fun_prop
  have htuple : AEStronglyMeasurable (fun x : Vec3 => (u x, (w x, Dw x))) volume :=
    huMeas.prodMk (hw2.aestronglyMeasurable.prodMk hDw2.aestronglyMeasurable)
  let F : Vec3 → ℝ := fun x => B (u x, (w x, Dw x))
  have hFmeas : AEStronglyMeasurable F volume := by
    simpa only [F] using hBcont.comp_aestronglyMeasurable htuple
  have hFbound (x : Vec3) : ‖F x‖ ≤
      9 * (vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) := by
    rw [Real.norm_eq_abs]
    simpa only [F, B] using lps_triple_pointwise_euclidean (u x) (w x) (Dw x)
  have hDom : Integrable (fun x : Vec3 =>
      9 * (vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖)) volume := hprodInt.const_mul 9
  have hFint : Integrable F volume := by
    refine hDom.mono' hFmeas (Eventually.of_forall fun x => ?_)
    simpa only [Real.norm_eq_abs] using hFbound x
  have hAbsolute : |∫ x : Vec3, F x| ≤ 9 * (U * N * D) := by
    calc
      |∫ x : Vec3, F x| ≤ ∫ x : Vec3, |F x| := abs_integral_le_integral_abs
      _ ≤ ∫ x : Vec3,
          9 * (vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖) := by
        apply integral_mono (by simpa only [Real.norm_eq_abs] using hFint.norm) hDom
        exact fun x => by simpa only [Real.norm_eq_abs] using hFbound x
      _ = 9 * ∫ x : Vec3,
          vec3EuclideanNorm (u x) * ‖w x‖ * ‖Dw x‖ := by
        rw [integral_const_mul]
      _ ≤ 9 * (U * N * D) := by
        simpa only [U, N, D] using mul_le_mul_of_nonneg_left hprodBound (by norm_num)
  have hTriple : |∫ x : Vec3, F x| ≤
      (9 * Cg * U) * W ^ (1 - θ) * D ^ (1 + θ) := by
    by_cases hDzero : D = 0
    · have hIntegralZero : |∫ x : Vec3, F x| = 0 := by
        have hInt : ∫ x : Vec3, F x = 0 := by
          have hle := hAbsolute
          simp [hDzero, D] at hle
          exact hle
        simp [hInt]
      rw [hIntegralZero]
      positivity
    · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDzero)
      have hDpow : D ^ θ * D = D ^ (1 + θ) := by
        calc
          D ^ θ * D = D ^ θ * D ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = D ^ (θ + 1) := by rw [← Real.rpow_add hDpos]
          _ = D ^ (1 + θ) := by congr 1; ring
      have hprodStep : 9 * (U * N * D) ≤
          (9 * U) * (Cg * W ^ (1 - θ) * D ^ θ) * D := by
        calc
          9 * (U * N * D) = (9 * U) * (N * D) := by ring
          _ ≤ (9 * U) * ((Cg * W ^ (1 - θ) * D ^ θ) * D) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hD0) (by positivity)
          _ = (9 * U) * (Cg * W ^ (1 - θ) * D ^ θ) * D := by ring
      calc
        |∫ x : Vec3, F x| ≤ 9 * (U * N * D) := hAbsolute
        _ ≤ (9 * U) * (Cg * W ^ (1 - θ) * D ^ θ) * D := hprodStep
        _ = (9 * Cg * U) * W ^ (1 - θ) * (D ^ θ * D) := by ring
        _ = (9 * Cg * U) * W ^ (1 - θ) * D ^ (1 + θ) := by rw [hDpow]
  let Cbase : ℝ := 9 * Cg
  let A : ℝ := Cbase * U
  let CY : ℝ := lps_power_young_coefficient θ
  have hCY0 : 0 ≤ CY := by
    dsimp [CY, lps_power_young_coefficient]
    positivity
  have hYoung := lps_power_young (A := A) (B := W) (D := D)
    hθ0 hθ1 (by dsimp [A, Cbase]; positivity) hW0 hD0
  rw [hell] at hYoung
  let K : ℝ := CY * Cbase ^ (2 * s / (s - 3))
  have hCbase0 : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hpow : (Cbase * U) ^ (2 * s / (s - 3)) =
      Cbase ^ (2 * s / (s - 3)) * U ^ (2 * s / (s - 3)) :=
    Real.mul_rpow hCbase0 hU0
  have hcoeff : CY * A ^ (2 * s / (s - 3)) =
      K * U ^ (2 * s / (s - 3)) := by
    calc
      CY * A ^ (2 * s / (s - 3)) = CY * (Cbase * U) ^ (2 * s / (s - 3)) := by rfl
      _ = CY * (Cbase ^ (2 * s / (s - 3)) * U ^ (2 * s / (s - 3))) := by rw [hpow]
      _ = K * U ^ (2 * s / (s - 3)) := by dsimp [K]; ring
  have hsqD := lps_slice_square_integrable_gradient hDw2
  have hsqW := lps_slice_square_integrable_velocity hw2
  have hD2 : D ^ 2 ≤ ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2 :=
    lps_sq_eLpNorm_le hDw2 _ (fun x => lps_norm_sq_le_sum_sq₂ (Dw x)) hsqD
  have hW2 : W ^ 2 ≤ ∫ x : Vec3, ∑ i : Fin 3, w x i ^ 2 :=
    lps_sq_eLpNorm_le hw2 _ (fun x => lps_norm_sq_le_sum_sq (w x)) hsqW
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  calc
    |∫ x : Vec3, F x| ≤ (1 / 2 : ℝ) * D ^ 2 + CY * A ^ (2 * s / (s - 3)) * W ^ 2 :=
      hTriple.trans hYoung
    _ = (1 / 2 : ℝ) * D ^ 2 +
        K * U ^ (2 * s / (s - 3)) * W ^ 2 := by rw [hcoeff]
    _ ≤ (1 / 2 : ℝ) * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) +
        K * U ^ (2 * s / (s - 3)) * (∫ x : Vec3, ∑ i : Fin 3, w x i ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hD2 (by norm_num))
        (mul_le_mul_of_nonneg_left hW2 (by positivity))
  
end ESS
