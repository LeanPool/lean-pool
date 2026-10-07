/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsSliceEstimates
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Reg Tails Slice Flux

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regTails_flux_product_integrable_and_bound
    {f g : Vec3 → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x : Vec3 => ‖f x‖ * ‖g x‖) volume ∧
      ∫ x : Vec3, ‖f x‖ * ‖g x‖ ∂volume ≤
        (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  have hint : Integrable (fun x : Vec3 => ‖f x‖ * ‖g x‖) volume :=
    hf.norm.integrable_mul hg.norm
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hg
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) ⟨by norm_num, by norm_num, by norm_num⟩ hf' hg'
  have hfnorm : (eLpNorm f 2 volume).toReal =
      Real.sqrt (∫ x : Vec3, f x ^ (2 : ℕ) ∂volume) := by
    rw [vorticity_eLpNorm_two_eq_sqrt hf,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hgnorm : (eLpNorm g 2 volume).toReal =
      Real.sqrt (∫ x : Vec3, g x ^ (2 : ℕ) ∂volume) := by
    rw [vorticity_eLpNorm_two_eq_sqrt hg,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hfint : (∫ x : Vec3, ‖f x‖ ^ (2 : ℝ) ∂volume) =
      ∫ x : Vec3, f x ^ (2 : ℕ) ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Real.norm_eq_abs, sq_abs]
  have hgint : (∫ x : Vec3, ‖g x‖ ^ (2 : ℝ) ∂volume) =
      ∫ x : Vec3, g x ^ (2 : ℕ) ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨hint, ?_⟩
  rw [Real.sqrt_eq_rpow] at hfnorm hgnorm
  rw [hfint, hgint, ← hfnorm, ← hgnorm] at hholder
  exact hholder

private theorem regTails_slice_flux_pointwise_majorant
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (D : ParabolicPoint → Fin 3 → Vec3) (t M : ℝ)
    (q : Vec3 → ℝ)
    (hDq : ∀ x : Vec3, ∀ j : Fin 3, |spatialDeriv q j x| ≤ M) :
    ∀ x : Vec3,
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| +
      ∑ j : Fin 3,
        ((vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) *
            |regUniformMollifiedVelocity ρ ε hε u (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j|) *
          |spatialDeriv q j x|) ≤
      18 * M * vec3EuclideanNorm (u (x, t)) *
          Real.sqrt (spatialGradientSq u D (x, t)) +
        3 * M * vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) *
          vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)) +
        6 * M * |p (x, t)| * vec3EuclideanNorm (u (x, t)) := by
  intro x
  let V : ℝ := vec3EuclideanNorm (u (x, t))
  let W : ℝ := Real.sqrt (spatialGradientSq u D (x, t))
  let J : ℝ := vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t))
  let P : ℝ := p (x, t)
  have hVnonneg : 0 ≤ V := by dsimp [V]; exact vec3EuclideanNorm_nonneg _
  have hWnonneg : 0 ≤ W := Real.sqrt_nonneg _
  have hucoord : ∀ i : Fin 3, |u (x, t) i| ≤ V := by
    intro i
    simpa [V] using abs_apply_le_vec3EuclideanNorm (u (x, t)) i
  have hDcoord : ∀ i j : Fin 3, |D (x, t) i j| ≤ W := by
    intro i j
    have hsq : (D (x, t) i j) ^ (2 : ℕ) ≤ spatialGradientSq u D (x, t) := by
      unfold spatialGradientSq
      calc
        _ ≤ ∑ l : Fin 3, (D (x, t) i l) ^ (2 : ℕ) :=
          Finset.single_le_sum
            (fun l _ => sq_nonneg (D (x, t) i l)) (Finset.mem_univ j)
        _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, (D (x, t) k l) ^ (2 : ℕ) :=
          Finset.single_le_sum
            (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (D (x, t) k l))
            (Finset.mem_univ i)
    dsimp [W]
    apply Real.le_sqrt_of_sq_le
    simpa [sq_abs] using hsq
  have hjcoord : ∀ j : Fin 3,
      |regUniformMollifiedVelocity ρ ε hε u (x, t) j| ≤ J := by
    intro j
    simpa [J] using abs_apply_le_vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t)) j
  have hdq : ∀ j : Fin 3, |spatialDeriv q j x| ≤ M := fun j => hDq x j
  have hdiff : 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| ≤
        18 * M * V * W := by
    have hsum :
        (∑ i : Fin 3, ∑ j : Fin 3,
          |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x|) ≤
          ∑ i : Fin 3, ∑ j : Fin 3, V * W * M := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hprod : |u (x, t) i| * |D (x, t) i j| ≤ V * W :=
        mul_le_mul (hucoord i) (hDcoord i j) (abs_nonneg _) hVnonneg
      calc
        |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| ≤
            (V * W) * |spatialDeriv q j x| :=
          mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
        _ ≤ (V * W) * M :=
          mul_le_mul_of_nonneg_left (hdq j)
            (mul_nonneg hVnonneg hWnonneg)
    calc
      _ ≤ 2 * ∑ i : Fin 3, ∑ j : Fin 3, (V * W * M) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 18 * M * V * W := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hfluxPoint : ∀ j : Fin 3,
      (V ^ (2 : ℕ) *
          |regUniformMollifiedVelocity ρ ε hε u (x, t) j| +
        2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x| ≤
      (V ^ (2 : ℕ) * J + 2 * |P| * V) * M := by
    intro j
    have hV2 : 0 ≤ V ^ (2 : ℕ) := by positivity
    have hfirst : V ^ (2 : ℕ) *
        |regUniformMollifiedVelocity ρ ε hε u (x, t) j| ≤ V ^ (2 : ℕ) * J :=
      mul_le_mul_of_nonneg_left (hjcoord j) hV2
    have hsecond : 2 * |p (x, t)| * |u (x, t) j| ≤ 2 * |P| * V := by
      calc
        2 * |p (x, t)| * |u (x, t) j| ≤ 2 * |p (x, t)| * V :=
          mul_le_mul_of_nonneg_left (hucoord j) (by positivity)
        _ = 2 * |P| * V := by rfl
    have hadd := add_le_add hfirst hsecond
    have haddNonneg : 0 ≤ V ^ (2 : ℕ) * J + 2 * |P| * V :=
      add_nonneg (mul_nonneg hV2 (vec3EuclideanNorm_nonneg _))
        (mul_nonneg (by positivity) hVnonneg)
    exact mul_le_mul hadd (hdq j) (abs_nonneg _) haddNonneg
  have hfluxSum : ∑ j : Fin 3,
      (V ^ (2 : ℕ) * J + 2 * |P| * V) * M =
      3 * M * V ^ (2 : ℕ) * J + 6 * M * |P| * V := by
    calc
      _ = 3 * ((V ^ (2 : ℕ) * J + 2 * |P| * V) * M) := by simp
      _ = _ := by ring
  have hflux := (Finset.sum_le_sum fun j hj => hfluxPoint j).trans_eq hfluxSum
  calc
    _ ≤ 18 * M * V * W +
        (3 * M * V ^ (2 : ℕ) * J + 6 * M * |P| * V) :=
      add_le_add hdiff hflux
    _ = _ := by dsimp [V, W, J, P]; ring

/-- A compact smooth spatial weight makes the nonnegative localized flux
density integrable on each positive-time slice. -/
theorem regTails_slice_flux_density_integrable
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (J : ParabolicPoint → Vec3)
    (t : ℝ) (q : Vec3 → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q)
    (hUcont : ∀ i : Fin 3, Continuous (fun x : Vec3 => u (x, t) i))
    (hDcont : ∀ i j : Fin 3, Continuous (fun x : Vec3 => D (x, t) i j))
    (hPcont : Continuous (fun x : Vec3 => p (x, t)))
    (hJcont : ∀ j : Fin 3,
      Continuous (fun x : Vec3 => J (x, t) j)) :
    Integrable (fun x : Vec3 =>
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| +
      ∑ j : Fin 3,
        ((vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * |J (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x|)) volume := by
  let V : Vec3 → ℝ := fun x => vec3EuclideanNorm (u (x, t))
  let F : Vec3 → ℝ := fun x =>
    2 * ∑ i : Fin 3, ∑ j : Fin 3,
      |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| +
    ∑ j : Fin 3,
      ((V x ^ (2 : ℕ) * |J (x, t) j| +
        2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x|)
  have hVcont : Continuous V :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp
      (continuous_pi_iff.2 hUcont)
  have hUabs (i : Fin 3) : Continuous (fun x : Vec3 => |u (x, t) i|) :=
    continuous_abs.comp (hUcont i)
  have hDabs (i j : Fin 3) : Continuous (fun x : Vec3 => |D (x, t) i j|) :=
    continuous_abs.comp (hDcont i j)
  have hPabs : Continuous (fun x : Vec3 => |p (x, t)|) :=
    continuous_abs.comp hPcont
  have hJabs (j : Fin 3) : Continuous (fun x : Vec3 => |J (x, t) j|) :=
    continuous_abs.comp (hJcont j)
  have hqderiv (j : Fin 3) : Continuous (fun x : Vec3 => |spatialDeriv q j x|) := by
    exact continuous_abs.comp (CKN.contDiff_spatialDeriv_smooth hq j).continuous
  have hFirst : Continuous (fun x : Vec3 =>
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x|) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact ((hUabs i).mul (hDabs i j)).mul (hqderiv j)
  have hSecond : Continuous (fun x : Vec3 =>
      ∑ j : Fin 3,
        ((V x ^ (2 : ℕ) * |J (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x|)) := by
    apply continuous_finsetSum
    intro j hj
    exact ((hVcont.pow 2).mul (hJabs j)).add
      ((continuous_const.mul hPabs).mul (hUabs j)) |>.mul (hqderiv j)
  have hFcont : Continuous F := by
    dsimp [F]
    exact hFirst.add hSecond
  have hderivSupport (j : Fin 3) :
      tsupport (fun x : Vec3 => spatialDeriv q j x) ⊆ tsupport q := by
    change tsupport (fun x : Vec3 => (fderiv ℝ q x) (basisVec j)) ⊆ tsupport q
    exact tsupport_fderiv_apply_subset ℝ (basisVec j)
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.intro hqc.isCompact
    intro x hx
    have hdzero (j : Fin 3) : spatialDeriv q j x = 0 := by
      by_contra hne
      exact hx (hderivSupport j
        (subset_tsupport _ (Function.mem_support.mpr hne)))
    simp [F, hdzero]
  change Integrable F volume
  exact hFcont.integrable_of_hasCompactSupport hFcompact

private theorem regTails_scalar_l4_flux_bounds
    (V W : Vec3 → ℝ) (B G : ℝ) (hGnonneg : 0 ≤ G)
    (_hVnonneg : ∀ x, 0 ≤ V x)
    (hV4bound : eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume ≤
      3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        eLpNorm V 2 volume ^ (1 / 4 : ℝ) * eLpNorm W 2 volume ^ (3 / 4 : ℝ))
    (hV4boundFinite :
      3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        eLpNorm V 2 volume ^ (1 / 4 : ℝ) * eLpNorm W 2 volume ^ (3 / 4 : ℝ) < ⊤)
    (hV4mem : MemLp V (ENNReal.ofReal (4 : ℝ)) volume)
    (hUboundL2 : (eLpNorm V 2 volume).toReal ≤ B)
    (hGdef : (eLpNorm W 2 volume).toReal = G) :
    ((eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
        B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ)) ∧
    MemLp (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume := by
  have hV4realBound : (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
        B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ) := by
    have htoReal := ENNReal.toReal_mono hV4boundFinite.ne hV4bound
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofNat] at htoReal
    have hWreal : (eLpNorm W 2 volume).toReal = G := by
      exact hGdef
    rw [hWreal] at htoReal
    calc
      (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
          3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
            (eLpNorm V 2 volume).toReal ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ) := htoReal
      _ ≤ 3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
            B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ) := by
        gcongr
  have hV4sqmem : MemLp (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume := by
    have h := hV4mem.norm_rpow_div (ENNReal.ofReal (2 : ℝ))
    have hexp : ENNReal.ofReal (4 : ℝ) / ENNReal.ofReal (2 : ℝ) = 2 := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hexp] at h
    simpa [Real.norm_eq_abs, _hVnonneg] using h
  exact ⟨hV4realBound, hV4sqmem⟩

private theorem regTails_mollified_velocity_l4_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ) (ht : 0 < t)
    (hU2 : ∀ s : ℝ, 0 ≤ s → MemLp (regUniformVelocitySlice u s) 2 volume)
    (hV4mem : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume) :
    (eLpNorm (fun x : Vec3 =>
      vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
  have hMoll4 := regTails_mollified_velocity_slice_L4 ρ ε hε u t
    (hU2 t (le_of_lt ht)) hV4mem
  exact ENNReal.toReal_mono hV4mem.eLpNorm_ne_top (by simpa using hMoll4.2)

private theorem regTails_pressure_l2_scalar_bound
    (V J P : Vec3 → ℝ) (B G : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hR4bound : (eLpNorm P (ENNReal.ofReal (2 : ℝ)) volume).toReal ≤
      9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        (eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal)
    (hMoll4bound : (eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal)
    (hV4realBound : (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
        B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ)) :
    (eLpNorm P (ENNReal.ofReal (2 : ℝ)) volume).toReal ≤
      81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          B ^ (1 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
  have hP := hR4bound
  have hMollBound : (eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
        B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ) := hMoll4bound.trans hV4realBound
  have hRnonneg : 0 ≤ rieszPressureOperatorBound (2 : ℝ) (by norm_num) := by
    unfold rieszPressureOperatorBound
    exact (Classical.choose_spec
      (CKN.Foundation.Euclidean.riesz_second_all_exponents (2 : ℝ) (by norm_num))).1
  have hPpre : (eLpNorm P (ENNReal.ofReal (2 : ℝ)) volume).toReal ≤
      9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        (3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
          B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ)) ^ 2 := by
    have hPbase : (eLpNorm P (ENNReal.ofReal (2 : ℝ)) volume).toReal ≤
        9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          (eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal *
            (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal := hP
    calc
      _ ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          ((eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal *
            (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal) := by
            calc
              _ ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
                  (eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal *
                    (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal := hPbase
              _ = _ := by ring
      _ ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          ((eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ^ 2) := by
            have hmul := mul_le_mul_of_nonneg_right hMoll4bound
              (by positivity : 0 ≤ (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal)
            have hcoef : 0 ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) := by positivity
            calc
              _ ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
                  ((eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal *
                    (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal) :=
                    mul_le_mul_of_nonneg_left hmul hcoef
              _ = _ := by ring
      _ ≤ _ := by
            have hpow := pow_le_pow_left₀ (by positivity)
              hV4realBound 2
            have hcoef : 0 ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) := by positivity
            exact mul_le_mul_of_nonneg_left hpow hcoef
  have hSsq : (CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ)) ^ 2 =
      CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; norm_num
  have hBpow : (B ^ (1 / 4 : ℝ)) ^ 2 = B ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; norm_num
  have hGpow : (G ^ (3 / 4 : ℝ)) ^ 2 = G ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; norm_num
  calc
    _ ≤ 9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        (3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
          B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ)) ^ 2 := hPpre
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, hSsq, hBpow, hGpow]; ring

private theorem regTails_flux_integral_assembly
    (F V W J P : Vec3 → ℝ) (M B G : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hVWint : Integrable (fun x : Vec3 => V x * W x) volume)
    (hV2Jint : Integrable (fun x : Vec3 => V x ^ (2 : ℕ) * J x) volume)
    (hPVint : Integrable (fun x : Vec3 => |P x| * V x) volume)
    (hDiffInt : ∫ x : Vec3, V x * W x ∂volume ≤ B * G)
    (hConvInt : ∫ x : Vec3, V x ^ (2 : ℕ) * J x ∂volume ≤
      9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
        B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ))
    (hPressInt : ∫ x : Vec3, |P x| * V x ∂volume ≤
      81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ))
    (hpoint : ∀ x : Vec3, F x ≤
      18 * M * V x * W x + 3 * M * V x ^ (2 : ℕ) * J x +
        6 * M * |P x| * V x) :
    ∫ x : Vec3, F x ∂volume ≤
      18 * M * B * G +
        (27 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) +
          486 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
            CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ)) *
          M * B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
  let K : Vec3 → ℝ := fun x =>
    18 * M * V x * W x + 3 * M * V x ^ (2 : ℕ) * J x +
      6 * M * |P x| * V x
  have hKintegrand : (fun x : Vec3 => K x) =
      fun x => 18 * M * (V x * W x) +
        (3 * M * (V x ^ (2 : ℕ) * J x) + 6 * M * (|P x| * V x)) := by
    funext x
    dsimp [K]
    ring
  have hKint : Integrable K volume := by
    change Integrable (fun x : Vec3 => K x) volume
    rw [hKintegrand]
    exact (hVWint.const_mul (18 * M)).add
      ((hV2Jint.const_mul (3 * M)).add (hPVint.const_mul (6 * M)))
  have hKval : ∫ x : Vec3, K x ∂volume =
      18 * M * (∫ x : Vec3, V x * W x ∂volume) +
        3 * M * (∫ x : Vec3, V x ^ (2 : ℕ) * J x ∂volume) +
        6 * M * (∫ x : Vec3, |P x| * V x ∂volume) := by
    change ∫ x : Vec3, (fun x => K x) x ∂volume = _
    rw [hKintegrand]
    calc
      ∫ x : Vec3,
          18 * M * (V x * W x) +
            (3 * M * (V x ^ (2 : ℕ) * J x) + 6 * M * (|P x| * V x)) ∂volume =
          (∫ x : Vec3, 18 * M * (V x * W x) ∂volume) +
            (∫ x : Vec3,
              3 * M * (V x ^ (2 : ℕ) * J x) + 6 * M * (|P x| * V x) ∂volume) :=
        integral_add (hVWint.const_mul (18 * M))
          ((hV2Jint.const_mul (3 * M)).add (hPVint.const_mul (6 * M)))
      _ = 18 * M * (∫ x : Vec3, V x * W x ∂volume) +
            (3 * M * (∫ x : Vec3, V x ^ (2 : ℕ) * J x ∂volume) +
              6 * M * (∫ x : Vec3, |P x| * V x ∂volume)) := by
        rw [integral_const_mul, integral_add (hV2Jint.const_mul (3 * M))
          (hPVint.const_mul (6 * M)), integral_const_mul, integral_const_mul]
      _ = _ := by ring
  have hKbound : ∫ x : Vec3, K x ∂volume ≤
      18 * M * B * G +
        (27 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) +
          486 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
            CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ)) *
          M * B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
    rw [hKval]
    calc
      _ ≤ 18 * M * (B * G) +
          3 * M * (9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
            B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) +
          6 * M * (81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
            CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
              B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) := by
        gcongr
      _ = _ := by ring
  by_cases hFint : Integrable F volume
  · calc
      ∫ x : Vec3, F x ∂volume ≤ ∫ x : Vec3, K x ∂volume :=
        integral_mono hFint hKint hpoint
      _ ≤ _ := hKbound
  · rw [integral_undef hFint]
    have hRnonneg : 0 ≤ rieszPressureOperatorBound (2 : ℝ) (by norm_num) := by
      unfold rieszPressureOperatorBound
      exact (Classical.choose_spec
        (CKN.Foundation.Euclidean.riesz_second_all_exponents (2 : ℝ) (by norm_num))).1
    positivity

private theorem regTails_holder_flux_estimates
    (V W J P : Vec3 → ℝ) (B G : ℝ) (hB : 0 ≤ B) (hGnonneg : 0 ≤ G)
    (hVmem : MemLp V 2 volume) (hWmem : MemLp W 2 volume)
    (hJmem : MemLp J 2 volume) (hPmem : MemLp P 2 volume)
    (hV4sqmem : MemLp (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume)
    (hVmeas : AEStronglyMeasurable V volume)
    (hVnonneg : ∀ x, 0 ≤ V x) (hWnonneg : ∀ x, 0 ≤ W x)
    (hJnonneg : ∀ x, 0 ≤ J x)
    (hUboundL2 : (eLpNorm V 2 volume).toReal ≤ B)
    (hGdef : (eLpNorm W 2 volume).toReal = G)
    (hJbound : (eLpNorm J 2 volume).toReal ≤ B)
    (hV4realBound : (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
        B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ))
    (hPnormBound : (eLpNorm P (ENNReal.ofReal (2 : ℝ)) volume).toReal ≤
      81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          B ^ (1 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) :
    Integrable (fun x : Vec3 => V x * W x) volume ∧
    Integrable (fun x : Vec3 => V x ^ (2 : ℕ) * J x) volume ∧
    Integrable (fun x : Vec3 => |P x| * V x) volume ∧
    (∫ x : Vec3, V x * W x ∂volume ≤ B * G) ∧
    (∫ x : Vec3, V x ^ (2 : ℕ) * J x ∂volume ≤
      9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
        B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) ∧
    (∫ x : Vec3, |P x| * V x ∂volume ≤
      81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) := by
  have hProdVW := regTails_flux_product_integrable_and_bound hVmem hWmem
  have hProdV2J := regTails_flux_product_integrable_and_bound hV4sqmem hJmem
  have hProdPV := regTails_flux_product_integrable_and_bound hPmem hVmem
  have hV2norm :
      (eLpNorm (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume).toReal =
        (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal ^ (2 : ℕ) := by
    have hraw := eLpNorm_norm_rpow V hVmeas (q := (2 : ℝ)) (by norm_num)
      (p := ENNReal.ofReal 2)
    have hexp : ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (2 : ℝ) =
        ENNReal.ofReal (4 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hexp] at hraw
    have htoReal := congrArg ENNReal.toReal hraw
    simpa [ENNReal.toReal_rpow, ENNReal.toReal_ofNat] using htoReal
  have hVWnorm : (fun x : Vec3 => ‖V x‖ * ‖W x‖) = fun x => V x * W x := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hVnonneg x),
      Real.norm_eq_abs, abs_of_nonneg (hWnonneg x)]
  have hDiffInt : ∫ x : Vec3, V x * W x ∂volume ≤ B * G := by
    have h := hProdVW.2
    have h' : ∫ x : Vec3, V x * W x ∂volume ≤
        (eLpNorm V 2 volume).toReal * (eLpNorm W 2 volume).toReal := by
      rw [← hVWnorm]
      exact h
    exact h'.trans (mul_le_mul hUboundL2 (le_of_eq hGdef)
      (by positivity) hB)
  have hV2Jnorm :
      (fun x : Vec3 => ‖V x ^ (2 : ℕ)‖ * ‖J x‖) =
        fun x => V x ^ (2 : ℕ) * J x := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (hJnonneg x)]
  have hVWint : Integrable (fun x : Vec3 => V x * W x) volume := by
    rw [← hVWnorm]
    exact hProdVW.1
  have hV2Jint : Integrable
      (fun x : Vec3 => V x ^ (2 : ℕ) * J x) volume := by
    rw [← hV2Jnorm]
    exact hProdV2J.1
  have hConvInt : ∫ x : Vec3, V x ^ (2 : ℕ) * J x ∂volume ≤
      9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
        B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
    have h := hProdV2J.2
    have h' : ∫ x : Vec3, V x ^ (2 : ℕ) * J x ∂volume ≤
        (eLpNorm (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume).toReal *
          (eLpNorm J 2 volume).toReal := by
      rw [← hV2Jnorm]
      exact h
    have hJ2 : (eLpNorm J 2 volume).toReal ≤ B := hJbound
    have hBcomb : B ^ (1 / 2 : ℝ) * B = B ^ (3 / 2 : ℝ) := by
      calc
        B ^ (1 / 2 : ℝ) * B = B ^ (1 / 2 : ℝ) * B ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = B ^ ((1 / 2 : ℝ) + 1) :=
          (Real.rpow_add' hB (by norm_num)).symm
        _ = B ^ (3 / 2 : ℝ) := by congr 1; norm_num
    have hV2 : (eLpNorm (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume).toReal ≤
        9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          B ^ (1 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
      rw [hV2norm]
      have hpow := pow_le_pow_left₀ (by positivity) hV4realBound 2
      have hSsq : (CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ)) ^ 2 =
          CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; norm_num
      have hBpow : (B ^ (1 / 4 : ℝ)) ^ 2 = B ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; norm_num
      have hGpow : (G ^ (3 / 4 : ℝ)) ^ 2 = G ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; norm_num
      calc
        _ = ((eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal) ^ 2 := by rfl
        _ ≤ (3 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 4 : ℝ) *
            B ^ (1 / 4 : ℝ) * G ^ (3 / 4 : ℝ)) ^ 2 := hpow
        _ = _ := by
          simp only [mul_pow, hSsq, hBpow, hGpow]
          norm_num
    calc
      _ ≤ (eLpNorm (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume).toReal *
          (eLpNorm J 2 volume).toReal := h'
      _ ≤ (eLpNorm (fun x : Vec3 => V x ^ (2 : ℕ)) 2 volume).toReal * B :=
        mul_le_mul_of_nonneg_left hJ2 (by positivity)
      _ ≤ 9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          (B ^ (1 / 2 : ℝ) * B) * G ^ (3 / 2 : ℝ) := by
        have hV2B := mul_le_mul_of_nonneg_right hV2 hB
        calc
          _ ≤ (9 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
                B ^ (1 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) * B := hV2B
          _ = _ := by ring
      _ = _ := by rw [hBcomb]
  have hPVnorm : (fun x : Vec3 => ‖P x‖ * ‖V x‖) =
      fun x => |P x| * V x := by
    funext x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hVnonneg x)]
  have hPVint : Integrable (fun x : Vec3 => |P x| * V x) volume := by
    rw [← hPVnorm]
    exact hProdPV.1
  have hPressInt : ∫ x : Vec3, |P x| * V x ∂volume ≤
      81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
        CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
          B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
    have h := hProdPV.2
    have h' : ∫ x : Vec3, |P x| * V x ∂volume ≤
        (eLpNorm (fun x : Vec3 => P x) 2 volume).toReal *
          (eLpNorm V 2 volume).toReal := by
      rw [← hPVnorm]
      exact h
    have hBcomb : B ^ (1 / 2 : ℝ) * B = B ^ (3 / 2 : ℝ) := by
      calc
        B ^ (1 / 2 : ℝ) * B = B ^ (1 / 2 : ℝ) * B ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = B ^ ((1 / 2 : ℝ) + 1) :=
          (Real.rpow_add' hB (by norm_num)).symm
        _ = B ^ (3 / 2 : ℝ) := by congr 1; norm_num
    have hPnormBound' : (eLpNorm P 2 volume).toReal ≤
        81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
            B ^ (1 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
      simpa using hPnormBound
    calc
      _ ≤ (eLpNorm (fun x : Vec3 => P x) 2 volume).toReal *
          (eLpNorm V 2 volume).toReal := h'
      _ ≤ (eLpNorm (fun x : Vec3 => P x) 2 volume).toReal * B :=
        mul_le_mul_of_nonneg_left hUboundL2 (by positivity)
      _ ≤ (81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
            CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
            B ^ (1 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) * B := by
        exact mul_le_mul_of_nonneg_right hPnormBound' hB
      _ = 81 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
            (B ^ (1 / 2 : ℝ) * B) * G ^ (3 / 2 : ℝ) := by ring
      _ = _ := by rw [hBcomb]
  exact ⟨hVWint, hV2Jint, hPVint, hDiffInt, hConvInt, hPressInt⟩

/-- The localized flux density in `lem:reg-tails` is controlled by the
slice energy and dissipation profiles. -/
theorem regTails_slice_flux_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hU2 : ∀ s : ℝ, 0 ≤ s → MemLp (regUniformVelocitySlice u s) 2 volume)
    (hUbound : ∀ s : ℝ, 0 < s → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Vec3,
      vec3EuclideanNorm (u (x, s)) ≤ K)
    (hR4 : ∀ s : ℝ, 0 < s → ∃ hF : ∀ i j : Fin 3,
      MemLp (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, s) i * u (x, s) j)
        (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => p (x, s)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (fun x : Vec3 =>
            regUniformMollifiedVelocity ρ ε hε u (x, s) i * u (x, s) j)))
    (t : ℝ) (ht : 0 < t)
    (hU : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hH1 : ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
      (∀ i x, (h i).toFun x = u (x, t) i) ∧
      (∀ i x j, (h i).grad x j =
        spatialPartial (fun y : ParabolicPoint => u y i) j (x, t)))
    (B G M : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hUboundL2 :
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume).toReal ≤ B)
    (hGdef :
      (eLpNorm (fun x : Vec3 => Real.sqrt
        (spatialGradientSq u
          (fun z i j => spatialPartial (fun y : ParabolicPoint => u y i) j z)
          (x, t))) 2 volume).toReal = G)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hDq : ∀ x : Vec3, ∀ j : Fin 3,
      |spatialDeriv q j x| ≤ M) :
    ∫ x : Vec3,
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        |u (x, t) i| *
          |spatialPartial (fun y : ParabolicPoint => u y i) j (x, t)| *
          |spatialDeriv q j x| +
      ∑ j : Fin 3,
        ((vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) *
            |regUniformMollifiedVelocity ρ ε hε u (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j|) *
          |spatialDeriv q j x|) ∂volume ≤
    18 * M * B * G +
        (27 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) +
          486 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
            CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ)) *
          M * B ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
  classical
  have _hSmooth : ContDiff ℝ (⊤ : ℕ∞) q := hq
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y : ParabolicPoint => u y i) j z
  let V : Vec3 → ℝ := fun x => vec3EuclideanNorm (u (x, t))
  let W : Vec3 → ℝ := fun x => Real.sqrt (spatialGradientSq u D (x, t))
  let J : Vec3 → ℝ := fun x =>
    vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε u (x, t))
  let P : Vec3 → ℝ := fun x => p (x, t)
  let F : Vec3 → ℝ := fun x =>
    2 * ∑ i : Fin 3, ∑ j : Fin 3,
      |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| +
    ∑ j : Fin 3,
      ((V x ^ (2 : ℕ) *
          |regUniformMollifiedVelocity ρ ε hε u (x, t) j| +
        2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x|)
  let K : Vec3 → ℝ := fun x =>
    18 * M * V x * W x + 3 * M * V x ^ (2 : ℕ) * J x +
      6 * M * |P x| * V x
  rcases hH1 with ⟨h, hValues, hGradients⟩
  have hGradD : ∀ i x j, (h i).grad x j = D (x, t) i j := by
    intro i x j
    simpa [D] using hGradients i x j
  have hDmem : ∀ i j, MemLp (fun x : Vec3 => D (x, t) i j) 2 volume := by
    intro i j
    simpa [CKN.GradMemLpOn, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ, D, hGradients i _ j] using (h i).grad_memL2 j
  have hWmeas : AEStronglyMeasurable W volume := by
    have hSq : AEStronglyMeasurable
        (fun x : Vec3 => spatialGradientSq u D (x, t)) volume := by
      unfold spatialGradientSq
      exact Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
        Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
          (hDmem i j).aestronglyMeasurable.pow 2
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hSq
  have hWsqInt : Integrable (fun x : Vec3 => W x ^ (2 : ℕ)) volume := by
    have hsum : Integrable (fun x : Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (D (x, t) i j) ^ (2 : ℕ)) volume :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hDmem i j).integrable_sq
    have hsum' : Integrable
        (fun x : Vec3 => spatialGradientSq u D (x, t)) volume :=
      hsum.congr (Eventually.of_forall fun x => rfl)
    have hEq : (fun x : Vec3 => W x ^ (2 : ℕ)) =
        fun x => spatialGradientSq u D (x, t) := by
      funext x
      dsimp [W]
      rw [Real.sq_sqrt]
      unfold spatialGradientSq
      exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg (D (x, t) i j)
    exact hsum'.congr hEq.symm.eventuallyEq
  have hWmem : MemLp W 2 volume :=
    (memLp_two_iff_integrable_sq hWmeas).2 hWsqInt
  have hVmeas : AEStronglyMeasurable V volume :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hU.aestronglyMeasurable
  have hVnonneg : ∀ x, 0 ≤ V x := fun x => vec3EuclideanNorm_nonneg _
  have hVmem : MemLp V 2 volume := by
    have hnorm : MemLp (fun x : Vec3 => ‖u (x, t)‖) 2 volume := hU.norm
    exact hnorm.of_le_mul (c := Real.sqrt 3) hVmeas
      (Filter.Eventually.of_forall fun x => by
        have hvec :=
          CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm
            (u ((x, t) : ParabolicPoint))
        calc
          ‖V x‖ = V x := by rw [Real.norm_eq_abs, abs_of_nonneg (hVnonneg x)]
          _ ≤ Real.sqrt 3 * ‖u ((x, t) : ParabolicPoint)‖ := by
            simpa [V] using hvec
          _ = Real.sqrt 3 * ‖‖u ((x, t) : ParabolicPoint)‖‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
  have hWnonneg : ∀ x, 0 ≤ W x := fun x => Real.sqrt_nonneg _
  have hJmem : MemLp J 2 volume := by
    simpa [J] using
      (regTails_mollified_velocity_slice_L2 ρ ε hε u t (hU2 t (le_of_lt ht))).1
  have hJbound : (eLpNorm J 2 volume).toReal ≤ B := by
    have hJ := (regTails_mollified_velocity_slice_L2 ρ ε hε u t
      (hU2 t (le_of_lt ht))).2
    have hJ' : (eLpNorm J 2 volume).toReal ≤
        (eLpNorm V 2 volume).toReal := by
      exact ENNReal.toReal_mono hVmem.eLpNorm_ne_top (by simpa [J, V] using hJ)
    exact hJ'.trans hUboundL2
  have hV4bound : eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume ≤
      3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        eLpNorm V 2 volume ^ (1 / 4 : ℝ) *
          eLpNorm W 2 volume ^ (3 / 4 : ℝ) := by
    simpa [V, W, D] using
      regTails_vector_slice_L4 u D t h hValues hGradD hU
  have hSfinite : CKN.gagliardoNirenbergSobolevConstant ≠ ⊤ :=
    CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
  have hVfinite : eLpNorm V 2 volume ≠ ⊤ := hVmem.eLpNorm_ne_top
  have hWfinite : eLpNorm W 2 volume ≠ ⊤ := hWmem.eLpNorm_ne_top
  have hV4boundFinite :
      3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        eLpNorm V 2 volume ^ (1 / 4 : ℝ) *
          eLpNorm W 2 volume ^ (3 / 4 : ℝ) < ⊤ := by
    have hSf : CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSfinite
    have hVf : (eLpNorm V 2 volume) ^ (1 / 4 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hVfinite
    have hWf : (eLpNorm W 2 volume) ^ (3 / 4 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hWfinite
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hSf) hVf) hWf
  have hV4mem : MemLp V (ENNReal.ofReal (4 : ℝ)) volume :=
    memLp_iff.mpr (lt_of_le_of_lt hV4bound hV4boundFinite)
  rcases regTails_scalar_l4_flux_bounds V W B G hG hVnonneg hV4bound
      hV4boundFinite hV4mem hUboundL2 hGdef with ⟨hV4realBound, hV4sqmem⟩
  have hMoll4bound : (eLpNorm J (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      (eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
    simpa [J, V] using
      regTails_mollified_velocity_l4_bound ρ ε hε u t ht hU2 hV4mem
  have hR4bound := regTails_pressure_slice_norm_bound ρ ε hε u p hU2 hUbound hR4 t ht
  rcases hR4 t ht with ⟨hF, hPressureEq⟩
  let Ftensor : PressureTensorLp (2 : ℝ) := fun i j =>
    (hF i j).toLp (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
  have hPressureRep : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
      rieszPressureSlice (2 : ℝ) (by norm_num) Ftensor := by
    exact hPressureEq.trans
      (rieszPressureSliceRepresentative_ae_eq (2 : ℝ) (by norm_num) Ftensor).symm
  have hPmem : MemLp (fun x : Vec3 => p (x, t)) 2 volume := by
    apply (memLp_congr_ae hPressureRep).2
    simpa using (Lp.memLp (rieszPressureSlice (2 : ℝ) (by norm_num) Ftensor))
  have hPnormBound := regTails_pressure_l2_scalar_bound V J P B G hB hG
    hR4bound hMoll4bound hV4realBound
  rcases regTails_holder_flux_estimates V W J P B G hB hG hVmem hWmem hJmem hPmem
      hV4sqmem hVmeas hVnonneg hWnonneg
      (fun x => vec3EuclideanNorm_nonneg _) hUboundL2 hGdef hJbound
      hV4realBound hPnormBound with
    ⟨hVWint, hV2Jint, hPVint, hDiffInt, hConvInt, hPressInt⟩
  have hpoint : ∀ x : Vec3, F x ≤
      18 * M * V x * W x + 3 * M * V x ^ (2 : ℕ) * J x +
        6 * M * |P x| * V x := by
    intro x
    simpa [F, D, V, W, J, P] using
      regTails_slice_flux_pointwise_majorant ρ ε hε u p D t M q hDq x
  exact regTails_flux_integral_assembly F V W J P M B G hM hB hG
    hVWint hV2Jint hPVint hDiffInt hConvInt hPressInt hpoint


end CKN.Leray

end
