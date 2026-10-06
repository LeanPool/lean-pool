/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropPairingModulus
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Reg Equicontinuity

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open CKN
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray



private theorem regEqui_ibp_against_compact
    {F DF G : Vec3 → ℝ} (j : Fin 3)
    (hF : Continuous F) (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (hFd : ∀ x, fderiv ℝ F x (basisVec j) = DF x)
    (hDF : Continuous DF) (hG : ContDiff ℝ 1 G)
    (hGc : HasCompactSupport G) :
    ∫ x, DF x * G x = -∫ x, F x * spatialDeriv G j x := by
  have hGd : Continuous (spatialDeriv G j) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hGdc : HasCompactSupport (spatialDeriv G j) := by
    change HasCompactSupport (fun x => (fderiv ℝ G x) (basisVec j))
    exact hGc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := F) (f' := DF) (g := G)
    (g' := fun x => (fderiv ℝ G x) (basisVec j)) (v := basisVec j)
    (lerayHopfLimit_integrable_mul_compact hDF hG.continuous hGc)
    (lerayHopfLimit_integrable_mul_compact hF hGd hGdc)
    (lerayHopfLimit_integrable_mul_compact hF hG.continuous hGc)
    (fun x _ => by
      rw [← hFd x]
      exact (hFdiff x).hasFDerivAt.hasLineDerivAt (basisVec j))
    (fun x _ => by
      exact (((hG.differentiable (by norm_num) x).hasFDerivAt).hasLineDerivAt
        (basisVec j)))
  have h' := congrArg (fun r : ℝ => -r) h
  simpa [spatialDeriv] using h'.symm

theorem regEqui_pairing_equation_ibp
    (f : Fin 3 → Vec3 → ℝ) (g : Fin 3 → Fin 3 → Vec3 → ℝ)
    (h : Fin 3 → Fin 3 → Fin 3 → Vec3 → ℝ) (P : Vec3 → ℝ)
    (q J F : Fin 3 → Vec3 → ℝ) (w : Fin 3 → Vec3 → ℝ)
    (hf : ∀ i, Continuous (f i)) (hfdiff : ∀ i x, DifferentiableAt ℝ (f i) x)
    (hfd : ∀ i j x, fderiv ℝ (f i) x (basisVec j) = g i j x)
    (hg : ∀ i j, Continuous (g i j))
    (hgdiff : ∀ i j x, DifferentiableAt ℝ (g i j) x)
    (hgd : ∀ i j k x, fderiv ℝ (g i j) x (basisVec k) = h i j k x)
    (hh : ∀ i j k, Continuous (h i j k))
    (hP : Continuous P) (hPdiff : ∀ x, DifferentiableAt ℝ P x)
    (hPd : ∀ i x, fderiv ℝ P x (basisVec i) = q i x)
    (hq : ∀ i, Continuous (q i))
    (hJ : ∀ j, ContDiff ℝ 1 (J j))
    (hdivJ : ∀ x, ∑ j : Fin 3, fderiv ℝ (J j) x (basisVec j) = 0)
    (hF : ∀ i x, F i x =
      (∑ j : Fin 3, h i j j x) - (∑ j : Fin 3, J j x * g i j x) - q i x)
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i))
    (hwc : ∀ i, HasCompactSupport (w i)) :
    ∫ x, ∑ i : Fin 3, F i x * w i x =
    (∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
          f i x * J j x * spatialDeriv (w i) j x)) +
      ∫ x, P x * ∑ i : Fin 3, spatialDeriv (w i) i x := by
  have hdw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (w i) j) :=
    fun i j => contDiff_spatialDeriv_smooth (hw i) j
  have hdwc : ∀ i j, HasCompactSupport (spatialDeriv (w i) j) := by
    intro i j
    change HasCompactSupport (fun x => (fderiv ℝ (w i) x) (basisVec j))
    exact (hwc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hddw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
      (spatialDeriv (spatialDeriv (w i) j) j) :=
    fun i j => contDiff_spatialDeriv_smooth (hdw i j) j
  have hddwc : ∀ i j, HasCompactSupport
      (spatialDeriv (spatialDeriv (w i) j) j) := by
    intro i j
    change HasCompactSupport
      (fun x => (fderiv ℝ (spatialDeriv (w i) j) x) (basisVec j))
    exact (hdwc i j).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hJc : ∀ j, Continuous (J j) := fun j => (hJ j).continuous
  have hJd : ∀ j, Continuous (fun x => fderiv ℝ (J j) x (basisVec j)) := by
    intro j
    exact (hJ j).continuous_fderiv (by norm_num) |>.clm_apply continuous_const
  have hvisc : ∀ i j, ∫ x, h i j j x * w i x =
      ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x := by
    intro i j
    have h1 := regEqui_ibp_against_compact j (hg i j) (hgdiff i j)
      (fun x => hgd i j j x) (hh i j j)
      ((hw i).of_le (by exact_mod_cast le_top)) (hwc i)
    have h2 := regEqui_ibp_against_compact j (hf i) (hfdiff i)
      (fun x => hfd i j x) (hg i j)
      ((hdw i j).of_le (by exact_mod_cast le_top)) (hdwc i j)
    calc
      ∫ x, h i j j x * w i x = -∫ x, g i j x * spatialDeriv (w i) j x := h1
      _ = ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x := by
        rw [h2]
        ring
  have hpress : ∀ i, ∫ x, q i x * w i x =
      -∫ x, P x * spatialDeriv (w i) i x := by
    intro i
    have h1 := regEqui_ibp_against_compact i hP hPdiff
      (hPd i) (hq i) ((hw i).of_le (by exact_mod_cast le_top)) (hwc i)
    linarith only [h1]
  have hprod : ∀ i j, ContDiff ℝ 1 (fun x => J j x * w i x) :=
    fun i j => (hJ j).mul ((hw i).of_le (by exact_mod_cast le_top))
  have hprodd : ∀ i j x,
      fderiv ℝ (fun x => J j x * w i x) x (basisVec j) =
        fderiv ℝ (J j) x (basisVec j) * w i x +
          J j x * spatialDeriv (w i) j x := by
    intro i j x
    have hwd : DifferentiableAt ℝ (w i) x := ((hw i).differentiable (by simp)) x
    rw [fderiv_fun_mul ((hJ j).differentiable (by norm_num) x) hwd]
    simp only [add_apply, smul_apply, smul_eq_mul, spatialDeriv]
    ring
  have hprodc : ∀ i j, HasCompactSupport (fun x => J j x * w i x) :=
    fun i j => (hwc i).mul_left
  have htrans : ∀ i j, ∫ x, J j x * g i j x * w i x =
      -∫ x, f i x * (fderiv ℝ (J j) x (basisVec j) * w i x +
        J j x * spatialDeriv (w i) j x) := by
    intro i j
    have hcont : Continuous (fun x =>
        fderiv ℝ (J j) x (basisVec j) * w i x +
          J j x * spatialDeriv (w i) j x) :=
      ((hJd j).mul (hw i).continuous).add ((hJc j).mul (hdw i j).continuous)
    have hcpt : HasCompactSupport (fun x =>
        fderiv ℝ (J j) x (basisVec j) * w i x +
          J j x * spatialDeriv (w i) j x) :=
      ((hwc i).mul_left).add ((hdwc i j).mul_left)
    have hIntDF : Integrable (fun x => f i x *
        (fderiv ℝ (J j) x (basisVec j) * w i x +
          J j x * spatialDeriv (w i) j x)) :=
      lerayHopfLimit_integrable_mul_compact (hf i) hcont hcpt
    have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) (f := f i)
      (f' := g i j) (g := fun x => J j x * w i x)
      (g' := fun x => fderiv ℝ (J j) x (basisVec j) * w i x +
        J j x * spatialDeriv (w i) j x) (v := basisVec j)
      (by
        have hcont' : Continuous (fun x => J j x * w i x) := (hJc j).mul (hw i).continuous
        exact lerayHopfLimit_integrable_mul_compact (hg i j) hcont' (hprodc i j))
      hIntDF
      (lerayHopfLimit_integrable_mul_compact (hf i) ((hJc j).mul (hw i).continuous)
        (hprodc i j))
      (fun x _ => by
        rw [← hfd i j x]
        exact (hfdiff i x).hasFDerivAt.hasLineDerivAt (basisVec j))
      (fun x _ => by
        have hdiffAt := (hprod i j).differentiable (by norm_num) x
        rw [← hprodd i j x]
        exact hdiffAt.hasFDerivAt.hasLineDerivAt (basisVec j))
    have hleft : ∫ x, J j x * g i j x * w i x =
        ∫ x, g i j x * (J j x * w i x) := by
      congr 1
      funext x
      ring
    have h' : ∫ x, f i x *
        (fderiv ℝ (J j) x (basisVec j) * w i x +
          J j x * spatialDeriv (w i) j x) =
          -∫ x, g i j x * (J j x * w i x) := by
      simpa only [ContinuousLinearMap.mul_apply'] using h
    linarith only [hleft, h']
  have htransSum : ∀ i, ∑ j : Fin 3, ∫ x, J j x * g i j x * w i x =
      -∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
    intro i
    have hderivInt : Integrable (fun x => ∑ j : Fin 3, f i x *
        (fderiv ℝ (J j) x (basisVec j) * w i x +
          J j x * spatialDeriv (w i) j x)) :=
      integrable_finsetSum _ (fun j _ => lerayHopfLimit_integrable_mul_compact (hf i)
        (((hJd j).mul (hw i).continuous).add ((hJc j).mul (hdw i j).continuous))
        (((hwc i).mul_left).add ((hdwc i j).mul_left)))
    calc
      ∑ j : Fin 3, ∫ x, J j x * g i j x * w i x =
          -∑ j : Fin 3, ∫ x, f i x *
            (fderiv ℝ (J j) x (basisVec j) * w i x +
              J j x * spatialDeriv (w i) j x) := by
                simp_rw [htrans]
                rw [Finset.sum_neg_distrib]
      _ = -∫ x, ∑ j : Fin 3, f i x *
            (fderiv ℝ (J j) x (basisVec j) * w i x +
              J j x * spatialDeriv (w i) j x) := by
                congr 1
                exact (integral_finsetSum _ (fun j _ =>
                  lerayHopfLimit_integrable_mul_compact (hf i)
                    (((hJd j).mul (hw i).continuous).add
                      ((hJc j).mul (hdw i j).continuous))
                    (((hwc i).mul_left).add ((hdwc i j).mul_left)))).symm
      _ = -∫ x, ∑ j : Fin 3,
            f i x * J j x * spatialDeriv (w i) j x := by
                congr 1
                apply integral_congr_ae
                filter_upwards [] with x
                have hsplit : ∑ j : Fin 3, f i x *
                    (fderiv ℝ (J j) x (basisVec j) * w i x +
                      J j x * spatialDeriv (w i) j x) =
                    f i x * w i x *
                        (∑ j : Fin 3, fderiv ℝ (J j) x (basisVec j)) +
                      ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
                  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
                rw [hsplit, hdivJ x, mul_zero, zero_add]
  have hIhw : ∀ i j, Integrable (fun x => h i j j x * w i x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact (hh i j j) (hw i).continuous (hwc i)
  have hIJgw : ∀ i j, Integrable (fun x => J j x * g i j x * w i x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact ((hJc j).mul (hg i j))
      (hw i).continuous (hwc i)
  have hIqw : ∀ i, Integrable (fun x => q i x * w i x) := fun i =>
    lerayHopfLimit_integrable_mul_compact (hq i) (hw i).continuous (hwc i)
  have hIfddw : ∀ i j, Integrable
      (fun x => f i x * spatialDeriv (spatialDeriv (w i) j) j x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact (hf i) (hddw i j).continuous (hddwc i j)
  have hIfJdw : ∀ i j, Integrable
      (fun x => f i x * J j x * spatialDeriv (w i) j x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact ((hf i).mul (hJc j))
      (hdw i j).continuous (hdwc i j)
  have hIfPdw : ∀ i, Integrable (fun x => P x * spatialDeriv (w i) i x) := fun i =>
    lerayHopfLimit_integrable_mul_compact hP (hdw i i).continuous (hdwc i i)
  have hpointwise : ∀ i, (fun x => F i x * w i x) = fun x =>
        (∑ j : Fin 3, h i j j x * w i x) -
          (∑ j : Fin 3, J j x * g i j x * w i x) - q i x * w i x := by
    intro i
    funext x
    rw [hF i x, sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
  have hIfw : ∀ i, Integrable (fun x => F i x * w i x) := by
    intro i
    rw [hpointwise i]
    exact ((integrable_finsetSum _ (fun j _ => hIhw i j)).sub
      (integrable_finsetSum _ (fun j _ => hIJgw i j))).sub (hIqw i)
  have hi : ∀ i, ∫ x, F i x * w i x =
      (∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
        ((∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x) +
          ∫ x, P x * spatialDeriv (w i) i x) := by
    intro i
    have hrows : Integrable (fun x => ∑ j : Fin 3,
        h i j j x * w i x) := integrable_finsetSum _ (fun j _ => hIhw i j)
    have htransrow : Integrable (fun x => ∑ j : Fin 3,
        J j x * g i j x * w i x) := integrable_finsetSum _ (fun j _ => hIJgw i j)
    have hpointwiseIntegral : ∫ x, F i x * w i x =
        ∫ x, (∑ j : Fin 3, h i j j x * w i x) -
          (∑ j : Fin 3, J j x * g i j x * w i x) - q i x * w i x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrFun (hpointwise i) x
    have hsubIntegral : ∫ x,
        (∑ j : Fin 3, h i j j x * w i x) -
          (∑ j : Fin 3, J j x * g i j x * w i x) - q i x * w i x =
        (∑ j : Fin 3, ∫ x, h i j j x * w i x) -
          (∑ j : Fin 3, ∫ x, J j x * g i j x * w i x) -
            ∫ x, q i x * w i x := by
      calc
        ∫ x, ((∑ j : Fin 3, h i j j x * w i x) -
            (∑ j : Fin 3, J j x * g i j x * w i x)) - q i x * w i x =
          (∫ x, (∑ j : Fin 3, h i j j x * w i x) -
            (∑ j : Fin 3, J j x * g i j x * w i x)) - ∫ x, q i x * w i x :=
              integral_sub (hrows.sub htransrow) (hIqw i)
        _ = ((∫ x, ∑ j : Fin 3, h i j j x * w i x) -
            ∫ x, ∑ j : Fin 3, J j x * g i j x * w i x) -
              ∫ x, q i x * w i x := by
                rw [integral_sub hrows htransrow]
        _ = ((∑ j : Fin 3, ∫ x, h i j j x * w i x) -
            ∑ j : Fin 3, ∫ x, J j x * g i j x * w i x) -
              ∫ x, q i x * w i x := by
                rw [integral_finsetSum _ (fun j _ => hIhw i j),
                  integral_finsetSum _ (fun j _ => hIJgw i j)]
    calc
      ∫ x, F i x * w i x =
          (∑ j : Fin 3, ∫ x, h i j j x * w i x) -
            (∑ j : Fin 3, ∫ x, J j x * g i j x * w i x) -
              ∫ x, q i x * w i x := hpointwiseIntegral.trans hsubIntegral
      _ = (∑ j : Fin 3, ∫ x, f i x *
            spatialDeriv (spatialDeriv (w i) j) j x) -
          (-∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x) -
          (-∫ x, P x * spatialDeriv (w i) i x) := by
            rw [htransSum i, hpress i]
            have hsumVisc :
                (∑ j : Fin 3, ∫ x, h i j j x * w i x) =
                  ∑ j : Fin 3, ∫ x, f i x *
                    spatialDeriv (spatialDeriv (w i) j) j x := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hvisc i j
            rw [hsumVisc]
      _ = (∑ j : Fin 3, ∫ x, f i x *
            spatialDeriv (spatialDeriv (w i) j) j x) +
          ((∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x) +
            ∫ x, P x * spatialDeriv (w i) i x) := by ring
  have hRHS : ∀ i, Integrable (fun x => ∑ j : Fin 3,
      (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
        f i x * J j x * spatialDeriv (w i) j x)) := by
    intro i
    exact integrable_finsetSum _ (fun j _ => (hIfddw i j).add (hIfJdw i j))
  have hpressRow : Integrable (fun x => P x *
      ∑ i : Fin 3, spatialDeriv (w i) i x) := by
    rw [show (fun x => P x * ∑ i : Fin 3, spatialDeriv (w i) i x) =
        fun x => ∑ i : Fin 3, P x * spatialDeriv (w i) i x by
          funext x; rw [Finset.mul_sum]]
    exact integrable_finsetSum _ (fun i _ => hIfPdw i)
  calc
    ∫ x, ∑ i : Fin 3, F i x * w i x =
        ∑ i : Fin 3, ∫ x, F i x * w i x :=
      integral_finsetSum _ (fun i _ => hIfw i)
    _ = ∑ i : Fin 3,
        ((∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
          ((∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x) +
            (∫ x, P x * spatialDeriv (w i) i x))) := by
      apply Finset.sum_congr rfl
      intro i hi'
      exact hi i
    _ = (∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
          (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
            f i x * J j x * spatialDeriv (w i) j x)) +
        ∫ x, P x * ∑ i : Fin 3, spatialDeriv (w i) i x := by
      have hsplitRow (i : Fin 3) :
          ∫ x, ∑ j : Fin 3,
              (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
                f i x * J j x * spatialDeriv (w i) j x) =
            (∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
              ∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
        calc
          ∫ x, ∑ j : Fin 3,
              (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
                f i x * J j x * spatialDeriv (w i) j x) =
              ∑ j : Fin 3, ∫ x,
                (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
                  f i x * J j x * spatialDeriv (w i) j x) :=
                    integral_finsetSum _ (fun j _ => (hIfddw i j).add (hIfJdw i j))
          _ = ∑ j : Fin 3,
                ((∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
                  ∫ x, f i x * J j x * spatialDeriv (w i) j x) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    exact integral_add (hIfddw i j) (hIfJdw i j)
          _ = (∑ j : Fin 3, ∫ x, f i x *
                spatialDeriv (spatialDeriv (w i) j) j x) +
              ∑ j : Fin 3, ∫ x, f i x * J j x * spatialDeriv (w i) j x :=
                Finset.sum_add_distrib
          _ = (∑ j : Fin 3, ∫ x, f i x *
                spatialDeriv (spatialDeriv (w i) j) j x) +
              ∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
                rw [← integral_finsetSum _ (fun j _ => hIfJdw i j)]
      have hrowSum : ∑ i : Fin 3,
          ((∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
            ∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x) =
          ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
            (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
              f i x * J j x * spatialDeriv (w i) j x) := by
        calc
          _ = ∑ i : Fin 3, ∫ x, ∑ j : Fin 3,
                (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
                  f i x * J j x * spatialDeriv (w i) j x) := by
                    apply Finset.sum_congr rfl
                    intro i hi'
                    exact (hsplitRow i).symm
          _ = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
                (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
                  f i x * J j x * spatialDeriv (w i) j x) :=
                    (integral_finsetSum _ (fun i _ => hRHS i)).symm
      have hpressSum : ∑ i : Fin 3, ∫ x, P x * spatialDeriv (w i) i x =
          ∫ x, P x * ∑ i : Fin 3, spatialDeriv (w i) i x := by
        calc
          _ = ∫ x, ∑ i : Fin 3, P x * spatialDeriv (w i) i x :=
                (integral_finsetSum _ (fun i _ => hIfPdw i)).symm
          _ = ∫ x, P x * ∑ i : Fin 3, spatialDeriv (w i) i x := by
                apply integral_congr_ae
                filter_upwards [] with x
                rw [Finset.mul_sum]
      let A : Fin 3 → ℝ := fun i =>
        ∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x
      let B : Fin 3 → ℝ := fun i =>
        ∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x
      let C : Fin 3 → ℝ := fun i => ∫ x, P x * spatialDeriv (w i) i x
      have hassoc :
          (∑ i : Fin 3, (A i + (B i + C i))) =
            ∑ i : Fin 3, ((A i + B i) + C i) := by
        apply Finset.sum_congr rfl
        intro i hi'
        exact (add_assoc (A i) (B i) (C i)).symm
      have hrowSum' : (∑ i : Fin 3, (A i + B i)) =
          ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
            (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
              f i x * J j x * spatialDeriv (w i) j x) := hrowSum
      have hpressSum' : (∑ i : Fin 3, C i) =
          ∫ x, P x * ∑ i : Fin 3, spatialDeriv (w i) i x := hpressSum
      change (∑ i : Fin 3, (A i + (B i + C i))) = _
      rw [hassoc, Finset.sum_add_distrib, hrowSum', hpressSum']



/-- The positive-time pressure bound can be localized to a measurable
space-time set before it is paired with a test derivative. -/
theorem regEquicontinuity_pressure_mul_memLp_one
    (p g : ParabolicPoint → ℝ) (Q : Set ParabolicPoint)
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      regUniformPositiveTimeMeasure)
    (hg : MemLp g (ENNReal.ofReal (5 / 2 : ℝ))
      (regUniformPositiveTimeMeasure.restrict Q)) :
    MemLp (fun z => p z * g z) 1
      (regUniformPositiveTimeMeasure.restrict Q) ∧
    eLpNorm (fun z => p z * g z) 1
      (regUniformPositiveTimeMeasure.restrict Q) ≤
      eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
        eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
          (regUniformPositiveTimeMeasure.restrict Q) := by
  have : ENNReal.HolderTriple (ENNReal.ofReal (5 / 3 : ℝ))
      (ENNReal.ofReal (5 / 2 : ℝ)) 1 := by
    have h : (5 / 3 : ℝ).HolderTriple (5 / 2 : ℝ) 1 := by
      constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hpQ : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      (regUniformPositiveTimeMeasure.restrict Q) :=
    hp.mono_measure (Measure.restrict_le_self)
  have hprod : MemLp (fun z => p z * g z) 1
      (regUniformPositiveTimeMeasure.restrict Q) := hpQ.mul hg
  have hnorm := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (p := ENNReal.ofReal (5 / 3 : ℝ)) (q := ENNReal.ofReal (5 / 2 : ℝ))
    (r := (1 : ℝ≥0∞))
    (fun x y : ℝ => x * y) 1 continuous_mul
    hpQ.aestronglyMeasurable hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      simp)
  refine ⟨hprod, ?_⟩
  calc
    eLpNorm (fun z => p z * g z) 1
        (regUniformPositiveTimeMeasure.restrict Q) ≤
          eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
          (regUniformPositiveTimeMeasure.restrict Q) *
          eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
            (regUniformPositiveTimeMeasure.restrict Q) := by
      simpa using hnorm
    _ ≤ eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
          regUniformPositiveTimeMeasure *
          eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
            (regUniformPositiveTimeMeasure.restrict Q) := by
      exact mul_le_mul_of_nonneg_right
        (eLpNorm_mono_measure p Measure.restrict_le_self)
        (by positivity)

/-- The exponent-two pressure slice formula identifies the pressure with the
space-time Riesz representative at exponent five-thirds whenever the
regularized tensor has its global five-thirds bound. This is the pressure
input to `lem:reg-equicontinuity`. -/
theorem regEquicontinuity_pressure_memLp_fiveThirds
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hFbound : ∀ i j,
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal M)
    (p : ParabolicPoint → ℝ) (hpMeasurable : Measurable p)
    (hR4 : ∀ t : ℝ, 0 < t → ∃ hFt : ∀ i j,
      MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal (2 : ℝ))
        (volume : Measure Vec3),
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t)))) :
    ∃ hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure,
      ‖hp.toLp p‖ ≤ 9 * rieszPressureOperatorBound
        (5 / 3 : ℝ) (by norm_num) * M := by
  let r : ℝ := 5 / 3
  let hr : 1 < r := by norm_num [r]
  let P : Vec3 × ℝ → ℝ := rieszPressureSpaceTime r hr F hF
  have hPFull : MemLp P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp r hr F hF
  have hPBound := regPressure_spaceTime_fiveThirds_norm_bound F hF M hM hFbound
  let hPClass := rieszPressureSpaceTimeClass r hr
    (rieszPressureSpaceTimeTensorToLp r hr F hF)
  have hPClassEq : P =ᵐ[volume] hPClass := by
    simpa [P, rieszPressureSpaceTime, rieszPressureSpaceTimeRepresentative,
      hPClass] using
      ((Lp.aestronglyMeasurable hPClass).aemeasurable.ae_eq_mk).symm
  have hSlice := rieszPressureSpaceTime_slice_ae_eq r hr F hF
  have hSliceEq : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        (fun x : Vec3 => P (x, t)) := by
    filter_upwards [ae_restrict_of_ae hSlice,
      ae_restrict_mem measurableSet_Ioi] with t hP hpos
    rcases hP with ⟨hFt53, hPae⟩
    obtain ⟨hFt2, hR4t⟩ := hR4 t hpos
    let F2 : PressureTensorLp (2 : ℝ) := fun i j =>
      (hFt2 i j).toLp (fun x : Vec3 => F i j (x, t))
    let F53 : PressureTensorLp r := fun i j =>
      (hFt53 i j).toLp (fun x : Vec3 => F i j (x, t))
    have hAgreement := rieszPressureSlice_ae_eq_of_memLp_common
      (2 : ℝ) (by norm_num) r hr (fun i j x => F i j (x, t)) hFt2 hFt53
    have hRep2 := rieszPressureSliceRepresentative_ae_eq
      (2 : ℝ) (by norm_num) F2
    change (fun x : Vec3 => p (x, t)) =ᵐ[volume] _ at hR4t
    change (fun x : Vec3 => P (x, t)) =ᵐ[volume]
      (rieszPressureSlice r hr F53 : Vec3 → ℝ) at hPae
    change (rieszPressureSlice (2 : ℝ) (by norm_num) F2 : Vec3 → ℝ) =ᵐ[volume]
      (rieszPressureSlice r hr F53 : Vec3 → ℝ) at hAgreement
    exact hR4t.trans (hRep2.symm.trans (hAgreement.trans hPae.symm))
  have hSmeas : MeasurableSet {z : Vec3 × ℝ | p z = P z} :=
    measurableSet_eq_fun hpMeasurable
      (rieszPressureSpaceTime_measurable r hr F hF)
  have hSliceEq' : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ x : Vec3 ∂volume, p (x, t) = P (x, t) := hSliceEq
  have hSswap : MeasurableSet
      {z : ℝ × Vec3 | p (z.2, z.1) = P (z.2, z.1)} := by
    change MeasurableSet (Prod.swap ⁻¹' {z : Vec3 × ℝ | p z = P z})
    exact measurableSet_swap_iff.mpr hSmeas
  have hSliceSwap : ∀ᵐ x : Vec3 ∂volume,
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), p (x, t) = P (x, t) :=
    (Measure.ae_ae_comm (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume) hSswap).mp hSliceEq'
  have hProduct : ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod
      (volume.restrict (Ioi (0 : ℝ)))), p z = P z :=
    (Measure.ae_prod_iff_ae_ae hSmeas).2 hSliceSwap
  have hPositiveTimeMeasure : regUniformPositiveTimeMeasure =
      (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hPositiveEq : p =ᵐ[regUniformPositiveTimeMeasure] P := by
    rw [hPositiveTimeMeasure]
    exact hProduct
  have hPositiveLe : regUniformPositiveTimeMeasure ≤
      (volume : Measure (Vec3 × ℝ)) := Measure.restrict_le_self
  let hPPositive : MemLp P (ENNReal.ofReal r) regUniformPositiveTimeMeasure :=
    hPFull.mono_measure hPositiveLe
  let hpPositive : MemLp p (ENNReal.ofReal r) regUniformPositiveTimeMeasure :=
    (memLp_congr_ae hPositiveEq).2 hPPositive
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hPFullEq : hPFull.toLp P = hPClass := by
    apply Lp.ext
    filter_upwards [hPFull.coeFn_toLp, hPClassEq] with z hz hclass
    exact hz.trans hclass
  refine ⟨hpPositive, ?_⟩
  calc
    ‖hpPositive.toLp p‖ ≤ ‖hPFull.toLp P‖ := by
      rw [Lp.norm_toLp p hpPositive, Lp.norm_toLp P hPFull]
      apply ENNReal.toReal_mono hPFull.eLpNorm_ne_top
      calc
        eLpNorm p (ENNReal.ofReal r) regUniformPositiveTimeMeasure =
            eLpNorm P (ENNReal.ofReal r) regUniformPositiveTimeMeasure :=
          eLpNorm_congr_ae hPositiveEq
        _ ≤ eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
          eLpNorm_mono_measure P hPositiveLe
    _ = ‖hPClass‖ := congrArg norm hPFullEq
    _ ≤ 9 * rieszPressureOperatorBound r hr * M := by
      simpa [hPClass] using hPBound

end CKN.Leray

end
