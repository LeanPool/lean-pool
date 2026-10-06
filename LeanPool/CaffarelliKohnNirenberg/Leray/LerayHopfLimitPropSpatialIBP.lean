/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Spatial integration by parts for the regularized pairing derivative

At a fixed positive time, the regularized momentum equation paired with a
smooth, compactly supported, divergence-free field reduces to the viscous
term with both derivatives on the test and the transport term with one
derivative on the test. This is the spatial computation in the proof of
`lem:reg-equicontinuity`.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A continuous scalar field times a continuous compactly supported field is
integrable. -/
theorem lerayHopfLimit_integrable_mul_compact
    {f g : Vec3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) := by
  exact (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- One-directional integration by parts against a smooth compactly supported
scalar test. -/
private theorem ibp_against_compact
    {F G : Vec3 → ℝ} {DF : Vec3 → ℝ} (j : Fin 3)
    (hF : Continuous F) (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (hFd : ∀ x, fderiv ℝ F x (basisVec j) = DF x) (hDF : Continuous DF)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ∫ x, F x * spatialDeriv G j x = -∫ x, DF x * G x := by
  have hGd : Continuous (spatialDeriv G j) :=
    (contDiff_spatialDeriv_smooth hG j).continuous
  have hGdc : HasCompactSupport (spatialDeriv G j) := by
    change HasCompactSupport (fun x => (fderiv ℝ G x) (basisVec j))
    exact hGc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := F) (g := G) (v := basisVec j)
    (by simpa only [hFd] using
      lerayHopfLimit_integrable_mul_compact hDF hG.continuous hGc)
    (lerayHopfLimit_integrable_mul_compact hF hGd hGdc)
    (lerayHopfLimit_integrable_mul_compact hF hG.continuous hGc)
    (fun x _ => hFdiff x)
    (fun x _ => (hG.differentiable (by simp)) x)
  simpa only [hFd, spatialDeriv] using h

/-- Pairing the classical regularized momentum equation at one time with a
smooth compactly supported divergence-free field. Here f i is the velocity
component, g i j its j-th partial derivative, h i j k the partial
derivative of g i j, P the pressure with partials q, and J the
divergence-free transport velocity. -/
theorem lerayHopfLimit_pairing_equation_ibp
    (f : Fin 3 → Vec3 → ℝ) (g : Fin 3 → Fin 3 → Vec3 → ℝ)
    (h : Fin 3 → Fin 3 → Fin 3 → Vec3 → ℝ)
    (P : Vec3 → ℝ) (q : Fin 3 → Vec3 → ℝ) (J : Fin 3 → Vec3 → ℝ)
    (F : Fin 3 → Vec3 → ℝ) (w : Fin 3 → Vec3 → ℝ)
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
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) (hwc : ∀ i, HasCompactSupport (w i))
    (hdivw : ∀ x, ∑ i : Fin 3, spatialDeriv (w i) i x = 0) :
    ∫ x, ∑ i : Fin 3, F i x * w i x =
      ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
          f i x * J j x * spatialDeriv (w i) j x) := by
  -- derivatives of the test
  have hdw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (w i) j) :=
    fun i j => contDiff_spatialDeriv_smooth (hw i) j
  have hdwc : ∀ i j, HasCompactSupport (spatialDeriv (w i) j) := by
    intro i j
    change HasCompactSupport (fun x => (fderiv ℝ (w i) x) (basisVec j))
    exact (hwc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hddw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (spatialDeriv (w i) j) j) :=
    fun i j => contDiff_spatialDeriv_smooth (hdw i j) j
  have hddwc : ∀ i j, HasCompactSupport (spatialDeriv (spatialDeriv (w i) j) j) := by
    intro i j
    change HasCompactSupport
      (fun x => (fderiv ℝ (spatialDeriv (w i) j) x) (basisVec j))
    exact (hdwc i j).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hJc : ∀ j, Continuous (J j) := fun j => (hJ j).continuous
  have hJdiff : ∀ j x, DifferentiableAt ℝ (J j) x :=
    fun j x => ((hJ j).differentiable (by norm_num)) x
  have hJd : ∀ j, Continuous (fun x => fderiv ℝ (J j) x (basisVec j)) := by
    intro j
    exact ((hJ j).continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- viscous term: two integrations by parts
  have hvisc : ∀ i j, ∫ x, h i j j x * w i x =
      ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x := by
    intro i j
    have h1 := ibp_against_compact (F := g i j) (DF := h i j j) j (hg i j)
      (hgdiff i j) (fun x => hgd i j j x) (hh i j j) (hw i) (hwc i)
    have h2 := ibp_against_compact (F := f i) (DF := g i j) j (hf i)
      (hfdiff i) (fun x => hfd i j x) (hg i j) (hdw i j) (hdwc i j)
    rw [h2]
    linarith only [h1]
  -- pressure term
  have hpress : ∀ i, ∫ x, q i x * w i x = -∫ x, P x * spatialDeriv (w i) i x := by
    intro i
    have h1 := ibp_against_compact (F := P) (DF := q i) i hP hPdiff
      (hPd i) (hq i) (hw i) (hwc i)
    linarith only [h1]
  have hpressSum : ∑ i : Fin 3, ∫ x, q i x * w i x = 0 := by
    simp only [hpress]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum]
    · simp only [← Finset.mul_sum, hdivw, mul_zero, integral_zero, neg_zero]
    · intro i _
      exact lerayHopfLimit_integrable_mul_compact hP (hdw i i).continuous (hdwc i i)
  -- transport term
  have hprod : ∀ i j, ContDiff ℝ 1 (fun x => J j x * w i x) :=
    fun i j => (hJ j).mul ((hw i).of_le (by exact_mod_cast le_top))
  have hprodd : ∀ i j x, fderiv ℝ (fun x => J j x * w i x) x (basisVec j) =
      fderiv ℝ (J j) x (basisVec j) * w i x + J j x * spatialDeriv (w i) j x := by
    intro i j x
    have hwd : DifferentiableAt ℝ (w i) x := ((hw i).differentiable (by simp)) x
    rw [fderiv_fun_mul (hJdiff j x) hwd]
    simp only [add_apply, smul_apply,
      smul_eq_mul, spatialDeriv]
    ring
  have hprodc : ∀ i j, HasCompactSupport (fun x => J j x * w i x) :=
    fun i j => (hwc i).mul_left
  have htrans : ∀ i j, ∫ x, J j x * g i j x * w i x =
      -∫ x, f i x * (fderiv ℝ (J j) x (basisVec j) * w i x +
        J j x * spatialDeriv (w i) j x) := by
    intro i j
    have hcont : Continuous (fun x => fderiv ℝ (J j) x (basisVec j) * w i x +
        J j x * spatialDeriv (w i) j x) :=
      ((hJd j).mul (hw i).continuous).add ((hJc j).mul (hdw i j).continuous)
    have hcpt : HasCompactSupport (fun x => fderiv ℝ (J j) x (basisVec j) * w i x +
        J j x * spatialDeriv (w i) j x) :=
      ((hwc i).mul_left).add ((hdwc i j).mul_left)
    have hint := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := f i) (g := fun x => J j x * w i x) (v := basisVec j)
      (by
        simp only [hfd]
        exact lerayHopfLimit_integrable_mul_compact (hg i j)
          ((hJc j).mul (hw i).continuous) (hprodc i j))
      (by
        simp only [hprodd]
        exact lerayHopfLimit_integrable_mul_compact (hf i) hcont hcpt)
      (lerayHopfLimit_integrable_mul_compact (hf i)
        ((hJc j).mul (hw i).continuous) (hprodc i j))
      (fun x _ => hfdiff i x)
      (fun x _ => ((hprod i j).differentiable (by norm_num)) x)
    simp only [hfd, hprodd] at hint
    have hleft : ∫ x, J j x * g i j x * w i x = ∫ x, g i j x * (J j x * w i x) := by
      congr 1
      funext x
      ring
    rw [hleft, hint, neg_neg]
  -- integrability of the pieces
  have hIhw : ∀ i j, Integrable (fun x => h i j j x * w i x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact (hh i j j) (hw i).continuous (hwc i)
  have hIJgw : ∀ i j, Integrable (fun x => J j x * g i j x * w i x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact ((hJc j).mul (hg i j)) (hw i).continuous (hwc i)
  have hIqw : ∀ i, Integrable (fun x => q i x * w i x) := fun i =>
    lerayHopfLimit_integrable_mul_compact (hq i) (hw i).continuous (hwc i)
  have hIfddw : ∀ i j, Integrable
      (fun x => f i x * spatialDeriv (spatialDeriv (w i) j) j x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact (hf i) (hddw i j).continuous (hddwc i j)
  have hIfJdw : ∀ i j, Integrable
      (fun x => f i x * J j x * spatialDeriv (w i) j x) := fun i j =>
    lerayHopfLimit_integrable_mul_compact ((hf i).mul (hJc j)) (hdw i j).continuous
      (hdwc i j)
  have hIfdJ : ∀ i j, Integrable (fun x => f i x *
      (fderiv ℝ (J j) x (basisVec j) * w i x + J j x * spatialDeriv (w i) j x)) := by
    intro i j
    exact lerayHopfLimit_integrable_mul_compact (hf i)
      (((hJd j).mul (hw i).continuous).add ((hJc j).mul (hdw i j).continuous))
      (((hwc i).mul_left).add ((hdwc i j).mul_left))
  have htransSum : ∀ i, ∑ j : Fin 3, ∫ x, J j x * g i j x * w i x =
      -∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
    intro i
    simp only [htrans]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hIfdJ i j)]
    congr 2
    funext x
    have hsplit : ∑ j : Fin 3, f i x *
        (fderiv ℝ (J j) x (basisVec j) * w i x + J j x * spatialDeriv (w i) j x) =
        f i x * w i x * (∑ j : Fin 3, fderiv ℝ (J j) x (basisVec j)) +
          ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit, hdivJ x, mul_zero, zero_add]
  have hpt : ∀ i, (fun x => F i x * w i x) = fun x =>
      (∑ j : Fin 3, h i j j x * w i x) - (∑ j : Fin 3, J j x * g i j x * w i x) -
        q i x * w i x := by
    intro i
    funext x
    rw [hF i x, sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
  have hIFw : ∀ i, Integrable (fun x => F i x * w i x) := by
    intro i
    rw [hpt i]
    exact ((integrable_finsetSum _ (fun j _ => hIhw i j)).sub
      (integrable_finsetSum _ (fun j _ => hIJgw i j))).sub (hIqw i)
  have hi : ∀ i, ∫ x, F i x * w i x =
      (∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
        (∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x) -
        ∫ x, q i x * w i x := by
    intro i
    rw [hpt i, integral_sub, integral_sub, integral_finsetSum _ (fun j _ => hIhw i j),
      integral_finsetSum _ (fun j _ => hIJgw i j), htransSum i]
    · simp only [hvisc]
      ring
    · exact integrable_finsetSum _ (fun j _ => hIhw i j)
    · exact integrable_finsetSum _ (fun j _ => hIJgw i j)
    · exact (integrable_finsetSum _ (fun j _ => hIhw i j)).sub
        (integrable_finsetSum _ (fun j _ => hIJgw i j))
    · exact hIqw i
  have hRHS : ∀ i, ∫ x, ∑ j : Fin 3,
      (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
        f i x * J j x * spatialDeriv (w i) j x) =
      (∑ j : Fin 3, ∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x) +
        ∫ x, ∑ j : Fin 3, f i x * J j x * spatialDeriv (w i) j x := by
    intro i
    simp only [Finset.sum_add_distrib]
    rw [integral_add (integrable_finsetSum _ (fun j _ => hIfddw i j))
      (integrable_finsetSum _ (fun j _ => hIfJdw i j)),
      integral_finsetSum _ (fun j _ => hIfddw i j)]
  have hIrow : ∀ i, Integrable (fun x => ∑ j : Fin 3,
      (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
        f i x * J j x * spatialDeriv (w i) j x)) := fun i =>
    integrable_finsetSum _ (fun j _ => (hIfddw i j).add (hIfJdw i j))
  rw [integral_finsetSum _ (fun i _ => hIFw i), integral_finsetSum _ (fun i _ => hIrow i)]
  simp only [hi, hRHS]
  rw [Finset.sum_sub_distrib, hpressSum, sub_zero]

end CKN.Leray

end
