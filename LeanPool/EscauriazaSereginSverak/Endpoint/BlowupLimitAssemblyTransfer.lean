/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientProjection
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Reading off the compactness conclusions

`lem:compactness` of the CKN manuscript states its conclusions in Hilbert-valued L² spaces.
These lemmas convert them into the coordinate pairings, the coordinate
L² distances, and the gradient integrability used in `prop:blowup-limit`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Hilbert pairing of two vector slices on a set carrying the second
slice is the whole-space coordinate pairing. -/
theorem blowupLimitAssembly_inner_eq_pairing
    {C : Set Vec3} (u ψ : Vec3 → Vec3) (hψC : ∀ x ∉ C, ψ x = 0)
    (hu : MemLp (fun x => (WithLp.toLp 2 (u x) : L2Vec3)) 2 (volume.restrict C))
    (hψ : MemLp (fun x => (WithLp.toLp 2 (ψ x) : L2Vec3)) 2 (volume.restrict C)) :
    inner ℝ (hu.toLp _) (hψ.toLp _) = ∫ x : Vec3, ∑ i : Fin 3, u x i * ψ x i := by
  rw [CKN.Leray.inner_toLp_vec3_eq_integral_dot_measure _ _ _ hu hψ]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [hψC x hx]

/-- A vector slice in L² of a set pairs integrably with a test carried by
that set. -/
theorem blowupLimitAssembly_integrable_pairing
    {C : Set Vec3} (u ψ : Vec3 → Vec3) (hψC : ∀ x ∉ C, ψ x = 0)
    (hu : MemLp (fun x => (WithLp.toLp 2 (u x) : L2Vec3)) 2 (volume.restrict C))
    (hψ : MemLp (fun x => (WithLp.toLp 2 (ψ x) : L2Vec3)) 2 (volume.restrict C)) :
    Integrable (fun x => ∑ i : Fin 3, u x i * ψ x i) := by
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hu.toLp _) (hψ.toLp _)
  have hon : IntegrableOn (fun x => ∑ i : Fin 3, u x i * ψ x i) C := by
    refine hint.congr ?_
    filter_upwards [hu.coeFn_toLp, hψ.coeFn_toLp] with x hx hy
    rw [hx, hy, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.inner_apply]
  apply hon.integrable_of_forall_notMem_eq_zero
  intro x hx
  simp [hψC x hx]

/-- The coordinate sup norm is dominated by the Euclidean norm of the
Hilbert copy. -/
theorem blowupLimitAssembly_norm_sub_le (a b : Vec3) :
    ‖a - b‖ ≤ ‖(WithLp.toLp 2 a : L2Vec3) - WithLp.toLp 2 b‖ := by
  rw [← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2]
  exact norm_le_vec3EuclideanNorm _

/-- The sup norm of a gradient matrix is controlled by its energy density. -/
theorem blowupLimitAssembly_norm_sq_le_spatialGradientSq
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    ‖Du z‖ ^ 2 ≤ spatialGradientSq u Du z := by
  have hnn : 0 ≤ spatialGradientSq u Du z := by
    unfold spatialGradientSq
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle : ‖Du z‖ ≤ Real.sqrt (spatialGradientSq u Du z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    unfold spatialGradientSq
    have hrow : (Du z i j) ^ 2 ≤ ∑ m : Fin 3, (Du z i m) ^ 2 :=
      Finset.single_le_sum (f := fun m => (Du z i m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ j)
    have hall : ∑ m : Fin 3, (Du z i m) ^ 2 ≤
        ∑ l : Fin 3, ∑ m : Fin 3, (Du z l m) ^ 2 :=
      Finset.single_le_sum (f := fun l => ∑ m : Fin 3, (Du z l m) ^ 2)
        (fun l _ => Finset.sum_nonneg fun m _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact hrow.trans hall
  calc
    ‖Du z‖ ^ 2 ≤ (Real.sqrt (spatialGradientSq u Du z)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = spatialGradientSq u Du z := Real.sq_sqrt hnn

/-- A measurable gradient with finite iterated energy on a product set is
square integrable on every subset. -/
theorem blowupLimitAssembly_memLp_gradient_of_energy
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hDu : Measurable Du) (C : Set Vec3) (a b : ℝ)
    (hfin : (∫⁻ t in Icc a b, ∫⁻ x in C,
      ENNReal.ofReal (spatialGradientSq u Du (x,t))) < ⊤)
    (Q : Set (Vec3 × ℝ)) (hQ : Q ⊆ C ×ˢ Icc a b) :
    MemLp Du 2 (volume.restrict Q) := by
  have hSGS : Measurable (fun z : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq u Du z)) :=
    ENNReal.measurable_ofReal.comp
      (blowupLimitAssembly_measurable_spatialGradientSq u Du hDu)
  have hprod : (∫⁻ z in C ×ˢ Icc a b,
      ENNReal.ofReal (spatialGradientSq u Du z)) =
      ∫⁻ t in Icc a b, ∫⁻ x in C,
        ENNReal.ofReal (spatialGradientSq u Du (x,t)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod_symm _ hSGS.aemeasurable]
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hDu.aestronglyMeasurable]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  apply ne_of_lt
  calc
    (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ≥0∞).toReal) ≤
        ∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z) := by
      apply lintegral_mono
      intro z
      change ‖Du z‖ₑ ^ (2 : ℝ≥0∞).toReal ≤
        ENNReal.ofReal (spatialGradientSq u Du z)
      rw [← ofReal_norm, ENNReal.toReal_ofNat,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have h := blowupLimitAssembly_norm_sq_le_spatialGradientSq u Du z
      rw [← Real.rpow_natCast] at h
      exact_mod_cast h
    _ ≤ ∫⁻ z in C ×ˢ Icc a b, ENNReal.ofReal (spatialGradientSq u Du z) :=
      lintegral_mono_set hQ
    _ < ⊤ := by rw [hprod]; exact hfin

end ESS

end
