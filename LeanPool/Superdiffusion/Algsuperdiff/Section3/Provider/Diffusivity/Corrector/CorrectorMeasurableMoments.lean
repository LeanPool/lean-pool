/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableGradient

/-!
# Measurable positive moments of finite-volume corrector gradients

The clamped norm powers give continuous functionals on the Hilbert `L²` carrier.
Monotone convergence then gives Borel measurability of every positive integral
moment, including the quartic and octic observables.

Adapted from Scott Armstrong’s quartic and octic arguments at upstream commit
7f20476385d4af418f110303085ad0740c9eba46.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- The norm power clamped at a natural height. -/
def hilbertVecMomentTrunc (p n : ℕ) (v : HilbertVec d) : ℝ :=
  max (min ‖v‖ (n : ℝ)) 0 ^ p

theorem hilbertVecMomentTrunc_zero (p : ℕ) (hp : 0 < p) (n : ℕ) :
    hilbertVecMomentTrunc (d := d) p n 0 = 0 := by
  simp [hilbertVecMomentTrunc, hp.ne']

theorem lipschitzWith_hilbertVecMomentTrunc (p n : ℕ) :
    LipschitzWith ((p : NNReal) * (n : NNReal) ^ (p - 1))
      (hilbertVecMomentTrunc (d := d) p n) := by
  have hclamp : LipschitzWith 1 (fun v : HilbertVec d => max (min ‖v‖ (n : ℝ)) 0) :=
    (lipschitzWith_one_norm.min_const _).max_const _
  have hpow : LipschitzOnWith ((p : NNReal) * (n : NNReal) ^ (p - 1))
      (fun t : ℝ => t ^ p) (Set.Icc 0 (n : ℝ)) := by
    apply (convex_Icc (0 : ℝ) n).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t _ => (hasDerivAt_pow p t).hasDerivWithinAt)
    intro t ht
    change ‖(p : ℝ) * t ^ (p - 1)‖ ≤
      (((p : NNReal) * (n : NNReal) ^ (p - 1) : NNReal) : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg p) (pow_nonneg ht.1 _))]
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 _) (Nat.cast_nonneg p)
  have hmem (v : HilbertVec d) : max (min ‖v‖ (n : ℝ)) 0 ∈ Set.Icc 0 (n : ℝ) :=
    ⟨le_max_right _ _, max_le (min_le_right _ _) (Nat.cast_nonneg n)⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  exact (hpow.dist_le_mul _ (hmem x) _ (hmem y)).trans
    (mul_le_mul_of_nonneg_left (by simpa using hclamp.dist_le_mul x y) (by positivity))

private theorem hilbertVecMomentTrunc_nonneg (p n : ℕ) (v : HilbertVec d) :
    0 ≤ hilbertVecMomentTrunc p n v :=
  pow_nonneg (le_max_right _ _) p

private theorem hilbertVecMomentTrunc_le (p n : ℕ) (v : HilbertVec d) :
    hilbertVecMomentTrunc p n v ≤ ‖v‖ ^ p :=
  pow_le_pow_left₀ (le_max_right _ _)
    (max_le (min_le_left _ _) (norm_nonneg v)) p

private theorem monotone_hilbertVecMomentTrunc (p : ℕ) (v : HilbertVec d) :
    Monotone fun n : ℕ => hilbertVecMomentTrunc p n v := by
  intro a b hab
  refine pow_le_pow_left₀ (le_max_right _ _) ?_ p
  refine max_le_max ?_ le_rfl
  exact min_le_min le_rfl (by exact_mod_cast hab)

private theorem iSup_ofReal_hilbertVecMomentTrunc (p : ℕ) (v : HilbertVec d) :
    ⨆ n : ℕ, ENNReal.ofReal (hilbertVecMomentTrunc p n v) =
      ENNReal.ofReal (‖v‖ ^ p) := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal
    (hilbertVecMomentTrunc_le p n v)) ?_
  refine le_iSup_of_le ⌈‖v‖⌉₊ (ENNReal.ofReal_le_ofReal ?_)
  have hmin : min ‖v‖ ((⌈‖v‖⌉₊ : ℕ) : ℝ) = ‖v‖ := min_eq_left (Nat.le_ceil _)
  unfold hilbertVecMomentTrunc
  rw [hmin, max_eq_left (norm_nonneg v)]

variable {U : Set (Vec d)}

/-- The truncated positive-moment window integral, continuous on the Hilbert `L²` carrier. -/
def windowMomentTrunc (p : ℕ) (hp : 0 < p) [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) (F : HilbertVectorL2 U) : ℝ :=
  scalarL2SetIntegralCLM (U := U) S hS
    ((lipschitzWith_hilbertVecMomentTrunc (d := d) p n).compLp
      (hilbertVecMomentTrunc_zero p hp n) F)

theorem continuous_windowMomentTrunc (p : ℕ) (hp : 0 < p) [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) :
    Continuous (windowMomentTrunc (U := U) p hp S hS n) :=
  (scalarL2SetIntegralCLM (U := U) S hS).continuous.comp
    (LipschitzWith.continuous_compLp _ _)

theorem windowMomentTrunc_eq (p : ℕ) (hp : 0 < p) [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) (F : HilbertVectorL2 U) :
    windowMomentTrunc (U := U) p hp S hS n F =
      ∫ x in S, hilbertVecMomentTrunc p n (F x) ∂(volumeMeasureOn U) := by
  rw [windowMomentTrunc, scalarL2SetIntegralCLM_apply]
  refine integral_congr_ae ?_
  exact ((lipschitzWith_hilbertVecMomentTrunc (d := d) p n).coeFn_compLp
    (hilbertVecMomentTrunc_zero p hp n) F).filter_mono
    (ae_mono Measure.restrict_le_self)

theorem measurable_setLIntegral_norm_pow (p : ℕ) (hp : 0 < p)
    [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) :
    Measurable fun F : HilbertVectorL2 U =>
      ∫⁻ x in S, ENNReal.ofReal (‖F x‖ ^ p) ∂(volumeMeasureOn U) := by
  have hmeas : ∀ n : ℕ, Measurable fun F : HilbertVectorL2 U =>
      ENNReal.ofReal (windowMomentTrunc (U := U) p hp S hS n F) := fun n =>
    (continuous_windowMomentTrunc (U := U) p hp S hS n).measurable.ennreal_ofReal
  have hEq : (fun F : HilbertVectorL2 U =>
      ∫⁻ x in S, ENNReal.ofReal (‖F x‖ ^ p) ∂(volumeMeasureOn U)) =
      fun F : HilbertVectorL2 U =>
        ⨆ n : ℕ, ENNReal.ofReal (windowMomentTrunc (U := U) p hp S hS n F) := by
    funext F
    have hcoe : AEStronglyMeasurable (fun x => (F : Vec d → HilbertVec d) x)
        ((volumeMeasureOn U).restrict S) := (Lp.aestronglyMeasurable F).restrict
    have haem : ∀ n : ℕ, AEMeasurable
        (fun x => ENNReal.ofReal (hilbertVecMomentTrunc p n ((F : Vec d → HilbertVec d) x)))
        ((volumeMeasureOn U).restrict S) := by
      intro n
      refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact (((lipschitzWith_hilbertVecMomentTrunc (d := d)
        p n).continuous).comp_aestronglyMeasurable hcoe).aemeasurable
    have hfin : ∀ n : ℕ,
        ∫⁻ x in S, ENNReal.ofReal (hilbertVecMomentTrunc p n
            ((F : Vec d → HilbertVec d) x)) ∂(volumeMeasureOn U) ≠ ⊤ := by
      intro n
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x =>
        ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (le_max_right _ _)
            (max_le (min_le_right _ _) (Nat.cast_nonneg n)) p))
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top ((volumeMeasureOn U).restrict S) Set.univ)
    have htrunc : ∀ n : ℕ,
        ENNReal.ofReal (windowMomentTrunc (U := U) p hp S hS n F) =
          ∫⁻ x in S, ENNReal.ofReal (hilbertVecMomentTrunc p n
            ((F : Vec d → HilbertVec d) x)) ∂(volumeMeasureOn U) := by
      intro n
      rw [windowMomentTrunc_eq p hp, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => hilbertVecMomentTrunc_nonneg p n _)
        ((((lipschitzWith_hilbertVecMomentTrunc (d := d) p n).continuous).comp_aestronglyMeasurable
          hcoe))]
      exact ENNReal.ofReal_toReal (hfin n)
    simp_rw [htrunc]
    rw [← lintegral_iSup' haem
      (Filter.Eventually.of_forall fun x => by
        intro a b hab
        exact ENNReal.ofReal_le_ofReal (monotone_hilbertVecMomentTrunc p _ hab))]
    exact lintegral_congr fun x => (iSup_ofReal_hilbertVecMomentTrunc p _).symm
  rw [hEq]
  exact Measurable.iSup hmeas

theorem measurable_setIntegral_norm_pow (p : ℕ) (hp : 0 < p) [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) :
    Measurable fun F : HilbertVectorL2 U =>
      ∫ x in S, ‖(F : Vec d → HilbertVec d) x‖ ^ p ∂(volumeMeasureOn U) := by
  have hEq : (fun F : HilbertVectorL2 U =>
      ∫ x in S, ‖(F : Vec d → HilbertVec d) x‖ ^ p ∂(volumeMeasureOn U)) =
      fun F : HilbertVectorL2 U =>
        (∫⁻ x in S, ENNReal.ofReal (‖(F : Vec d → HilbertVec d) x‖ ^ p)
          ∂(volumeMeasureOn U)).toReal := by
    funext F
    refine integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => by positivity) ?_
    exact ((continuous_pow p).comp continuous_norm).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable F).restrict
  rw [hEq]
  exact (measurable_setLIntegral_norm_pow (U := U) p hp S hS).ennreal_toReal

theorem setIntegral_vecNormSq_pow_eq (k : ℕ) (w : H1Function U) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫ x in S, ‖(w.gradToHilbertVectorL2 : Vec d → HilbertVec d) x‖ ^ (2 * k)
        ∂(volumeMeasureOn U) =
      ∫ x in S, vecNormSq (w.grad x) ^ k ∂volume := by
  have hrestrict : (volumeMeasureOn U).restrict S = volume.restrict S := by
    rw [Measure.restrict_restrict hS, Set.inter_eq_self_of_subset_left hSU]
  have hae : ∀ᵐ x ∂((volumeMeasureOn U).restrict S),
      ‖(w.gradToHilbertVectorL2 : Vec d → HilbertVec d) x‖ ^ (2 * k) =
        vecNormSq (w.grad x) ^ k := by
    refine (w.coeFn_gradToHilbertVectorL2.filter_mono
      (ae_mono Measure.restrict_le_self)).mono fun x hx => ?_
    rw [hx]
    change ‖HilbertVec.ofVec (w.grad x)‖ ^ (2 * k) = vecNormSq (w.grad x) ^ k
    rw [pow_mul, HilbertVec.norm_sq_ofVec]
    rfl
  rw [integral_congr_ae hae, hrestrict]

theorem measurable_volumeAverage_vecNormSq_pow (k : ℕ) (hk : 0 < k) {Omega : Type*}
    [MeasurableSpace Omega] [IsFiniteMeasure (volumeMeasureOn U)]
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    {F : Omega → HilbertVectorL2 U} (hF : Measurable F)
    {w : Omega → H1Function U}
    (hw : ∀ omega, F omega = (w omega).gradToHilbertVectorL2) :
    Measurable fun omega =>
      volumeAverage S (fun x => vecNormSq ((w omega).grad x) ^ k) := by
  have hEq : (fun omega =>
      volumeAverage S (fun x => vecNormSq ((w omega).grad x) ^ k)) =
      fun omega => (volume S).toReal⁻¹ *
        ∫ x in S, ‖((F omega : Vec d → HilbertVec d)) x‖ ^ (2 * k)
          ∂(volumeMeasureOn U) := by
    funext omega
    rw [hw omega, setIntegral_vecNormSq_pow_eq k (w omega) hS hSU, volumeAverage]
  rw [hEq]
  exact measurable_const.mul
    ((measurable_setIntegral_norm_pow (U := U) (2 * k) (by omega) S hS).comp hF)

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
