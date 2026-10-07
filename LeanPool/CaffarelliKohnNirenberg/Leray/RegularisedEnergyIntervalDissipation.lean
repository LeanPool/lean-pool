/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEnergyIntervalReal
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedDissipation

/-!
# The classical dissipation of the regularized solution

For a time slice that is continuously differentiable in space and agrees with
the real part of a complex `L²` field whose transform is conjugation symmetric,
the classical dissipation `∫ |∇u|²` equals the frequency dissipation
`∫ 4π²|ξ|² |v̂|²`. Integrating in time identifies the dissipation term of the
energy equality in `thm:regularised`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform ComplexConjugate

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A tensor fixed by coordinatewise conjugation has squared norm equal to
the sum of the squares of the real parts of its entries. -/
theorem norm_sq_eq_sum_sq_re_of_conj (T : ComplexTensor3) (hT : complexTensorConj T = T) :
    ‖T‖ ^ 2 = ∑ i : Fin 3, ∑ j : Fin 3, (T j i).re ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hji := congrArg (fun S : ComplexTensor3 => S j i) hT
  simp only [complexTensorConj_apply, complexVecConj_apply] at hji
  have him : (T j i).im = 0 := Complex.conj_eq_iff_im.mp hji
  rw [Complex.sq_norm, Complex.normSq_apply, him]
  ring

/-- The classical squared gradient of a spatially `C¹` slice equals the
frequency dissipation of a conjugation-symmetric complex field representing
it. -/
theorem lintegral_spatialGradientSq_slice_eq {u : ParabolicPoint → Vec3} {s : ℝ}
    (v : ComplexVectorL2) (hv : MemLp (forcedFourierGradHat v) 2 volume)
    (hreal : conjReflectLp complexVecConj (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v) =
      Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v)
    (hrep : (fun x => u (x, s)) =ᵐ[volume] realPartVectorL2Representative v)
    (hC1 : ∀ i, ContDiff ℝ 1 (fun x : Vec3 => u (x, s) i)) :
    ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u
        (fun z i j => CKN.spatialPartial (fun y => u y i) j z) (x, s)) =
      ENNReal.ofReal (forcedFourierDissipation v) := by
  set G := forcedFourierGrad v hv with hGdef
  have hcomp : ∀ i, (fun x => realPartVectorL2Representative v x i) =ᵐ[volume]
      fun x => u (x, s) i := fun i => by
    filter_upwards [hrep] with x hx
    rw [hx]
  have hweak : ∀ i, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u (x, s) i)
      (fun x j => ((G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re) := fun i =>
    hasWeakGradientOn_congr_ae_left (hcomp i) (forcedFourierGrad_hasWeakGradientOn v hv i)
  have hclass : ∀ i j, (fun x => CKN.spatialPartial (fun y => u y i) j (x, s)) =ᵐ[volume]
      fun x => ((G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re := by
    intro i j
    have h1 : CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => u (x, s) i)
        (fun x => (fderiv ℝ (fun x' : Vec3 => u (x', s) i) x) (CKN.basisVec j)) :=
      CKN.HasWeakPartialDerivOn.of_contDiff (hC1 i)
    have hcont : Continuous fun x =>
        (fderiv ℝ (fun x' : Vec3 => u (x', s) i) x) (CKN.basisVec j) :=
      ((hC1 i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h := CKN.hasWeakPartialDerivOn_unique_ae isOpen_univ
      (hcont.locallyIntegrable.locallyIntegrableOn _)
      (((memLp_re_tensor_coord G j i).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      h1 (hweak i j)
    rw [Measure.restrict_univ] at h
    exact h
  have hGreal := conjLp_ae complexTensorConj G
  rw [conjLp_forcedFourierGrad v hv hreal] at hGreal
  have hGreal' := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hGreal
  have hall := ae_all_iff.2 fun i => ae_all_iff.2 fun j => hclass i j
  have heq : ∀ᵐ x ∂(volume : Measure Vec3),
      ENNReal.ofReal (CKN.spatialGradientSq u
        (fun z i j => CKN.spatialPartial (fun y => u y i) j z) (x, s)) =
        ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x)‖ ^ 2) := by
    filter_upwards [hall, hGreal'] with x hx hxr
    congr 1
    rw [norm_sq_eq_sum_sq_re_of_conj _ hxr.symm]
    simp only [CKN.spatialGradientSq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hx i j]
  rw [lintegral_congr_ae heq]
  have hmp := vec3ToL2Vec3_measurePreserving
  have h1 : ∫⁻ x : Vec3, ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x)‖ ^ 2) =
      ∫⁻ y : L2Vec3, ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) y‖ ^ 2) :=
    hmp.lintegral_comp (f := fun y => ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) y‖ ^ 2))
      ((Lp.stronglyMeasurable G).norm.pow 2).measurable.ennreal_ofReal
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp G).integrable_norm_pow two_ne_zero) (Eventually.of_forall fun y => by positivity),
    integral_norm_sq_eq_norm_sq_Lp, hGdef, norm_sq_forcedFourierGrad]
  rfl

/-- The dissipation of a velocity whose spatial derivatives are continuous on
positive times up to `T` is the time integral of its slice dissipations. -/
theorem regUniformDissipation_eq_ofReal_integral {u : ParabolicPoint → Vec3} {t T : ℝ}
    (htT : t ≤ T)
    (hDcont : ∀ i j, ContinuousOn
      (fun z : Vec3 × ℝ => CKN.spatialPartial (fun y => u y i) j z)
      ((Set.univ : Set Vec3) ×ˢ Ioc 0 T))
    (d : ℝ → ℝ) (hd : IntegrableOn d (Ioc 0 t)) (hd0 : ∀ s, 0 ≤ d s)
    (hslice : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)),
      ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u
        (fun z i j => CKN.spatialPartial (fun y => u y i) j z) (x, s)) = ENNReal.ofReal (d s)) :
    regUniformDissipation u (fun z i j => CKN.spatialPartial (fun y => u y i) j z) t =
      ENNReal.ofReal (∫ s in Ioc 0 t, d s) := by
  set f : Vec3 × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (CKN.spatialGradientSq u
    (fun z i j => CKN.spatialPartial (fun y => u y i) j z) z) with hfdef
  have hsub : (Set.univ : Set Vec3) ×ˢ Ioo 0 t ⊆ (Set.univ : Set Vec3) ×ˢ Ioc 0 T := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.le.trans htT⟩
  have hcont : ContinuousOn (fun z : Vec3 × ℝ => CKN.spatialGradientSq u
      (fun z i j => CKN.spatialPartial (fun y => u y i) j z) z)
      ((Set.univ : Set Vec3) ×ˢ Ioo 0 t) := by
    simp only [CKN.spatialGradientSq]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((hDcont i j).mono hsub).pow 2
  have hmeasSet : MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioo (0 : ℝ) t) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hfm0 := (hcont.aemeasurable
    (μ := (volume : Measure Vec3).prod (volume : Measure ℝ)) hmeasSet).ennreal_ofReal
  have hfm : AEMeasurable f (volume.prod (volume.restrict (Ioo 0 t))) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ] at hfm0
    exact hfm0
  rw [regUniformDissipation_eq_slab, restrict_spaceTimeSet_eq_prod]
  change ∫⁻ z : Vec3 × ℝ, f z ∂(volume.prod (volume.restrict (Ioo 0 t))) = _
  rw [lintegral_prod_symm _ hfm]
  rw [lintegral_congr_ae hslice, ← ofReal_integral_eq_lintegral_ofReal
    (hd.mono_set Ioo_subset_Ioc_self) (Eventually.of_forall fun s => hd0 s),
    integral_Ioc_eq_integral_Ioo]

end CKN.Leray

end
