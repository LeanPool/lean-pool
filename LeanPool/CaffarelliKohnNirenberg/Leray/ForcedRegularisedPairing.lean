/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedTransportField
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedTruncation
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureGradientClosure

/-!
# The transport pairing vanishes

The frequency pairing of the solution with the divergence of its regularized
tensor is the pairing of its weak gradient with the tensor. For the tensor
`(J_ε w)ᵢ wⱼ` of a multiple `w` of the divergence-free solution, it is a
multiple of `∑ᵢⱼ ∫ (J_ε w)ᵢ uⱼ ∂ᵢuⱼ`, which vanishes by the transport
cancellation. This removes the nonlinear term from the energy balance of
`lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The divergence pairing at one frequency is the tensor pairing with the
frequency gradient. -/
theorem inner_neg_tensorDivergence_eq (ξ : L2Vec3) (y : ComplexVec3) (T : ComplexTensor3) :
    inner ℂ y (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ T)) =
      inner ℂ (WithLp.toLp 2 fun i => ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) • y :
        ComplexTensor3) T := by
  rw [inner_neg_right, inner_smul_right, tensorDivergenceLinear_apply, inner_sum,
    PiLp.inner_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, WithLp.ofLp_toLp, inner_smul_left]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- The frequency pairing is the pairing of the weak gradient with the tensor. -/
theorem forcedStokesPairing_eq (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume) (G : ComplexTensorL2) :
    forcedStokesPairing v G = (inner ℂ (forcedFourierGrad v hv) G).re := by
  rw [← LinearIsometryEquiv.inner_map_map (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3),
    forcedFourierGrad, LinearIsometryEquiv.apply_symm_apply, L2.inner_def,
    ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  unfold forcedStokesPairing
  refine integral_congr_ae ?_
  filter_upwards [hv.coeFn_toLp] with ξ hξ
  rw [hξ, inner_neg_tensorDivergence_eq]
  rfl

/-- The real part of the pairing of a complex tensor field with a complexified
real tensor field. -/
theorem re_inner_complexifyTensorL2 (Z : ComplexTensorL2) (T : RealTensorL2) :
    (inner ℂ Z (complexifyTensorL2 T)).re =
      ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        ((Z : L2Vec3 → ComplexTensor3) y i j).re * (T : L2Vec3 → RealTensor3) y i j := by
  rw [L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [complexifyTensorValue.coeFn_compLpL (p := 2) (μ := volume) T] with y hy
  change RCLike.re (inner ℂ (Z y) ((complexifyTensorL2 T : L2Vec3 → ComplexTensor3) y)) = _
  rw [show (complexifyTensorL2 T : L2Vec3 → ComplexTensor3) y =
    complexifyTensorValue (T y) from hy]
  rw [PiLp.inner_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (inner ℂ (Z y i) (complexifyFrequency (T y i))).re = _
  rw [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexifyFrequency, WithLp.ofLp_toLp, RCLike.inner_apply, Complex.mul_re,
    Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Weak divergence freedom is preserved by scalar multiples. -/
theorem isWeakDivFreeL2_const_smul (c : ℝ) {a : Vec3 → Vec3} (ha : CKN.IsWeakDivFreeL2 a) :
    CKN.IsWeakDivFreeL2 (c • a) := by
  refine ⟨ha.1.const_smul c, fun ψ => ?_⟩
  have h := ha.2 ψ
  calc ∫ x, ∑ i : Fin 3, (c • a) x i * ψ.partialDeriv i x
      = ∫ x, c * ∑ i : Fin 3, a x i * ψ.partialDeriv i x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by rw [integral_const_mul, h, mul_zero]

/-- The divergence-free data space is closed under scalar multiples. -/
theorem regularizedMildJData_const_smul (c : ℝ) {u : RealVectorL2}
    (hu : RegularizedMildJData u) : RegularizedMildJData (c • u) := by
  have hweak := CKN.isInJ_iff_weakDivFree.1 hu
  have hrep : c • realVectorL2Representative u =ᵐ[volume] realVectorL2Representative (c • u) := by
    have h := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae (Lp.coeFn_smul c u)
    filter_upwards [h] with x hx
    simp only [realVectorL2Representative, Pi.smul_apply]
    change _ = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
      ((c • u : RealVectorL2) (WithLp.toLp 2 x))
    rw [show ((c • u : RealVectorL2) : L2Vec3 → L2Vec3) (WithLp.toLp 2 x) =
      (c • ⇑u) (WithLp.toLp 2 x) from hx, Pi.smul_apply, map_smul]
    rfl
  exact CKN.isInJ_iff_weakDivFree.2
    (isWeakDivFree_congr_ae hrep (isWeakDivFreeL2_const_smul c hweak))

theorem regUniformSpatialField_realVectorL2Representative (w : RealVectorL2) :
    regUniformSpatialField (realVectorL2Representative w) = (w : L2Vec3 → L2Vec3) := by
  funext y
  simp only [regUniformSpatialField, realVectorL2Representative]
  rfl

/-- A coordinate of the real part of a complex `L²` field, in physical
coordinates, is square integrable. -/
theorem memLp_re_coord (v : ComplexVectorL2) (j : Fin 3) :
    MemLp (fun x : Vec3 => ((v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x) j).re) 2 volume := by
  have hv : MemLp (fun x : Vec3 => (v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp v).comp_measurePreserving vec3ToL2Vec3_measurePreserving
  refine hv.of_le_mul (c := 1) ?_ (Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_re.comp (PiLp.continuous_apply 2 _ j)).comp_aestronglyMeasurable
      hv.aestronglyMeasurable
  · rw [one_mul, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le _ j)

/-- An entry of the real part of a complex tensor `L²` field, in physical
coordinates, is square integrable. -/
theorem memLp_re_tensor_coord (Z : ComplexTensorL2) (i j : Fin 3) :
    MemLp (fun x : Vec3 => ((Z : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) i j).re)
      2 volume := by
  have hZ : MemLp (fun x : Vec3 => (Z : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp Z).comp_measurePreserving vec3ToL2Vec3_measurePreserving
  refine hZ.of_le_mul (c := 1) ?_ (Eventually.of_forall fun x => ?_)
  · have hc : Continuous fun T : ComplexTensor3 => (T i j).re :=
      Complex.continuous_re.comp ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ComplexVec3) i))
    exact hc.comp_aestronglyMeasurable hZ.aestronglyMeasurable
  · rw [one_mul, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans ((PiLp.norm_apply_le _ j).trans
      (PiLp.norm_apply_le _ i))

/-- The frequency pairing of the solution with the divergence of the
regularized tensor of its truncation vanishes. -/
theorem forcedStokesPairing_truncTensor_eq_zero (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {R : ℝ} (v : ComplexVectorL2) (hv : MemLp (forcedFourierGradHat v) 2 volume)
    (hJ : RegularizedMildJData (realPartVectorL2 v)) :
    forcedStokesPairing v (complexifyTensorL2
      (forcedTruncTensor ρ ε hε R (realPartVectorL2 v))) = 0 := by
  set u := realPartVectorL2 v with hudef
  set c := forcedTruncFactor R u with hcdef
  set w : RealVectorL2 := c • u with hwdef
  have hwtrunc : forcedTrunc R u = w := rfl
  set Z := forcedFourierGrad v hv with hZdef
  set a := realVectorL2Representative w with hadef
  have hJw : CKN.IsInJ a := regularizedMildJData_const_smul c hJ
  set V : Vec3 → Vec3 := regUniformMollifiedInitial ρ ε hε a with hVdef
  have hVeq : ∀ x i, V x i = (regMollifyVector ρ ε hε (w : L2Vec3 → L2Vec3)
      (WithLp.toLp 2 x)) i := by
    intro x i
    simp only [hVdef, regUniformMollifiedInitial, hadef,
      regUniformSpatialField_realVectorL2Representative]
  set ut : Vec3 → Vec3 := fun x j => ((v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x) j).re
  set D : Vec3 → Fin 3 → Vec3 := fun x i j =>
    ((Z : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) i j).re
  obtain ⟨M, hVb, hdVb⟩ :=
    forcedTransport_bounded (ρ := ρ) hε (realVectorL2Representative_memLp_two w)
  have hcancel := transport_cancellation V ut D
    (fun i => forcedTransport_contDiff hε (realVectorL2Representative_memLp_two w) i) M hVb hdVb
    (fun x => forcedTransport_div_eq_zero hε hJw x) (fun j => memLp_re_coord v j)
    (fun i j => memLp_re_tensor_coord Z i j)
    (fun i j => forcedFourierGrad_hasWeakPartialDerivOn v hv i j)
  rw [forcedStokesPairing_eq v hv, re_inner_complexifyTensorL2]
  have hT : ((forcedTruncTensor ρ ε hε R u : RealTensorL2) : L2Vec3 → RealTensor3) =ᵐ[volume]
      regularizedMildTensorField ρ ε hε w := by
    unfold forcedTruncTensor regularizedMildTensor
    rw [hwtrunc]
    exact MemLp.coeFn_toLp _
  have hw : (w : L2Vec3 → L2Vec3) =ᵐ[volume]
      fun y => c • realPartValue ((v : L2Vec3 → ComplexVec3) y) := by
    filter_upwards [Lp.coeFn_smul c u, realPartValue.coeFn_compLpL (p := 2) (μ := volume) v]
      with y h1 h2
    rw [h1, Pi.smul_apply]
    congr 1
  -- rewrite the integrand on the frequency carrier
  have hstep1 : ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
      ((Z : L2Vec3 → ComplexTensor3) y i j).re *
        ((forcedTruncTensor ρ ε hε R u : RealTensorL2) : L2Vec3 → RealTensor3) y i j =
      ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ((Z : L2Vec3 → ComplexTensor3) y i j).re *
        ((regMollifyVector ρ ε hε (w : L2Vec3 → L2Vec3) y) i *
          (c * ((v : L2Vec3 → ComplexVec3) y j).re)) := by
    refine integral_congr_ae ?_
    filter_upwards [hT, hw] with y h1 h2
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp only [regularizedMildTensorField, regularizedTensorOuter, WithLp.ofLp_toLp]
    rw [h2]
    rfl
  -- transport to coordinates
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    vec3ToL2Vec3_measurePreserving
  have hstep2 := hmp.integral_comp' (fun y : L2Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      ((Z : L2Vec3 → ComplexTensor3) y i j).re *
        ((regMollifyVector ρ ε hε (w : L2Vec3 → L2Vec3) y) i *
          (c * ((v : L2Vec3 → ComplexVec3) y j).re)))
  simp only [MeasurableEquiv.coe_toLp] at hstep2
  rw [hstep1, ← hstep2]
  have hint : ∀ i j, Integrable (fun x => V x i * (ut x j * D x i j)) volume := fun i j =>
    ((memLp_re_coord v j).integrable_mul (memLp_re_tensor_coord Z i j)).bdd_mul
      (forcedTransport_contDiff hε (realVectorL2Representative_memLp_two w)
        i).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => hVb x i)
  calc ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        ((Z : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) i j).re *
          ((regMollifyVector ρ ε hε (w : L2Vec3 → L2Vec3) (WithLp.toLp 2 x)) i *
            (c * ((v : L2Vec3 → ComplexVec3) (WithLp.toLp 2 x) j).re))
      = ∫ x : Vec3, c * ∑ i : Fin 3, ∑ j : Fin 3, V x i * (ut x j * D x i j) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Finset.mul_sum, hVeq, ut, D]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = c * ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, V x i * (ut x j * D x i j) := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ =>
          integrable_finsetSum _ fun j _ => hint i j]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hint i j]
    _ = 0 := by rw [hcancel, mul_zero]

end CKN.Leray

end
