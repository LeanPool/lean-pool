/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildDefinition

/-!
# The regularized quadratic term

The tensor-valued nonlinearity used in `eq:reg-mild` and
`lem:reg-local-mild`.
-/

public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The bilinear scalar multiplication map on the local Hilbert velocity space. -/
@[expose]
def localScalarVectorActionLinear : ℝ →ₗ[ℝ] L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

/-- The continuous scalar multiplication map on local Hilbert velocities. -/
@[expose]
def localScalarVectorAction : ℝ →L[ℝ] L2Vec3 →L[ℝ] L2Vec3 :=
  localScalarVectorActionLinear.mkContinuous₂ 1 (by
    intro c x
    change ‖c • x‖ ≤ 1 * ‖c‖ * ‖x‖
    simpa [one_mul] using (norm_smul_le c x))

/-- Regularized convolution is linear on vector `L²` inputs. -/
theorem regMollifyVector_add
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f g : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    regMollifyVector ρ ε hε (f + g) =
      regMollifyVector ρ ε hε f + regMollifyVector ρ ε hε g := by
  let hk := regMollifierKernel_memLp_two ρ ε hε
  have hconvf : MeasureTheory.ConvolutionExists (regMollifierKernel ρ ε hε) f
      localScalarVectorAction volume :=
    MeasureTheory.ConvolutionExists.of_memLp_memLp
      (L := localScalarVectorAction) hk hf
  have hconvg : MeasureTheory.ConvolutionExists (regMollifierKernel ρ ε hε) g
      localScalarVectorAction volume :=
    MeasureTheory.ConvolutionExists.of_memLp_memLp
      (L := localScalarVectorAction) hk hg
  change MeasureTheory.convolution (regMollifierKernel ρ ε hε) (f + g)
      localScalarVectorAction volume = _
  exact hconvf.distrib_add hconvg

/-- The pointwise tensor product `(v_i u_j)_{i,j}` in the Euclidean
three-component carriers of `eq:reg-mild`. -/
@[expose]
def regularizedTensorOuter (v u : L2Vec3) : RealTensor3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    WithLp.toLp 2 (fun j : Fin 3 => v i * u j))

/-- The Euclidean tensor norm of a rank-one tensor is the product of the
Euclidean vector norms. -/
theorem regularizedTensorOuter_norm (v u : L2Vec3) :
    ‖regularizedTensorOuter v u‖ = ‖v‖ * ‖u‖ := by
  have hv : ‖v‖ ^ 2 = ∑ i : Fin 3, ‖v i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ v
  have hu : ‖u‖ ^ 2 = ∑ j : Fin 3, ‖u j‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ u
  have hout : ‖regularizedTensorOuter v u‖ ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, ‖v i‖ ^ 2 * ‖u j‖ ^ 2 := by
    rw [regularizedTensorOuter, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i hi
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j hj
    simp [mul_pow]
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, ‖v i‖ ^ 2 * ‖u j‖ ^ 2) =
      (∑ i : Fin 3, ‖v i‖ ^ 2) * (∑ j : Fin 3, ‖u j‖ ^ 2) := by
    rw [Finset.sum_mul_sum]
  have hnormsq : ‖regularizedTensorOuter v u‖ ^ 2 = (‖v‖ * ‖u‖) ^ 2 := by
    rw [hout, hsum, ← hv, ← hu, mul_pow]
  have hnonneg : 0 ≤ ‖regularizedTensorOuter v u‖ := norm_nonneg _
  have htarget : 0 ≤ ‖v‖ * ‖u‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith only [hnormsq, hnonneg, htarget]

/-- The bilinear map sending two Hilbert vectors to their regularized componentwise tensor
product. -/
@[expose]
def regularizedTensorOuterLinear : L2Vec3 →ₗ[ℝ] L2Vec3 →ₗ[ℝ] RealTensor3 :=
  LinearMap.mk₂ ℝ regularizedTensorOuter
    (by
      intro v w u
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp [regularizedTensorOuter, add_mul])
    (by
      intro c v u
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp only [regularizedTensorOuter, PiLp.smul_apply]
      ring)
    (by
      intro v u w
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp [regularizedTensorOuter, mul_add])
    (by
      intro c v u
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp only [regularizedTensorOuter, PiLp.smul_apply, smul_eq_mul]
      ring)

/-- The continuous bilinear tensor product on Euclidean vector values. -/
@[expose]
def regularizedTensorOuterCLM :
    L2Vec3 →L[ℝ] L2Vec3 →L[ℝ] RealTensor3 :=
  regularizedTensorOuterLinear.mkContinuous₂ 1 (by
    intro v u
    change ‖regularizedTensorOuter v u‖ ≤ 1 * ‖v‖ * ‖u‖
    rw [regularizedTensorOuter_norm]
    calc
      ‖v‖ * ‖u‖ ≤ 1 * ‖v‖ * ‖u‖ := by simp
  )

/-- The raw tensor field in the regularized mild equation. -/
@[expose]
def regularizedMildTensorField (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (u : RealVectorL2) : L2Vec3 → RealTensor3 :=
  fun x => regularizedTensorOuter (regMollifyVector ρ ε hε u x) (u x)

private theorem regularizedMildTensorField_aestronglyMeasurable
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : RealVectorL2) :
    AEStronglyMeasurable (regularizedMildTensorField ρ ε hε u) volume := by
  have hpair : AEStronglyMeasurable
      (fun x : L2Vec3 => (regMollifyVector ρ ε hε u x, u x)) volume :=
    (regMollifyVector_aestronglyMeasurable ρ ε hε (Lp.memLp u)).prodMk
      (Lp.aestronglyMeasurable u)
  exact (regularizedTensorOuterCLM.continuous₂.comp_aestronglyMeasurable hpair).congr
    (Filter.Eventually.of_forall fun _ => rfl)

private theorem regularizedMildTensorField_pointwise_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : RealVectorL2) (x : L2Vec3) :
    ‖regularizedMildTensorField ρ ε hε u x‖ ≤
      ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
        ‖u‖ * ‖u x‖ := by
  rw [regularizedMildTensorField, regularizedTensorOuter_norm]
  have hpoint := regMollifyVector_pointwise_enorm_le_scaled ρ ε hε
    (Lp.memLp u) x
  have hfinite : eLpNorm u 2 volume ≠ ∞ := (Lp.memLp u).eLpNorm_ne_top
  have hprofile : eLpNorm ρ.rho 2 volume ≠ ∞ := by
    exact (ρ.smooth.continuous.memLp_of_hasCompactSupport ρ.compact).eLpNorm_ne_top
  have hfiniteCoef :
      ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume * eLpNorm u 2 volume ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hprofile) hfinite
  have hreal : ‖regMollifyVector ρ ε hε u x‖ ≤
      ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) * ‖u‖ := by
    have htoReal := ENNReal.toReal_mono hfiniteCoef hpoint
    simpa [← ofReal_norm, ENNReal.toReal_mul, hprofile, hfinite, Lp.norm_def,
      ENNReal.toReal_ofReal (le_of_lt (Real.rpow_pos_of_pos hε _))] using htoReal
  calc
    ‖regMollifyVector ρ ε hε u x‖ * ‖u x‖ ≤
        (ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
          ‖u‖) * ‖u x‖ := mul_le_mul_of_nonneg_right hreal (norm_nonneg (u x))
    _ = ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
        ‖u‖ * ‖u x‖ := by ring

theorem regularizedMildTensorField_memLp (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (u : RealVectorL2) :
    MemLp (regularizedMildTensorField ρ ε hε u) (2 : ℝ≥0∞) volume := by
  apply (Lp.memLp u).of_le_mul
    (c := ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) *
      eLpNorm ρ.rho 2 volume) * ‖u‖)
    (regularizedMildTensorField_aestronglyMeasurable ρ ε hε u)
  filter_upwards [] with x
  exact regularizedMildTensorField_pointwise_bound ρ ε hε u x

/-- The nonlinearity in `eq:reg-mild` belongs to tensor-valued `L²` and has
the source's quadratic norm bound. -/
@[expose]
def regularizedMildTensor (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (u : RealVectorL2) : RealTensorL2 :=
  (regularizedMildTensorField_memLp ρ ε hε u).toLp
    (regularizedMildTensorField ρ ε hε u)

/-- The nonlinearity in `eq:reg-mild` is bounded quadratically in `L²`. -/
theorem regularizedMildTensor_norm_le (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (u : RealVectorL2) :
    ‖regularizedMildTensor ρ ε hε u‖ ≤
      ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) * ‖u‖ ^ 2 := by
  have hpoint : ∀ᵐ x ∂volume,
      ‖regularizedMildTensorField ρ ε hε u x‖ ≤
        ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
          ‖u‖ * ‖u x‖ :=
    Filter.Eventually.of_forall (regularizedMildTensorField_pointwise_bound ρ ε hε u)
  have hrep : (regularizedMildTensor ρ ε hε u : Lp RealTensor3 2 volume) =ᵐ[volume]
      regularizedMildTensorField ρ ε hε u :=
    (regularizedMildTensorField_memLp ρ ε hε u).coeFn_toLp
  have hpoint' : ∀ᵐ x ∂volume,
      ‖(regularizedMildTensor ρ ε hε u : Lp RealTensor3 2 volume) x‖ ≤
        ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
          ‖u‖ * ‖u x‖ := by
    filter_upwards [hrep, hpoint] with x hx1 hx2
    rw [hx1]
    exact hx2
  have hnorm : ‖regularizedMildTensor ρ ε hε u‖ ≤
      ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
        ‖u‖ * ‖u‖ :=
    Lp.norm_le_mul_norm_of_ae_le_mul hpoint'
  calc
    ‖regularizedMildTensor ρ ε hε u‖ ≤
        ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
          ‖u‖ * ‖u‖ := hnorm
    _ = ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
          ‖u‖ ^ 2 := by rw [sq]; ring

end CKN.Leray

end
