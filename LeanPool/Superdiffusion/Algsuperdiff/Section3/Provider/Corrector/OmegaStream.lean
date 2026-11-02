/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.DivergenceKernel
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifiedDecorrelation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifierGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.SolenoidalApproximation

/-!
# OmegaStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the `Ω`-level approximate antisymmetric stream of the kernel route

`Algsuperdiff/Section3/Provider/Corrector/SolenoidalApproximation.lean` proves the
cutoff core of part (ii) of `l.approximation.stationary.by.local` under three
*disclosed* stream hypotheses `hstreamSmooth`, `hstreamAnti`, `hstreamDiv`, and
records in its module docstring that the `Ω`-level stream itself "is not
constructed in this file and does not yet exist in the repository".

This file constructs it, in the **approximate** form, by the elementary kernel
route.  For a family `g = (g_m)` of smooth compactly supported scalar fields on
`ℝᵈ` and a stationary square-integrable `X : Ω → ℝᵈ`, put

`S_{im} := A_{g_m} X_i − A_{g_i} X_m`  (`kernelStream`),

where `A_κ` is the mollification along the translation action of
`Algsuperdiff/Section3/Provider/Corrector/Mollification.lean`.  Three facts, all
elementary:

* `S` is antisymmetric by construction
  (`streamRealization_kernelStream_neg`), its realizations are smooth
  (`contDiff_streamRealization_kernelStream`), and it is a stationary
  square-integrable field (`stronglyMeasurable_kernelStream`,
  `memLp_two_kernelStream`);

* the row divergence of its realization is, **at every point of space and with no
  error term**, the realization of an explicit `Ω`-level field
  (`streamDivergence_kernelStream`):
  `Σ_m ∂_m S_{im} = A_{Σ_m ∂_m g_m} X_i − Σ_m A_{∂_m g_i} X_m`;

* the second, "cross", term vanishes almost surely for a field in the stationary
  *solenoidal* subspace (`mollifyDiv_ae_eq_zero`).  This is the only place where
  solenoidality is used, and the proof is a duality: the adjoint of `A_κ` is
  `A_{κ(−·)}` (`integral_mul_mollify_eq`), so pairing `Σ_m A_{∂_m g_i} X_m`
  against a test scalar `φ` produces `−E[⟪X, ∇A_{g_hat_i}φ⟫]`, which vanishes because
  mollified gradients lie in the stationary potential subspace
  (`toLp_mollifyGrad_mem_stationaryPotentialSubspace`) and `X` is orthogonal to
  it.  Taking `φ` to be the cross term itself gives `E[|cross|²] = 0`.

Choosing `g` so that `Σ_m ∂_m g_m = χ_1 − χ_2` — which the explicit telescoping
kernel of `Algsuperdiff/Section3/Provider/Corrector/DivergenceKernel.lean` does
for any two product densities — the stream divergence becomes `A_{χ_1} X −
A_{χ_2} X` almost surely, so

`‖div S − X‖_{L²(Ω)} ≤ ‖A_{χ_1} X − X‖_{L²(Ω)} + ‖A_{χ_2} X‖_{L²(Ω)}`,

the first term small by the approximate-identity layer of
`Algsuperdiff/Section3/Provider/Corrector/MollifierConvergence.lean` and the
second small by the decorrelation layer of
`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean`.  That
last step, and the discharge of both legs at the fresh shell, are carried out in
`Algsuperdiff/Section3/Provider/Corrector/OmegaStreamAssembly.lean`; this file
stops at the exact divergence identity and the almost-sure identification of its
right-hand side (`kernelStreamDiv_ae_eq`).

No resolvent, no Newtonian potential, no Newton theorem and no ergodic theorem is
used.

**What is *not* proved here.**  The divergence identity produced is the
`ε`-approximate one: the stream reproduces an `Ω`-level field `D` *exactly*, and
`D` is within a controlled `L²(Ω)` distance of `X`, but `D ≠ X`.  The consumer
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream` asks for the
*exact* hypothesis `hstreamDiv`, so the output of this file does **not** discharge
that hypothesis verbatim; see the note on
`exists_kernelStream_integral_normSq_le` in
`Algsuperdiff/Section3/Provider/Corrector/OmegaStreamAssembly.lean`.

**Disclosure.**  Nothing in this file realizes any source node.  It supplies the
approximate form of the representation leg disclosed by
`SolenoidalApproximation.lean`; it does not prove part (ii) of
`l.approximation.stationary.by.local`, and it claims no node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

variable {d : ℕ}

/-! ### The reflected kernel -/

/-- The reflected kernel `y ↦ κ (-y)`.  It is the adjoint kernel of the
mollification `A_κ` on `L²(Ω)` (`integral_mul_mollify_eq`). -/
def kernelReflect (κ : Vec d → ℝ) : Vec d → ℝ := fun y => κ (-y)

theorem contDiff_kernelReflect {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelReflect κ) :=
  hκ.comp contDiff_neg

theorem continuous_kernelReflect {κ : Vec d → ℝ} (hκ : Continuous κ) :
    Continuous (kernelReflect κ) :=
  hκ.comp continuous_neg

theorem hasCompactSupport_kernelReflect {κ : Vec d → ℝ} (hκ : HasCompactSupport κ) :
    HasCompactSupport (kernelReflect κ) :=
  hκ.comp_homeomorph (Homeomorph.neg (Vec d))

theorem integrable_kernelReflect {κ : Vec d → ℝ} (hκ : Integrable κ volume) :
    Integrable (kernelReflect κ) volume :=
  hκ.comp_neg

/-- The real inner product is multiplication. -/
theorem real_inner_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  simp [RCLike.inner_apply, mul_comm]

/-- **Reflection reverses the sign of a partial derivative.** -/
theorem kernelDeriv_kernelReflect {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d) :
    kernelDeriv (kernelReflect κ) i = fun y => -kernelReflect (kernelDeriv κ i) y := by
  funext y
  have hneg : HasFDerivAt (fun z : Vec d => -z) (-ContinuousLinearMap.id ℝ (Vec d)) y := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) y).neg
  have hκy : HasFDerivAt κ (fderiv ℝ κ (-y)) (-y) :=
    ((hκ.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hcomp : HasFDerivAt (kernelReflect κ)
      ((fderiv ℝ κ (-y)).comp (-ContinuousLinearMap.id ℝ (Vec d))) y := hκy.comp y hneg
  change fderiv ℝ (kernelReflect κ) y (basisVec i) = _
  rw [hcomp.fderiv]
  simp [kernelDeriv, kernelReflect]

/-! ### Elementary algebra of the mollification kernel -/

section KernelAlgebra

variable {Ω : Type*} [AddAction (Vec d) Ω]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Negating the kernel negates the mollification. -/
theorem mollify_neg_kernel (κ : Vec d → ℝ) (X : Ω → E) (ω : Ω) :
    mollify (fun y => -κ y) X ω = -mollify κ X ω := by
  change (∫ y, (-κ y) • X ((-y) +ᵥ ω)) = -∫ y, κ y • X ((-y) +ᵥ ω)
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change (-κ y) • X ((-y) +ᵥ ω) = -(κ y • X ((-y) +ᵥ ω))
  rw [neg_smul]

/-- Splitting a kernel that is a pointwise difference. -/
theorem mollify_kernel_sub {κ₁ κ₂ ν : Vec d → ℝ} (hν : ∀ y, ν y = κ₁ y - κ₂ y)
    {X : Ω → E} {ω : Ω}
    (h1 : Integrable (fun y => κ₁ y • X ((-y) +ᵥ ω)) volume)
    (h2 : Integrable (fun y => κ₂ y • X ((-y) +ᵥ ω)) volume) :
    mollify ν X ω = mollify κ₁ X ω - mollify κ₂ X ω := by
  change (∫ y, ν y • X ((-y) +ᵥ ω)) = (∫ y, κ₁ y • X ((-y) +ᵥ ω)) - ∫ y, κ₂ y • X ((-y) +ᵥ ω)
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ν y • X ((-y) +ᵥ ω) = κ₁ y • X ((-y) +ᵥ ω) - κ₂ y • X ((-y) +ᵥ ω)
  rw [hν y, sub_smul]

end KernelAlgebra

/-! ### Euclidean-vector fields assembled from scalars -/

section Pack

variable {Ω : Type*}

/-- A Euclidean-vector stationary field assembled from its `d` scalar
coordinates. -/
def vecPack (ψ : Fin d → (Ω → ℝ)) (ω : Ω) : HilbertVec d :=
  HilbertVec.ofVec fun i => ψ i ω

end Pack

section PackLp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem stronglyMeasurable_vecPack {ψ : Fin d → (Ω → ℝ)}
    (hψ : ∀ i, StronglyMeasurable (ψ i)) : StronglyMeasurable (vecPack ψ) := by
  have hvec : Measurable fun ω : Ω => (fun i => ψ i ω : Vec d) :=
    Measurable.of_eval fun i => (hψ i).measurable
  exact ((HilbertVec.continuousLinearEquivVec d).symm.continuous).comp_stronglyMeasurable
    hvec.stronglyMeasurable

theorem memLp_two_vecPack {ψ : Fin d → (Ω → ℝ)} (hψm : ∀ i, StronglyMeasurable (ψ i))
    (hψ : ∀ i, MemLp (ψ i) 2 μ) : MemLp (vecPack ψ) 2 μ := by
  classical
  refine (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_vecPack hψm).aestronglyMeasurable).2 ?_
  have hsum : Integrable (fun ω => ∑ i : Fin d, (ψ i ω) ^ 2) μ :=
    integrable_finsetSum _ fun i _ =>
      ((memLp_two_iff_integrable_sq_norm (hψm i).aestronglyMeasurable).1 (hψ i)).congr
        (Filter.Eventually.of_forall fun ω => by
          change ‖ψ i ω‖ ^ 2 = ψ i ω ^ 2
          rw [Real.norm_eq_abs, sq_abs])
  refine hsum.congr (Filter.Eventually.of_forall fun ω => ?_)
  change (∑ i : Fin d, ψ i ω ^ 2) = ‖vecPack ψ ω‖ ^ 2
  rw [HilbertVec.norm_sq_eq_sum_sq]
  exact Finset.sum_congr rfl fun i _ => rfl

end PackLp

/-! ### The mollified horizontal divergence and its vanishing -/

section Div

variable {Ω : Type*} [AddAction (Vec d) Ω]

/-- The mollified horizontal divergence `Σ_m A_{∂_m κ} X_m`.  It is the cross
term of the row divergence of `kernelStream`. -/
def mollifyDiv (κ : Vec d → ℝ) (X : Ω → HilbertVec d) (ω : Ω) : ℝ :=
  ∑ m : Fin d, mollify (kernelDeriv κ m) (coordField X m) ω

theorem mollifyDiv_apply (κ : Vec d → ℝ) (X : Ω → HilbertVec d) (ω : Ω) :
    mollifyDiv κ X ω = ∑ m : Fin d, mollify (kernelDeriv κ m) (coordField X m) ω := rfl

end Div

section DivLp

variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

omit [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
theorem stronglyMeasurable_mollifyDiv {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) :
    StronglyMeasurable (mollifyDiv (Ω := Ω) κ X) :=
  Finset.stronglyMeasurable_fun_sum _ fun m _ =>
    stronglyMeasurable_mollify (continuous_kernelDeriv hκ m)
      (stronglyMeasurable_coordField hXm m)

theorem memLp_two_mollifyDiv {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) : MemLp (mollifyDiv (Ω := Ω) κ X) 2 μ :=
  memLp_finsetSum _ fun m _ =>
    memLp_two_mollify (continuous_kernelDeriv hκ m) (integrable_kernelDeriv hκc hκ m)
      (stronglyMeasurable_coordField hXm m) (memLp_coordField hXm hX m)

/-- **The adjoint of mollification is mollification by the reflected kernel.**
The proof is the change of variables `y ↦ -y` on `ℝᵈ` together with the
translation invariance of `μ`; no integration by parts is used. -/
theorem integral_mul_mollify_eq {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {X φ : Ω → ℝ} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    ∫ ω, mollify κ X ω * φ ω ∂μ = ∫ ω, X ω * mollify (kernelReflect κ) φ ω ∂μ := by
  have hL := integral_inner_mollify (μ := μ) hκc hκi hXm hX hφm hφ
  have hR := integral_inner_mollify (μ := μ) (continuous_kernelReflect hκc)
    (integrable_kernelReflect hκi) hφm hφ hXm hX
  simp only [real_inner_eq_mul] at hL hR
  have hshift : ∀ y : Vec d,
      (∫ ω, X ((-y) +ᵥ ω) * φ ω ∂μ) = ∫ ω, φ (y +ᵥ ω) * X ω ∂μ := by
    intro y
    have h := integral_comp_const_vadd (μ := μ) (fun ω => X ((-y) +ᵥ ω) * φ ω) y
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [vadd_vadd, neg_add_cancel, zero_vadd]
    ring
  have hrefl : (∫ z, kernelReflect κ z * ∫ ω, φ ((-z) +ᵥ ω) * X ω ∂μ)
      = ∫ y, κ y * ∫ ω, φ (y +ᵥ ω) * X ω ∂μ := by
    have h := integral_neg_eq_self
      (fun z : Vec d => kernelReflect κ z * ∫ ω, φ ((-z) +ᵥ ω) * X ω ∂μ) volume
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [kernelReflect, neg_neg]
  rw [hL]
  have hRR : ∫ ω, X ω * mollify (kernelReflect κ) φ ω ∂μ
      = ∫ z, kernelReflect κ z * ∫ ω, φ ((-z) +ᵥ ω) * X ω ∂μ := by
    rw [← hR]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  rw [hRR, hrefl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change κ y * (∫ ω, X ((-y) +ᵥ ω) * φ ω ∂μ) = κ y * ∫ ω, φ (y +ᵥ ω) * X ω ∂μ
  rw [hshift y]

/-- **The pairing identity for the mollified divergence**: its `L²(Ω)` adjoint is
minus the mollified gradient at the reflected kernel. -/
theorem integral_mul_mollifyDiv_eq {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    ∫ ω, mollifyDiv κ X ω * φ ω ∂μ
      = -∫ ω, inner ℝ (X ω) (mollifyGrad (kernelReflect κ) φ ω) ∂μ := by
  classical
  have hterm : ∀ m : Fin d, MemLp (mollify (Ω := Ω) (kernelDeriv κ m) (coordField X m)) 2 μ :=
    fun m => memLp_two_mollify (continuous_kernelDeriv hκ m) (integrable_kernelDeriv hκc hκ m)
      (stronglyMeasurable_coordField hXm m) (memLp_coordField hXm hX m)
  have hgm : StronglyMeasurable (mollifyGrad (Ω := Ω) (kernelReflect κ) φ) :=
    stronglyMeasurable_mollifyGrad (contDiff_kernelReflect hκ) hφm
  have hg : MemLp (mollifyGrad (Ω := Ω) (kernelReflect κ) φ) 2 μ :=
    memLp_two_mollifyGrad (hasCompactSupport_kernelReflect hκc) (contDiff_kernelReflect hκ)
      hφm hφ
  have hleft : ∫ ω, mollifyDiv κ X ω * φ ω ∂μ
      = ∑ m : Fin d, ∫ ω, mollify (kernelDeriv κ m) (coordField X m) ω * φ ω ∂μ := by
    have hsplit : ∀ ω : Ω, mollifyDiv κ X ω * φ ω
        = ∑ m : Fin d, mollify (kernelDeriv κ m) (coordField X m) ω * φ ω := by
      intro ω
      rw [mollifyDiv_apply, Finset.sum_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
    exact integral_finsetSum _ fun m _ => (hterm m).integrable_mul hφ
  have hright : ∫ ω, inner ℝ (X ω) (mollifyGrad (kernelReflect κ) φ ω) ∂μ
      = ∑ m : Fin d,
          ∫ ω, coordField X m ω * coordField (mollifyGrad (kernelReflect κ) φ) m ω ∂μ := by
    have hsplit : ∀ ω : Ω, inner ℝ (X ω) (mollifyGrad (kernelReflect κ) φ ω)
        = ∑ m : Fin d,
            coordField X m ω * coordField (mollifyGrad (kernelReflect κ) φ) m ω := by
      intro ω
      rw [HilbertVec.inner_def, vecDot]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
    exact integral_finsetSum _ fun m _ =>
      (memLp_coordField hXm hX m).integrable_mul (memLp_coordField hgm hg m)
  rw [hleft, hright, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_mollify_eq (continuous_kernelDeriv hκ m) (integrable_kernelDeriv hκc hκ m)
    (stronglyMeasurable_coordField hXm m) (memLp_coordField hXm hX m) hφm hφ]
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hker : kernelReflect (kernelDeriv κ m)
      = fun y => -kernelDeriv (kernelReflect κ) m y := by
    funext y
    rw [kernelDeriv_kernelReflect hκ m]
    simp
  have hval : mollify (kernelReflect (kernelDeriv κ m)) φ ω
      = -mollify (kernelDeriv (kernelReflect κ) m) φ ω := by
    rw [hker]
    exact mollify_neg_kernel _ _ _
  change coordField X m ω * mollify (kernelReflect (kernelDeriv κ m)) φ ω
      = -(coordField X m ω * coordField (mollifyGrad (kernelReflect κ) φ) m ω)
  rw [hval]
  have hcoord : coordField (mollifyGrad (kernelReflect κ) φ) m ω
      = mollify (kernelDeriv (kernelReflect κ) m) φ ω := rfl
  rw [hcoord]
  ring

/-- **The cross term vanishes.**  For a field in the stationary solenoidal
subspace the mollified horizontal divergence is almost surely zero.  This is the
only use of solenoidality in the construction of the stream. -/
theorem mollifyDiv_ae_eq_zero {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    ∀ᵐ ω ∂μ, mollifyDiv κ X ω = 0 := by
  set φ : Ω → ℝ := mollifyDiv (Ω := Ω) κ X with hφdef
  have hφm : StronglyMeasurable φ := stronglyMeasurable_mollifyDiv hκ hXm
  have hφ : MemLp φ 2 μ := memLp_two_mollifyDiv hκc hκ hXm hX
  have hg : MemLp (mollifyGrad (Ω := Ω) (kernelReflect κ) φ) 2 μ :=
    memLp_two_mollifyGrad (hasCompactSupport_kernelReflect hκc) (contDiff_kernelReflect hκ)
      hφm hφ
  have hgmem : hg.toLp (mollifyGrad (kernelReflect κ) φ)
      ∈ stationaryPotentialSubspace (μ := μ) (d := d) :=
    toLp_mollifyGrad_mem_stationaryPotentialSubspace (hasCompactSupport_kernelReflect hκc)
      (contDiff_kernelReflect hκ) hφm hφ
  have hzero : ∫ ω, inner ℝ (X ω) (mollifyGrad (kernelReflect κ) φ ω) ∂μ = 0 := by
    rw [← inner_toLp_toLp hX hg]
    have h := (Submodule.mem_orthogonal _ _).1 hmem _ hgmem
    rwa [real_inner_comm] at h
  have hsq : ∫ ω, φ ω * φ ω ∂μ = 0 := by
    rw [integral_mul_mollifyDiv_eq hκc hκ hXm hX hφm hφ, hzero, neg_zero]
  have hint : Integrable (fun ω => φ ω * φ ω) μ := hφ.integrable_mul hφ
  have hnn : 0 ≤ fun ω => φ ω * φ ω := fun ω => mul_self_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hint).1 hsq] with ω hω
  exact mul_self_eq_zero.1 hω

end DivLp

/-! ### The kernel stream and its realizations -/

section Stream

variable {Ω : Type*} [AddAction (Vec d) Ω]

/-- Smoothness of a mollified realization, for an arbitrary smooth compactly
supported kernel. -/
theorem contDiff_realize_mollify_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {X : Ω → E} {ω : Ω}
    (hloc : LocallyIntegrable (realize (d := d) X ω) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (realize (d := d) (mollify κ X) ω) := by
  rw [realize_mollify]
  exact hκc.contDiff_convolution_left _ hκ hloc

/-- A mollified realization as an honest convolution integral. -/
theorem realize_mollify_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Vec d → ℝ) (X : Ω → E) (ω : Ω) (x : Vec d) :
    realize (d := d) (mollify κ X) ω x = ∫ y, κ y • realize (d := d) X ω (x - y) := by
  rw [realize_mollify]
  rfl

/-- **Kernel additivity of the mollified realization**, at every point of space. -/
theorem realize_mollify_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Fin d → (Vec d → ℝ)} {ν : Vec d → ℝ}
    (hκc : ∀ m, Continuous (κ m)) (hκs : ∀ m, HasCompactSupport (κ m))
    (hν : ∀ y, ν y = ∑ m : Fin d, κ m y) {X : Ω → E} {ω : Ω}
    (hloc : LocallyIntegrable (realize (d := d) X ω) volume) (x : Vec d) :
    realize (d := d) (mollify ν X) ω x
      = ∑ m : Fin d, realize (d := d) (mollify (κ m) X) ω x := by
  classical
  have hint : ∀ m : Fin d,
      Integrable (fun y => κ m y • realize (d := d) X ω (x - y)) volume := fun m =>
    (hκs m).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hκc m) hloc x
  rw [realize_mollify_apply]
  have hsplit : ∀ y : Vec d, ν y • realize (d := d) X ω (x - y)
      = ∑ m : Fin d, κ m y • realize (d := d) X ω (x - y) := by
    intro y
    rw [hν y, Finset.sum_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_finsetSum _ fun m _ => hint m]
  exact Finset.sum_congr rfl fun m _ => (realize_mollify_apply (κ m) X ω x).symm

/-- **The kernel stream** `S_{im} = A_{g_m} X_i − A_{g_i} X_m`, in the column
convention of `Algsuperdiff.Section3.Provider.Corrector.streamRealization`: the
value `S ω m` is the `m`-th column, so the entry `S_{im}` is `(S ω m) i`. -/
def kernelStream (g : Fin d → (Vec d → ℝ)) (X : Ω → HilbertVec d) (ω : Ω) :
    Fin d → HilbertVec d :=
  fun m => vecPack (fun i => fun a : Ω =>
    mollify (g m) (coordField X i) a - mollify (g i) (coordField X m) a) ω

theorem streamRealization_kernelStream_eq_fun (g : Fin d → (Vec d → ℝ))
    (X : Ω → HilbertVec d) (ω : Ω) (i m : Fin d) :
    streamRealization (kernelStream g X) ω i m
      = fun x => realize (d := d) (mollify (g m) (coordField X i)) ω x
        - realize (d := d) (mollify (g i) (coordField X m)) ω x := rfl

/-- **The kernel stream is antisymmetric**, for every sample, by construction. -/
theorem streamRealization_kernelStream_neg (g : Fin d → (Vec d → ℝ))
    (X : Ω → HilbertVec d) (ω : Ω) (i m : Fin d) :
    streamRealization (kernelStream g X) ω m i
      = -streamRealization (kernelStream g X) ω i m := by
  funext x
  change _ = -(_ - _)
  rw [neg_sub]
  rfl

/-- **The realizations of the kernel stream are smooth.** -/
theorem contDiff_streamRealization_kernelStream {g : Fin d → (Vec d → ℝ)}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    {X : Ω → HilbertVec d} {ω : Ω}
    (hloc : ∀ i : Fin d, LocallyIntegrable (realize (d := d) (coordField X i) ω) volume)
    (i m : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (streamRealization (kernelStream g X) ω i m) := by
  rw [streamRealization_kernelStream_eq_fun]
  exact (contDiff_realize_mollify_of_hasCompactSupport (hgc m) (hgs m) (hloc i)).sub
    (contDiff_realize_mollify_of_hasCompactSupport (hgc i) (hgs i) (hloc m))

/-- The coordinate derivative of a mollified realization falls on the kernel. -/
theorem coordDeriv_realize_mollify {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {φ : Ω → ℝ} {ω : Ω}
    (hloc : LocallyIntegrable (realize (d := d) φ ω) volume) (i : Fin d) (x : Vec d) :
    coordDeriv (realize (d := d) (mollify κ φ) ω) i x
      = realize (d := d) (mollify (kernelDeriv κ i) φ) ω x :=
  fderiv_realize_mollify hκc hκ hloc x i

/-- The single coordinate derivative of an entry of the kernel stream. -/
theorem coordDeriv_streamRealization_kernelStream {g : Fin d → (Vec d → ℝ)}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    {X : Ω → HilbertVec d} {ω : Ω}
    (hloc : ∀ i : Fin d, LocallyIntegrable (realize (d := d) (coordField X i) ω) volume)
    (i m : Fin d) (x : Vec d) :
    coordDeriv (streamRealization (kernelStream g X) ω i m) m x
      = realize (d := d) (mollify (kernelDeriv (g m) m) (coordField X i)) ω x
        - realize (d := d) (mollify (kernelDeriv (g i) m) (coordField X m)) ω x := by
  have hA : DifferentiableAt ℝ
      (realize (d := d) (mollify (g m) (coordField X i)) ω) x :=
    (((contDiff_realize_mollify_of_hasCompactSupport (hgc m) (hgs m)
      (hloc i)).differentiable (by simp)).differentiableAt)
  have hB : DifferentiableAt ℝ
      (realize (d := d) (mollify (g i) (coordField X m)) ω) x :=
    (((contDiff_realize_mollify_of_hasCompactSupport (hgc i) (hgs i)
      (hloc m)).differentiable (by simp)).differentiableAt)
  change fderiv ℝ (streamRealization (kernelStream g X) ω i m) x (basisVec m) = _
  rw [streamRealization_kernelStream_eq_fun, fderiv_fun_sub hA hB]
  rw [sub_apply]
  have hrw : (fderiv ℝ (realize (d := d) (mollify (g m) (coordField X i)) ω) x) (basisVec m)
      - (fderiv ℝ (realize (d := d) (mollify (g i) (coordField X m)) ω) x) (basisVec m)
      = coordDeriv (realize (d := d) (mollify (g m) (coordField X i)) ω) m x
        - coordDeriv (realize (d := d) (mollify (g i) (coordField X m)) ω) m x := rfl
  rw [hrw, coordDeriv_realize_mollify (hgc m) (hgs m) (hloc i) m x,
    coordDeriv_realize_mollify (hgc i) (hgs i) (hloc m) m x]

/-- **The `Ω`-level row divergence of the kernel stream**: the smoothing of `X`
by the divergence of `g`, minus the cross term. -/
def kernelStreamDiv (g : Fin d → (Vec d → ℝ)) (ν : Vec d → ℝ) (X : Ω → HilbertVec d) :
    Ω → HilbertVec d :=
  vecPack fun i => fun ω => mollify ν (coordField X i) ω - mollifyDiv (g i) X ω

/-- **The exact divergence identity.**  At *every* point of space the row
divergence of the realization of the kernel stream is the realization of the
`Ω`-level field `kernelStreamDiv`.  There is no error term here: the whole
approximation is carried by the distance between `kernelStreamDiv` and `X`. -/
theorem streamDivergence_kernelStream {g : Fin d → (Vec d → ℝ)} {ν : Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    (hν : ∀ y, ν y = ∑ m : Fin d, kernelDeriv (g m) m y)
    {X : Ω → HilbertVec d} {ω : Ω}
    (hloc : ∀ i : Fin d, LocallyIntegrable (realize (d := d) (coordField X i) ω) volume)
    (x : Vec d) :
    streamDivergence (streamRealization (kernelStream g X) ω) x
      = (realize (d := d) (kernelStreamDiv g ν X) ω x).toVec := by
  classical
  funext i
  rw [streamDivergence_apply]
  have hterm : ∀ m : Fin d,
      coordDeriv (streamRealization (kernelStream g X) ω i m) m x
        = realize (d := d) (mollify (kernelDeriv (g m) m) (coordField X i)) ω x
          - realize (d := d) (mollify (kernelDeriv (g i) m) (coordField X m)) ω x :=
    fun m => coordDeriv_streamRealization_kernelStream hgs hgc hloc i m x
  rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => hterm m, Finset.sum_sub_distrib]
  have hfirst : (∑ m : Fin d,
      realize (d := d) (mollify (kernelDeriv (g m) m) (coordField X i)) ω x)
      = realize (d := d) (mollify ν (coordField X i)) ω x :=
    (realize_mollify_eq_sum (fun m => continuous_kernelDeriv (hgs m) m)
      (fun m => hasCompactSupport_kernelDeriv (hgc m) m) hν (hloc i) x).symm
  have hsecond : (∑ m : Fin d,
      realize (d := d) (mollify (kernelDeriv (g i) m) (coordField X m)) ω x)
      = realize (d := d) (mollifyDiv (g i) X) ω x := rfl
  rw [hfirst, hsecond]
  rfl

end Stream

/-! ### Measurability and square integrability of the kernel stream -/

section StreamLp

variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

omit [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] [SFinite μ] in
theorem stronglyMeasurable_kernelStream_apply {g : Fin d → (Vec d → ℝ)}
    (hgc : ∀ m, Continuous (g m)) {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X)
    (m : Fin d) : StronglyMeasurable fun ω : Ω => kernelStream g X ω m :=
  stronglyMeasurable_vecPack fun i =>
    (stronglyMeasurable_mollify (hgc m) (stronglyMeasurable_coordField hXm i)).sub
      (stronglyMeasurable_mollify (hgc i) (stronglyMeasurable_coordField hXm m))

theorem memLp_two_kernelStream_apply {g : Fin d → (Vec d → ℝ)}
    (hgc : ∀ m, Continuous (g m)) (hgi : ∀ m, Integrable (g m) volume)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) (m : Fin d) :
    MemLp (fun ω : Ω => kernelStream g X ω m) 2 μ :=
  memLp_two_vecPack
    (fun i => (stronglyMeasurable_mollify (hgc m) (stronglyMeasurable_coordField hXm i)).sub
      (stronglyMeasurable_mollify (hgc i) (stronglyMeasurable_coordField hXm m)))
    (fun i => (memLp_two_mollify (hgc m) (hgi m) (stronglyMeasurable_coordField hXm i)
      (memLp_coordField hXm hX i)).sub
      (memLp_two_mollify (hgc i) (hgi i) (stronglyMeasurable_coordField hXm m)
        (memLp_coordField hXm hX m)))

omit [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] [SFinite μ] in
/-- **The kernel stream is a measurable stationary field.** -/
theorem stronglyMeasurable_kernelStream {g : Fin d → (Vec d → ℝ)}
    (hgc : ∀ m, Continuous (g m)) {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) :
    StronglyMeasurable (kernelStream (Ω := Ω) g X) :=
  (Measurable.of_eval fun m =>
    (stronglyMeasurable_kernelStream_apply hgc hXm m).measurable).stronglyMeasurable

/-- **The kernel stream is square integrable.** -/
theorem memLp_two_kernelStream {g : Fin d → (Vec d → ℝ)}
    (hgc : ∀ m, Continuous (g m)) (hgi : ∀ m, Integrable (g m) volume)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    MemLp (kernelStream (Ω := Ω) g X) 2 μ := by
  classical
  have hdom : MemLp (fun ω : Ω => ∑ m : Fin d, ‖kernelStream g X ω m‖) 2 μ :=
    memLp_finsetSum _ fun m _ => (memLp_two_kernelStream_apply hgc hgi hXm hX m).norm
  refine MemLp.mono' hdom
    (stronglyMeasurable_kernelStream hgc hXm).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hnn : (0 : ℝ) ≤ ∑ m : Fin d, ‖kernelStream g X ω m‖ :=
    Finset.sum_nonneg fun m _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun m => ?_
  exact Finset.single_le_sum (f := fun m => ‖kernelStream g X ω m‖)
    (fun k _ => norm_nonneg _) (Finset.mem_univ m)

omit [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] [SFinite μ] in
theorem stronglyMeasurable_kernelStreamDiv {g : Fin d → (Vec d → ℝ)} {ν : Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hνc : Continuous ν)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) :
    StronglyMeasurable (kernelStreamDiv (Ω := Ω) g ν X) :=
  stronglyMeasurable_vecPack fun i =>
    (stronglyMeasurable_mollify hνc (stronglyMeasurable_coordField hXm i)).sub
      (stronglyMeasurable_mollifyDiv (hgs i) hXm)

theorem memLp_two_kernelStreamDiv {g : Fin d → (Vec d → ℝ)} {ν : Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    (hνc : Continuous ν) (hνi : Integrable ν volume)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    MemLp (kernelStreamDiv (Ω := Ω) g ν X) 2 μ :=
  memLp_two_vecPack
    (fun i => (stronglyMeasurable_mollify hνc (stronglyMeasurable_coordField hXm i)).sub
      (stronglyMeasurable_mollifyDiv (hgs i) hXm))
    (fun i => (memLp_two_mollify hνc hνi (stronglyMeasurable_coordField hXm i)
      (memLp_coordField hXm hX i)).sub (memLp_two_mollifyDiv (hgc i) (hgs i) hXm hX))

/-- **The row divergence is the two-scale smoothing of the field.**  Almost
surely the `Ω`-level row divergence of the kernel stream is `A_{κ₁} X − A_{κ₂} X`:
the cross term is killed by solenoidality and the remaining kernel splits. -/
theorem kernelStreamDiv_ae_eq {g : Fin d → (Vec d → ℝ)} {ν κ₁ κ₂ : Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    (hκ₁c : Continuous κ₁) (hκ₁i : Integrable κ₁ volume)
    (hκ₂c : Continuous κ₂) (hκ₂i : Integrable κ₂ volume)
    (hν : ∀ y, ν y = κ₁ y - κ₂ y)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    ∀ᵐ ω ∂μ, kernelStreamDiv g ν X ω = mollify κ₁ X ω - mollify κ₂ X ω := by
  classical
  have hz : ∀ᵐ ω ∂μ, ∀ i : Fin d, mollifyDiv (g i) X ω = 0 :=
    ae_all_iff.2 fun i => mollifyDiv_ae_eq_zero (hgc i) (hgs i) hXm hX hmem
  have hs1 : ∀ᵐ ω ∂μ, ∀ i : Fin d,
      Integrable (fun y => κ₁ y • coordField X i ((-y) +ᵥ ω)) volume :=
    ae_all_iff.2 fun i => ae_integrable_smul_comp_vadd (μ := μ) hκ₁c hκ₁i
      (stronglyMeasurable_coordField hXm i) (memLp_coordField hXm hX i)
  have hs2 : ∀ᵐ ω ∂μ, ∀ i : Fin d,
      Integrable (fun y => κ₂ y • coordField X i ((-y) +ᵥ ω)) volume :=
    ae_all_iff.2 fun i => ae_integrable_smul_comp_vadd (μ := μ) hκ₂c hκ₂i
      (stronglyMeasurable_coordField hXm i) (memLp_coordField hXm hX i)
  filter_upwards [hz, hs1, hs2,
    ae_integrable_smul_comp_vadd (μ := μ) hκ₁c hκ₁i hXm hX,
    ae_integrable_smul_comp_vadd (μ := μ) hκ₂c hκ₂i hXm hX] with ω h0 h1 h2 hv1 hv2
  refine HilbertVec.ext fun i => ?_
  have hlhs : kernelStreamDiv g ν X ω i
      = mollify ν (coordField X i) ω - mollifyDiv (g i) X ω := rfl
  rw [hlhs, h0 i, sub_zero, mollify_kernel_sub hν (h1 i) (h2 i),
    mollify_coordField_eq hv1 i, mollify_coordField_eq hv2 i]
  rfl

end StreamLp

end

end Algsuperdiff.Section3.Provider.Corrector
