/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Coarea.RegularChart
public import LeanPool.KLS.FunctionalInequalities.Analysis.Coarea.FiberIntegral
public import Mathlib.MeasureTheory.Function.Jacobian

/-! # Change of variables along `m`-dimensional fibres

The ambient side of the codimension-`m` regular coarea formula.  The scalar chain reduces the
ambient integral to the parameter space by Tonelli plus the **one-dimensional** Jacobian theorem on
each vertical fibre (`setLIntegral_image_verticalMap`).  This module is its codimension-`m`
analogue, where each fibre is `m`-dimensional and the vertical map goes from `W` to `K`.

**Mathlib's change of variables is a self-map statement**, `f : E → E` against an additive Haar
measure, and its volume factor is `|det (f' x)|`, a determinant of an endomorphism.  A fibre map
`t ↦ ψ (y, t)` goes from the level space `W` to the normal factor `K`, which are two **different**
spaces of the same dimension, so that determinant does not typecheck.
`lintegral_image_eq_lintegral_normDet_fderiv_mul` supplies the missing statement: the volume factor
is `LinearMap.normDet`, which is defined between different spaces, and the proof conjugates by a
linear isometry — measure preserving, and of unit norm determinant, so nothing is added.

With that, `setLIntegral_image_vectorVerticalMap` is the codimension-`m` vertical substitution, and
`setLIntegral_image_levelGraphMap` transports it to the ambient space along the measure-preserving
splitting proved in `Analysis/Vector/Graph/CoareaJacobian.lean`.  Finally
`setLIntegral_coareaJacobian_levelGraphFamily` replaces the ambient density by the graph area
density, using the fibre Jacobian identity; this is the ambient half of the local coarea equality.

This module supplies the ambient half of the local coarea argument. The weighted fibre area
formula is in `Analysis/Vector/Graph/Integral.lean`; the Tonelli assembly and regular-open-set
patching are in `Analysis/Vector/Coarea/{Local,Regular}.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

/-! ### Change of variables between two spaces of the same dimension -/

section ChangeOfVariables

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Two inner product spaces of the same finite dimension are linearly isometric.  Only existence
is used below; the choice never appears in a statement. -/
def isometryEquivOfFinrankEq (h : finrank ℝ E = finrank ℝ F) : E ≃ₗᵢ[ℝ] F :=
  (stdOrthonormalBasis ℝ E).repr.trans
    (((stdOrthonormalBasis ℝ F).reindex (finCongr h.symm)).repr.symm)

/-- **Change of variables between two spaces of the same dimension.**  Mathlib proves the self-map
case with the volume factor `|det f'|`; between different spaces that determinant does not
typecheck, and the volume factor is `LinearMap.normDet f'`.  The weight is an arbitrary
`ℝ≥0∞`-valued function: no integrability, finiteness or continuity is assumed, and `f` needs only a
derivative within `s` at each point of `s` together with injectivity there. -/
theorem lintegral_image_eq_lintegral_normDet_fderiv_mul (h : finrank ℝ E = finrank ℝ F)
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hinj : InjOn f s) (g : F → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂(volume : Measure F)
      = ∫⁻ x in s, ENNReal.ofReal (LinearMap.normDet ((f' x : E →ₗ[ℝ] F))) * g (f x)
          ∂(volume : Measure E) := by
  set ε : F ≃ₗᵢ[ℝ] E := isometryEquivOfFinrankEq h.symm with hεdef
  have hcomp : ∀ x ∈ s, HasFDerivWithinAt (fun z => ε (f z))
      ((ε.toLinearIsometry.toContinuousLinearMap) ∘L f' x) s x := fun x hx =>
    (ε.toLinearIsometry.toContinuousLinearMap.hasFDerivAt).comp_hasFDerivWithinAt x (hf' x hx)
  have hinj' : InjOn (fun z => ε (f z)) s := fun x hx y hy hxy => hinj hx hy (ε.injective hxy)
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure E))
    hs hcomp hinj' (fun z => g (ε.symm z))
  have himg : (fun z => ε (f z)) '' s = ε '' (f '' s) := by rw [Set.image_image]
  have hmp : MeasurePreserving (ε : F → E) volume volume := ε.measurePreserving
  have hemb : MeasurableEmbedding (ε : F → E) := ε.toHomeomorph.measurableEmbedding
  have hlhs : ∫⁻ z in ε '' (f '' s), g (ε.symm z) ∂(volume : Measure E)
      = ∫⁻ y in f '' s, g y ∂(volume : Measure F) := by
    rw [← hmp.setLIntegral_comp_emb hemb (fun z => g (ε.symm z)) (f '' s)]
    simp
  rw [himg, hlhs] at key
  rw [key]
  apply setLIntegral_congr_fun hs
  intro x hx
  have hdet : |(((ε.toLinearIsometry.toContinuousLinearMap) ∘L f' x)).det|
      = LinearMap.normDet ((f' x : E →ₗ[ℝ] F)) := by
    rw [← LinearMap.normDet_eq_abs_det]
    have hc : LinearMap.normDet
        (((ε.toLinearIsometry.toContinuousLinearMap ∘L f' x : E →L[ℝ] E) : E →ₗ[ℝ] E))
        = LinearMap.normDet (ε.toLinearIsometry.toLinearMap)
          * LinearMap.normDet ((f' x : E →ₗ[ℝ] F)) :=
      LinearMap.normDet_comp_of_finrank_eq _ _ h
    rw [hc, LinearIsometry.normDet_eq_one, one_mul]
  simp only [hdet, LinearIsometryEquiv.symm_apply_apply]

end ChangeOfVariables

/-! ### The vertical derivative -/

section Vertical

variable {H K W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- The derivative in the level coordinate is the joint derivative restricted to the level
factor. -/
theorem fderiv_snd_eq {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) (p : H × W) :
    fderiv ℝ (fun t => ψ (p.1, t)) p.2 = fderiv ℝ ψ p ∘L (ContinuousLinearMap.inr ℝ H W) := by
  have hpath : HasFDerivAt (fun t : W => (p.1, t)) (ContinuousLinearMap.inr ℝ H W) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  exact (((hψ.differentiable one_ne_zero p).hasFDerivAt).comp p.2 hpath).fderiv

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace K]
  [BorelSpace K] [MeasurableSpace W] [BorelSpace W] in
/-- The vertical volume factor varies continuously with both coordinates. -/
theorem continuous_normDet_fderiv_snd {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (fun p : H × W =>
      LinearMap.normDet ((fderiv ℝ (fun t => ψ (p.1, t)) p.2 : W →ₗ[ℝ] K))) := by
  simp_rw [fderiv_snd_eq hψ]
  exact continuous_normDet.comp
    (((ContinuousLinearMap.compL ℝ W (H × W) K).flip
      (ContinuousLinearMap.inr ℝ H W)).continuous.comp (hψ.continuous_fderiv (by simp)))

/-- **Weighted substitution for a `C¹` vertical map in codimension `m`**, on an arbitrary injective
Borel piece.  The weight is an arbitrary `ℝ≥0∞`-valued measurable function; no finite measure or
integrability is assumed.  This is the codimension-`m` analogue of
`setLIntegral_image_verticalMap`, and the level space `W` and the normal factor `K` stay distinct
throughout. -/
theorem setLIntegral_image_vectorVerticalMap (hdim : finrank ℝ W = finrank ℝ K)
    {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) {A : Set (H × W)} (hA : MeasurableSet A)
    (hi : InjOn (fun p : H × W => (p.1, ψ p)) A) {f : H × K → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q in (fun p : H × W => (p.1, ψ p)) '' A, f q ∂(volume : Measure (H × K))
      = ∫⁻ p in A, ENNReal.ofReal (LinearMap.normDet
            ((fderiv ℝ (fun t => ψ (p.1, t)) p.2 : W →ₗ[ℝ] K))) * f (p.1, ψ p)
          ∂(volume : Measure (H × W)) := by
  have hc : Continuous (fun p : H × W => (p.1, ψ p)) := continuous_fst.prodMk hψ.continuous
  have hI := hA.image_of_continuousOn_injOn hc.continuousOn hi
  have hm : Measurable (fun p : H × W => ENNReal.ofReal (LinearMap.normDet
      ((fderiv ℝ (fun t => ψ (p.1, t)) p.2 : W →ₗ[ℝ] K))) * f (p.1, ψ p)) :=
    (continuous_normDet_fderiv_snd hψ).measurable.ennreal_ofReal.mul (hf.comp hc.measurable)
  rw [Measure.volume_eq_prod, setLIntegral_prod_fibers hI hf,
    Measure.volume_eq_prod, setLIntegral_prod_fibers hA hm]
  apply lintegral_congr
  intro y
  have hAy : MeasurableSet {t : W | (y, t) ∈ A} :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have himg : {s : K | (y, s) ∈ (fun p : H × W => (p.1, ψ p)) '' A}
      = (fun t => ψ (y, t)) '' {t : W | (y, t) ∈ A} := by
    ext s
    constructor
    · rintro ⟨⟨z, t⟩, hp, he⟩
      have hz : z = y := congrArg Prod.fst he
      subst hz
      exact ⟨t, hp, congrArg Prod.snd he⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(y, t), ht, rfl⟩
  rw [himg]
  exact lintegral_image_eq_lintegral_normDet_fderiv_mul hdim hAy
    (fun t _ => ((hψ.differentiable one_ne_zero (y, t)).comp t
      ((differentiableAt_const _).prodMk differentiableAt_id)).hasFDerivAt.hasFDerivWithinAt)
    (fun t ht s hs he => congrArg Prod.snd (hi ht hs (Prod.ext rfl he))) _

end Vertical

/-! ### Transport to the ambient space -/

section Ambient

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace V] [BorelSpace V] in
/-- The splitting as a continuous linear equivalence, with the component retractions as its
explicit inverse. -/
def splitVectorEquiv {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V} (hs : IsVectorGraphSplitting ι κ) :
    (H × K) ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse
    (ι.toContinuousLinearMap ∘L (ContinuousLinearMap.fst ℝ H K)
      + κ.toContinuousLinearMap ∘L (ContinuousLinearMap.snd ℝ H K))
    ((graphProj ι).prod (graphProj κ))
    (by rintro ⟨y, z⟩; exact Prod.ext (hs.proj_left y z) (hs.proj_right y z))
    (fun x => hs.split x)

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem splitVectorEquiv_apply {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) (p : H × K) :
    splitVectorEquiv hs p = ι p.1 + κ p.2 := rfl

/-- **Weighted substitution along the graph map of a level family.**  The vertical substitution
transported to the ambient space by the measure-preserving splitting. -/
theorem setLIntegral_image_levelGraphMap {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) (hdim : finrank ℝ W = finrank ℝ K)
    {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) {A : Set (H × W)} (hA : MeasurableSet A)
    (hi : InjOn (fun p : H × W => ι p.1 + κ (ψ p)) A) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in (fun p : H × W => ι p.1 + κ (ψ p)) '' A, f x ∂(volume : Measure V)
      = ∫⁻ p in A, ENNReal.ofReal (LinearMap.normDet
            ((fderiv ℝ (fun t => ψ (p.1, t)) p.2 : W →ₗ[ℝ] K))) * f (ι p.1 + κ (ψ p))
          ∂(volume : Measure (H × W)) := by
  set E : (H × K) ≃L[ℝ] V := splitVectorEquiv hs with hEdef
  set T : H × W → H × K := fun p => (p.1, ψ p) with hTdef
  have hET : ∀ p : H × W, E (T p) = ι p.1 + κ (ψ p) := fun p => rfl
  have hTinj : InjOn T A := fun p hp q hq hpq => by
    refine hi hp hq ?_
    change ι p.1 + κ (ψ p) = ι q.1 + κ (ψ q)
    rw [← hET p, ← hET q, hpq]
  have himage : (fun p : H × W => ι p.1 + κ (ψ p)) '' A = E '' (T '' A) := by
    rw [← Set.image_comp]
    rfl
  have hmp : MeasurePreserving (E : H × K → V) volume volume := measurePreserving_split hs
  have hemb : MeasurableEmbedding (E : H × K → V) := E.toHomeomorph.measurableEmbedding
  rw [himage, ← hmp.setLIntegral_comp_emb hemb f (T '' A)]
  exact setLIntegral_image_vectorVerticalMap hdim hψ hA hTinj (hf.comp E.continuous.measurable)

/-- **The ambient side of the local coarea equality.**  On a Borel piece of a level-graph family the
integral of the ambient coarea density against an arbitrary weight becomes an integral over the
parameter–level domain of the **graph area density**, which is what the normalized area formula
`hausdorffNormalized_image_vectorGraphMap` consumes.  The substitution is the codimension-`m`
vertical one; the change of density is the fibre Jacobian identity, applied pointwise.

**This is not a coarea formula**: the remaining steps are Tonelli in the level variable, the
*weighted* codimension-`m` area formula on each fibre, and the patching. -/
theorem setLIntegral_coareaJacobian_levelGraphFamily {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) (hdim : finrank ℝ K = finrank ℝ W)
    {u : V → W} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    {Ω : Set (H × W)} (hΩ : IsOpen Ω) {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ)
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2)
    (hmem : ∀ p ∈ Ω, ι p.1 + κ (ψ p) ∈ O)
    (hinj : InjOn (fun p : H × W => ι p.1 + κ (ψ p)) Ω)
    {A : Set (H × W)} (hA : MeasurableSet A) (hAΩ : A ⊆ Ω)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in (fun p : H × W => ι p.1 + κ (ψ p)) '' A,
        ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ p in A, ENNReal.ofReal (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, p.2)) p.1) : H →ₗ[ℝ] V)))
          * g (ι p.1 + κ (ψ p)) ∂(volume : Measure (H × W)) := by
  have hdens : Measurable fun x : V =>
      ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x :=
    (measurable_coareaJacobian_fderiv u).ennreal_ofReal.mul hg
  rw [setLIntegral_image_levelGraphMap hs hdim.symm hψ hA (hinj.mono hAΩ) hdens]
  apply setLIntegral_congr_fun hA
  intro p hp
  have hpoint := normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily hs hdim hO hu hΩ hψ
    hlevel hmem (y₀ := p.1) (t₀ := p.2) (by simpa using hAΩ hp)
  change ENNReal.ofReal (LinearMap.normDet
        ((fderiv ℝ (fun t => ψ (p.1, t)) p.2 : W →ₗ[ℝ] K)))
      * (ENNReal.ofReal (coareaJacobian (fderiv ℝ u (ι p.1 + κ (ψ p)))) * g (ι p.1 + κ (ψ p)))
    = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), hpoint]

end Ambient

end FunctionalInequalities.Analysis
