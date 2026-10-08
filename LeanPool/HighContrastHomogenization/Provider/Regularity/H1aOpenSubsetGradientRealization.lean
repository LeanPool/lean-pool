/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.H1aGradientL2
public import LeanPool.HighContrastHomogenization.Analytic.H1a0GraphClosure
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Hodge

/-!
# High-contrast homogenization: Provider.Regularity.H1aOpenSubsetGradientRealization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Realizing an H1a gradient on an interior open carrier

The root `MemH1a` hypothesis is posed on the closed physical ellipsoid.  A
rounded physical cube used by the finite recurrence is an open bounded convex
subset of that carrier.  The global smooth approximation in `MemH1a`
restricts to the cube, so its gradient slot has an actual local `H1Function`
representative there.  No membership statement on a widened or changed
domain is introduced.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- On an open bounded convex subset of a bounded `MemH1a` carrier, the
gradient slot is the gradient of an actual local `H1Function`. -/
theorem isPotentialOn_grad_on_openSubset_of_memH1a
    {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hUV : U ⊆ V)
    (hVb : Bornology.IsBounded V)
    {b : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) :
    IsPotentialOn U Du := by
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  obtain ⟨hpair, hweak, v, hv, hvh1, hvskew⟩ := hu
  have hu' : MemH1a b V u Du :=
    ⟨hpair, hweak, v, hv, hvh1, hvskew⟩
  let w : ℕ → H1Function U := fun n ↦
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
      ((hv n).of_le (by simp))
  have hDuV : MemVectorL2 V Du :=
    memVectorL2_grad_of_memH1a hlam hell hVb hu'
  have hmeasure : volume.restrict U ≤ volume.restrict V :=
    Measure.restrict_mono_set volume hUV
  have hDu : MemVectorL2 U Du := hDuV.mono_measure hmeasure
  have hvgrad : ∀ n, MemVectorL2 U (smoothGrad (v n)) := by
    intro n
    simpa [w, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain, H1Function.ofContDiff,
      smoothGrad] using! (w n).grad_memVectorL2
  have hunweighted : Tendsto
      (fun n ↦ h1NormSqOnUnweighted V (fun x ↦ v n x - u x)
        (fun x ↦ smoothGrad (v n) x - Du x)) atTop (nhds 0) :=
    (tendsto_h1sNormSqOn_sub_zero_iff hlam hell u Du v).mp hvh1
  have hgradIntegralV : Tendsto
      (fun n ↦ ∫⁻ x in V,
        ENNReal.ofReal (vecNormSq (smoothGrad (v n) x - Du x)) ∂volume)
      atTop (nhds 0) := by
    exact tendsto_zero_of_le_of_tendsto_zero (fun n ↦ by
      unfold h1NormSqOnUnweighted
      exact le_add_of_nonneg_left zero_le) hunweighted
  have hgradIntegral : Tendsto
      (fun n ↦ ∫⁻ x in U,
        ENNReal.ofReal (vecNormSq (smoothGrad (v n) x - Du x)) ∂volume)
      atTop (nhds 0) := by
    exact tendsto_zero_of_le_of_tendsto_zero (fun n ↦
      lintegral_mono' hmeasure le_rfl) hgradIntegralV
  have hgradELp : Tendsto
      (fun n ↦ eLpNorm
        (hilbertifyVecField (fun x ↦ smoothGrad (v n) x - Du x)) 2
        (volume.restrict U)) atTop (nhds 0) := by
    have hroot : Tendsto
        (fun n ↦ (∫⁻ x in U,
          ENNReal.ofReal (vecNormSq (smoothGrad (v n) x - Du x)) ∂volume) ^
            (1 / 2 : ℝ)) atTop (nhds (0 ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hgradIntegral
    have hmeas : ∀ n, AEStronglyMeasurable
        (hilbertifyVecField (fun x ↦ smoothGrad (v n) x - Du x)) (volume.restrict U) :=
      fun n ↦ (memHilbertVectorL2_hilbertifyVecField ((hvgrad n).sub hDu)).aestronglyMeasurable
    simpa [eLpNorm_hilbertifyVecField_eq_rpow_lintegral_vecNormSq, hmeas] using hroot
  have hgradELp' : Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ hilbertifyVecField (smoothGrad (v n)) x -
          hilbertifyVecField Du x) 2 (volume.restrict U)) atTop (nhds 0) := by
    convert hgradELp using 1
    funext n
    congr 1
  have hgrad : Tendsto (fun n ↦ (w n).gradToHilbertVectorL2)
      atTop (nhds (toHilbertVectorL2OfVecField hDu)) := by
    let hvhilb : ∀ n,
        MemHilbertVectorL2 U (hilbertifyVecField (smoothGrad (v n))) :=
      fun n ↦ memHilbertVectorL2_hilbertifyVecField (hvgrad n)
    let hDuhilb : MemHilbertVectorL2 U (hilbertifyVecField Du) :=
      memHilbertVectorL2_hilbertifyVecField hDu
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (p := (2 : ENNReal)) (fi := atTop)
      (fun n ↦ hilbertifyVecField (smoothGrad (v n))) hvhilb
      (hilbertifyVecField Du) hDuhilb).2 hgradELp'
    simpa [w, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain, H1Function.ofContDiff,
      smoothGrad, H1Function.gradToHilbertVectorL2,
      toHilbertVectorL2OfVecField, toHilbertVectorL2] using! ht
  apply hodgeConverseCriterion_of_isOpenBoundedConvexDomain hU hDu
  intro g hg hsol
  let G : HilbertVectorL2 U := toHilbertVectorL2OfVecField hg
  have hpairLimit : Tendsto
      (fun n ↦ inner ℝ G (w n).gradToHilbertVectorL2) atTop
      (nhds (inner ℝ G (toHilbertVectorL2OfVecField hDu))) := by
    exact _root_.Filter.Tendsto.inner tendsto_const_nhds hgrad
  have hpairZero : Tendsto
      (fun n ↦ inner ℝ G (w n).gradToHilbertVectorL2) atTop (nhds 0) := by
    convert tendsto_const_nhds using 1
    funext n
    change inner ℝ (toHilbertVectorL2OfVecField hg)
      (toHilbertVectorL2OfVecField (w n).grad_memVectorL2) = 0
    rw [inner_toHilbertVectorL2OfVecField_eq_integral]
    exact hsol (w n)
  have hinner : inner ℝ G (toHilbertVectorL2OfVecField hDu) = 0 :=
    tendsto_nhds_unique hpairLimit hpairZero
  change inner ℝ (toHilbertVectorL2OfVecField hg)
    (toHilbertVectorL2OfVecField hDu) = 0 at hinner
  rw [inner_toHilbertVectorL2OfVecField_eq_integral] at hinner
  exact hinner

end

end HighContrast
end HCPolySupport
