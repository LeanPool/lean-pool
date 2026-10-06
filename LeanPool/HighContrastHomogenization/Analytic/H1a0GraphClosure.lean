/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH1a0
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.H10Graph

/-!
# High-contrast homogenization: Analytic.H1a0GraphClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Closed-graph realization of coefficient-weighted zero-trace gradients

The approximation clause of `MemH1a0` gives unweighted gradient convergence.
Zero-trace Poincaré then makes the scalar `L²` representatives Cauchy, so the
smooth graph pairs converge inside the closed `H¹₀` graph.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

private theorem memVectorL2_smoothGrad_of_isLocalTest {U : Set (Vec d)}
    (hU : IsOpen U) {f : Vec d → ℝ} (hf : IsLocalTest U f) :
    MemVectorL2 U (smoothGrad f) := by
  let w : H10Function U :=
    H10Function.ofContDiff hU hf.contDiff hf.hasCompactSupport hf.tsupport_subset
  simpa [w, H10Function.ofContDiff, H1Function.ofContDiff, smoothGrad] using!
    w.toH1Function.grad_memVectorL2

/-- The Hilbert-vector `L²` seminorm is the square root of the integral of
the Euclidean squared norm of the underlying vector field. -/
theorem eLpNorm_hilbertifyVecField_eq_rpow_lintegral_vecNormSq
    {U : Set (Vec d)} (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (volume.restrict U)) :
    eLpNorm (hilbertifyVecField F) 2 (volume.restrict U) =
      (∫⁻ x in U, ENNReal.ofReal (vecNormSq (F x)) ∂volume) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  apply lintegral_congr
  intro x
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  congr 1
  rw [Real.rpow_two, HilbertVec.norm_sq_eq_sum_sq, vecNormSq_eq_sum_sq]
  rfl

/-- The gradient slot of a coefficient-weighted zero-trace pair has an honest
vector-valued `L²` realization. -/
theorem memVectorL2_grad_of_memH1a0 {U : Set (Vec d)} {b : CoeffField d}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b U u Du) :
    MemVectorL2 U Du := by
  have hsq : IntegrableOn (fun x ↦ vecNormSq (Du x)) U volume :=
    integrableOn_vecNormSq_grad_of_memH1a0_class hlam hell hu
  have hcoord : ∀ i, MemScalarL2 U (fun x ↦ Du x i) := by
    intro i
    apply (memLp_two_iff_integrable_sq (hu.1.2 i)).2
    refine hsq.mono' ((hu.1.2 i).pow 2) ?_
    filter_upwards with x
    have hi : 0 ≤ Du x i ^ 2 := sq_nonneg _
    have hvec : 0 ≤ vecNormSq (Du x) := vecNormSq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hi, abs_of_nonneg hvec] using
      sq_apply_le_vecNormSq (Du x) i
  simpa [MemVectorL2, volumeMeasureOn] using
    (MemLp.of_eval hcoord : MemLp Du 2 (volumeMeasureOn U))

/-- On a bounded open convex domain, the gradient slot of a `MemH1a0` pair is
the weak gradient of an actual `H¹₀` function. -/
theorem exists_h10Function_grad_ae_eq_of_memH1a0 [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {b : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b U u Du) :
    ∃ w : H10Function U,
      w.toH1Function.grad =ᵐ[volume.restrict U] Du := by
  obtain ⟨hpair, hweak, v, hvtest, hvh1, hvskew⟩ := hu
  have hu0 : MemH1a0 b U u Du :=
    ⟨hpair, hweak, v, hvtest, hvh1, hvskew⟩
  let w : ℕ → H10Function U := fun n ↦
    H10Function.ofContDiff hU.isOpen (hvtest n).contDiff
      (hvtest n).hasCompactSupport (hvtest n).tsupport_subset
  have hDu : MemVectorL2 U Du :=
    memVectorL2_grad_of_memH1a0 hlam hell hu0
  have hvgrad : ∀ n, MemVectorL2 U (smoothGrad (v n)) :=
    fun n ↦ memVectorL2_smoothGrad_of_isLocalTest hU.isOpen (hvtest n)
  have hunweighted : Tendsto
      (fun n ↦ h1NormSqOnUnweighted U (fun x ↦ v n x - u x)
        (fun x ↦ smoothGrad (v n) x - Du x)) atTop (nhds 0) :=
    (tendsto_h1sNormSqOn_sub_zero_iff hlam hell u Du v).mp hvh1
  have hgradIntegral : Tendsto
      (fun n ↦ ∫⁻ x in U,
        ENNReal.ofReal (vecNormSq (smoothGrad (v n) x - Du x)) ∂volume)
      atTop (nhds 0) := by
    exact tendsto_zero_of_le_of_tendsto_zero (fun n ↦ by
      unfold h1NormSqOnUnweighted
      exact le_add_of_nonneg_left zero_le) hunweighted
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
  have hgrad : Tendsto (fun n ↦ (w n).toH1Function.gradToHilbertVectorL2)
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
    simpa [w, H10Function.ofContDiff, H1Function.ofContDiff, smoothGrad,
      H1Function.gradToHilbertVectorL2, toHilbertVectorL2OfVecField,
      toHilbertVectorL2] using! ht
  rcases h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient hU with
    ⟨C, hC, hPoincare⟩
  have hscalarCauchy : CauchySeq (fun n ↦ (w n).toH1Function.toScalarL2) := by
    rcases cauchySeq_iff_le_tendsto_0.mp hgrad.cauchySeq with
      ⟨a, ha, hdist, hatend⟩
    apply cauchySeq_iff_le_tendsto_0.mpr
    refine ⟨fun N ↦ C * a N, fun N ↦ mul_nonneg hC (ha N), ?_, ?_⟩
    · intro n m N hn hm
      have hnmem :
          ((w n).toH1Function.toScalarL2,
            (w n).toH1Function.gradToHilbertVectorL2) ∈
            h10GraphClosedSubmodule U :=
        Submodule.le_topologicalClosure _ (h10_pair_mem_h10GraphSubmodule (w n))
      have hmmem :
          ((w m).toH1Function.toScalarL2,
            (w m).toH1Function.gradToHilbertVectorL2) ∈
            h10GraphClosedSubmodule U :=
        Submodule.le_topologicalClosure _ (h10_pair_mem_h10GraphSubmodule (w m))
      have hp := hPoincare _ ((h10GraphClosedSubmodule U).sub_mem hnmem hmmem)
      calc
        dist (w n).toH1Function.toScalarL2 (w m).toH1Function.toScalarL2 =
            ‖(w n).toH1Function.toScalarL2 -
              (w m).toH1Function.toScalarL2‖ := dist_eq_norm _ _
        _ ≤ C * ‖(w n).toH1Function.gradToHilbertVectorL2 -
            (w m).toH1Function.gradToHilbertVectorL2‖ := by simpa using hp
        _ = C * dist (w n).toH1Function.gradToHilbertVectorL2
            (w m).toH1Function.gradToHilbertVectorL2 := by rw [dist_eq_norm]
        _ ≤ C * a N := mul_le_mul_of_nonneg_left (hdist n m N hn hm) hC
    · have ht := hatend.const_mul C
      simpa using ht
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hscalarCauchy
  have hpairTendsto : Tendsto
      (fun n ↦ ((w n).toH1Function.toScalarL2,
        (w n).toH1Function.gradToHilbertVectorL2)) atTop
      (nhds (z, toHilbertVectorL2OfVecField hDu)) := hz.prodMk_nhds hgrad
  have hclosure :
      (z, toHilbertVectorL2OfVecField hDu) ∈
        closure ((h10GraphSubmodule U : Submodule ℝ
          (ScalarL2 U × HilbertVectorL2 U)) : Set
            (ScalarL2 U × HilbertVectorL2 U)) :=
    mem_closure_of_tendsto hpairTendsto
      (Filter.Eventually.of_forall fun n ↦ h10_pair_mem_h10GraphSubmodule (w n))
  have hclosed : (z, toHilbertVectorL2OfVecField hDu) ∈
      (h10GraphClosedSubmodule U).toSubmodule := by
    change (z, toHilbertVectorL2OfVecField hDu) ∈
      (h10GraphSubmodule U).topologicalClosure
    exact hclosure
  obtain ⟨w0, -, hw0grad⟩ :=
    exists_h10Function_of_mem_h10GraphClosedSubmodule hU hclosed
  refine ⟨w0, ?_⟩
  filter_upwards [w0.toH1Function.coeFn_gradToHilbertVectorL2,
    coeFn_toHilbertVectorL2OfVecField hDu] with x hwx hDux
  have heq : hilbertifyVecField w0.toH1Function.grad x =
      hilbertifyVecField Du x := by
    rw [← hwx, ← hDux, hw0grad]
  simpa [hilbertifyVecField] using congrArg HilbertVec.toVec heq

end

end HighContrast
end HCPolySupport
