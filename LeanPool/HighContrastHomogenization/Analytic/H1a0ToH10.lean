/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.H1a0GraphClosure

/-!
# High-contrast homogenization: Analytic.H1a0ToH10

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Realizing coefficient-weighted zero-trace pairs as `H¹₀` functions

The closed-graph gradient realization is identified with the original scalar
slot by comparing the same compactly supported approximants in `L²` and `L¹`.
The resulting representative is then repackaged with the original scalar and
gradient functions as its literal fields.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

private theorem memScalarL2_of_isLocalTest {U : Set (Vec d)}
    (hU : IsOpen U) {f : Vec d → ℝ} (hf : IsLocalTest U f) :
    MemScalarL2 U f := by
  let w : H10Function U :=
    H10Function.ofContDiff hU hf.contDiff hf.hasCompactSupport hf.tsupport_subset
  simpa [w, H10Function.ofContDiff, H1Function.ofContDiff] using
    w.toH1Function.memL2

private theorem tendsto_self_of_tendsto_sq {f : ℕ → ℝ≥0∞}
    (h : Tendsto (fun n ↦ (f n) ^ 2) atTop (nhds 0)) :
    Tendsto f atTop (nhds 0) := by
  have hroot : Tendsto (fun n ↦ ((f n) ^ 2) ^ (1 / 2 : ℝ)) atTop
      (nhds (0 ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h
  convert hroot using 1
  · funext n
    rw [← ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_mul]
    norm_num
  · norm_num

private theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm_two
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {F : ℕ → Vec d → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict U))
    (h : Tendsto (fun n ↦ eLpNorm (F n) 2 (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto (fun n ↦ eLpNorm (F n) 1 (volume.restrict U))
      atTop (nhds 0) := by
  let q : ℝ := 1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal
  let M : ℝ≥0∞ := (volume.restrict U) Set.univ ^ q
  have hq : 0 ≤ q := by norm_num [q]
  have hM : M ≠ ⊤ := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq
      (measure_lt_top (volume.restrict U) Set.univ).ne).ne
  have hbound : ∀ n,
      eLpNorm (F n) 1 (volume.restrict U) ≤
        eLpNorm (F n) 2 (volume.restrict U) * M := by
    intro n
    simpa [M, q] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (by norm_num : (1 : ENNReal) ≤ 2) (hF n))
  have hscaled := ENNReal.Tendsto.mul_const h (Or.inr hM)
  rw [zero_mul] at hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hscaled (fun _ ↦ zero_le) hbound

/-- On a bounded open convex domain, every coefficient-weighted zero-trace
pair is represented, with its literal scalar and gradient fields, by an actual
`H¹₀` function. -/
theorem exists_h10Function_of_memH1a0 [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {b : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b U u Du) :
    ∃ w : H10Function U,
      w.toH1Function.toFun = u ∧ w.toH1Function.grad = Du := by
  obtain ⟨w0, hgradAE⟩ :=
    exists_h10Function_grad_ae_eq_of_memH1a0 hU hlam hell hu
  obtain ⟨hpair, hweak, v, hvtest, hvh1, -⟩ := hu
  let w : ℕ → H10Function U := fun n ↦
    H10Function.ofContDiff hU.isOpen (hvtest n).contDiff
      (hvtest n).hasCompactSupport (hvtest n).tsupport_subset
  have hvL2 : ∀ n, MemScalarL2 U (v n) :=
    fun n ↦ memScalarL2_of_isLocalTest hU.isOpen (hvtest n)
  have hvgrad : ∀ n, MemVectorL2 U (smoothGrad (v n)) := by
    intro n
    simpa [w, H10Function.ofContDiff, H1Function.ofContDiff, smoothGrad] using!
      (w n).toH1Function.grad_memVectorL2
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
      exact le_add_of_nonneg_left (zero_le)) hunweighted
  have hgradELp : Tendsto
      (fun n ↦ eLpNorm
        (hilbertifyVecField (fun x ↦ smoothGrad (v n) x - Du x)) 2
        (volume.restrict U)) atTop (nhds 0) := by
    have hroot : Tendsto
        (fun n ↦ (∫⁻ x in U,
          ENNReal.ofReal (vecNormSq (smoothGrad (v n) x - Du x)) ∂volume) ^
            (1 / 2 : ℝ)) atTop (nhds (0 ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hgradIntegral
    have hDu : MemVectorL2 U Du :=
      w0.toH1Function.grad_memVectorL2.ae_eq hgradAE
    have hmeas : ∀ n, AEStronglyMeasurable
        (hilbertifyVecField (fun x ↦ smoothGrad (v n) x - Du x)) (volume.restrict U) :=
      fun n ↦ (memHilbertVectorL2_hilbertifyVecField ((hvgrad n).sub hDu)).aestronglyMeasurable
    simpa [eLpNorm_hilbertifyVecField_eq_rpow_lintegral_vecNormSq, hmeas] using hroot
  have hgradELp' : Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ hilbertifyVecField (smoothGrad (v n)) x -
          hilbertifyVecField w0.toH1Function.grad x) 2 (volume.restrict U))
      atTop (nhds 0) := by
    convert hgradELp using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hgradAE] with x hx
    simp only [hilbertifyVecField, hx]
    apply HilbertVec.ext
    intro i
    rfl
  have hgrad : Tendsto (fun n ↦ (w n).toH1Function.gradToHilbertVectorL2)
      atTop (nhds w0.toH1Function.gradToHilbertVectorL2) := by
    let hvhilb : ∀ n,
        MemHilbertVectorL2 U (hilbertifyVecField (smoothGrad (v n))) :=
      fun n ↦ memHilbertVectorL2_hilbertifyVecField (hvgrad n)
    let hwhilb : MemHilbertVectorL2 U
        (hilbertifyVecField w0.toH1Function.grad) :=
      memHilbertVectorL2_hilbertifyVecField w0.toH1Function.grad_memVectorL2
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (p := (2 : ENNReal)) (fi := atTop)
      (fun n ↦ hilbertifyVecField (smoothGrad (v n))) hvhilb
      (hilbertifyVecField w0.toH1Function.grad) hwhilb).2 hgradELp'
    simpa [w, H10Function.ofContDiff, H1Function.ofContDiff, smoothGrad,
      H1Function.gradToHilbertVectorL2, toHilbertVectorL2OfVecField,
      toHilbertVectorL2] using! ht
  rcases h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient hU with
    ⟨C, hC, hPoincare⟩
  have hscalarDist : Tendsto
      (fun n ↦ dist (w n).toH1Function.toScalarL2
        w0.toH1Function.toScalarL2) atTop (nhds 0) := by
    have hgradDist := tendsto_iff_dist_tendsto_zero.mp hgrad
    have hscaled := hgradDist.const_mul C
    rw [mul_zero] at hscaled
    have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hscaled
    · exact fun _ ↦ dist_nonneg
    · intro n
      have hnmem :
          ((w n).toH1Function.toScalarL2,
            (w n).toH1Function.gradToHilbertVectorL2) ∈
            h10GraphClosedSubmodule U :=
        Submodule.le_topologicalClosure _ (h10_pair_mem_h10GraphSubmodule (w n))
      have h0mem :
          (w0.toH1Function.toScalarL2,
            w0.toH1Function.gradToHilbertVectorL2) ∈
            h10GraphClosedSubmodule U :=
        Submodule.le_topologicalClosure _ (h10_pair_mem_h10GraphSubmodule w0)
      have hp := hPoincare _ ((h10GraphClosedSubmodule U).sub_mem hnmem h0mem)
      simpa [dist_eq_norm] using hp
  have hscalar : Tendsto (fun n ↦ (w n).toH1Function.toScalarL2)
      atTop (nhds w0.toH1Function.toScalarL2) :=
    tendsto_iff_dist_tendsto_zero.mpr hscalarDist
  have hvalueL2 : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ v n x - w0.toH1Function.toFun x) 2
        (volume.restrict U)) atTop (nhds 0) := by
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (p := (2 : ENNReal)) (fi := atTop) v hvL2
      w0.toH1Function.toFun w0.toH1Function.memL2).mp (by
        simpa [w, H10Function.ofContDiff, H1Function.ofContDiff,
          H1Function.toScalarL2, toScalarL2] using hscalar)
    simpa only [Pi.sub_apply] using! ht
  let : IsFiniteMeasure (volume.restrict U) := by
    simpa using hU.isFiniteMeasure_restrict_volume
  have hvalueL1 : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ v n x - w0.toH1Function.toFun x) 1
        (volume.restrict U)) atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendsto_eLpNorm_two
      (fun n ↦ (hvL2 n).aestronglyMeasurable.sub
        w0.toH1Function.memL2.aestronglyMeasurable) hvalueL2
  have hvalueIntegralSq : Tendsto
      (fun n ↦ (∫⁻ x in U, ENNReal.ofReal |v n x - u x| ∂volume) ^ 2)
      atTop (nhds 0) := by
    exact tendsto_zero_of_le_of_tendsto_zero (fun n ↦ by
      unfold h1NormSqOnUnweighted
      exact le_add_of_nonneg_right (zero_le)) hunweighted
  have hvalueIntegral : Tendsto
      (fun n ↦ ∫⁻ x in U, ENNReal.ofReal |v n x - u x| ∂volume)
      atTop (nhds 0) := tendsto_self_of_tendsto_sq hvalueIntegralSq
  have hsourceL1 : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ v n x - u x) 1 (volume.restrict U))
      atTop (nhds 0) := by
    convert hvalueIntegral using 1
    funext n
    have hmeas : AEStronglyMeasurable (fun x ↦ v n x - u x) (volume.restrict U) :=
      (hvL2 n).aestronglyMeasurable.sub hpair.1
    rw [eLpNorm_one_eq_lintegral_enorm hmeas]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm]
    simp only [Real.norm_eq_abs]
  have hsum : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ v n x - w0.toH1Function.toFun x) 1
          (volume.restrict U) +
        eLpNorm (fun x ↦ v n x - u x) 1 (volume.restrict U))
      atTop (nhds 0) := by
    simpa using hvalueL1.add hsourceL1
  have hvalueZero : eLpNorm
      (fun x ↦ w0.toH1Function.toFun x - u x) 1 (volume.restrict U) = 0 := by
    apply le_antisymm ?_ (zero_le)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hsum (fun n ↦ by
      calc
        eLpNorm (fun x ↦ w0.toH1Function.toFun x - u x) 1
            (volume.restrict U) =
            eLpNorm ((fun x ↦ w0.toH1Function.toFun x - v n x) +
              (fun x ↦ v n x - u x)) 1 (volume.restrict U) := by
                congr 1
                funext x
                change w0.toH1Function.toFun x - u x =
                  (w0.toH1Function.toFun x - v n x) + (v n x - u x)
                ring
        _ ≤ eLpNorm (fun x ↦ w0.toH1Function.toFun x - v n x) 1
              (volume.restrict U) +
            eLpNorm (fun x ↦ v n x - u x) 1 (volume.restrict U) :=
          eLpNorm_add_le (by norm_num)
        _ = eLpNorm (fun x ↦ v n x - w0.toH1Function.toFun x) 1
              (volume.restrict U) +
            eLpNorm (fun x ↦ v n x - u x) 1 (volume.restrict U) := by
          congr 1
          simpa only [Pi.sub_apply] using!
            (eLpNorm_sub_comm w0.toH1Function.toFun (v n) 1
              (volume.restrict U)))
  have hvalueAE : w0.toH1Function.toFun =ᵐ[volume.restrict U] u := by
    have hzero := (eLpNorm_eq_zero_iff
      (by norm_num : (1 : ENNReal) ≠ 0)).mp hvalueZero
    filter_upwards [hzero] with x hx
    exact sub_eq_zero.mp hx
  have huL2 : MemScalarL2 U u :=
    w0.toH1Function.memL2.ae_eq hvalueAE
  have hDuL2 : ∀ i, MemScalarL2 U (fun x ↦ Du x i) := by
    intro i
    exact (w0.toH1Function.gradMemL2 i).ae_eq
      (hgradAE.mono fun x hx ↦ congrFun hx i)
  let u0 : H1Function U :=
    { toFun := u
      grad := Du
      memL2 := huL2
      gradMemL2 := hDuL2
      hasWeakGradient := hweak }
  let wExact : H10Function U :=
    { toH1Function := u0
      approx := w0.approx
      approx_smooth := w0.approx_smooth
      approx_hasCompactSupport := w0.approx_hasCompactSupport
      approx_support_subset := w0.approx_support_subset
      tendsto_approx := by
        have heq :
            (fun n ↦ eLpNorm (fun x ↦ w0.approx n x - u x) 2
              (volume.restrict U)) =
              fun n ↦ eLpNorm
                (fun x ↦ w0.approx n x - w0.toH1Function.toFun x) 2
                (volume.restrict U) := by
          funext n
          apply eLpNorm_congr_ae
          filter_upwards [hvalueAE] with x hx
          rw [hx]
        rw [heq]
        exact w0.tendsto_approx
      tendsto_approx_grad := fun i ↦ by
        change Tendsto
          (fun n ↦ eLpNorm
            (fun x ↦ smoothGrad (w0.approx n) x i - Du x i) 2
            (volume.restrict U)) atTop (nhds 0)
        have heq :
            (fun n ↦ eLpNorm (fun x ↦ smoothGrad (w0.approx n) x i - Du x i) 2
              (volume.restrict U)) =
              fun n ↦ eLpNorm
                (fun x ↦ smoothGrad (w0.approx n) x i -
                  w0.toH1Function.grad x i) 2 (volume.restrict U) := by
          funext n
          apply eLpNorm_congr_ae
          filter_upwards [hgradAE] with x hx
          rw [hx]
        rw [heq]
        exact w0.tendsto_approx_grad i }
  exact ⟨wExact, rfl, rfl⟩

end

end HighContrast
end HCPolySupport
