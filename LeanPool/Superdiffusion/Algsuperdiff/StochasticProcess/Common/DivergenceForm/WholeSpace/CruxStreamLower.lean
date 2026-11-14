/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxLowerProcess
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamBarrier

/-!
# CruxStreamLower

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# S-free lower process comparison

The excessive-barrier stopping argument is repeated with
`WholeSpaceC0BarrierData` in place of global small contrast.  Its explicit
inputs are vanishing and dense range for the analytic minimal `C₀` resolver,
compact-data vanishing for the barrier, the ordinary axis-cube barrier data
with its continuity witnesses, kernel identification, and the `C₀` operator
identification.  No global coefficient-contrast hypothesis is used.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d}

namespace WholeSpaceBarrierData

variable (P : WholeSpaceBarrierData A)

private theorem frontier_image_coe_subset_image_frontier_cruxStream :
    frontier (((↑) : Vec d → OnePoint (Vec d)) '' P.V) ⊆
      ((↑) : Vec d → OnePoint (Vec d)) '' frontier P.V := by
  intro z hz
  have hcompact : IsCompact (closure P.V) :=
    P.hV.isBoundedDomain.isBounded.isCompact_closure
  have hclosed : IsClosed (((↑) : Vec d → OnePoint (Vec d)) '' closure P.V) :=
    OnePoint.isClosed_image_coe.mpr ⟨isClosed_closure, hcompact⟩
  have hzclosure : z ∈ closure (((↑) : Vec d → OnePoint (Vec d)) '' P.V) :=
    frontier_subset_closure hz
  have hzlarge : z ∈ ((↑) : Vec d → OnePoint (Vec d)) '' closure P.V :=
    closure_minimal (Set.image_mono subset_closure) hclosed hzclosure
  obtain ⟨y, hy, rfl⟩ := hzlarge
  refine ⟨y, ?_, rfl⟩
  have hy' : y ∈ ((↑) : Vec d → OnePoint (Vec d)) ⁻¹'
      frontier (((↑) : Vec d → OnePoint (Vec d)) '' P.V) := hz
  rw [OnePoint.isOpenMap_coe.preimage_frontier_eq_frontier_preimage
    OnePoint.continuous_coe, Set.preimage_image_eq _ OnePoint.coe_injective] at hy'
  exact hy'

private theorem kernelResolvent_eq_analyticMinimal_cruxStream
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (x : Vec d) :
    R.kernelSemigroup.kernelResolvent (P.lam : ℝ)
        (fun y ↦ ENNReal.ofReal (P.f y)) x =
      A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x := by
  let C : ℝ := max P.D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let g : Vec d → ℝ := fun y ↦ C⁻¹ * P.f y
  have hg : Measurable g := P.hf.const_smul C⁻¹
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦
    mul_nonneg (inv_nonneg.mpr hC.le) (P.hf0 y)
  have hDle : P.D ≤ C := le_max_left _ _
  have hg1 : ∀ y, |g y| ≤ 1 := by
    intro y
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hC.le)]
    calc
      C⁻¹ * |P.f y| ≤ C⁻¹ * P.D :=
        mul_le_mul_of_nonneg_left (P.hfD y) (inv_nonneg.mpr hC.le)
      _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hDle (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hkernel := hid P.lam hg hg0 hg1 x
  have hkernel' : R.kernelSemigroup.kernelResolvent (P.lam : ℝ)
      (ENNReal.ofReal ∘ g) x =
        A.analyticMinimalResolvent P.lam g hg hg1 x := hkernel
  have hfscale : (fun y ↦ ENNReal.ofReal C * ENNReal.ofReal (g y)) =
      fun y ↦ ENNReal.ofReal (P.f y) := by
    funext y
    rw [← ENNReal.ofReal_mul hC.le]
    dsimp only [g]
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
  rw [← hfscale]
  have hhom := R.kernelSemigroup.kernelResolvent_const_mul (P.lam : ℝ)
    (ENNReal.ofReal C) (ENNReal.measurable_ofReal.comp hg) x
  change R.kernelSemigroup.kernelResolvent (P.lam : ℝ)
      (fun y ↦ ENNReal.ofReal C * (ENNReal.ofReal ∘ g) y) x = _
  rw [hhom, hkernel']
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (A.analyticMinimalResolvent_ne_top P.lam hg hg0 (by norm_num) hg1 x))
    (A.analyticMinimalResolvent_ne_top P.lam P.hf P.hf0
      ((abs_nonneg (P.f 0)).trans (P.hfD 0)) P.hfD x)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
  have hscaled := A.toReal_analyticMinimalResolvent_smul P.lam hC.le hg hg0
    (by norm_num) hg1 x
  rw [← hscaled]
  apply congrArg ENNReal.toReal
  apply A.analyticMinimalResolvent_congr_ae P.lam (hg.const_smul C) P.hf
    (fun y ↦ by
      change |C * g y| ≤ C * 1
      rw [abs_mul, abs_of_nonneg hC.le]
      exact mul_le_mul_of_nonneg_left (hg1 y) hC.le)
    P.hfD
  exact Filter.Eventually.of_forall fun y ↦ by
    change C * (C⁻¹ * P.f y) = P.f y
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]

/-- **S-free lower process comparison.**  The process killed on leaving the
compactified part domain dominates the continuous part-resolvent
representative.  All coefficient-dependent `C₀` inputs are carried by `B`;
the general global-small-contrast case is not asserted. -/
theorem killedResolvent_ge_partResolvent_wholeSpace_of_c0Barrier
    (B : WholeSpaceC0BarrierData A)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        A.analyticMinimalC0ResolventOfVanishing B.vanishing mu g)
    {x : Vec d} (hx : x ∈ P.V) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ENNReal.ofReal (P.utilde x) ≤
      IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y ↦ ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) := by
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  let K := R.onePointKernelSemigroup
  let hKcons := R.isConservative_onePointKernelSemigroup
  let U : Set (OnePoint (Vec d)) := ((↑) : Vec d → OnePoint (Vec d)) '' P.V
  have hU : IsOpen U := OnePoint.isOpen_image_coe.mpr P.hV.isOpen
  let F : OnePoint (Vec d) → ℝ≥0∞ :=
    PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun y ↦ ENNReal.ofReal (P.f y))
  have hF : Measurable F :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension
      (ENNReal.measurable_ofReal.comp P.hf)
  have hFeller := R.isFellerKernelSemigroup_onePointKernelSemigroup
  have hKol := hreg.kolmogorovRegular
  have hpath (z : OnePoint (Vec d)) :
      (∫⁻ omega, ContinuousPath.pathResolvent (P.lam : ℝ) F omega
          ∂IsConservative.continuousProcess K hKcons z) =
        K.kernelResolvent (P.lam : ℝ) F z := by
    calc
      _ = IsConservative.killedResolvent K hKcons Set.univ isOpen_univ
          (P.lam : ℝ) F z :=
        IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ
          K hKcons (P.lam : ℝ) hF z
      _ = K.kernelResolvent (P.lam : ℝ) F z :=
        (hFeller.kernelResolvent_eq_killedResolvent_univ K hKcons hKol
          (P.lam : ℝ) hF z).symm
  have hdecomp := hFeller.lintegral_pathResolvent_eq_killedResolvent_add
    K hKcons hKol U hU (P.lam : ℝ) hF (x : OnePoint (Vec d))
  rw [hpath] at hdecomp
  simp_rw [hpath] at hdecomp
  have hrestart :
      (∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
            (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal)) *
          K.kernelResolvent (P.lam : ℝ) F
            (omega ((ContinuousPath.exitTime U omega).untopD 0))) omega
        ∂IsConservative.continuousProcess K hKcons (x : OnePoint (Vec d))) =
      ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal) *
            PositiveC0ContractiveResolvent.onePointAssemble
              (P.barrierC0OfData B) 0
              (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
        ∂IsConservative.continuousProcess K hKcons (x : OnePoint (Vec d)) := by
    apply lintegral_congr_ae
    filter_upwards [IsConservative.ae_eval_zero_eq hKcons hKol
      (x : OnePoint (Vec d))] with omega hzero
    by_cases hfin : ContinuousPath.exitTime U omega < ⊤
    · have hmem : omega ∈ {omega | ContinuousPath.exitTime U omega < ⊤} := hfin
      have hind₁ := Set.indicator_of_mem hmem
        (fun omega ↦ ENNReal.ofReal
            (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal)) *
          K.kernelResolvent (P.lam : ℝ) F
            (omega ((ContinuousPath.exitTime U omega).untopD 0)))
      have hind₂ := Set.indicator_of_mem hmem
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal) *
            PositiveC0ContractiveResolvent.onePointAssemble
              (P.barrierC0OfData B) 0
              (omega ((ContinuousPath.exitTime U omega).untopD 0))))
      refine hind₁.trans (Eq.trans ?_ hind₂.symm)
      have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU omega
        (hzero ▸ ⟨x, hx, rfl⟩) (ne_top_of_lt hfin)
      obtain ⟨y, hy, heq⟩ :=
        P.frontier_image_coe_subset_image_frontier_cruxStream hfront
      rw [ContinuousPath.untopD_exitTime, ← heq]
      have hyV : y ∉ P.V := by
        rw [frontier, P.hV.isOpen.interior_eq] at hy
        exact hy.2
      have hu : P.utilde y = 0 := P.hutildeOff y hyV
      change ENNReal.ofReal
          (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal)) *
            R.onePointKernelSemigroup.kernelResolvent (P.lam : ℝ)
              (PositiveC0ContractiveResolvent.onePointLiveExtension
                (fun z ↦ ENNReal.ofReal (P.f z))) (y : OnePoint (Vec d)) = _
      have hlive := onePointKernelResolvent_liveExtension_eq R (P.lam : ℝ)
        (f := fun z ↦ ENNReal.ofReal (P.f z))
        (ENNReal.measurable_ofReal.comp P.hf) y
      rw [hlive, P.kernelResolvent_eq_analyticMinimal_cruxStream R hid y,
        PositiveC0ContractiveResolvent.onePointAssemble_coe,
        P.barrierC0OfData_apply B, WholeSpaceBarrierData.barrier, hu, sub_zero,
        ← ENNReal.ofReal_toReal
          (A.analyticMinimalResolvent_ne_top P.lam P.hf P.hf0
            ((abs_nonneg (P.f 0)).trans (P.hfD 0)) P.hfD y),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ENNReal.toReal_ofReal ENNReal.toReal_nonneg, add_zero]
    · have hnmem : omega ∉ {omega | ContinuousPath.exitTime U omega < ⊤} := hfin
      have hind₁ := Set.indicator_of_notMem hnmem
        (fun omega ↦ ENNReal.ofReal
            (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal)) *
          K.kernelResolvent (P.lam : ℝ) F
            (omega ((ContinuousPath.exitTime U omega).untopD 0)))
      have hind₂ := Set.indicator_of_notMem hnmem
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal) *
            PositiveC0ContractiveResolvent.onePointAssemble
              (P.barrierC0OfData B) 0
              (omega ((ContinuousPath.exitTime U omega).untopD 0))))
      exact hind₁.trans hind₂.symm
  replace hdecomp := hdecomp.trans (congrArg (HAdd.hAdd _) hrestart)
  have hexcessive :=
    P.isLambdaExcessive_onePointAssemble_barrierC0OfData B R hT
  have hstop := hexcessive.lintegral_ofReal_discountedValue_exitTime_le
    hKcons hFeller hKol U hU (x : OnePoint (Vec d))
  have hambient : K.kernelResolvent (P.lam : ℝ) F (x : OnePoint (Vec d)) =
      A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x := by
    change R.onePointKernelSemigroup.kernelResolvent (P.lam : ℝ)
      (PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y ↦ ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) = _
    exact (onePointKernelResolvent_liveExtension_eq R (P.lam : ℝ)
      (ENNReal.measurable_ofReal.comp P.hf) x).trans
        (P.kernelResolvent_eq_analyticMinimal_cruxStream R hid x)
  let killed := IsConservative.killedResolvent K hKcons U hU
    (P.lam : ℝ) F (x : OnePoint (Vec d))
  let restart := ∫⁻ omega,
    ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
      (fun omega ↦ ENNReal.ofReal
        (Real.exp (-(P.lam : ℝ) * (ContinuousPath.exitTime U omega).toReal) *
          PositiveC0ContractiveResolvent.onePointAssemble
            (P.barrierC0OfData B) 0
            (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
      ∂IsConservative.continuousProcess K hKcons (x : OnePoint (Vec d))
  have hambFin : A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x ≠ ⊤ :=
    A.analyticMinimalResolvent_ne_top P.lam P.hf P.hf0
      ((abs_nonneg (P.f 0)).trans (P.hfD 0)) P.hfD x
  have hsum : A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x =
      killed + restart := by
    simpa only [K, F, U, killed, restart, hambient] using hdecomp
  have hfins : killed ≠ ⊤ ∧ restart ≠ ⊤ :=
    ENNReal.add_ne_top.mp (hsum ▸ hambFin)
  have hrestartReal : restart.toReal ≤ P.barrierC0OfData B x := by
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstop
    have hrhs : (ENNReal.ofReal (PositiveC0ContractiveResolvent.onePointAssemble
        (P.barrierC0OfData B) 0 (x : OnePoint (Vec d)))).toReal =
          P.barrierC0OfData B x := by
      have h0 : PositiveC0ContractiveResolvent.onePointAssemble
          (P.barrierC0OfData B) 0 (x : OnePoint (Vec d)) =
            P.barrierC0OfData B x + 0 := rfl
      rw [h0, add_zero, ENNReal.toReal_ofReal (P.barrierC0OfData_nonneg B x)]
    exact le_trans hreal (le_of_eq hrhs)
  have hrealSum :
      (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal =
        killed.toReal + restart.toReal := by
    rw [hsum, ENNReal.toReal_add hfins.1 hfins.2]
  have hbarrier : P.barrierC0OfData B x =
      (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal -
        P.utilde x := rfl
  apply (ENNReal.ofReal_le_iff_le_toReal hfins.1).2
  rw [hbarrier] at hrestartReal
  linarith only [hrealSum, hrestartReal]

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
