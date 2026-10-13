/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamMeanValueCubeSetAt
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamMeanValueIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CubeSetAtHarmonicDensity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartWholeHarmonic

/-!
# CubeSetAtMeanValueStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exit mean-value property on a translated triadic cube for the stream field

`CubeSetAtMeanValueConsumer.lean` carries a global small-contrast datum, because the exit
decomposition it invokes does.  The stream field of the model supplies no such datum, and the
coefficient-generic `C₀` barrier comparison replaces it.  This file is the small-contrast-free
copy of that chain on `cubeSetAt y n`: the same statements, with the small-contrast datum removed
from every hypothesis list and the analytic data fixed to the stream field of the model.

The analytic half — the Green potential of the cube, the harmonic part, and its `H¹` packaging —
carries no process hypothesis at all and is shared verbatim with the small-contrast route; only
the four process statements and the two consumer lemmas are repeated here.

The assumptions are those of the coefficient-generic comparison: the resolvent carrying the
process, its one-point regularity data, conservativity of the live kernel semigroup, the
bounded-measurable identification of the kernel resolvent with the analytic minimal resolvent,
and the operator identification against the `C₀` barrier resolvent of the stream field.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : (streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
  (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
    R.toContractiveResolvent.operator mu g =
      ((streamWholeSpaceC0BarrierData M omega).resolvent).toContractiveResolvent.operator mu g)

include hcons hid hT in
/-- **The harmonic part of a resolvent datum on a translated triadic cube is represented by the
exit distribution, for the stream field.** -/
theorem hasExitMeanValueOn_cubeSetAtHarmonicPart_stream (y : Vec d) (n : ℤ)
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (hg0 : ∀ z, 0 ≤ g z) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension ((streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n
        mu g)) :=
  hasExitMeanValueOn_of_isCubeSetAtResolventHarmonicPart_stream R hreg hcons hid hT y n mu g hg0
    ((streamWholeSpaceAnalyticData M omega).isCubeSetAtResolventHarmonicPart_cubeSetAtHarmonicPart
      R y n mu g)
    (fun _ hz ↦ expectedExitTime_cubeSetAt_ne_top_stream R hreg hcons hid hT y n hz)

include hcons hid hT in
/-- **A difference of harmonic parts on a translated triadic cube is represented by the exit
distribution, for the stream field.** -/
theorem hasExitMeanValueOn_cubeSetAtHarmonicPart_sub_stream (y : Vec d) (n : ℤ)
    (mu : PositiveShift) (g₁ g₂ : C₀(Vec d, ℝ)) (hg₁ : ∀ z, 0 ≤ g₁ z) (hg₂ : ∀ z, 0 ≤ g₂ z) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension fun z ↦
        (streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n mu g₁ z -
          (streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n mu g₂ z) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  set A := streamWholeSpaceAnalyticData M omega with hA
  have h₁ := hasExitMeanValueOn_cubeSetAtHarmonicPart_stream R hreg hcons hid hT y n mu g₁ hg₁
  have h₂ := hasExitMeanValueOn_cubeSetAtHarmonicPart_stream R hreg hcons hid hT y n mu g₂ hg₂
  have hb₁ : ∀ w : OnePoint (Vec d),
      ‖onePointRealExtension (A.cubeSetAtHarmonicPart R y n mu g₁) w‖ ≤
        A.cubeSetAtHarmonicPartBound R y n mu g₁ := by
    intro w
    rw [Real.norm_eq_abs]
    exact abs_onePointRealExtension_le (A.cubeSetAtHarmonicPartBound_nonneg R y n mu g₁)
      (A.abs_cubeSetAtHarmonicPart_le' R y n mu g₁) w
  have hb₂ : ∀ w : OnePoint (Vec d),
      ‖onePointRealExtension (A.cubeSetAtHarmonicPart R y n mu g₂) w‖ ≤
        A.cubeSetAtHarmonicPartBound R y n mu g₂ := by
    intro w
    rw [Real.norm_eq_abs]
    exact abs_onePointRealExtension_le (A.cubeSetAtHarmonicPartBound_nonneg R y n mu g₂)
      (A.abs_cubeSetAtHarmonicPart_le' R y n mu g₂) w
  have hkey := hasExitMeanValueOn_sub R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup
    (OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n))
    (measurable_onePointRealExtension (A.measurable_cubeSetAtHarmonicPart R y n mu g₁))
    (measurable_onePointRealExtension (A.measurable_cubeSetAtHarmonicPart R y n mu g₂))
    hb₁ hb₂ h₁ h₂
  have hshape : onePointRealExtension (fun z ↦ A.cubeSetAtHarmonicPart R y n mu g₁ z -
        A.cubeSetAtHarmonicPart R y n mu g₂ z) =
      fun w ↦ onePointRealExtension (A.cubeSetAtHarmonicPart R y n mu g₁) w -
        onePointRealExtension (A.cubeSetAtHarmonicPart R y n mu g₂) w := by
    funext w
    induction w using OnePoint.rec with
    | infty =>
      rw [onePointRealExtension_infty, onePointRealExtension_infty,
        onePointRealExtension_infty, sub_zero]
    | coe z =>
      rw [onePointRealExtension_coe, onePointRealExtension_coe, onePointRealExtension_coe]
  rw [hshape]
  exact hkey

include hcons hid hT in
/-- **A uniform limit of differences of harmonic parts on a translated triadic cube is
represented by the exit distribution, for the stream field.** -/
theorem hasExitMeanValueOn_onePointRealExtension_of_forall_approx_harmonicPart_cubeSetAt_stream
    (y : Vec d) (n : ℤ) {h : Vec d → ℝ} (hh : Measurable h) {N : ℝ} (hN : ∀ z, |h z| ≤ N)
    (happrox : ∀ eps > (0 : ℝ), ∃ mu : PositiveShift, ∃ g₁ g₂ : C₀(Vec d, ℝ),
      (∀ z, 0 ≤ g₁ z) ∧ (∀ z, 0 ≤ g₂ z) ∧
        ∀ z, |(streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n mu g₁ z -
          (streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n mu g₂ z -
            h z| ≤ eps) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension h) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  set A := streamWholeSpaceAnalyticData M omega with hA
  refine hasExitMeanValueOn_onePointRealExtension_of_forall_approx_cubeSetAt R hreg y n hh hN
    fun eps heps ↦ ?_
  obtain ⟨mu, g₁, g₂, hg₁, hg₂, hclose⟩ := happrox eps heps
  have hharm := hasExitMeanValueOn_cubeSetAtHarmonicPart_sub_stream R hreg hcons hid hT y n mu
    g₁ g₂ hg₁ hg₂
  refine ⟨fun z ↦ A.cubeSetAtHarmonicPart R y n mu g₁ z - A.cubeSetAtHarmonicPart R y n mu g₂ z,
    (A.measurable_cubeSetAtHarmonicPart R y n mu g₁).sub
      (A.measurable_cubeSetAtHarmonicPart R y n mu g₂),
    ⟨A.cubeSetAtHarmonicPartBound R y n mu g₁ + A.cubeSetAtHarmonicPartBound R y n mu g₂,
      fun z ↦ ?_⟩, hharm, hclose⟩
  exact (abs_sub _ _).trans (add_le_add (A.abs_cubeSetAtHarmonicPart_le' R y n mu g₁ z)
    (A.abs_cubeSetAtHarmonicPart_le' R y n mu g₂ z))

include hT in
/-- **The harmonic part of a stream resolvent datum on a translated triadic cube is the
whole-space harmonic part of that datum there.** -/
theorem cubeSetAtHarmonicPart_eq_partWholeSpaceHarmonicPart_stream (y : Vec d) (n : ℤ)
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (z : Vec d) :
    (streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n mu g z =
      (streamWholeSpaceAnalyticData M omega).partWholeSpaceHarmonicPart
        (isOpenBoundedConvexDomain_cubeSetAt y n) mu g.continuous.measurable (norm_nonneg g)
        (abs_apply_le_norm_zeroAtInfty g) z := by
  set A := streamWholeSpaceAnalyticData M omega with hA
  have heqOn : Set.EqOn (cubeSetAtResolventResidual R y n mu g)
      (A.wholeSpaceResidual mu g.continuous.measurable (abs_apply_le_norm_zeroAtInfty g))
      (cubeSetAt y n) := by
    intro w hw
    change cubeSetAtC0Datum y n g w -
      (mu : ℝ) * cubeSetAtC0Datum y n (R.toContractiveResolvent.operator mu g) w = _
    rw [cubeSetAtC0Datum_of_mem g hw, cubeSetAtC0Datum_of_mem _ hw]
    show g w - (mu : ℝ) * R.toContractiveResolvent.operator mu g w = _
    rw [operator_eq_analyticMinimalResolventReal_stream R hT mu g w]
    rfl
  rw [cubeSetAtHarmonicPart, partWholeSpaceHarmonicPart,
    operator_eq_analyticMinimalResolventReal_stream R hT mu g z,
    A.partGreenPotential_eq_of_eqOn (isOpenBoundedConvexDomain_cubeSetAt y n)
      (measurable_cubeSetAtResolventResidual R y n mu g)
      (A.measurable_wholeSpaceResidual mu g.continuous.measurable
        (abs_apply_le_norm_zeroAtInfty g))
      (cubeResolventResidualBound_nonneg R mu g)
      (cubeLevelResidualBound_nonneg (norm_nonneg g))
      (abs_cubeSetAtResolventResidual_le R y n mu g)
      (A.abs_wholeSpaceResidual_le mu g.continuous.measurable
        (abs_apply_le_norm_zeroAtInfty g)) heqOn z]
  rfl

include hT in
/-- **The `H¹` package of a harmonic part on a translated triadic cube, for the stream
field.** -/
theorem exists_h1Function_cubeSetAtHarmonicPart_stream (y : Vec d) (n : ℤ)
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) :
    ∃ z h : H1Function (cubeSetAt y n),
      (∀ w, z.toFun w = R.toContractiveResolvent.operator mu g w) ∧
        (∀ w, h.toFun w = (streamWholeSpaceAnalyticData M omega).cubeSetAtHarmonicPart R y n mu g
          w) ∧
          IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a (cubeSetAt y n)
              (fun _ ↦ (0 : ℝ)) h ∧
            MemH10 (cubeSetAt y n) fun w ↦ z.toFun w - h.toFun w := by
  set A := streamWholeSpaceAnalyticData M omega with hA
  obtain ⟨z, hzval, hzsol⟩ := A.exists_h1Function_analyticMinimalResolventReal_part
    (isOpenBoundedConvexDomain_cubeSetAt y n) mu g.continuous.measurable (norm_nonneg g)
    (abs_apply_le_norm_zeroAtInfty g)
  obtain ⟨h, hhval, hhsol, hdiff⟩ := A.exists_h1Function_partWholeSpaceHarmonicPart
    (isOpenBoundedConvexDomain_cubeSetAt y n) mu g.continuous.measurable (norm_nonneg g)
    (abs_apply_le_norm_zeroAtInfty g)
  refine ⟨z, h, fun w ↦ ?_, fun w ↦ ?_, hhsol, ?_⟩
  · rw [hzval, operator_eq_analyticMinimalResolventReal_stream R hT mu g w]
    rfl
  · rw [hhval, cubeSetAtHarmonicPart_eq_partWholeSpaceHarmonicPart_stream R hT y n mu g w]
  · have hshape : (fun w ↦ z.toFun w - h.toFun w) =
        (A.partGreenH10 (isOpenBoundedConvexDomain_cubeSetAt y n)
          (A.measurable_wholeSpaceResidual mu g.continuous.measurable
            (abs_apply_le_norm_zeroAtInfty g))
          (cubeLevelResidualBound_nonneg (norm_nonneg g))
          (A.abs_wholeSpaceResidual_le mu g.continuous.measurable
            (abs_apply_le_norm_zeroAtInfty g))).toH1Function.toFun := by
      funext w
      rw [hzval]
      exact hdiff w
    rw [hshape]
    exact ⟨_, rfl⟩

include hcons hid hT in
/-- **A weakly `a`-harmonic function on a translated triadic cube with a continuous boundary
datum vanishing at infinity has the exit mean-value property, for the stream field.** -/
theorem hasExitMeanValueOn_onePointRealExtension_of_isWeaklyHarmonicOn_cubeSetAt_stream
    (y : Vec d) (n : ℤ) (F : C₀(Vec d, ℝ)) (Phi : H1Function (cubeSetAt y n))
    (hPhi : ∀ w, Phi.toFun w = F w)
    {u : Vec d → ℝ} (hu : Measurable u) {N : ℝ} (hN : ∀ w, |u w| ≤ N)
    (hoff : ∀ w, w ∉ cubeSetAt y n → u w = F w)
    (hucont : ContinuousOn u (cubeSetAt y n))
    (Y : H1Function (cubeSetAt y n)) (hY : ∀ w, Y.toFun w = u w)
    (hharm : IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a
      (cubeSetAt y n) (fun _ ↦ (0 : ℝ)) Y)
    (htrace : MemH10 (cubeSetAt y n) fun w ↦ Y.toFun w - Phi.toFun w) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension u) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  set A := streamWholeSpaceAnalyticData M omega with hA
  refine hasExitMeanValueOn_onePointRealExtension_of_forall_approx_harmonicPart_cubeSetAt_stream
    R hreg hcons hid hT y n hu hN fun eps heps ↦ ?_
  set mu : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩ with hmu
  obtain ⟨g₁, g₂, hg₁, hg₂, happ⟩ := exists_nonneg_c0_resolvent_approx R mu F heps
  refine ⟨mu, g₁, g₂, hg₁, hg₂, fun w ↦ ?_⟩
  obtain ⟨z₁, h₁, hz₁, hh₁, hharm₁, htr₁⟩ :=
    exists_h1Function_cubeSetAtHarmonicPart_stream R hT y n mu g₁
  obtain ⟨z₂, h₂, hz₂, hh₂, hharm₂, htr₂⟩ :=
    exists_h1Function_cubeSetAtHarmonicPart_stream R hT y n mu g₂
  by_cases hw : w ∈ cubeSetAt y n
  · have hVdom := isOpenBoundedConvexDomain_cubeSetAt y n
    have hEll := partEllipticity A hVdom
    have hYdifffun : ∀ v, ((h₁ - h₂) - Y).toFun v =
        A.cubeSetAtHarmonicPart R y n mu g₁ v - A.cubeSetAtHarmonicPart R y n mu g₂ v - u v := by
      intro v
      simp only [hA, H1Function.sub_toFun, hh₁, hh₂, hY]
    have hqfun : ∀ v, ((z₁ - z₂) - Phi).toFun v =
        R.toContractiveResolvent.operator mu g₁ v -
          R.toContractiveResolvent.operator mu g₂ v - F v := by
      intro v
      simp only [H1Function.sub_toFun, hz₁, hz₂, hPhi]
    have hqbound : ∀ v, |((z₁ - z₂) - Phi).toFun v| ≤ eps := by
      intro v
      rw [hqfun v]
      exact happ v
    have hYharm : IsScalarForcedWeakSolution A.a (cubeSetAt y n) (fun _ ↦ (0 : ℝ))
        ((h₁ - h₂) - Y) := by
      have hstep := ((hharm₁.sub hEll hharm₂).sub hEll hharm)
      refine hstep.congr_datum ?_
      filter_upwards with v
      show (0 : ℝ) = 0 - 0 - 0
      ring
    have hmem : MemH10 (cubeSetAt y n) fun v ↦
        ((h₁ - h₂) - Y).toFun v - ((z₁ - z₂) - Phi).toFun v := by
      have hshape : (fun v ↦ ((h₁ - h₂) - Y).toFun v - ((z₁ - z₂) - Phi).toFun v) =
          fun v ↦ (-(z₁.toFun v - h₁.toFun v) + (z₂.toFun v - h₂.toFun v)) -
            (Y.toFun v - Phi.toFun v) := by
        funext v
        simp only [H1Function.sub_toFun]
        ring
      rw [hshape]
      exact memH10_sub (memH10_add (memH10_neg htr₁) htr₂) htrace
    have hae := ae_abs_le_of_isScalarForcedWeakSolution_zero hVdom A.hnu hEll hYharm hmem
      hqbound
    have hcont : ContinuousOn (fun v ↦ |((h₁ - h₂) - Y).toFun v|) (cubeSetAt y n) := by
      have hbase : ContinuousOn (fun v ↦ A.cubeSetAtHarmonicPart R y n mu g₁ v -
          A.cubeSetAtHarmonicPart R y n mu g₂ v - u v) (cubeSetAt y n) :=
        ((A.continuousOn_cubeSetAtHarmonicPart R y n mu g₁).sub
          (A.continuousOn_cubeSetAtHarmonicPart R y n mu g₂)).sub hucont
      exact (hbase.congr fun v _ ↦ hYdifffun v).abs
    have hpt := le_of_ae_le_of_continuousOn hVdom.isOpen hcont continuousOn_const hae w hw
    rw [← hYdifffun w]
    exact hpt
  · rw [A.cubeSetAtHarmonicPart_of_notMem R y n mu g₁ hw,
      A.cubeSetAtHarmonicPart_of_notMem R y n mu g₂ hw, hoff w hw]
    exact happ w

include hcons hid hT in
/-- **The instantiation shape on a translated triadic cube, for the stream field.**  When the
boundary datum is a smooth compactly supported function `b`, the continuous datum vanishing at
infinity and its `H¹` realization on the cube are both supplied by `b` itself, and the only
inputs left are the weak harmonicity of the observable inside the cube, its continuity there,
its agreement with `b` outside, and its trace. -/
theorem hasExitMeanValueOn_onePointRealExtension_of_contDiffBoundaryDatum_cubeSetAt_stream
    (y : Vec d) (n : ℤ) {b : Vec d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b)
    {u : Vec d → ℝ} (hu : Measurable u) {N : ℝ} (hN : ∀ w, |u w| ≤ N)
    (hoff : ∀ w, w ∉ cubeSetAt y n → u w = b w)
    (hucont : ContinuousOn u (cubeSetAt y n))
    (Y : H1Function (cubeSetAt y n)) (hY : ∀ w, Y.toFun w = u w)
    (hharm : IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a
      (cubeSetAt y n) (fun _ ↦ (0 : ℝ)) Y)
    (htrace : MemH10 (cubeSetAt y n) fun w ↦ u w - b w) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension u) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  set F : C₀(Vec d, ℝ) := ⟨⟨b, hb.continuous⟩, hbCompact.is_zero_at_infty⟩ with hF
  set Phi : H1Function (cubeSetAt y n) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_cubeSetAt y n) (hb.of_le (by norm_num)) with hPhidef
  have hPhi : ∀ w, Phi.toFun w = F w := fun _ ↦ rfl
  have htrace' : MemH10 (cubeSetAt y n) fun w ↦ Y.toFun w - Phi.toFun w := by
    have hshape : (fun w ↦ Y.toFun w - Phi.toFun w) = fun w ↦ u w - b w := by
      funext w
      rw [hY w]
      rfl
    rw [hshape]
    exact htrace
  exact hasExitMeanValueOn_onePointRealExtension_of_isWeaklyHarmonicOn_cubeSetAt_stream R hreg
    hcons hid hT y n F Phi hPhi hu hN hoff hucont Y hY hharm htrace'

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
