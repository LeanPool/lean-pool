/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainSubsolution
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.EllipticityWitness
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PotentialComparison

/-!
# PotentialDomainMonotonicity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Domain monotonicity for bounded nonnegative potentials

The ordinary part-domain truncation theorem applies after replacing a
potential bounded by `C` with an added shift `C` and the nonnegative forcing
`f + (C-q)u`.  This gives comparison of potential resolvents on nested open
bounded convex domains.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter
open scoped RealInnerProductSpace

variable {d : ℕ} {V U : Set (Vec d)}

private theorem potential_solution_h1_test (a : CoeffField d) (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hEll : IsEllipticFieldOn lam Lam V a) (q : Vec d → ℝ)
    (hq : IsBoundedNonnegativePotential V q C) (f : ScalarL2 V)
    (u : ZeroTraceSobolev V) (huSol : IsPotentialWeakSolution a α q V u f)
    (hf : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ f x)
    (hu : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ ZeroTraceSobolev.toL2 u x)
    (φ : H1Function V) (hφ : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ φ.toFun x) :
    α * inner ℝ (ZeroTraceSobolev.toL2 u) φ.toScalarL2 +
        coefficientPairing a V (ZeroTraceSobolev.gradient u)
          φ.gradToHilbertVectorL2 +
        ∫ x, q x * ZeroTraceSobolev.toL2 u x * φ.toScalarL2 x
          ∂volumeMeasureOn V ≤
      inner ℝ f φ.toScalarL2 := by
  let g : ScalarL2 V :=
    f + C • ZeroTraceSobolev.toL2 u -
      potentialMul q hq (ZeroTraceSobolev.toL2 u)
  have hg : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ g x := by
    filter_upwards [hf, hu, hq.2.2,
      Lp.coeFn_sub (f + C • ZeroTraceSobolev.toL2 u)
        (potentialMul q hq (ZeroTraceSobolev.toL2 u)),
      Lp.coeFn_add f (C • ZeroTraceSobolev.toL2 u),
      Lp.coeFn_smul C (ZeroTraceSobolev.toL2 u),
      potentialMul_coeFn q hq (ZeroTraceSobolev.toL2 u)]
      with x hfx hux hqC hsub hadd hsmul hpot
    rw [hsub, Pi.sub_apply, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
      smul_eq_mul, hpot]
    have hterm : 0 ≤ (C - q x) * ZeroTraceSobolev.toL2 u x :=
      mul_nonneg (sub_nonneg.mpr hqC) hux
    linarith only [hfx, hterm]
  have hshift : IsAlphaShiftedWeakSolution a V (α + C) g u := by
    intro ψ
    have hweak := huSol ψ
    unfold shiftedPotentialBilin at hweak
    dsimp only [g]
    rw [inner_sub_left, inner_add_left, real_inner_smul_left,
      inner_potentialMul_eq_integral]
    linarith only [hweak]
  have hαC : 0 < α + C := lt_of_lt_of_le hα (le_add_of_nonneg_right hC)
  have hcore := part_solution_test_inequality a hV hαC hlam hEll g u hshift
    hg hu φ hφ
  dsimp only [g] at hcore
  rw [inner_sub_left, inner_add_left, real_inner_smul_left,
    inner_potentialMul_eq_integral] at hcore
  linarith only [hcore]

/-- The zero extension of a part-domain potential resolvent is a potential
weak subsolution on the larger bounded convex domain. -/
theorem potentialPartDomainZeroExtension_isSubsolution
    (a : CoeffField d) (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hEll : IsEllipticFieldOn lam Lam U a) (q : Vec d → ℝ)
    (hqU : IsBoundedNonnegativePotential U q C) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    IsPotentialWeakSubsolution a α q U
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
        (potentialSolution a hα hlam
          (hEll.mono hV.isOpen.measurableSet hVU) q
          ⟨hqU.1, ae_restrict_of_ae_restrict_of_subset hVU hqU.2.1,
            ae_restrict_of_ae_restrict_of_subset hVU hqU.2.2⟩
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))) f := by
  classical
  let hEllV := hEll.mono hV.isOpen.measurableSet hVU
  let hqV : IsBoundedNonnegativePotential V q C :=
    ⟨hqU.1, ae_restrict_of_ae_restrict_of_subset hVU hqU.2.1,
      ae_restrict_of_ae_restrict_of_subset hVU hqU.2.2⟩
  let fV : ScalarL2 V := restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f
  let uV : ZeroTraceSobolev V := potentialSolution a hα hlam hEllV q hqV fV
  let uU : ZeroTraceSobolev U :=
    ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU uV
  have hfVspec : fV =ᵐ[volumeMeasureOn V] f := by
    simpa only [fV] using restrictScalarL2ToPart_coeFn
      hV.isOpen.measurableSet hU.isOpen.measurableSet hVU f
  have hfV : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ fV x := by
    filter_upwards [hfVspec, ae_restrict_of_ae_restrict_of_subset hVU hf]
      with x hfx hx
    rwa [hfx]
  have huV : ∀ᵐ x ∂volumeMeasureOn V,
      0 ≤ ZeroTraceSobolev.toL2 uV x := by
    simpa only [uV, potentialResolvent_apply] using
      potentialResolvent_nonneg_ae a hV hα hlam hEllV q hqV fV hfV
  have huVSol : IsPotentialWeakSolution a α q V uV fV := by
    simpa only [uV] using
      potentialSolution_isPotentialWeakSolution a hα hlam hEllV q hqV fV
  intro φ hφ
  let w : H10Function U := Classical.choose
    (ZeroTraceSobolev.exists_h10Function hU φ)
  have hw := Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hU φ)
  let φV : H1Function V := w.toH1Function.restrict hV.isOpen hVU
  have hwValueV := ae_restrict_of_ae_restrict_of_subset hVU
    w.toH1Function.coeFn_toScalarL2
  have hwGradientV := ae_restrict_of_ae_restrict_of_subset hVU
    w.toH1Function.coeFn_gradToHilbertVectorL2
  have hφVValue : φV.toScalarL2 =ᵐ[volumeMeasureOn V]
      ZeroTraceSobolev.toL2 φ := by
    filter_upwards [φV.coeFn_toScalarL2, hwValueV] with x h1 h2
    rw [h1]
    change w.toH1Function.toFun x = ZeroTraceSobolev.toL2 φ x
    rw [← h2]
    exact congrArg (fun z : ScalarL2 U ↦ z x) hw.1
  have hφVGradient : φV.gradToHilbertVectorL2 =ᵐ[volumeMeasureOn V]
      ZeroTraceSobolev.gradient φ := by
    filter_upwards [φV.coeFn_gradToHilbertVectorL2, hwGradientV]
      with x h1 h2
    rw [h1]
    change HilbertVec.ofVec (w.toH1Function.grad x) =
      ZeroTraceSobolev.gradient φ x
    have h2' : w.toH1Function.gradToHilbertVectorL2 x =
        HilbertVec.ofVec (w.toH1Function.grad x) := by
      simpa only [hilbertifyVecField] using h2
    rw [← h2']
    exact congrArg (fun z : HilbertVectorL2 U ↦ z x) hw.2
  have hφV : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ φV.toFun x := by
    filter_upwards [φV.coeFn_toScalarL2, hφVValue,
      ae_restrict_of_ae_restrict_of_subset hVU hφ] with x h1 h2 h3
    rw [← h1, h2]
    exact h3
  have hcore := potential_solution_h1_test a hV hα hlam hC hEllV q hqV
    fV uV huVSol hfV huV φV hφV
  have huUSpec := ZeroTraceSobolev.extendByZeroToPartSuperset_toL2
    hV hU.isOpen hVU uV
  have hgradUSpec := ZeroTraceSobolev.extendByZeroToPartSuperset_gradient
    hV hU.isOpen hVU uV
  have hmass := scalar_inner_zeroExtension_eq_restriction
    hV.isOpen.measurableSet hU.isOpen.measurableSet hVU
    (ZeroTraceSobolev.toL2 uU) (ZeroTraceSobolev.toL2 uV)
    (ZeroTraceSobolev.toL2 φ) φV.toScalarL2 huUSpec hφVValue
  have hcoeff := coefficientPairing_zeroExtension_eq_restriction a
    hV.isOpen.measurableSet hU.isOpen.measurableSet hVU
    (ZeroTraceSobolev.gradient uU) (ZeroTraceSobolev.gradient uV)
    (ZeroTraceSobolev.gradient φ) φV.gradToHilbertVectorL2
    hgradUSpec hφVGradient
  let quU := potentialMul q hqU (ZeroTraceSobolev.toL2 uU)
  let quV := potentialMul q hqV (ZeroTraceSobolev.toL2 uV)
  have hquVOnU : ∀ᵐ x ∂volumeMeasureOn U,
      x ∈ V → quV x = q x * ZeroTraceSobolev.toL2 uV x := by
    exact ae_restrict_of_ae
      (ae_restrict_iff' hV.isOpen.measurableSet |>.mp
        (potentialMul_coeFn q hqV (ZeroTraceSobolev.toL2 uV)))
  have hquUSpec : quU =ᵐ[volumeMeasureOn U] V.indicator fun x ↦ quV x := by
    filter_upwards [potentialMul_coeFn q hqU (ZeroTraceSobolev.toL2 uU),
      hquVOnU, huUSpec] with x hUq hVq hu
    rw [hUq, hu, Set.indicator_apply]
    by_cases hx : x ∈ V
    · rw [ite_eq_left hx, Set.indicator_of_mem hx, hVq hx]
    · rw [ite_eq_right hx, Set.indicator_of_notMem hx, mul_zero]
  have hpotential :
      (∫ x, q x * ZeroTraceSobolev.toL2 uU x *
          ZeroTraceSobolev.toL2 φ x ∂volumeMeasureOn U) =
        ∫ x, q x * ZeroTraceSobolev.toL2 uV x * φV.toScalarL2 x
          ∂volumeMeasureOn V := by
    rw [← inner_potentialMul_eq_integral q hqU,
      ← inner_potentialMul_eq_integral q hqV]
    exact scalar_inner_zeroExtension_eq_restriction
      hV.isOpen.measurableSet hU.isOpen.measurableSet hVU quU quV
      (ZeroTraceSobolev.toL2 φ) φV.toScalarL2 hquUSpec hφVValue
  have hforcing := scalar_inner_restriction_le hVU f fV
    (ZeroTraceSobolev.toL2 φ) φV.toScalarL2 hfVspec hφVValue hf hφ
  change shiftedPotentialBilin a α q U uU φ ≤
    inner ℝ f (ZeroTraceSobolev.toL2 φ)
  unfold shiftedPotentialBilin
  calc
    _ = α * inner ℝ (ZeroTraceSobolev.toL2 uV) φV.toScalarL2 +
          coefficientPairing a V (ZeroTraceSobolev.gradient uV)
            φV.gradToHilbertVectorL2 +
          ∫ x, q x * ZeroTraceSobolev.toL2 uV x * φV.toScalarL2 x
            ∂volumeMeasureOn V := by rw [hmass, hcoeff, hpotential]
    _ ≤ inner ℝ fV φV.toScalarL2 := hcore
    _ ≤ inner ℝ f (ZeroTraceSobolev.toL2 φ) := hforcing

/-- Potential Dirichlet resolvents increase under inclusion of bounded open
convex domains for nonnegative forcing. -/
theorem potentialPartDomainResolvent_le_ae (a : CoeffField d) (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hEll : IsEllipticFieldOn lam Lam U a) (q : Vec d → ℝ)
    (hqU : IsBoundedNonnegativePotential U q C) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn V,
      potentialResolvent a hα hlam (hEll.mono hV.isOpen.measurableSet hVU) q
          ⟨hqU.1, ae_restrict_of_ae_restrict_of_subset hVU hqU.2.1,
            ae_restrict_of_ae_restrict_of_subset hVU hqU.2.2⟩
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) x ≤
        potentialResolvent a hα hlam hEll q hqU f x := by
  let uV := potentialSolution a hα hlam
    (hEll.mono hV.isOpen.measurableSet hVU) q
    ⟨hqU.1, ae_restrict_of_ae_restrict_of_subset hVU hqU.2.1,
      ae_restrict_of_ae_restrict_of_subset hVU hqU.2.2⟩
    (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f)
  let uExt := ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU uV
  let uU := potentialSolution a hα hlam hEll q hqU f
  have hsub : IsPotentialWeakSubsolution a α q U uExt f := by
    simpa only [uExt, uV] using potentialPartDomainZeroExtension_isSubsolution
      a hV hU hVU hα hlam hC hEll q hqU f hf
  have hsup : IsPotentialWeakSupersolution a α q U uU f := by
    exact (potentialSolution_isPotentialWeakSolution a hα hlam hEll q hqU f).isSupersolution
  have hle := potentialWeakSubsolution_le_weakSupersolution_ae a hU hα hEll
    q hqU hsub hsup (Filter.Eventually.of_forall fun _ ↦ le_rfl)
  have hleV := ae_restrict_of_ae_restrict_of_subset hVU hle
  have hextV := ae_restrict_of_ae_restrict_of_subset hVU
    (ZeroTraceSobolev.extendByZeroToPartSuperset_toL2 hV hU.isOpen hVU uV)
  filter_upwards [hleV, hextV, self_mem_ae_restrict hV.isOpen.measurableSet]
    with x hx hext hxV
  change ZeroTraceSobolev.toL2 uV x ≤ ZeroTraceSobolev.toL2 uU x
  rw [← Set.indicator_of_mem (f := fun y ↦ ZeroTraceSobolev.toL2 uV y) hxV,
    ← hext]
  exact hx

/-- Potential domain monotonicity with independently supplied ellipticity and
potential-bound certificates on the two domains.  The weak equation, hence
the represented resolvent, is independent of those certificates. -/
theorem potentialPartDomainResolvent_le_ae_of_ellipticityWitness
    (a : CoeffField d) (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {alpha lamV LamV lamU LamU CV CU : ℝ} (halpha : 0 < alpha)
    (hlamV : 0 < lamV) (hlamU : 0 < lamU) (hCU : 0 ≤ CU)
    (hEllV : IsEllipticFieldOn lamV LamV V a)
    (hEllU : IsEllipticFieldOn lamU LamU U a) (q : Vec d → ℝ)
    (hqV : IsBoundedNonnegativePotential V q CV)
    (hqU : IsBoundedNonnegativePotential U q CU) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn V,
      potentialResolvent a halpha hlamV hEllV q hqV
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) x ≤
        potentialResolvent a halpha hlamU hEllU q hqU f x := by
  let hEllV' := hEllU.mono hV.isOpen.measurableSet hVU
  let hqV' : IsBoundedNonnegativePotential V q CU :=
    ⟨hqU.1, ae_restrict_of_ae_restrict_of_subset hVU hqU.2.1,
      ae_restrict_of_ae_restrict_of_subset hVU hqU.2.2⟩
  have hbase := potentialPartDomainResolvent_le_ae a hV hU hVU halpha
    hlamU hCU hEllU q hqU f hf
  have hwitness :
      potentialResolvent a halpha hlamV hEllV q hqV =
        potentialResolvent a halpha hlamU hEllV' q hqV' :=
    potentialResolvent_eq_of_ellipticityWitness a halpha hlamV hlamU
      hEllV hEllV' q hqV hqV'
  rw [hwitness]
  exact hbase

end DivergenceFormProcess.Form
