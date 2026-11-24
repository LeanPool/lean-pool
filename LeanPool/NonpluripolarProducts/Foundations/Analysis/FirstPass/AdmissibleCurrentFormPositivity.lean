/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothThetaCriterion
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothOffPole

/-!
# Pointwise positivity of admissible currents off their poles

Source: Copy-4, `eq:def-restricted-volume` (`transcendental-nakamaye-copy4-20260911`);
CT22, Section 2.

Let `T + εω = θ + εω + ddᶜu` come from an admissible presentation.  Off the pole
set, `u` is locally `c log Σ|fⱼ|² + b` with `Σ|fⱼ|² > 0` and `b` smooth, hence a
smooth real function, and the coordinate two-form
`NumericalRestrictedVolume.coordinateCurrentForm` is the genuine smooth form
`θ + εω + ddᶜu`.  This file shows that it is of type `(1,1)` and semipositive
there, which is what makes the top-power densities in restricted volumes
comparable.

* `coefficientSemipositive_add_smoothDDC_of_thetaPlurisubharmonic`: pointwise
  semipositivity of `θ + ddᶜu` at a point near which a `θ`-PSH `u` is smooth.
* `coordinateCurrentForm_isOneOne`, `coordinateCurrentForm_semipositive`.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity

noncomputable section

open PositiveClasses NumericalRestrictedVolumeScaffold NumericalRestrictedVolume

variable {n : ℕ}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Off its poles, `θ + ddᶜu` is a semipositive `(1,1)`-form** for a `θ`-PSH
potential with smooth analytic singularities.  This is the smooth-analytic
specialization of `isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPoleSet`. -/
theorem isOneOne_and_semipositive_add_smoothDDC
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hpsh : ThetaPlurisubharmonic θ.val u)
    (hsing : HasManifoldSmoothAnalyticSingularities (n := n) u)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : e.val.symm z ∉ poleSet u) :
    IsOneOne (θ.val.coeff e z + smoothDDC (fun y => (u (e.val.symm y)).toReal) z) ∧
      CoefficientSemipositive
        (θ.val.coeff e z + smoothDDC (fun y => (u (e.val.symm y)).toReal) z) :=
  isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPoleSet θ hpsh
    (SmoothOffPoleSet.of_hasManifoldSmoothAnalyticSingularities hsing) e hz hpole

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- **Off its poles, `θ + ddᶜu` is a semipositive `(1,1)`-form** for a `θ`-PSH potential with
analytic singularities in the bounded-remainder convention: bounded remainder, smooth off the
    poles.
Only the off-pole gateway is used, so nothing of the remainder at the pole is needed. -/
theorem isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPole
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hpsh : ThetaPlurisubharmonic θ.val u)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : e.val.symm z ∉ poleSet u) :
    IsOneOne (θ.val.coeff e z + smoothDDC (fun y => (u (e.val.symm y)).toReal) z) ∧
      CoefficientSemipositive
        (θ.val.coeff e z + smoothDDC (fun y => (u (e.val.symm y)).toReal) z) :=
  isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPoleSet θ hpsh
    (SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole hsing) e hz hpole

/-- **Off the pole set, the coordinate form of `T + εω` is a semipositive
`(1,1)`-form.** -/
theorem coordinateCurrentForm_isOneOne_and_semipositive
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : e.val.symm z ∉ poleSet p.potential) :
    IsOneOne (coordinateCurrentForm p e z) ∧
      CoefficientSemipositive (coordinateCurrentForm p e z) :=
  isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPole (perturbedRepresentative p)
    p.potential_psh.1 p.smoothAnalyticSingularities e hz hpole

/-- The plane inclusion `ℂ^k → ℂ^n`, `w ↦ (w, 0)`, as a continuous `ℂ`-linear map. -/
def planeInclusionCLM (k n : ℕ) : ComplexModel k →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := planeInclusion k n
      map_add' := fun a b => by
        ext i
        simp only [planeInclusion, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := fun c a => by
        ext i
        simp only [planeInclusion, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

@[simp] theorem planeInclusionCLM_apply (k n : ℕ) (w : ComplexModel k) :
    planeInclusionCLM k n w = planeInclusion k n w := rfl

theorem planeInclusion_injective {k n : ℕ} (hk : k ≤ n) :
    Function.Injective (planeInclusion k n) := by
  intro a b hab
  ext i
  have := congrArg (fun x : ComplexModel n => x ⟨i.1, lt_of_lt_of_le i.2 hk⟩) hab
  simpa [planeInclusion, i.2] using this

namespace RegularPatchDerivative

variable (P : RegularPatch V)

theorem isOpen_parameterDomain : IsOpen P.parameterDomain :=
  P.flattening.isOpen_target.preimage (planeInclusionCLM V.dim n).continuous

theorem differentiableAt_coordinateParametrization {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) :
    DifferentiableAt ℂ P.coordinateParametrization w := by
  have hinv : DifferentiableAt ℂ P.flattening.invFun (planeInclusion V.dim n w) :=
    P.flattening.invFun_holomorphic.differentiableAt
      (P.flattening.isOpen_target.mem_nhds hw)
  exact hinv.comp w (planeInclusionCLM V.dim n).differentiableAt

/-- The real derivative of the patch parametrization is complex linear. -/
theorem fderiv_coordinateParametrization_I_smul {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) (v : ComplexModel V.dim) :
    fderiv ℝ P.coordinateParametrization w (Complex.I • v) =
      Complex.I • fderiv ℝ P.coordinateParametrization w v := by
  rw [(differentiableAt_coordinateParametrization P hw).fderiv_restrictScalars ℝ]
  exact (fderiv ℂ P.coordinateParametrization w).map_smul Complex.I v

/-- The real derivative of the patch parametrization is injective. -/
theorem fderiv_coordinateParametrization_injective {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) :
    Function.Injective (fderiv ℝ P.coordinateParametrization w) := by
  have hsrc : P.coordinateParametrization w ∈ P.flattening.source :=
    P.flattening.mapsTo_invFun hw
  have hto : DifferentiableAt ℝ P.flattening.toFun (P.coordinateParametrization w) :=
    (P.flattening.toFun_holomorphic.differentiableAt
      (P.flattening.isOpen_source.mem_nhds hsrc)).restrictScalars ℝ
  have hφ : DifferentiableAt ℝ P.coordinateParametrization w :=
    (differentiableAt_coordinateParametrization P hw).restrictScalars ℝ
  have heq : (P.flattening.toFun ∘ P.coordinateParametrization) =ᶠ[𝓝 w]
      ((planeInclusionCLM V.dim n).restrictScalars ℝ : ComplexModel V.dim → ComplexModel n) := by
    filter_upwards [(isOpen_parameterDomain P).mem_nhds hw] with y hy
    exact P.flattening.right_inv _ hy
  have hderiv := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp w hto hφ, ContinuousLinearMap.fderiv] at hderiv
  intro a b hab
  have := congrArg (fun L : ComplexModel V.dim →L[ℝ] ComplexModel n => L a) hderiv
  have hb := congrArg (fun L : ComplexModel V.dim →L[ℝ] ComplexModel n => L b) hderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    planeInclusionCLM_apply] at this hb
  apply planeInclusion_injective V.dim_le
  rw [← this, ← hb, hab]

end RegularPatchDerivative

end

end SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
