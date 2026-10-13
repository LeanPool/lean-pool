/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.CorrectorLimitNode
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.StationaryCarrierTransport

/-!
# FreshShellCorrectorEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The fresh-shell corrector energy is the (J4) constant

ABK26, assumption `a.j.nondeg` and the first equality of `e.perturb.assumption`,
at the fresh shell `k = 0`.

`Algsuperdiff/Section3/Provider/Corrector/CorrectorLimitNode.lean` proves the
corrector limit `e.corrector.limit` at the fresh shell, on the continuous-path
carrier `C(Vec d, Mat d)`; its limit value is the energy `E[|∇w|²] = ∫
‖valuePathCorrectorRepr M he‖²` of the canonical Helmholtz corrector *of that
carrier*.  The frozen assumption (J4)
(`Algsuperdiff/Frozen/Assumptions/ShellLawJ4.lean`) states the corrector energy
on CoarseGraining's regular-field carrier `RegCoeffField d`, as
`‖ShellField.zeroShellPotentialCorrector …‖² = c⋆ log 3`.

`Algsuperdiff/Section3/Provider/Corrector/ValuePathTransport.lean` states
explicitly that its canonical corrector is *not* identified with
`ShellField.zeroShellPotentialCorrector`: only the forcing, its covariance and
its **forcing** energy are shown to agree there.  This file supplies the missing
identification — of the **corrector** energies — and therefore evaluates the
corrector limit at the literal constant `c⋆ log 3`.

## How the identification is made

The two carriers are related by the forgetful map

`regOfPath : C(Vec d, Mat d) → RegCoeffField d`

— a continuous matrix path *is* an entrywise measurable, locally integrable
coefficient field — which is measurable, equivariant for the two real
translation actions, satisfies `regOfPath ∘ valuePath = forgetShell`, and hence
pushes the transported zero-shell law forward to CoarseGraining's zero-shell
law.  The generic comparison of
`Algsuperdiff/Section3/Provider/Corrector/StationaryCarrierTransport.lean` then
gives, for the Koopman isometry `T` of `regOfPath` and its Hilbert adjoint,

`P_path (T F) = T (P_reg F)`,

whence the two projected energies agree.  No identification of the two carrier
`σ`-algebras, no surjectivity of `T`, and no cyclic-subspace or
covariance-isomorphism argument is used: the adjoint replaces all of them.

## Main results

* `norm_valuePathPotentialCorrector_eq` — the two canonical corrector energies
  agree.
* `integral_normSq_valuePathCorrectorRepr_eq` — the path-carrier corrector energy
  equals `c⋆ log 3`, with `c⋆ = Disorder.cstar M` the selected (J4) constant.

**Disclosure.**  This file realizes the fresh-shell (`k = 0`) instance of the
first equality of `e.perturb.assumption`, with its `|e|²` factor, and *without*
the shell sum `Σ_{k = m-h+1}^m`, the `σ_{m-h}^{-2}` normalization and the
`3^{2γk}` dilation factor; those three are *not* proved here.  Its inputs are the frozen assumptions
(J1),
(J2), (J4) through `ABKModel`, the proved corrector limit of
`CorrectorLimitNode.lean`, and Mathlib.  No draft theorem, in particular not
`Frozen.External.calderon_zygmund`, is used.
-/

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Probability.Stationary

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The forgetful map from continuous paths to CoarseGraining regular fields -/

/-- A continuous matrix-valued path, read as an CoarseGraining regular coefficient
field.  Continuity supplies both carrier obligations: entrywise measurability
and entrywise local integrability. -/
def regOfPath (f : C(Vec d, Mat d)) : RegCoeffField d where
  toFun := f
  entry_measurable := fun i k ↦
    ((continuous_apply k).comp ((continuous_apply i).comp f.continuous)).measurable
  entry_locInt := fun i k ↦
    ((continuous_apply k).comp ((continuous_apply i).comp f.continuous)).locallyIntegrable

/-- The two forgetful maps of the shell carrier agree: forgetting the shell
packaging is reading the value path as a regular field. -/
theorem regOfPath_valuePath (j : ShellField d) :
    regOfPath (ShellField.valuePath j) = ShellField.forgetShell j :=
  rfl

/-- Both carriers use the manuscript translation convention, so the forgetful
map is equivariant. -/
theorem regOfPath_vadd (z : Vec d) (f : C(Vec d, Mat d)) :
    regOfPath (z +ᵥ f) = z +ᵥ regOfPath f :=
  rfl

private theorem measurable_regOfPath_entryTest (i k : Fin d)
    (phi : Vec d → ℝ) (hphi : IsProbeR phi) :
    Measurable (fun f : C(Vec d, Mat d) ↦ entryTestR i k phi (regOfPath f)) := by
  let F : C(Vec d, Mat d) × Vec d → ℝ := fun q ↦ q.1 q.2 i k * phi q.2
  have hFcont : Continuous (fun q : C(Vec d, Mat d) × Vec d ↦ q.1 q.2 i k) :=
    (continuous_apply k).comp ((continuous_apply i).comp ContinuousEval.continuous_eval)
  have hFmeas : Measurable F :=
    hFcont.measurable.mul (hphi.measurable.comp measurable_snd)
  have hInt : StronglyMeasurable
      (fun f : C(Vec d, Mat d) ↦ ∫ x, F (f, x) ∂volume) :=
    hFmeas.stronglyMeasurable.integral_prod_right'
  have hEq : (fun f : C(Vec d, Mat d) ↦ ∫ x, F (f, x) ∂volume) =
      fun f ↦ entryTestR i k phi (regOfPath f) := rfl
  rw [← hEq]
  exact hInt.measurable

/-- The forgetful map is measurable for CoarseGraining's full regular-field
`σ`-algebra, including the compactly supported integral generators. -/
theorem measurable_regOfPath : Measurable (regOfPath (d := d)) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro x i k
    have hx : Continuous (fun f : C(Vec d, Mat d) ↦ f x) := continuous_eval_const x
    exact ((continuous_apply k).comp ((continuous_apply i).comp hx)).measurable
  · intro i k phi hphi
    exact measurable_regOfPath_entryTest i k phi hphi

/-- The forgetful map pushes the transported zero-shell law forward to
CoarseGraining's zero-shell law: both are pushforwards of one and the same
shell-zero law. -/
theorem measurePreserving_regOfPath (M : ABKModel d) :
    MeasurePreserving (regOfPath (d := d))
      (zeroShellValuePathLaw M.P).toMeasure
      (ShellField.zeroShellRegLaw M.P).toMeasure := by
  refine ⟨measurable_regOfPath, ?_⟩
  rw [zeroShellValuePathLaw_toMeasure_eq_map_valuePath,
    ShellField.zeroShellRegLaw_toMeasure_eq_map_forgetShell,
    Measure.map_map measurable_regOfPath ShellField.measurable_valuePath]
  exact congrArg
    (fun g : ShellField d → RegCoeffField d ↦
      Measure.map g (ShellField.zeroShellLaw M.P).toMeasure)
    (funext regOfPath_valuePath)

/-! ### The transported forcing is the path-carrier forcing -/

/-- The Koopman transport of the CoarseGraining forcing is the path-carrier
forcing. -/
theorem carrierTransport_zeroShellForcingL2 (M : ABKModel d) {e : Vec d}
    (he : Book.Ch02.vecNorm e = 1)
    (hmem : MemLp (ShellField.originForcing e) 2
      (ShellField.zeroShellRegLaw M.P).toMeasure) :
    carrierTransport (HilbertVec d) (measurePreserving_regOfPath M)
        (ShellField.zeroShellForcingL2 M.P e hmem)
      = valuePathForcingL2 M he :=
  Lp.toLp_compMeasurePreserving hmem (measurePreserving_regOfPath M)

/-! ### The two corrector energies agree -/

/-- **The canonical fresh-shell corrector energies of the two carriers agree.** -/
theorem norm_valuePathPotentialCorrector_eq (M : ABKModel d) {e : Vec d}
    (he : Book.Ch02.vecNorm e = 1)
    (hmem : MemLp (ShellField.originForcing e) 2
      (ShellField.zeroShellRegLaw M.P).toMeasure) :
    ‖valuePathPotentialCorrector M he‖
      = ‖ShellField.zeroShellPotentialCorrector M.P
          (ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
            M.P M.J1.stationary) e hmem‖ := by
  have : VAddInvariantMeasure (Vec d) (RegCoeffField d)
      (ShellField.zeroShellRegLaw M.P).toMeasure :=
    vaddInvariantMeasure_zeroShellRegLaw M
  have hproj := norm_stationaryPotentialProjection_carrierTransport
    (d := d) (measurePreserving_regOfPath M) regOfPath_vadd
    (ShellField.zeroShellForcingL2 M.P e hmem)
  rw [carrierTransport_zeroShellForcingL2 M he hmem] at hproj
  simpa only [valuePathPotentialCorrector, ShellField.zeroShellPotentialCorrector,
    ShellField.zeroShellProjectedForcing, norm_neg] using hproj

/-- The `L²` norm square of the path-carrier corrector is the expectation of the
squared Euclidean norm of its strongly measurable representative. -/
theorem integral_normSq_valuePathCorrectorRepr_eq_norm_sq (M : ABKModel d)
    {e : Vec d} (he : Book.Ch02.vecNorm e = 1) :
    ∫ f, ‖valuePathCorrectorRepr M he f‖ ^ 2 ∂(zeroShellValuePathLaw M.P).toMeasure
      = ‖valuePathPotentialCorrector M he‖ ^ 2 := by
  set q := valuePathPotentialCorrector M he with hq
  have hae : (fun f : C(Vec d, Mat d) ↦ ‖valuePathCorrectorRepr M he f‖ ^ 2)
      =ᵐ[(zeroShellValuePathLaw M.P).toMeasure]
      fun f ↦ ‖(q : C(Vec d, Mat d) → HilbertVec d) f‖ ^ 2 := by
    filter_upwards [(Lp.aestronglyMeasurable q).ae_eq_mk] with f hf
    exact congrArg (fun v : HilbertVec d ↦ ‖v‖ ^ 2) hf.symm
  rw [integral_congr_ae hae]
  calc ∫ f, ‖(q : C(Vec d, Mat d) → HilbertVec d) f‖ ^ 2
        ∂(zeroShellValuePathLaw M.P).toMeasure
      = ∫ f, (inner ℝ ((q : C(Vec d, Mat d) → HilbertVec d) f)
          ((q : C(Vec d, Mat d) → HilbertVec d) f) : ℝ)
          ∂(zeroShellValuePathLaw M.P).toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun f ↦ ?_)
        exact (real_inner_self_eq_norm_sq _).symm
    _ = (inner ℝ q q : ℝ) := (MeasureTheory.L2.inner_def q q).symm
    _ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q

/-- **The fresh-shell corrector energy is `c⋆ log 3`** — the first equality of
`e.perturb.assumption` at the fresh shell `k = 0`, at a unit direction, read
through assumption `a.j.nondeg`. -/
theorem integral_normSq_valuePathCorrectorRepr_eq (M : ABKModel d) {e : Vec d}
    (he : Book.Ch02.vecNorm e = 1) :
    ∫ f, ‖valuePathCorrectorRepr M he f‖ ^ 2 ∂(zeroShellValuePathLaw M.P).toMeasure
      = Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 := by
  rw [integral_normSq_valuePathCorrectorRepr_eq_norm_sq M he,
    norm_valuePathPotentialCorrector_eq M he
      (ShellField.memLp_originForcing_of_j2_tail M.P M.J2.gaussian_tail e he)]
  exact (Algsuperdiff.Section3.Disorder.cstar_characterization M).2.1 ⟨e, he⟩

end

end Algsuperdiff.Section3.Provider.Corrector
