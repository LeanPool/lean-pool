/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueCubeSetAtProcess
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartGreenPotential

/-!
# CubeSetAtHarmonicPart

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The harmonic part of a resolvent datum on a translated triadic cube

Fix a translated triadic cube `cubeSetAt y n`, a positive shift `mu` and a continuous datum `g`
vanishing at infinity, and write `psi = R_mu g` for the analytic resolvent supplied with the
process.  The vanishing-shift family of `ExitMeanValueCubeSetAtProcess.lean`,

  `psi - R^V_lam g + (mu - lam) R^V_lam psi`,

is rewritten here by linearity of the Dirichlet resolvent in its datum.  With the *residual*

  `cubeSetAtResolventResidual = g - mu psi`   (restricted to the cube),

which does not depend on the shift, the family is

  `psi - R^V_lam (residual) - lam R^V_lam psi`   (`cubeSetAtHarmonicApprox_eq`).

The first Dirichlet resolvent converges to the Green potential of the residual as the shift
decreases to zero, and the second term carries a factor of the shift against a bound uniform in
the shift, so it vanishes.  The limit is therefore

  `cubeSetAtHarmonicPart = psi - partGreenPotential (residual)`,

which agrees with `psi` off the cube because the Green potential does.  This discharges the
predicate `IsCubeSetAtResolventHarmonicPart` of `ExitMeanValueCubeSetAtProcess.lean` for that
function, with no hypothesis beyond the data.

This is the statement of `ExitMeanValueHarmonicPart.lean` on the translated triadic cube, with
the shift-uniform bound supplied by `PartTorsion.lean`.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## The residual datum -/

/-- The residual of a resolvent datum on a translated triadic cube: the datum less the shift
times the resolvent, both restricted to the cube.  It does not depend on the Dirichlet shift. -/
def cubeSetAtResolventResidual (R : PositiveC0ContractiveResolvent (Vec d)) (y : Vec d) (n : ℤ)
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) : Vec d → ℝ :=
  fun z ↦ cubeSetAtC0Datum y n g z -
    (mu : ℝ) * cubeSetAtC0Datum y n (R.toContractiveResolvent.operator mu g) z

theorem measurable_cubeSetAtResolventResidual (R : PositiveC0ContractiveResolvent (Vec d))
    (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ)) :
    Measurable (cubeSetAtResolventResidual R y n mu g) :=
  (measurable_cubeSetAtC0Datum y n g).sub
    ((measurable_cubeSetAtC0Datum y n (R.toContractiveResolvent.operator mu g)).const_mul _)

theorem abs_cubeSetAtResolventResidual_le (R : PositiveC0ContractiveResolvent (Vec d))
    (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (z : Vec d) :
    |cubeSetAtResolventResidual R y n mu g z| ≤ cubeResolventResidualBound R mu g := by
  have hsecond : |(mu : ℝ) *
      cubeSetAtC0Datum y n (R.toContractiveResolvent.operator mu g) z| ≤
      (mu : ℝ) * ‖R.toContractiveResolvent.operator mu g‖ := by
    rw [abs_mul, abs_of_pos mu.property]
    exact mul_le_mul_of_nonneg_left
      (abs_cubeSetAtC0Datum_le y n (R.toContractiveResolvent.operator mu g) z) mu.property.le
  refine (abs_sub _ _).trans ?_
  exact add_le_add (abs_cubeSetAtC0Datum_le y n g z) hsecond

variable [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The Dirichlet resolvent of the cube as a shift-indexed part resolvent -/

/-- The Dirichlet resolvent of a continuous datum vanishing at infinity on a translated triadic
cube is the shift-indexed Dirichlet resolvent of the part domain at the restricted datum. -/
theorem cubeSetAtC0Resolvent_eq_partShiftResolvent (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ))
    (lam : ℝ) (x : Vec d) :
    A.cubeSetAtC0Resolvent y n g lam x =
      A.partShiftResolvent (isOpenBoundedConvexDomain_cubeSetAt y n) (cubeSetAtC0Datum y n g)
        (measurable_cubeSetAtC0Datum y n g) (abs_cubeSetAtC0Datum_le y n g) lam x := by
  rw [cubeSetAtC0Resolvent, partShiftResolvent]
  split_ifs with h
  · rfl
  · rfl

theorem abs_cubeSetAtC0Resolvent_le (y : Vec d) (n : ℤ) (g : C₀(Vec d, ℝ)) (lam : ℝ)
    (x : Vec d) :
    |A.cubeSetAtC0Resolvent y n g lam x| ≤
      ‖g‖ * A.partTorsionBound (isOpenBoundedConvexDomain_cubeSetAt y n) := by
  rw [A.cubeSetAtC0Resolvent_eq_partShiftResolvent y n g lam x]
  exact A.abs_partShiftResolvent_le (isOpenBoundedConvexDomain_cubeSetAt y n)
    (measurable_cubeSetAtC0Datum y n g) (norm_nonneg g) (abs_cubeSetAtC0Datum_le y n g) lam x

variable (R : PositiveC0ContractiveResolvent (Vec d))

/-! ## The vanishing-shift family at the residual datum -/

/-- **The vanishing-shift family, rewritten at the residual datum.**  At every positive shift the
family of `ExitMeanValueCubeSetAtProcess.lean` is the resolvent datum less the Dirichlet resolvent
of the residual less the shift times the Dirichlet resolvent of the datum. -/
theorem cubeSetAtHarmonicApprox_eq (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ))
    {lam : ℝ} (hlam : 0 < lam) (x : Vec d) :
    R.toContractiveResolvent.operator mu g x - A.cubeSetAtC0Resolvent y n g lam x +
        ((mu : ℝ) - lam) *
          A.cubeSetAtC0Resolvent y n (R.toContractiveResolvent.operator mu g) lam x =
      R.toContractiveResolvent.operator mu g x -
        A.partShiftResolvent (isOpenBoundedConvexDomain_cubeSetAt y n)
          (cubeSetAtResolventResidual R y n mu g)
          (measurable_cubeSetAtResolventResidual R y n mu g)
          (abs_cubeSetAtResolventResidual_le R y n mu g) lam x -
        lam * A.cubeSetAtC0Resolvent y n (R.toContractiveResolvent.operator mu g) lam x := by
  have hV := isOpenBoundedConvexDomain_cubeSetAt y n
  set psi : C₀(Vec d, ℝ) := R.toContractiveResolvent.operator mu g with hpsidef
  set gc : Vec d → ℝ := cubeSetAtC0Datum y n g with hgcdef
  set pc : Vec d → ℝ := cubeSetAtC0Datum y n psi with hpcdef
  set res : Vec d → ℝ := cubeSetAtResolventResidual R y n mu g with hresdef
  have hgcmeas : Measurable gc := measurable_cubeSetAtC0Datum y n g
  have hpcmeas : Measurable pc := measurable_cubeSetAtC0Datum y n psi
  have hresmeas : Measurable res := measurable_cubeSetAtResolventResidual R y n mu g
  have hgcD : ∀ z, |gc z| ≤ ‖g‖ := abs_cubeSetAtC0Datum_le y n g
  have hpcD : ∀ z, |pc z| ≤ ‖psi‖ := abs_cubeSetAtC0Datum_le y n psi
  have hresD : ∀ z, |res z| ≤ cubeResolventResidualBound R mu g :=
    abs_cubeSetAtResolventResidual_le R y n mu g
  have hleft : Measurable fun z ↦ gc z + (-((mu : ℝ) - lam)) * pc z :=
    hgcmeas.add (hpcmeas.const_mul _)
  have hright : Measurable fun z ↦ res z + lam * pc z := hresmeas.add (hpcmeas.const_mul _)
  have hleftb : ∀ z, |gc z + (-((mu : ℝ) - lam)) * pc z| ≤ ‖g‖ + |(mu : ℝ) - lam| * ‖psi‖ := by
    intro z
    refine (abs_add_le _ _).trans (add_le_add (hgcD z) ?_)
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hpcD z) (abs_nonneg _)
  have hrightb : ∀ z, |res z + lam * pc z| ≤
      cubeResolventResidualBound R mu g + |lam| * ‖psi‖ := by
    intro z
    refine (abs_add_le _ _).trans (add_le_add (hresD z) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hpcD z) (abs_nonneg _)
  have hdata : Set.EqOn (fun z ↦ gc z + (-((mu : ℝ) - lam)) * pc z)
      (fun z ↦ res z + lam * pc z) (cubeSetAt y n) := by
    intro z _
    show gc z + (-((mu : ℝ) - lam)) * pc z = res z + lam * pc z
    rw [hresdef]
    show gc z + (-((mu : ℝ) - lam)) * pc z = (gc z - (mu : ℝ) * pc z) + lam * pc z
    ring
  have hA := A.partC0Resolvent_add_const_mul hV ⟨lam, hlam⟩ (-((mu : ℝ) - lam))
    hgcmeas hpcmeas hgcD hpcD hleft hleftb x
  have hB := A.partC0Resolvent_add_const_mul hV ⟨lam, hlam⟩ lam
    hresmeas hpcmeas hresD hpcD hright hrightb x
  have hC : A.partC0Resolvent hV ⟨lam, hlam⟩ (fun z ↦ gc z + (-((mu : ℝ) - lam)) * pc z)
        hleft hleftb x =
      A.partC0Resolvent hV ⟨lam, hlam⟩ (fun z ↦ res z + lam * pc z) hright hrightb x :=
    A.partC0Resolvent_eq_of_eqOn hV ⟨lam, hlam⟩ hleft hright hleftb hrightb hdata x
  rw [hA, hB] at hC
  rw [A.cubeSetAtC0Resolvent_eq_partShiftResolvent y n g lam x,
    A.cubeSetAtC0Resolvent_eq_partShiftResolvent y n psi lam x,
    A.partShiftResolvent_of_pos hV hgcmeas hgcD hlam x,
    A.partShiftResolvent_of_pos hV hpcmeas hpcD hlam x,
    A.partShiftResolvent_of_pos hV hresmeas hresD hlam x]
  linarith only [hC]

/-! ## The harmonic part -/

/-- **The harmonic part of a resolvent datum on a translated triadic cube**: the analytic
resolvent of the datum less the Green potential of the residual. -/
def cubeSetAtHarmonicPart (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ)) :
    Vec d → ℝ :=
  fun z ↦ R.toContractiveResolvent.operator mu g z -
    A.partGreenPotential (isOpenBoundedConvexDomain_cubeSetAt y n)
      (cubeSetAtResolventResidual R y n mu g)
      (measurable_cubeSetAtResolventResidual R y n mu g)
      (cubeResolventResidualBound_nonneg R mu g)
      (abs_cubeSetAtResolventResidual_le R y n mu g) z

theorem cubeSetAtHarmonicPart_of_notMem (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) {z : Vec d} (hz : z ∉ cubeSetAt y n) :
    A.cubeSetAtHarmonicPart R y n mu g z = R.toContractiveResolvent.operator mu g z := by
  rw [cubeSetAtHarmonicPart, A.partGreenPotential_of_notMem _ _ _ _ hz, sub_zero]

theorem measurable_cubeSetAtHarmonicPart (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) : Measurable (A.cubeSetAtHarmonicPart R y n mu g) :=
  (R.toContractiveResolvent.operator mu g).continuous.measurable.sub
    (A.measurable_partGreenPotential _ _ _ _)

/-- **The harmonic part is continuous on the cube.**  The resolvent datum is continuous on the
whole space and the Green potential is continuous on the cube. -/
theorem continuousOn_cubeSetAtHarmonicPart (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) :
    ContinuousOn (A.cubeSetAtHarmonicPart R y n mu g) (cubeSetAt y n) :=
  (R.toContractiveResolvent.operator mu g).continuous.continuousOn.sub
    (A.continuousOn_partGreenPotential _ _ _ _)

theorem abs_cubeSetAtHarmonicPart_le (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) (z : Vec d) :
    |A.cubeSetAtHarmonicPart R y n mu g z| ≤
      ‖R.toContractiveResolvent.operator mu g‖ +
        cubeResolventResidualBound R mu g *
          A.partTorsionBound (isOpenBoundedConvexDomain_cubeSetAt y n) := by
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm
      (R.toContractiveResolvent.operator mu g).toBCF z
  · exact A.abs_partGreenPotential_le _ _ _ _ z

/-- **The harmonic part discharges the vanishing-shift predicate.**  No hypothesis beyond the
data appears: the limit defining the predicate exists and is the harmonic part. -/
theorem isCubeSetAtResolventHarmonicPart_cubeSetAtHarmonicPart (y : Vec d) (n : ℤ)
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) :
    A.IsCubeSetAtResolventHarmonicPart R y n mu g (A.cubeSetAtHarmonicPart R y n mu g) := by
  have hV := isOpenBoundedConvexDomain_cubeSetAt y n
  set psi : C₀(Vec d, ℝ) := R.toContractiveResolvent.operator mu g with hpsidef
  refine ⟨fun z hz ↦ A.cubeSetAtHarmonicPart_of_notMem R y n mu g hz, fun z _ ↦ ?_⟩
  have hgreen : Tendsto (fun lam : ℝ ↦ A.partShiftResolvent hV
        (cubeSetAtResolventResidual R y n mu g)
        (measurable_cubeSetAtResolventResidual R y n mu g)
        (abs_cubeSetAtResolventResidual_le R y n mu g) lam z) (𝓝[>] (0 : ℝ))
      (𝓝 (A.partGreenPotential hV (cubeSetAtResolventResidual R y n mu g)
        (measurable_cubeSetAtResolventResidual R y n mu g)
        (cubeResolventResidualBound_nonneg R mu g)
        (abs_cubeSetAtResolventResidual_le R y n mu g) z)) :=
    A.tendsto_partShiftResolvent_nhdsGT_zero hV _ _ _ z
  have htail : Tendsto (fun lam : ℝ ↦ lam * A.cubeSetAtC0Resolvent y n psi lam z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun lam : ℝ ↦ |lam| * (‖psi‖ * A.partTorsionBound hV))
      (Eventually.of_forall fun lam ↦ ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (A.abs_cubeSetAtC0Resolvent_le y n psi lam z)
        (abs_nonneg lam)
    · have hcont : Tendsto (fun lam : ℝ ↦ |lam| * (‖psi‖ * A.partTorsionBound hV)) (𝓝 (0 : ℝ))
          (𝓝 (|(0 : ℝ)| * (‖psi‖ * A.partTorsionBound hV))) :=
        ((continuous_abs.mul continuous_const).tendsto 0)
      rw [abs_zero, zero_mul] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
  have hconst : Tendsto (fun _ : ℝ ↦ psi z) (𝓝[>] (0 : ℝ)) (𝓝 (psi z)) := tendsto_const_nhds
  have hlimit := (hconst.sub hgreen).sub htail
  rw [sub_zero] at hlimit
  refine Tendsto.congr' ?_ hlimit
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  exact (A.cubeSetAtHarmonicApprox_eq R y n mu g hlam z).symm

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
