/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicPotential
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartResolventAlgebra

/-!
# PartTorsion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The shift-uniform bound of the Dirichlet resolvent of a bounded part domain

The vanishing-shift limit of the Dirichlet resolvents of a fixed bounded datum exists because the
resolvents are bounded *uniformly in the shift* and are Lipschitz in the shift.  On an exhaustion
cube both facts come from the torsion function of that cube.  A general bounded part domain has
no torsion function of its own here, and none is constructed: the domain is bounded, so it lies
inside an exhaustion cube, and the Dirichlet resolvent of a nonnegative datum on the smaller
domain is below the Dirichlet resolvent of the same datum on the larger one.

* `partC0Resolvent_le_analyticCubeResolvent` is that domain monotonicity.  It is the weak
  maximum principle of `PartDomainSubsolution.lean`, which is already stated for an arbitrary
  bounded open convex domain inside another, read through the continuous representatives.
* `partTorsionBound` is the torsion bound of the containing exhaustion cube, and
  `abs_partC0Resolvent_le_partTorsionBound` bounds the Dirichlet resolvent of a datum bounded by
  `D` by `D` times it, uniformly in the shift.
* `abs_partC0Resolvent_sub_le` is the Lipschitz estimate in the shift, obtained from the uniform
  bound and the resolvent identity exactly as on an exhaustion cube.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## Domain monotonicity -/

/-- **The Dirichlet resolvent of a nonnegative datum increases with the domain.**  On a bounded
open convex domain inside an exhaustion cube, the zero extension of the part solution is a weak
subsolution with the same forcing, so it lies below the solution on the cube; both sides are
continuous on the part domain, so the inequality holds at every point of it. -/
theorem partC0Resolvent_le_analyticCubeResolvent {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {m : ℕ}
    (hVU : V ⊆ wholeSpaceCube d m) {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    {D : ℝ} (hfD : ∀ z, |f z| ≤ D) {x : Vec d} (hx : x ∈ V) :
    A.partC0Resolvent hV lam f hf hfD x ≤ A.analyticCubeResolvent lam f hf hfD m x := by
  have hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  set F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) with hFdef
  have hF0 : ∀ᵐ z ∂volumeMeasureOn (wholeSpaceCube d m), 0 ≤ F z :=
    ae_nonneg_boundedMeasurableToScalarL2 hU hf hf0 hfD
  have hrem := partDomainRemainder_nonneg_ae A.a hV hU hVU lam.property A.hnu
    (A.cubeEllipticity m) F hF0
  set uV : ZeroTraceSobolev V := alphaShiftedSolution A.a lam.property A.hnu
    ((A.cubeEllipticity m).mono hV.isOpen.measurableSet hVU)
    (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet F) with huVdef
  set rU : ZeroTraceSobolev (wholeSpaceCube d m) :=
    alphaShiftedSolution A.a lam.property A.hnu (A.cubeEllipticity m) F with hrUdef
  have hpart : uV = alphaShiftedSolution A.a lam.property A.hnu (partEllipticity A hV)
      (partDatumL2 hV hf hfD) := by
    rw [huVdef, hFdef, restrictScalarL2ToPart_boundedMeasurableToScalarL2 hV hU hVU hf hfD]
    exact alphaShiftedSolution_congr_ellipticity A.a lam.property A.hnu A.hnu _ _ _
  refine le_of_ae_le_of_continuousOn hV.isOpen
    (A.continuousOn_partC0Resolvent hV lam f hf hfD)
    ((A.continuousOn_analyticCubeResolvent lam hf hfD m).mono hVU) ?_ x hx
  filter_upwards [A.partC0Resolvent_ae hV lam f hf hfD,
    ae_restrict_of_ae_restrict_of_subset hVU (A.analyticCubeResolvent_ae lam hf hfD m),
    ae_restrict_of_ae_restrict_of_subset hVU hrem,
    ae_restrict_of_ae_restrict_of_subset hVU
      (ZeroTraceSobolev.extendByZeroToPartSuperset_toL2 hV hU.isOpen hVU uV),
    ae_restrict_of_ae_restrict_of_subset hVU (MeasureTheory.Lp.coeFn_sub
      (ZeroTraceSobolev.toL2 rU)
      (ZeroTraceSobolev.toL2 (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU uV))),
    self_mem_ae_restrict hV.isOpen.measurableSet] with z h1 h2 h3 h4 h5 hzV
  rw [h1, h2]
  have hsub : ZeroTraceSobolev.toL2 (rU -
      ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU uV) z =
      ZeroTraceSobolev.toL2 rU z -
        ZeroTraceSobolev.toL2 (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU uV) z
      := by
    rw [map_sub, h5, Pi.sub_apply]
  rw [hsub, h4, Set.indicator_of_mem hzV] at h3
  have hval : ZeroTraceSobolev.toL2 uV z =
      alphaShiftedResolvent A.a lam.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD) z := by
    have happly := alphaShiftedResolvent_apply A.a lam.property A.hnu (partEllipticity A hV)
      (partDatumL2 hV hf hfD)
    rw [hpart, happly]
  rw [hval] at h3
  have hrval : ZeroTraceSobolev.toL2 rU z =
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity m) F z := by
    have happly := alphaShiftedResolvent_apply A.a lam.property A.hnu (A.cubeEllipticity m) F
    rw [hrUdef, happly]
  rw [hrval] at h3
  linarith only [h3]

/-! ## The shift-uniform bound -/

/-- The torsion bound of an exhaustion cube containing a bounded part domain. -/
def partTorsionBound {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) : ℝ :=
  A.cubeTorsionBound (partCubeIndex hV)

theorem partTorsionBound_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) :
    0 ≤ A.partTorsionBound hV :=
  A.cubeTorsionBound_nonneg _

/-- **The Dirichlet resolvent of a bounded datum on a bounded part domain is bounded uniformly
in the shift.**  Comparison with the constant datum of a containing exhaustion cube, whose
Dirichlet resolvents are below the torsion function of that cube at every shift, replaces the
shift-dependent bound `D / lam` by `D` times the torsion bound of the cube. -/
theorem abs_partC0Resolvent_le_partTorsionBound {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ z, |f z| ≤ D) (x : Vec d) :
    |A.partC0Resolvent hV lam f hf hfD x| ≤ D * A.partTorsionBound hV := by
  have hM : 0 ≤ A.partTorsionBound hV := A.partTorsionBound_nonneg hV
  set m : ℕ := partCubeIndex hV with hmdef
  have hVU : V ⊆ wholeSpaceCube d m := subset_wholeSpaceCube_partCubeIndex hV
  by_cases hx : x ∈ V
  · have hcbound : ∀ c : ℝ, ∀ z : Vec d, |c * cubeOneDatum d m z| ≤ |c| * 1 := by
      intro c z
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_cubeOneDatum_le d m z) (abs_nonneg c)
    set fc : Vec d → ℝ := V.indicator f with hfcdef
    have hfczero : ∀ {z : Vec d}, z ∉ V → fc z = 0 := by
      intro z hz
      rw [hfcdef]
      exact Set.indicator_of_notMem hz _
    have hfcmem : ∀ {z : Vec d}, z ∈ V → fc z = f z := by
      intro z hz
      rw [hfcdef]
      exact Set.indicator_of_mem hz _
    have hfcmeas : Measurable fc := hf.indicator hV.isOpen.measurableSet
    have hfcD : ∀ z, |fc z| ≤ D := by
      intro z
      by_cases hz : z ∈ V
      · rw [hfcmem hz]; exact hfD z
      · rw [hfczero hz, abs_zero]; exact hD
    have heq : A.partC0Resolvent hV lam f hf hfD x =
        A.partC0Resolvent hV lam fc hfcmeas hfcD x :=
      A.partC0Resolvent_eq_of_eqOn hV lam hf hfcmeas hfD hfcD (fun z hz ↦ (hfcmem hz).symm) x
    set R1 : ℝ := A.partC0Resolvent hV lam (cubeOneDatum d m) (measurable_cubeOneDatum d m)
      (abs_cubeOneDatum_le d m) x with hR1def
    have hR1le : R1 ≤ A.partTorsionBound hV := by
      calc R1 ≤ A.analyticCubeResolvent lam (cubeOneDatum d m) (measurable_cubeOneDatum d m)
              (abs_cubeOneDatum_le d m) m x :=
            A.partC0Resolvent_le_analyticCubeResolvent hV lam hVU
              (measurable_cubeOneDatum d m) (cubeOneDatum_nonneg d m)
              (abs_cubeOneDatum_le d m) hx
        _ ≤ A.cubeTorsionRepresentative m x :=
            A.analyticCubeResolvent_cubeOneDatum_le_cubeTorsionRepresentative m lam (hVU hx)
        _ ≤ A.partTorsionBound hV := A.cubeTorsionRepresentative_le m x
    have hscaled : ∀ c : ℝ,
        A.partC0Resolvent hV lam (fun z ↦ c * cubeOneDatum d m z)
          ((measurable_cubeOneDatum d m).const_smul c) (hcbound c) x = c * R1 := fun c ↦
      A.partC0Resolvent_smul hV lam c (measurable_cubeOneDatum d m)
        (abs_cubeOneDatum_le d m) (hcbound c) x
    have hcmp : ∀ z : Vec d, fc z ≤ D * cubeOneDatum d m z := by
      intro z
      by_cases hz : z ∈ V
      · rw [hfcmem hz, cubeOneDatum_of_mem (hVU hz), mul_one]
        exact (le_abs_self (f z)).trans (hfD z)
      · rw [hfczero hz]
        exact mul_nonneg hD (cubeOneDatum_nonneg d m z)
    have hcmp' : ∀ z : Vec d, (-D) * cubeOneDatum d m z ≤ fc z := by
      intro z
      by_cases hz : z ∈ V
      · rw [hfcmem hz, cubeOneDatum_of_mem (hVU hz), mul_one]
        exact (abs_le.mp (hfD z)).1
      · rw [hfczero hz]
        have hnn := mul_nonneg hD (cubeOneDatum_nonneg d m z)
        linarith only [hnn]
    have hupper : A.partC0Resolvent hV lam fc hfcmeas hfcD x ≤ D * R1 := by
      rw [← hscaled D]
      exact A.partC0Resolvent_mono hV lam hfcmeas
        ((measurable_cubeOneDatum d m).const_smul D) hfcD (hcbound D) hcmp x
    have hlower : (-D) * R1 ≤ A.partC0Resolvent hV lam fc hfcmeas hfcD x := by
      rw [← hscaled (-D)]
      exact A.partC0Resolvent_mono hV lam ((measurable_cubeOneDatum d m).const_smul (-D))
        hfcmeas (hcbound (-D)) hfcD hcmp' x
    have hgap : D * R1 ≤ D * A.partTorsionBound hV := mul_le_mul_of_nonneg_left hR1le hD
    rw [heq, abs_le]
    exact ⟨by linarith only [hlower, hgap], by linarith only [hupper, hgap]⟩
  · rw [A.partC0Resolvent_of_notMem hV lam f hf hfD hx, abs_zero]
    exact mul_nonneg hD hM

/-! ## The Lipschitz estimate in the shift -/

/-- **The Dirichlet resolvents of a bounded datum on a bounded part domain are Lipschitz in the
shift.**  The resolvent identity writes the difference of the values at two shifts as the
difference of the shifts times a third Dirichlet resolvent, and the uniform bound applies twice
to that third resolvent. -/
theorem abs_partC0Resolvent_sub_le {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (lam nu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ z, |f z| ≤ D) (x : Vec d) :
    |A.partC0Resolvent hV lam f hf hfD x - A.partC0Resolvent hV nu f hf hfD x| ≤
      D * (A.partTorsionBound hV * A.partTorsionBound hV) * |(lam : ℝ) - (nu : ℝ)| := by
  have hM : 0 ≤ A.partTorsionBound hV := A.partTorsionBound_nonneg hV
  set w : Vec d → ℝ := A.partC0Resolvent hV lam f hf hfD with hwdef
  have hwmeas : Measurable w := A.measurable_partC0Resolvent hV lam f hf hfD
  have hwbd : ∀ z, |w z| ≤ D * A.partTorsionBound hV := fun z ↦
    A.abs_partC0Resolvent_le_partTorsionBound hV lam hf hD hfD z
  have hid := A.partC0Resolvent_resolvent_identity hV lam nu hf hD hfD x
  have hswap : A.partC0Resolvent hV nu w hwmeas
        (A.abs_partC0Resolvent_le hV lam hf hD hfD) x =
      A.partC0Resolvent hV nu w hwmeas hwbd x :=
    A.partC0Resolvent_eq_of_eqOn hV nu hwmeas hwmeas _ hwbd (Set.eqOn_refl _ _) x
  rw [hswap] at hid
  have hinner : |A.partC0Resolvent hV nu w hwmeas hwbd x| ≤
      D * (A.partTorsionBound hV * A.partTorsionBound hV) := by
    have h := A.abs_partC0Resolvent_le_partTorsionBound hV nu hwmeas (mul_nonneg hD hM) hwbd x
    calc |A.partC0Resolvent hV nu w hwmeas hwbd x|
        ≤ D * A.partTorsionBound hV * A.partTorsionBound hV := h
      _ = D * (A.partTorsionBound hV * A.partTorsionBound hV) := by ring
  have hsub : A.partC0Resolvent hV lam f hf hfD x - A.partC0Resolvent hV nu f hf hfD x =
      ((nu : ℝ) - (lam : ℝ)) * A.partC0Resolvent hV nu w hwmeas hwbd x := by
    rw [hid]; ring
  rw [hsub, abs_mul, abs_sub_comm]
  calc |(lam : ℝ) - (nu : ℝ)| * |A.partC0Resolvent hV nu w hwmeas hwbd x|
      ≤ |(lam : ℝ) - (nu : ℝ)| * (D * (A.partTorsionBound hV * A.partTorsionBound hV)) :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = D * (A.partTorsionBound hV * A.partTorsionBound hV) * |(lam : ℝ) - (nu : ℝ)| := by ring

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
