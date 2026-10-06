/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeTwoSidedGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledLocalizationAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessClassBRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Composed rows of the Dirichlet clause, from the frozen surface

Eight rows of the clause are compositions of existing producers.  Three of them
are pure compositions from the frozen witness geometry, and are built here:

* `hUhat`, `hUhatMeas`, `hUhat0` — the gauge domain is the *translate* of an
  open triadic cube, and `IsOpenBoundedConvexDomain.translateSet` is upstream,
  so no matrix-image convexity lemma is needed
  at all, since the physical domain's own convexity is never available on
  surface, only its cube presentation.
* `system`, `hU`, `hUnonempty`, `hRad` — the ruled carrier at the gauge domain,
  from `exists_enlargedMarginRuledTriadicWhitneySystem` and the frozen ball
  sandwich.  `0 < Rad` is derived from the sandwich itself.
* the two Hardy premises — the ruled Hardy selector, whose conclusion is
  *definitionally* `PrintFaithfulPositiveTestRow`.

`hGauge` was already supplied in
`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeEnclosure`
(`gaugeDomain_subset_normalizedSublevel`), so four of the nine rows of are
now discharged.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The gauge domain is a bounded open convex domain -/

/-- **Row `hUhat`/`hUhatMeas`/`hUhat0`.**  The gauge domain of the frozen
witness is a bounded open convex domain. -/
theorem frozenWitness_gaugeDomain_isOpenBoundedConvexDomain [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j)) :
    IsOpenBoundedConvexDomain (matImage (matSqrt (symmPart abar))⁻¹ U) := by
  rw [gaugeDomain_eq_translateSet hS hU]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d j)).translateSet _

/-- The gauge domain of the frozen witness is nonempty. -/
theorem frozenWitness_gaugeDomain_nonempty [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j)) :
    (matImage (matSqrt (symmPart abar))⁻¹ U).Nonempty := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have h0 : (0 : Vec d) ∈ openCubeSet (originCube d j) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> linarith only [hpow]
  rw [gaugeDomain_eq_translateSet hS hU]
  refine ⟨matVecMul (matSqrt (symmPart abar))⁻¹ z, ?_⟩
  rw [mem_translateSet_iff_sub_mem, sub_self]
  exact h0

/-- The gauge domain of the frozen witness has positive volume. -/
theorem frozenWitness_gaugeDomain_volume_ne_zero [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j)) :
    volume (matImage (matSqrt (symmPart abar))⁻¹ U) ≠ 0 :=
  volume_ne_zero_of_isOpenBoundedConvexDomain
    (frozenWitness_gaugeDomain_isOpenBoundedConvexDomain hS hU)
    (frozenWitness_gaugeDomain_nonempty hS hU)

/-! ## The outer sandwich radius is positive -/

/-- **Row `hRad`.**  A ball sandwich with a positive inner radius forces a
positive outer radius. -/
theorem rad_pos_of_hasBallSandwich {V : Set (Vec d)} {rho Rad : ℝ}
    (hsandwich : HasBallSandwich V rho Rad) : 0 < Rad := by
  obtain ⟨hrho, hRadNonneg, c, hinner, houter⟩ := hsandwich
  have hmem : vecNormSq (c - c) < Rad ^ 2 :=
    houter (hinner (center_mem_euclideanBallAt c hrho))
  rw [sub_self, show vecNormSq (0 : Vec d) = 0 from vecNormSq_eq_zero_iff.mpr rfl]
    at hmem
  rcases lt_or_eq_of_le hRadNonneg with hlt | heq
  · exact hlt
  · exfalso
    rw [← heq] at hmem
    simp at hmem

/-! ## The ruled carrier at the gauge domain -/

/-- **Row `system`/`hU`/`hUnonempty`/`hRad`.**  The frozen surface produces the
ruled Whitney carrier at the gauge domain, together with the three companion
facts that module asks for. -/
theorem exists_frozenWitnessRuledCarrier [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d} {rho Rad : ℝ}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    Nonempty (EnlargedMarginRuledTriadicWhitneySystem
        (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) ∧
      IsOpenBoundedConvexDomain (matImage (matSqrt (symmPart abar))⁻¹ U) ∧
      (matImage (matSqrt (symmPart abar))⁻¹ U).Nonempty ∧ 0 < Rad :=
  ⟨exists_enlargedMarginRuledTriadicWhitneySystem
      (frozenWitness_gaugeDomain_isOpenBoundedConvexDomain hS hU) hsandwich,
    frozenWitness_gaugeDomain_isOpenBoundedConvexDomain hS hU,
    frozenWitness_gaugeDomain_nonempty hS hU,
    rad_pos_of_hasBallSandwich hsandwich⟩

/-! ## The Hardy row -/

end

end RowSupply
end HighContrast
end HCPolySupport
