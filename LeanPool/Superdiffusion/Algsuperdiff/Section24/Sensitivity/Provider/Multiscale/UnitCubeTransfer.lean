/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.PerturbCoeffOn
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.BigLambda.UnitCubeBigLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.EllipticityLocality

/-!
# UnitCubeTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Localization transfer between the unit cube and its triadic descendants

The Section 2.4 sensitivity proofs apply a one-cube estimate on every triadic
descendant `z + cube_n` of the unit cube and then aggregate.  Two transfers
are needed.

## Root transfer

The frozen scalars `unitCubeLambda` and `unitCubeBigLambda` are characterized
against *every* compatible CoarseGraining triadic family, so any inequality
proved at the family level for one compatible pair of families transfers to
them.  That is `unitCubeLambda_inv_le_of_family_bound` and
`unitCubeBigLambda_le_of_family_bound` below; they are proved from
`exists_compatibleTriadicCoeffFamily` together with the frozen characterization
theorems, never by unfolding a `Classical.choose` definition.

## Descendant transfer

The perturbation `a ↦ a + t h` commutes with passing to a descendant cube: the
descendant representative of any family compatible with `perturbCoeffOn U a h t`
is a.e. equal to `perturbCoeffOn` of the descendant representative of any family
compatible with `a`, with `h` restricted to the descendant cube.  This is
`coeffOn_descendant_aeeq_perturbCoeffOn` below, and it is what lets the
per-descendant one-cube estimates of the neighbouring modules be fed into the
aggregation lemmas.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.UnitCubeMultiscale

noncomputable section

variable {d : ℕ}

/-! ## Restricting an `L^∞` skew field to a subdomain -/

/-- An `L^∞` skew-symmetric matrix field on a domain restricts to any
subdomain.  The underlying representative is unchanged; only the `L^∞` and a.e.
skewness data are transported along the inclusion of measures. -/
def restrictLInfSkewMatrixFieldOn {U V : Domain d}
    (hsub : (V : Set (Vec d)) ⊆ (U : Set (Vec d)))
    (h : LInfSkewMatrixFieldOn U) : LInfSkewMatrixFieldOn V :=
  ⟨⟨h.1.1, fun i j =>
      (h.1.2 i j).mono_measure (Measure.restrict_mono hsub le_rfl)⟩,
    ae_restrict_of_ae_restrict_of_subset hsub h.2⟩

@[simp] theorem restrictLInfSkewMatrixFieldOn_apply {U V : Domain d}
    (hsub : (V : Set (Vec d)) ⊆ (U : Set (Vec d)))
    (h : LInfSkewMatrixFieldOn U) (x : Vec d) :
    (restrictLInfSkewMatrixFieldOn hsub h).1.1 x = h.1.1 x :=
  rfl

/-! ## The perturbation commutes with restriction -/

@[simp] theorem perturbCoeffOn_toCoeffField {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t : ℝ) (x : Vec d) :
    (perturbCoeffOn U a h t).toCoeffField x = a.toCoeffField x + t • h.1.1 x :=
  rfl

/-- **Descendant localization of the perturbation.**  If `F` is any CoarseGraining
family compatible with `a` at the origin cube and `G` is any CoarseGraining
family compatible with `a + t h` there, then on every triadic descendant `R` of
the origin cube the representative of `G` is a.e. the `t`-perturbation of the
representative of `F` by the restriction of `h`. -/
theorem coeffOn_descendant_aeeq_perturbCoeffOn
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (t : ℝ)
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h t))
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    CoeffOn.AEEq (G.coeffOn R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
        (restrictLInfSkewMatrixFieldOn
          (U := cubeDomain (originCube d 0)) (V := cubeDomain R)
          (openCubeSet_subset_of_mem_descendantsAtScale hk hR) h) t) := by
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d 0) :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  -- `G` restricted to `R` is a.e. the perturbation of `a`.
  have hGchild : (G.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)]
        (G.coeffOn (originCube d 0)).toCoeffField :=
    G.restrictsTo_of_subset hsub
  have hGroot : (G.coeffOn (originCube d 0)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)]
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h t).toCoeffField :=
    ae_restrict_of_ae_restrict_of_subset hsub hG
  -- `F` restricted to `R` is a.e. `a`.
  have hFchild : (F.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)]
        (F.coeffOn (originCube d 0)).toCoeffField :=
    F.restrictsTo_of_subset hsub
  have hFroot : (F.coeffOn (originCube d 0)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)] a.toCoeffField :=
    ae_restrict_of_ae_restrict_of_subset hsub hF
  have hFa : (F.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)] a.toCoeffField := hFchild.trans hFroot
  refine (hGchild.trans hGroot).trans ?_
  filter_upwards [hFa] with x hx
  show a.toCoeffField x + t • h.1.1 x = (F.coeffOn R).toCoeffField x + t • h.1.1 x
  rw [hx]

/-! ## Root transfer to the frozen unit-cube scalars -/

/-- Family-level ratio bounds for the lower coarse-grained ellipticity transfer
to the frozen `unitCubeLambda`. -/
theorem unitCubeLambda_inv_le_of_family_bound
    (a b : CoeffOn (cubeDomain (originCube d 0))) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (ρ : ℝ)
    (hfam : ∀ F G : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      CoeffOn.AEEq (G.coeffOn (originCube d 0)) b →
      (Ch02.lambdaSq (originCube d 0) s q G)⁻¹ ≤
        ρ * (Ch02.lambdaSq (originCube d 0) s q F)⁻¹) :
    (unitCubeLambda s q b)⁻¹ ≤ ρ * (unitCubeLambda s q a)⁻¹ := by
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  obtain ⟨G, hG⟩ := exists_compatibleTriadicCoeffFamily b
  rw [unitCubeLambda_characterization s q a F hF,
    unitCubeLambda_characterization s q b G hG]
  exact hfam F G hF hG

/-- Family-level bounds for the upper coarse-grained ellipticity transfer to the
frozen `unitCubeBigLambda`. -/
theorem unitCubeBigLambda_le_of_family_bound
    (a b : CoeffOn (cubeDomain (originCube d 0))) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (c C : ℝ)
    (hfam : ∀ F G : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      CoeffOn.AEEq (G.coeffOn (originCube d 0)) b →
      Ch02.LambdaSq (originCube d 0) s q G ≤
        c * Ch02.LambdaSq (originCube d 0) s q F + C) :
    unitCubeBigLambda s q b ≤ c * unitCubeBigLambda s q a + C := by
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  obtain ⟨G, hG⟩ := exists_compatibleTriadicCoeffFamily b
  rw [unitCubeBigLambda_characterization s q a F hF,
    unitCubeBigLambda_characterization s q b G hG]
  exact hfam F G hF hG

end

end Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
