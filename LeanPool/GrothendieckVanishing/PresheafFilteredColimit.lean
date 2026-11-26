/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitCore
public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitZero
public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitDegreeOne
import Mathlib.Algebra.Category.Grp.AB

/-!
# Degree-one and higher filtered-colimit comparisons

The degree-`1` and higher comparison arguments showing that sheaf cohomology commutes
with filtered colimits on Noetherian spaces, building on the presheaf-boundary and
successor-stage infrastructure in `PresheafFilteredColimitCore`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

attribute [local implicit_reducible]
  sheafHFilteredColimitSuccInjCocone sheafHFilteredColimitSuccShortComplex
  sheafHFilteredColimitSuccQuotient sheafHFilteredColimitSuccQuotientCocone
  sheafHFilteredColimitSuccShiftCodomainIso sheafHFilteredColimitComparison

section FilteredColimitComparison

variable {X : TopCat.{u}} [NoetherianSpace X]
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable (csh : Cocone Ysh) (hcsh : IsColimit csh)
include hcsh

private theorem sheafH_filtered_colimit_comparison_isIso_zero :
    IsIso (sheafHFilteredColimitComparison Ysh 0 csh) := by
  rw [← sheafH_filtered_colimit_comparison_zero_iso_hom
    (Ysh := Ysh) (csh := csh) (hcsh := hcsh)]
  infer_instance

private theorem sheafH_filtered_colimit_comparison_isIso_one :
    IsIso (sheafHFilteredColimitComparison Ysh 1 csh) := by
  rw [← sheafH_filtered_colimit_comparison_one_iso_hom
    (Ysh := Ysh) (csh := csh) (hcsh := hcsh)]
  infer_instance

private theorem sheafH_filtered_colimit_comparison_isIso_succ_succ
    (m : ℕ)
    (ih :
      ∀ {J'' : Type u} [SmallCategory J''] [IsFiltered J'']
        (Ysh : J'' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
        (csh : Cocone Ysh) (_ : IsColimit csh),
        IsIso (sheafHFilteredColimitComparison Ysh (m + 1) csh)) :
    IsIso (sheafHFilteredColimitComparison Ysh (m + 1 + 1) csh) := by
  let : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafHFilteredColimitSuccInj Ysh
  let injCocone := sheafHFilteredColimitSuccInjCocone Ysh
  let qCocone := sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh
  have :
      IsIso
        (sheafHFilteredColimitComparison
          (sheafHFilteredColimitSuccQuotient Ysh) (m + 1) qCocone) :=
    ih
      (Ysh := sheafHFilteredColimitSuccQuotient Ysh) (csh := qCocone)
      (sheafHFilteredColimitSuccQuotientCoconeIsColimit Ysh csh hcsh)
  have hInj (j) : Injective (Inj.obj j) := by
    exact sheafH_filtered_colimit_succ_inj_obj_isInjective (Y' := Ysh) j
  have h_mid (r) (j) : Subsingleton (Sheaf.H (Inj.obj j) (r + 1)) :=
    @sheafH_subsingleton_of_injective
      (Opens X) _ (Opens.grothendieckTopology X) _ _ (Inj.obj j) (hInj j) r
  have h_colim (r) : Subsingleton (Sheaf.H injCocone.pt (r + 1)) := by
    simpa [injCocone] using sheafH_filtered_colimit_succ_inj_subsingleton (Y' := Ysh) r hInj
  let domainIso :=
    sheafHFilteredColimitSuccShiftDomainIso Ysh (m + 1) (h_mid m) (h_mid (m + 1))
  let codomainIso :=
    sheafHFilteredColimitSuccShiftCodomainIso
      Ysh csh hcsh (m + 1) (h_colim m) (h_colim (m + 1))
  exact IsIso.of_isIso_fac_left (by
    simpa [domainIso, codomainIso, qCocone] using
      sheafH_filtered_colimit_comparison_succ_compatibility
        (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (n := m + 1)
        (h_mid m) (h_mid (m + 1)) (h_colim m) (h_colim (m + 1)))

end FilteredColimitComparison

private theorem sheafH_filtered_colimit_comparison_isIso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh)
    (n : ℕ) :
    IsIso (sheafHFilteredColimitComparison Ysh n csh) := by
  let P : ℕ → Prop := fun n ↦
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (csh : Cocone Ysh) (hcsh : IsColimit csh),
      IsIso (sheafHFilteredColimitComparison Ysh n csh)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro J' _ _ Ysh csh hcsh
        exact sheafH_filtered_colimit_comparison_isIso_zero Ysh csh hcsh
    | succ n ih =>
        cases n with
        | zero =>
            intro J' _ _ Ysh csh hcsh
            exact sheafH_filtered_colimit_comparison_isIso_one Ysh csh hcsh
        | succ m =>
            intro J' _ _ Ysh csh hcsh
            exact sheafH_filtered_colimit_comparison_isIso_succ_succ
              (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (m := m) ih
  exact hP n Ysh csh hcsh

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces:
    the canonical comparison `colim H^n(F_j) ≅ H^n(colim F_j)` is an isomorphism. -/
noncomputable def sheafHPreservesFilteredColimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ) :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ≅
      (sheafCohomologyFunctor X n).obj c'.pt := by
  haveI : IsIso (sheafHFilteredColimitComparison Y' n c') := by
    exact sheafH_filtered_colimit_comparison_isIso Y' c' hc' n
  exact asIso (sheafHFilteredColimitComparison Y' n c')
