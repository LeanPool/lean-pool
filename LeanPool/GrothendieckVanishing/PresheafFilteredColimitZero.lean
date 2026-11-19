/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitBase

/-!
# Degree-zero filtered-colimit comparison

The comparison in degree zero follows from the natural identification with global sections.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

attribute [local implicit_reducible] sheafHFilteredColimitComparison

/-- The global-sections functor used in the degree-`1` filtered-colimit boundary
construction. -/
@[implicit_reducible]
noncomputable def sheafHFilteredColimitH1SectionsFunctor
    {X : TopCat.{u}} :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

-- Transport the comparison along a natural isomorphism before specializing to
-- sheaves, so the categorical rewrites do not elaborate the cohomology groups.
private theorem colimit_transport_comparison {J C D : Type*}
    [Category J] [Category C] [Category D] {F : J ⥤ C} {H S : C ⥤ D}
    (e : H ≅ S) (c : Cocone F) [HasColimit (F ⋙ H)] [HasColimit (F ⋙ S)]
    (hc : IsColimit (S.mapCocone c)) :
    ((HasColimit.isoOfNatIso (Functor.isoWhiskerLeft F e) ≪≫
        (colimit.isColimit (F ⋙ S)).coconePointUniqueUpToIso hc) ≪≫
      (e.app c.pt).symm).hom = colimit.desc (F ⋙ H) (H.mapCocone c) := by
  apply colimit.hom_ext
  intro j
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, HasColimit.ι_isoOfNatIso_hom_assoc,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc, colimit.ι_desc]
  change e.hom.app (F.obj j) ≫ S.map (c.ι.app j) ≫ e.inv.app c.pt = H.map (c.ι.app j)
  rw [← Category.assoc, ← e.hom.naturality, Category.assoc]
  change H.map (c.ι.app j) ≫ e.hom.app c.pt ≫ e.inv.app c.pt = H.map (c.ι.app j)
  rw [Iso.hom_inv_id_app]
  exact Category.comp_id _

section FilteredColimitComparison

variable {X : TopCat.{u}} [NoetherianSpace X]
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable (csh : Cocone Ysh) (hcsh : IsColimit csh)
include hcsh

/-- The degree-`0` comparison up to identifying `H⁰` with global sections. -/
noncomputable def sheafHFilteredColimitZeroSectionsIso :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 0) ≅
      (sheafHFilteredColimitH1SectionsFunctor (X := X)).obj csh.pt := by
  let sectionsFunctor := sheafHFilteredColimitH1SectionsFunctor (X := X)
  let h0Iso :
      Ysh ⋙ sheafCohomologyFunctor X 0 ≅ Ysh ⋙ sectionsFunctor :=
    Functor.isoWhiskerLeft Ysh (sheafH0NatIsoSections (X := X))
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  haveI : CreatesColimit Ysh toPsh :=
    createsFilteredColimit Ysh
  haveI hPres : PreservesColimit Ysh toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit Ysh toPsh
  have hc_psh : IsColimit (toPsh.mapCocone csh) :=
    (hPres.preserves hcsh).some
  have hc_sections : IsColimit (sectionsFunctor.mapCocone csh) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
  exact
    HasColimit.isoOfNatIso h0Iso ≪≫
      (colimit.isColimit (Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections

/-- The degree-`0` filtered-colimit comparison isomorphism, obtained from global sections. -/
noncomputable def sheafHFilteredColimitComparisonZeroIso :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 0) ≅
      (sheafCohomologyFunctor X 0).obj csh.pt :=
  sheafHFilteredColimitZeroSectionsIso (Ysh := Ysh) csh hcsh ≪≫
    ((sheafH0EquivSections csh.pt).toAddCommGrpIso).symm

@[simp] theorem sheafH_filtered_colimit_comparison_zero_iso_hom :
    (sheafHFilteredColimitComparisonZeroIso
      (Ysh := Ysh) (csh := csh) (hcsh := hcsh)).hom =
      sheafHFilteredColimitComparison Ysh 0 csh := by
  let sectionsFunctor := sheafHFilteredColimitH1SectionsFunctor (X := X)
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : CreatesColimit Ysh toPsh :=
    createsFilteredColimit Ysh
  have hPres : PreservesColimit Ysh toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit Ysh toPsh
  have hc_psh : IsColimit (toPsh.mapCocone csh) :=
    (hPres.preserves hcsh).some
  have hc_sections : IsColimit (sectionsFunctor.mapCocone csh) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
  exact colimit_transport_comparison (H := sheafCohomologyFunctor X 0) (S := sectionsFunctor)
    (sheafH0NatIsoSections (X := X)) csh hc_sections

end FilteredColimitComparison
