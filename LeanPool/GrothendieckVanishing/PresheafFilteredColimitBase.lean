/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Mathlib.Topology.NoetherianSpace
public import LeanPool.GrothendieckVanishing.CohomologyAPI
import LeanPool.GrothendieckVanishing.PresheafFilteredColimitGeneral

/-!
# Basic filtered-colimit constructions for sheaf cohomology

The forgetful functor to presheaves creates filtered colimits on a Noetherian
space. Every cocone induces a comparison from the colimit of cohomology groups.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- On a Noetherian space, a filtered colimit cocone of presheaves is a sheaf if all
    diagram objects are sheaves. Proof: compactness reduces the sheaf condition to finite
    covers, then filtered colimit merging passes from per-piece data to glued data. -/
theorem isSheaf_of_isColimit_of_isSheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ j, TopCat.Presheaf.IsSheaf (P.obj j))
    (c : Cocone P) (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (↑(iSup U) : Set X)).elim_finite_subcover
    (fun i ↦ ↑(U i)) (fun i ↦ (U i).isOpen) (by simp [Opens.coe_iSup])
  have hsup_le : iSup U ≤ ⨆ i ∈ t, U i := by
    rw [IsConcreteLE.le_iff]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hi, hxi⟩⟩
  exact colimit_existsUnique_gluing_of_compatible_finite_subcover
    P hP hc U sf hcompat hsup_le

/-- On a Noetherian space, `sheafToPresheaf` creates filtered colimits of sheaves by
    applying `isSheaf_of_isColimit_of_isSheaf` to the underlying presheaf diagram. -/
@[implicit_reducible]
noncomputable def createsFilteredColimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    CreatesColimit Y' (sheafToPresheaf _ _) :=
  Sheaf.createsColimitOfIsSheaf Y' (fun c hc ↦
    isSheaf_of_isColimit_of_isSheaf
      (P := Y' ⋙ sheafToPresheaf _ _)
      (hP := fun j ↦ (Y'.obj j).property)
      (c := c) (hc := hc))

/-- The canonical comparison morphism `colim H^n(F_j) ⟶ H^n(colim F_j)` induced by a cocone. -/
noncomputable def sheafHFilteredColimitComparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ⟶
      (sheafCohomologyFunctor X n).obj c'.pt :=
  colimit.desc _ ((sheafCohomologyFunctor X n).mapCocone c')
