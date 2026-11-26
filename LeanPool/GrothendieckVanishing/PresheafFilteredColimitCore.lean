/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Mathlib.Topology.NoetherianSpace
public import LeanPool.GrothendieckVanishing.FlasqueVanishing
public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitBase
public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitDiagrams
public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitVanishing

/-!
# Successor comparison for filtered sheaf diagrams

The stage and colimit dimension shifts give a commutative square for the
comparison maps in successive degrees.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

-- Prove the colimit square once for arbitrary cocones. Specializing the square to
-- the cohomology diagrams avoids unfolding their isomorphisms in each rewrite.
private theorem colimit_isoOfNatIso_hom_desc {J C : Type*} [Category J] [Category C]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G] (e : F ≅ G)
    (cF : Cocone F) (cG : Cocone G) (f : cF.pt ⟶ cG.pt)
    (comm : ∀ j, e.hom.app j ≫ cG.ι.app j = cF.ι.app j ≫ f) :
    (HasColimit.isoOfNatIso e).hom ≫ colimit.desc G cG = colimit.desc F cF ≫ f := by
  apply colimit.hom_ext
  intro j
  rw [HasColimit.ι_isoOfNatIso_hom_assoc, colimit.ι_desc, colimit.ι_desc_assoc, comm]

/-- Successor-step compatibility for the filtered-colimit comparison map: whenever the
associated sheaf diagram and its colimit have vanishing injective-replacement cohomology in
degrees `n` and `n + 1`, the degree-`n + 1` comparison is conjugate to the degree-`n`
comparison for the quotient diagram. -/
theorem sheafH_filtered_colimit_comparison_succ_compatibility
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh)
    (n : ℕ)
    (h_mid_n : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafHFilteredColimitSuccInj Ysh).obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafHFilteredColimitSuccInj Ysh).obj j) (n + 1)))
    (h_colim_n :
      Subsingleton (Sheaf.H
        (sheafHFilteredColimitSuccInjCocone Ysh).pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H
        (sheafHFilteredColimitSuccInjCocone Ysh).pt (n + 1))) :
    (sheafHFilteredColimitSuccShiftDomainIso Ysh n h_mid_n h_mid_succ).hom ≫
        sheafHFilteredColimitComparison Ysh (n + 1) csh =
      sheafHFilteredColimitComparison (sheafHFilteredColimitSuccQuotient Ysh) n
        (sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh) ≫
      (sheafHFilteredColimitSuccShiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom := by
  let shift := sheafHFilteredColimitSuccShiftNatIso Ysh n h_mid_n h_mid_succ
  let quotientCocone := sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh
  let source := (sheafCohomologyFunctor X n).mapCocone quotientCocone
  let target := (sheafCohomologyFunctor X (n + 1)).mapCocone csh
  let shiftOnColimit :=
    (sheafHFilteredColimitSuccShiftCodomainIso Ysh csh hcsh n h_colim_n h_colim_succ).hom
  refine colimit_isoOfNatIso_hom_desc shift source target shiftOnColimit ?_
  intro j
  let φ := sheafHFilteredColimitSuccStageHom Ysh csh hcsh j
  exact sheafH_succ_iso_of_subsingleton_middle_natural
    (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j)
    (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh)
    φ n (h_mid_n j) (h_mid_succ j) h_colim_n h_colim_succ
