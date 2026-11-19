/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.FinitelyGeneratedDiagrams
public import LeanPool.GrothendieckVanishing.GeneratedSubsheaf
public import Mathlib.Topology.NoetherianSpace
import LeanPool.GrothendieckVanishing.PresheafFilteredColimit
import Mathlib.Algebra.Category.Grp.AB

/-!
# Finitely generated vanishing reduction

On a Noetherian space, every sheaf is the filtered colimit of its finitely generated
subsheaves, and sheaf cohomology commutes with filtered colimits. Combining the two
reduces vanishing of `Hⁿ` for arbitrary sheaves to vanishing for finitely generated ones.
This file packages that reduction; together with the Noetherian-shrinking step, it
underlies the irreducible positive-dimensional case of Grothendieck vanishing.

## Main definitions

* `finsetGenFunctor` — the filtered diagram of finitely generated subsheaves.
* `finsetGenCocone`, `finsetGenCoconeIsColimit` — exhibits `K` as the colimit.

## Main results

* `cohomology_vanishing_of_finitelyGenerated_vanishing` — vanishing for f.g. subsheaves
  propagates to the whole sheaf via the filtered-colimit comparison.
* `finsetGeneratedSheaf_vanishing` — `Finset.induction` reducing vanishing for finitely
  generated subsheaves to vanishing for the epi-images of `zeroOutsideInt V`.
* `directLimit_cohomology_vanishing` — composes both above into the headline reduction.

The `isFlasque_filtered_colimit` and `sheafHPreservesFilteredColimits` building blocks
live in the `PresheafFilteredColimit` modules.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- **Hartshorne III, Ex. 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Uses the filtered-colimit comparison isomorphism
    for the diagram of finitely generated subsheaves and transports zero across it. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hfg : ∀ (S : Finset
        (TopCat.Presheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m)) :
    Subsingleton (Sheaf.H (TopCat.Presheaf.sheafOfIsSheaf hK) m) := by
  have hZeroDiagram : IsZero (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m) := by
    refine Functor.isZero _ ?_
    intro S
    have : Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := hfg S
    change IsZero
      (AddCommGrpCat.of (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m))
    exact AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m))
  have hZeroColim :
      IsZero (colimit (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m)) :=
    (colimit.isColimit _).isZero_pt hZeroDiagram
  have hZeroTarget :
      IsZero (AddCommGrpCat.of
        (Sheaf.H (TopCat.Presheaf.sheafOfIsSheaf hK) m)) := by
    change IsZero (AddCommGrpCat.of (Sheaf.H (finsetGenCocone hK).pt m))
    exact IsZero.of_iso hZeroColim
      (sheafHPreservesFilteredColimits
        (Y' := finsetGenFunctor hK)
        (c' := finsetGenCocone hK)
        (hc' := finsetGenCoconeIsColimit hK)
        m).symm
  simpa using AddCommGrpCat.subsingleton_of_isZero hZeroTarget

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (TopCat.Presheaf.sheafOfIsSheaf hG) m)) :
    Subsingleton (Sheaf.H (TopCat.Presheaf.sheafOfIsSheaf hK) m) :=
  cohomology_vanishing_of_finitelyGenerated_vanishing hK m
    (fun S _ ↦ finsetGeneratedSheaf_vanishing hK m hzero S)
