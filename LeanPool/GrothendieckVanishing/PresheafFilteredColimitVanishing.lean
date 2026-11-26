/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.FlasqueVanishing
public import LeanPool.GrothendieckVanishing.PresheafFilteredColimitDiagrams
import Mathlib.Algebra.Category.Grp.AB

/-!
# Vanishing for filtered colimits of injective replacements

Filtered colimits of flasque sheaves on a Noetherian space are flasque.
Apply this to the diagram of injective replacements.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Filtered colimits of flasque sheaves

On Noetherian spaces, `sheafToPresheaf` creates filtered colimits, so restrictions of
filtered colimits are colimits of restrictions. Filtered colimits in `AddCommGrpCat`
preserve surjections, hence stagewise flasque sheaves have flasque colimit. -/

/-- Filtered colimits of stagewise flasque sheaves on Noetherian spaces are flasque. -/
theorem isFlasque_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (hFlasque : ∀ j, IsFlasqueSheaf (F.obj j))
    {c : Cocone F} (hc : IsColimit c) :
    IsFlasqueSheaf c.pt := by
  let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : CreatesColimit F G :=
    createsFilteredColimit F
  have : PreservesColimit F G :=
    preservesColimit_of_createsColimit_and_hasColimit F G
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro b
  have hc_presheaf : IsColimit (G.mapCocone c) :=
    isColimitOfPreserves G hc
  have hc_U := isColimitOfPreserves
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
    hc_presheaf
  obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ hc_U b
  obtain ⟨a₀, ha₀⟩ :=
    (AddCommGrpCat.epi_iff_surjective _).mp ((hFlasque j₀) i) b₀
  refine ⟨ConcreteCategory.hom ((c.ι.app j₀).hom.app (op V)) a₀, ?_⟩
  rw [show ConcreteCategory.hom (c.pt.obj.map i.op)
      (ConcreteCategory.hom ((c.ι.app j₀).hom.app (op V)) a₀) =
    ConcreteCategory.hom ((c.ι.app j₀).hom.app (op U))
      (ConcreteCategory.hom ((F.obj j₀).obj.map i.op) a₀) from
    congrFun (congrArg DFunLike.coe
      (congrArg ConcreteCategory.hom ((c.ι.app j₀).hom.naturality i.op).symm)) a₀]
  rw [ha₀]
  exact hb₀

section SheafHFilteredColimitSucc

variable {X : TopCat.{u}}
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]

attribute [local implicit_reducible] sheafHFilteredColimitSuccInjCocone

/-- The filtered-colimit successor-step vanishing lemma for the injective replacement:
the middle term of the induced short exact sequence has trivial cohomology in degree `n + 1`. -/
theorem sheafH_filtered_colimit_succ_inj_subsingleton
    [NoetherianSpace X] (n : ℕ)
    (hInj : ∀ j, Injective ((sheafHFilteredColimitSuccInj Y').obj j)) :
    Subsingleton (Sheaf.H (sheafHFilteredColimitSuccInjCocone Y').pt (n + 1)) := by
  let Inj := sheafHFilteredColimitSuccInj Y'
  let injCocone := sheafHFilteredColimitSuccInjCocone Y'
  have hFlasque : IsFlasqueSheaf injCocone.pt := fun i ↦ by
    simpa [Inj, injCocone] using
      (isFlasque_filtered_colimit
        (F := Inj)
        (hFlasque := fun j ↦ by
          let : Injective (Inj.obj j) := hInj j
          exact fun {_ _} i ↦ (isFlasque_of_injective (Inj.obj j)) i)
        (c := injCocone)
        (hc := colimit.isColimit Inj)) i
  simpa [injCocone] using
    (sheafH_subsingleton_of_flasque X injCocone.pt hFlasque n)

end SheafHFilteredColimitSucc
