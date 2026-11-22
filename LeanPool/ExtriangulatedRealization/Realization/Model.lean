/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Functor
public import LeanPool.ExtriangulatedRealization.CD.Subcategory

/-!
# `CDJ` is a model of `C_J`

The inclusion of the intervals with index in `J` induces a fully faithful functor
`CDJ J D ⥤ CD D` whose essential image is `subcatJ D J`, hence an equivalence
`CDJ J D ≌ (labelsIn D J).FullSubcategory`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (J : Set I)
  (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The inclusion `IndJ J D ⥤ IndCat D`. -/
noncomputable abbrev indJIncl : IndJ J D ⥤ IndCat D :=
  OnePointExtension.map (LabelInJ (k := k) J).ι

/-- The inclusion `CDJ J D ⥤ CD D`. -/
noncomputable abbrev cdjIncl : CDJ J D ⥤ CD D := (indJIncl J D).mapMat_

variable {J D}

lemma labelIn_indJIncl (x : IndJ J D) : labelIn J ((indJIncl J D).obj x) := by
  rcases x with _ | ⟨_ | i | i, h⟩
  · trivial
  · trivial
  · exact h
  · exact h

/-- A label with index in `J`, as an object of `IndJ J D`. -/
def toIndJ : ∀ l : IndCat D, labelIn J l → IndJ J D
  | none, _ => none
  | some l, h => some ⟨l, h⟩

lemma indJIncl_obj_toIndJ (l : IndCat D) (h : labelIn J l) :
    (indJIncl J D).obj (toIndJ l h) = l := by
  rcases l with _ | l
  · rfl
  · rfl

variable (J D)

/-- The lift of `cdjIncl` to `C_J`. -/
noncomputable def cdjLift : CDJ J D ⥤ (labelsIn D J).FullSubcategory :=
  (labelsIn D J).lift (cdjIncl J D) fun M i => labelIn_indJIncl (M.X i)

instance : (cdjLift J D).EssSurj where
  mem_essImage M := by
    refine ⟨⟨M.obj.ι, fun i => toIndJ (M.obj.X i) (M.property i)⟩, ⟨eqToIso ?_⟩⟩
    apply ObjectProperty.FullSubcategory.ext
    cases M with | mk obj h => ?_
    cases obj with | mk ι X => ?_
    change Mat_.mk ι (fun i => (indJIncl J D).obj (toIndJ (X i) (h i))) = Mat_.mk ι X
    congr 1
    funext i
    exact indJIncl_obj_toIndJ (X i) (h i)

instance : (indJIncl J D).Additive := inferInstanceAs (OnePointExtension.map _).Additive

instance : (cdjIncl J D).Additive := inferInstanceAs (indJIncl J D).mapMat_.Additive

instance : (cdjLift J D).Additive where
  map_add {X Y f g} := (labelsIn D J).ι.map_injective (by
    rw [(labelsIn D J).ι.map_add]
    exact (cdjIncl J D).map_add)

instance : (cdjLift J D).Full :=
  Functor.Full.of_comp_faithful_iso ((labelsIn D J).liftCompιIso _ _)

instance : (cdjLift J D).Faithful :=
  Functor.Faithful.of_comp_iso ((labelsIn D J).liftCompιIso _ _)

/-- `CDJ J D ≌ C_J`. -/
noncomputable def cdjEquiv : CDJ J D ≌ (labelsIn D J).FullSubcategory :=
  have : (cdjLift J D).IsEquivalence := {}
  (cdjLift J D).asEquivalence

end ExtriangulatedRealization
