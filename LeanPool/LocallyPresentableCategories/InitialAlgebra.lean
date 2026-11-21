/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Adámek's initial algebra theorem

For an endofunctor `F` of a category with an initial object `0`, the initial chain is
`0 ⟶ F 0 ⟶ F² 0 ⟶ ⋯`. If this chain has a colimit `L` and `F` preserves it, then `F L` is the
colimit of the shifted chain, which gives a structure map `F L ⟶ L`; we prove that the resulting
`F`-algebra is initial (`exists_isInitial_algebra_colimit_initialChain`, roadmap 4.4; Adámek 1974,
*Free algebras and automata realizations in the language of categories*, §I).

The transfinite version (an accessible endofunctor of a locally presentable category has an
initial algebra) is not formalised here.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits

universe v u

section InitialChain

variable {C : Type u} [Category.{v} C] [HasInitial C] (F : C ⥤ C)

/-- The objects `Fⁿ 0` of the initial chain of `F`. -/
noncomputable def initialChainObj : ℕ → C
  | 0 => ⊥_ C
  | n + 1 => F.obj (initialChainObj n)

/-- The maps `Fⁿ 0 ⟶ Fⁿ⁺¹ 0` of the initial chain: `initial.to` first, then `F.map` of the
previous map. -/
noncomputable def initialChainMap : (n : ℕ) → initialChainObj F n ⟶ initialChainObj F (n + 1)
  | 0 => initial.to _
  | n + 1 => F.map (initialChainMap n)

/-- The initial chain `0 ⟶ F 0 ⟶ F² 0 ⟶ ⋯` of an endofunctor. -/
noncomputable def initialChain : ℕ ⥤ C :=
  Functor.ofSequence (initialChainMap F)

@[simp]
lemma initialChain_obj (n : ℕ) : (initialChain F).obj n = initialChainObj F n := rfl

lemma initialChain_map_succ (n : ℕ) :
    (initialChain F).map (homOfLE (Nat.le_add_right n 1)) = initialChainMap F n :=
  Functor.ofSequence_map_homOfLE_succ _ n

variable {F}

/-- The canonical maps `Fⁿ 0 ⟶ A` to the carrier of an `F`-algebra. -/
noncomputable def initialChainToAlgebra (A : Endofunctor.Algebra F) :
    (n : ℕ) → initialChainObj F n ⟶ A.a
  | 0 => initial.to _
  | n + 1 => F.map (initialChainToAlgebra A n) ≫ A.str

lemma initialChainMap_comp_initialChainToAlgebra (A : Endofunctor.Algebra F) (n : ℕ) :
    initialChainMap F n ≫ initialChainToAlgebra A (n + 1) = initialChainToAlgebra A n := by
  induction n with
  | zero => exact initial.hom_ext _ _
  | succ n ih =>
    change F.map (initialChainMap F n) ≫ F.map (initialChainToAlgebra A (n + 1)) ≫ A.str =
      F.map (initialChainToAlgebra A n) ≫ A.str
    rw [← F.map_comp_assoc, ih]

/-- The cocone over the initial chain with point the carrier of an `F`-algebra. -/
noncomputable def initialChainCocone (A : Endofunctor.Algebra F) : Cocone (initialChain F) where
  pt := A.a
  ι := NatTrans.ofSequence (initialChainToAlgebra A) (fun n ↦ by
    exact (congrArg (· ≫ _) (initialChain_map_succ F n)).trans
      ((initialChainMap_comp_initialChainToAlgebra A n).trans (Category.comp_id _).symm))

variable [HasColimit (initialChain F)]

/-- The cocone over the shifted chain `initialChain F ⋙ F` with point `colimit (initialChain F)`.
-/
noncomputable def shiftedCocone : Cocone (initialChain F ⋙ F) where
  pt := colimit (initialChain F)
  ι := NatTrans.ofSequence (fun n ↦ colimit.ι (initialChain F) (n + 1)) (fun n ↦ by
    have := colimit.w (initialChain F) (homOfLE (Nat.le_add_right (n + 1) 1))
    refine Eq.trans ?_ (this.trans (Category.comp_id _).symm)
    exact congrArg (· ≫ _) ((congrArg F.map (initialChain_map_succ F n)).trans
      (initialChain_map_succ F (n + 1)).symm))

variable [PreservesColimit (initialChain F) F]

/-- The structure map `F L ⟶ L` on the colimit `L` of the initial chain. -/
noncomputable def colimitInitialChainStr : F.obj (colimit (initialChain F)) ⟶
    colimit (initialChain F) :=
  (isColimitOfPreserves F (colimit.isColimit (initialChain F))).desc shiftedCocone

@[reassoc]
lemma map_ι_colimitInitialChainStr (n : ℕ) :
    F.map (colimit.ι (initialChain F) n) ≫ colimitInitialChainStr =
      colimit.ι (initialChain F) (n + 1) :=
  (isColimitOfPreserves F (colimit.isColimit (initialChain F))).fac shiftedCocone n

/-- The `F`-algebra structure on the colimit of the initial chain. -/
noncomputable abbrev colimitInitialChainAlgebra : Endofunctor.Algebra F :=
  ⟨colimit (initialChain F), colimitInitialChainStr⟩

/-- The canonical map from the colimit of the initial chain to an `F`-algebra. -/
noncomputable def descAlgebra (A : Endofunctor.Algebra F) : colimit (initialChain F) ⟶ A.a :=
  colimit.desc _ (initialChainCocone A)

omit [PreservesColimit (initialChain F) F] in
@[reassoc]
lemma ι_descAlgebra (A : Endofunctor.Algebra F) (n : ℕ) :
    colimit.ι (initialChain F) n ≫ descAlgebra A = initialChainToAlgebra A n :=
  colimit.ι_desc _ _

/-- The colimit of the initial chain, when preserved by `F`, is an initial `F`-algebra. -/
noncomputable def isInitialColimitInitialChainAlgebra :
    IsInitial (colimitInitialChainAlgebra (F := F)) := by
  refine IsInitial.ofUniqueHom (fun A ↦
    { f := descAlgebra A
      h := (isColimitOfPreserves F (colimit.isColimit (initialChain F))).hom_ext fun n ↦ by
        change F.map (colimit.ι (initialChain F) n) ≫ F.map (descAlgebra A) ≫ A.str =
          F.map (colimit.ι (initialChain F) n) ≫ colimitInitialChainStr ≫ descAlgebra A
        rw [map_ι_colimitInitialChainStr_assoc, ← F.map_comp_assoc, ι_descAlgebra]
        exact (ι_descAlgebra A (n + 1)).symm }) (fun A g ↦ ?_)
  apply Endofunctor.Algebra.Hom.ext
  change g.f = descAlgebra A
  refine colimit.hom_ext fun n ↦ ?_
  rw [ι_descAlgebra]
  induction n with
  | zero => exact initial.hom_ext _ _
  | succ n ih =>
    have h : F.map (colimit.ι (initialChain F) n) ≫ colimitInitialChainStr ≫ g.f =
        F.map (initialChainToAlgebra A n) ≫ A.str :=
      (congrArg (F.map (colimit.ι (initialChain F) n) ≫ ·) g.h.symm).trans
        ((F.map_comp_assoc _ _ _).symm.trans
          (congrArg (fun x : (initialChain F).obj n ⟶ A.a ↦ F.map x ≫ A.str) ih))
    exact (congrArg (· ≫ g.f) (map_ι_colimitInitialChainStr n).symm).trans
      ((Category.assoc _ _ _).trans h)

/-- Roadmap 4.4. If `F` preserves the colimit of its initial chain, that colimit carries an
initial `F`-algebra structure (Adámek 1974, §I). -/
theorem exists_isInitial_algebra_colimit_initialChain :
    ∃ str : F.obj (colimit (initialChain F)) ⟶ colimit (initialChain F),
      Nonempty (IsInitial (Endofunctor.Algebra.mk (colimit (initialChain F)) str)) :=
  ⟨colimitInitialChainStr, ⟨isInitialColimitInitialChainAlgebra⟩⟩

end InitialChain

end LeanPool.LocallyPresentableCategories
