/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Monad.Monadicity

/-!
# Beck's monadicity theorem as a characterization

Mathlib proves the sufficient direction of Beck's monadicity theorem
(`CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`) and its
dual for comonads. This file adds the converse, so that both theorems read as equivalences.

## Main statements

* `CategoryTheory.Monad.isEquivalence_comparison_iff`: for `adj : F ⊣ G`, the comparison functor
  is an equivalence iff `G` reflects isomorphisms and, for every `G`-split pair, the coequalizer
  exists and is preserved by `G`;
* `CategoryTheory.Comonad.isEquivalence_comparison_iff`: the dual statement for comonads;
* the instances `reflectsIsomorphisms_of_monadicRightAdjoint` and
  `reflectsIsomorphisms_of_comonadicLeftAdjoint`.

## References

* Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VI.7: a variant of
  Theorem VI.7.1, stated for an equivalence rather than an isomorphism of categories
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

namespace Comonad

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- A comonadic left adjoint reflects isomorphisms. -/
instance (priority := 100) reflectsIsomorphisms_of_comonadicLeftAdjoint
    [ComonadicLeftAdjoint F] : F.ReflectsIsomorphisms where
  reflects {X Y} φ hφ := by
    let adj := comonadicAdjunction F
    have : IsIso ((Comonad.forget adj.toComonad).map ((Comonad.comparison adj).map φ)) := hφ
    have := isIso_of_reflects_iso ((Comonad.comparison adj).map φ) (Comonad.forget _)
    exact isIso_of_fully_faithful (Comonad.comparison adj) φ

/-- **Beck's comonadicity theorem**, in the form of a characterization: the comparison functor
of `adj : F ⊣ G` is an equivalence if and only if `F` reflects isomorphisms and, for every
`F`-cosplit pair `u, v`, the equalizer of `u` and `v` exists and is preserved by `F`. -/
theorem isEquivalence_comparison_iff : (Comonad.comparison adj).IsEquivalence ↔
    F.ReflectsIsomorphisms ∧ ∀ ⦃X Y : C⦄ (u v : X ⟶ Y), F.IsCosplitPair u v →
      HasEqualizer u v ∧ PreservesLimit (parallelPair u v) F := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ ?_⟩
  · let _ : ComonadicLeftAdjoint F := ⟨G, adj, h⟩
    refine ⟨inferInstance, fun X Y u v _ ↦ ?_⟩
    have := createsFSplitEqualizersOfComonadic (F := F) u v
    have : HasLimit (parallelPair u v ⋙ F) :=
      hasLimit_of_iso (F := parallelPair (F.map u) (F.map v))
        (diagramIsoParallelPair (parallelPair u v ⋙ F)).symm
    exact ⟨hasLimit_of_created (parallelPair u v) F, inferInstance⟩
  · have : HasEqualizerOfIsCosplitPair F := ⟨fun u v _ ↦ (h u v inferInstance).1⟩
    have : PreservesLimitOfIsCosplitPair F := ⟨fun u v _ ↦ (h u v inferInstance).2⟩
    exact (comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj).eqv

end Comonad

namespace Monad

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

/-- A monadic right adjoint reflects isomorphisms. -/
instance (priority := 100) reflectsIsomorphisms_of_monadicRightAdjoint
    [MonadicRightAdjoint G] : G.ReflectsIsomorphisms where
  reflects {X Y} φ hφ := by
    let adj := monadicAdjunction G
    have : IsIso ((Monad.forget adj.toMonad).map ((Monad.comparison adj).map φ)) := hφ
    have := isIso_of_reflects_iso ((Monad.comparison adj).map φ) (Monad.forget _)
    exact isIso_of_fully_faithful (Monad.comparison adj) φ

/-- **Beck's monadicity theorem**, in the form of a characterization: the comparison functor
of `adj : F ⊣ G` is an equivalence if and only if `G` reflects isomorphisms and, for every
`G`-split pair `u, v`, the coequalizer of `u` and `v` exists and is preserved by `G`. -/
theorem isEquivalence_comparison_iff : (Monad.comparison adj).IsEquivalence ↔
    G.ReflectsIsomorphisms ∧ ∀ ⦃X Y : D⦄ (u v : X ⟶ Y), G.IsSplitPair u v →
      HasCoequalizer u v ∧ PreservesColimit (parallelPair u v) G := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ ?_⟩
  · let _ : MonadicRightAdjoint G := ⟨F, adj, h⟩
    refine ⟨inferInstance, fun X Y u v _ ↦ ?_⟩
    have := createsGSplitCoequalizersOfMonadic G u v
    have : HasColimit (parallelPair u v ⋙ G) :=
      hasColimit_of_iso (F := parallelPair (G.map u) (G.map v)) (diagramIsoParallelPair _)
    exact ⟨hasColimit_of_created (parallelPair u v) G, inferInstance⟩
  · have : HasCoequalizerOfIsSplitPair G := ⟨fun u v _ ↦ (h u v inferInstance).1⟩
    have : PreservesColimitOfIsSplitPair G := ⟨fun u v _ ↦ (h u v inferInstance).2⟩
    exact (monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms adj).eqv

end Monad

end CategoryTheory
