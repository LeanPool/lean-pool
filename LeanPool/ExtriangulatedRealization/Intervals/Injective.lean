/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Maps
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Injectivity of the intervals `k_{[*,t]}` (Lemma 2.1, Step 1)

For `t ∈ I_*` and a representation `M`, evaluation at `t` identifies morphisms
`M ⟶ k_{[*,t]}` with linear functionals on `M(t)`: a functional `λ` gives the morphism with
components `λ ∘ M(s ≤ t)` for `s ≤ t`. Since evaluation and duality of vector spaces are exact,
`k_{[*,t]}` is injective; in particular `P i` and `Y` are injective in `Rep k I`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- The interval `k_{[*,t]}`. -/
noncomputable abbrev lowerRep (t : WithBot I) : Rep k I := intervalRep (Set.Iic t)

/-- The morphism `M ⟶ k_{[*,t]}` attached to a functional on `M(t)`. -/
noncomputable def toLower (M : Rep k I) (t : WithBot I) (μ : M.obj t →ₗ[k] k) :
    M ⟶ lowerRep (k := k) t where
  app s := ModuleCat.ofHom
    { toFun := fun m x => μ ((M.map (homOfLE (show s ≤ t from x.2))).hom m)
      map_add' := fun m m' => by funext x; simp
      map_smul' := fun r m => by funext x; simp }
  naturality s s' f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext x
    have hs : s ∈ Set.Iic t := (leOfHom f).trans x.2
    rw [show f = homOfLE (leOfHom f) from Subsingleton.elim _ _]
    refine Eq.trans ?_ (intervalRep_map_apply (k := k) (U := Set.Iic t) (leOfHom f) _ x).symm
    refine Eq.trans ?_ (dite_eq_left hs).symm
    change μ ((M.map (homOfLE (show s' ≤ t from x.2))).hom ((M.map (homOfLE _)).hom m)) =
      μ ((M.map (homOfLE (show s ≤ t from hs))).hom m)
    rw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl

/-- The functional on `M(t)` attached to a morphism `M ⟶ k_{[*,t]}`. -/
noncomputable def fromLower (M : Rep k I) (t : WithBot I) (g : M ⟶ lowerRep (k := k) t) :
    M.obj t →ₗ[k] k where
  toFun m := (g.app t).hom m ⟨(), show t ≤ t from le_rfl⟩
  map_add' m m' := by rw [map_add]; rfl
  map_smul' r m := by rw [map_smul]; rfl

lemma toLower_fromLower (M : Rep k I) (t : WithBot I) (g : M ⟶ lowerRep (k := k) t) :
    toLower M t (fromLower M t g) = g := by
  apply NatTrans.ext
  funext s
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  funext x
  have hst : s ≤ t := x.2
  have h := congrArg (fun φ => φ.hom m ⟨(), show t ≤ t from le_rfl⟩) (g.naturality (homOfLE hst))
  change (g.app t).hom ((M.map (homOfLE hst)).hom m) ⟨(), show t ≤ t from le_rfl⟩ =
    (g.app s).hom m x
  refine h.trans ?_
  exact (intervalRep_map_apply (k := k) (U := Set.Iic t) hst ((g.app s).hom m)
    ⟨(), show t ≤ t from le_rfl⟩).trans (dite_eq_left x.2)

lemma lowerRep_injective (t : WithBot I) : Injective (lowerRep (k := k) t) where
  factors {X Y} g f hf := by
    have hinj : Function.Injective (f.app t).hom := by
      rw [← ModuleCat.mono_iff_injective]
      exact (NatTrans.mono_iff_mono_app f).mp hf t
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (f.app t).hom
      (LinearMap.ker_eq_bot.mpr hinj)
    refine ⟨toLower Y t (fromLower X t g ∘ₗ r), ?_⟩
    conv_rhs => rw [← toLower_fromLower X t g]
    apply NatTrans.ext
    funext s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext x
    have hst : s ≤ t := x.2
    change (fromLower X t g ∘ₗ r) ((Y.map (homOfLE hst)).hom ((f.app s).hom m)) =
      fromLower X t g ((X.map (homOfLE hst)).hom m)
    have hnat := congrArg (fun φ => φ.hom m) (f.naturality (homOfLE hst))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [← hnat, LinearMap.comp_apply, ← LinearMap.comp_apply r, hr, LinearMap.id_apply]

lemma injective_P (i : I) : Injective ((P i).rep k) := lowerRep_injective (i : WithBot I)

lemma injective_Y : Injective ((Y (I := I)).rep k) := lowerRep_injective (⊥ : WithBot I)

end ExtriangulatedRealization
