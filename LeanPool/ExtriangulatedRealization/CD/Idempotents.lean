/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Categories.Biproduct
public import LeanPool.ExtriangulatedRealization.Categories.Idempotents
public import LeanPool.ExtriangulatedRealization.Categories.Mat
public import LeanPool.ExtriangulatedRealization.CD.Existence

/-!
# `C(D)` is idempotent complete (Proposition 4.4, Step 1)

Write an object `M` as `bPart M ⊞ xPart M`. Since there are no nonzero morphisms from an object
without copies of `X` to copies of `X`, an idempotent on `M` is triangular, so it splits once
idempotents on `bPart M` and on `xPart M` split.

* On an object `N` without copies of `X`, `ρ` is fully faithful; an idempotent `ρp` splits in
  the abelian category `Rep k I`, its image is a retract of the good representation `ρN`, hence
  good, hence `ρ` of an object `N'` without copies of `X`, and the splitting lifts.
* An object all of whose entries are `X` has endomorphisms the square matrices over `k`, and an
  idempotent matrix factors through its rank.

This replaces the appeal to Krause [Kr, Corollary 4.4] in the manuscript by a direct argument.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Idempotents

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-! ### Objects all of whose entries are `X` -/

/-- The direct sum of copies of `X` indexed by `ι`. -/
abbrev xObj (ι : Type) [Fintype ι] : CD D := ⟨ι, fun _ => indX D⟩

variable {D} in
/-- The matrix of a morphism between direct sums of copies of `X`. -/
def toMatrix {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (f : xObj D ι₁ ⟶ xObj D ι₂) : Matrix ι₁ ι₂ k := fun a b => f a b

/-- The morphism between direct sums of copies of `X` given by a matrix. -/
def ofMatrix {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (P : Matrix ι₁ ι₂ k) : xObj D ι₁ ⟶ xObj D ι₂ := fun a b => P a b

lemma toMatrix_injective {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    : Function.Injective (toMatrix (D := D) (ι₁ := ι₁) (ι₂ := ι₂)) :=
  fun f g h => by
    ext a b
    exact congrFun (congrFun h a) b

lemma toMatrix_ofMatrix {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (P : Matrix ι₁ ι₂ k) : toMatrix (ofMatrix D P) = P := rfl

lemma toMatrix_comp {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂]
    [Fintype ι₃] (f : xObj D ι₁ ⟶ xObj D ι₂)
    (g : xObj D ι₂ ⟶ xObj D ι₃) : toMatrix (f ≫ g) = toMatrix f * toMatrix g := by
  ext a c
  rw [Matrix.mul_apply]
  exact Mat_.comp_apply _ _ _ _

lemma toMatrix_id (ι : Type) [Fintype ι] [DecidableEq ι] :
    toMatrix (𝟙 (xObj D ι)) = (1 : Matrix ι ι k) := by
  ext a c
  by_cases h : a = c
  · subst h
    rw [Matrix.one_apply_eq]
    exact Mat_.id_apply_self _ _
  · rw [Matrix.one_apply_ne h]
    exact Mat_.id_apply_of_ne _ _ _ h

/-- Idempotents on a direct sum of copies of `X` split. -/
lemma idempotentsSplit_xObj (ι : Type) [Fintype ι] : IdempotentsSplit (xObj D ι) := by
  classical
  intro p hp
  have hPP : toMatrix p * toMatrix p = toMatrix p := by rw [← toMatrix_comp, hp]
  obtain ⟨r, E, I', hIE, hEI⟩ := Matrix.exists_factor_of_mul_self (toMatrix p) hPP
  refine ⟨xObj D (Fin r), ofMatrix D I', ofMatrix D E, toMatrix_injective D ?_,
    toMatrix_injective D ?_⟩
  · rw [toMatrix_comp, toMatrix_ofMatrix, toMatrix_ofMatrix, hIE, toMatrix_id]
  · rw [toMatrix_comp, toMatrix_ofMatrix, toMatrix_ofMatrix, hEI]

/-- Idempotents on the `X`-part of an object split. -/
lemma idempotentsSplit_xPart (M : CD D) : IdempotentsSplit (xPart D M) := by
  classical
  let φ : xPart D M ≅ xObj D (xPart D M).ι :=
    Mat_.isoOfEntries _ _ (Equiv.refl _) fun i => Option.isNone_iff_eq_none.mp i.2
  intro q hq
  refine split_imp_of_iso φ.symm (φ.inv ≫ q ≫ φ.hom) q (by simp) ?_
  exact idempotentsSplit_xObj D _ _ (by simp [reassoc_of% hq])

/-! ### Objects without copies of `X` -/

variable [WellFoundedLT I] [Nonempty I]

/-- Idempotents on an object without copies of `X` split. -/
lemma idempotentsSplit_of_xFree {N : CD D} (hN : XFree D N) : IdempotentsSplit N := by
  intro p hp
  obtain ⟨K, i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split ((rho D).obj N)
    ((rho D).map p) (by rw [← Functor.map_comp, hp])
  have hK : IsGood (objIdx D N) K :=
    (isGood_rho D _ N (labelIn_objIdx D N subset_rfl)).of_retract _ i e hie
  obtain ⟨N', hN', ⟨eK⟩⟩ := exists_xFree_of_isGood D hK
  obtain ⟨i', hi'⟩ := (rho_map_bijective D hN' hN).2 (eK.hom ≫ i)
  obtain ⟨e', he'⟩ := (rho_map_bijective D hN hN').2 (e ≫ eK.inv)
  refine ⟨N', i', e', (rho_map_bijective D hN' hN').1 ?_, (rho_map_bijective D hN hN).1 ?_⟩
  · rw [Functor.map_comp, hi', he', CategoryTheory.Functor.map_id]
    simp [reassoc_of% hie]
  · rw [Functor.map_comp, hi', he']
    simp [hei]

/-- **Proposition 4.4**: `C(D)` is idempotent complete. -/
theorem isIdempotentComplete_CD : IsIdempotentComplete (CD D) := by
  refine ⟨fun M p hp => ?_⟩
  let iso : M ≅ bPart D M ⊞ xPart D M :=
    isoBiprodOfTotal (bIncl D M) (xIncl D M) (bProj D M) (xProj D M) (bIncl_bProj D M)
      (xIncl_xProj D M) (bIncl_xProj D M) (xIncl_bProj D M) (bProj_bIncl_add D M)
  let p' := iso.inv ≫ p ≫ iso.hom
  have hp' : p' ≫ p' = p' := by simp [p', reassoc_of% hp]
  have h0 : biprod.inl ≫ p' ≫ biprod.snd = 0 := hom_xFree_xPart_eq_zero D (xFree_bPart D M) _
  exact split_imp_of_iso iso.symm p' p (by simp [p'])
    (split_biprod_of_triangular (idempotentsSplit_of_xFree D (xFree_bPart D M))
      (idempotentsSplit_xPart D M) p' hp' h0)

end ExtriangulatedRealization
