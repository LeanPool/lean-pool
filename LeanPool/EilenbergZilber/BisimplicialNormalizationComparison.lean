/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li
-/
module

public import LeanPool.EilenbergZilber.Bisimplicial
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# The normalization comparison equivalence

This file constructs the homotopy equivalence
`normalizationComparison : HomotopyEquiv (N₁.obj X) (F₁.obj X)` used in the normalized
Eilenberg-Zilber argument.

The construction is factored as

`N₁(X) ≃ M₁(X) ≃ F₁(X)`,

where `M₁` is outer-unnormalized and inner-normalized.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

/-- The symmetry of the total complex shape on `ChainComplex _ ℕ` bicomplexes, with respect to the
canonical `TotalComplexShape (down ℕ) (down ℕ) (down ℕ)`. The sign `σ i₁ i₂ = (-1)^(i₁ * i₂)`
(written via the alternating sign `ε`) is exactly what is needed for the flip symmetry
`HomologicalComplex₂.totalFlipIso`. Mirrors the `up ℤ` instance in Mathlib. -/
instance LeanPool.EilenbergZilber.instTotalComplexShapeSymmetryNatDown :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) where
  symm i₁ i₂ := add_comm i₂ i₁
  σ i₁ i₂ := (ComplexShape.down ℕ).ε (i₁ * i₂)
  σ_ε₁ := by
    intro i₁ i₁' h₁ i₂
    obtain rfl : i₁' + 1 = i₁ := h₁
    change (ComplexShape.down ℕ).ε ((i₁' + 1) * i₂) * 1 =
      (ComplexShape.down ℕ).ε i₂ * (ComplexShape.down ℕ).ε (i₁' * i₂)
    rw [mul_one, add_mul, one_mul, ComplexShape.ε_add, mul_comm]
  σ_ε₂ := by
    intro i₁ i₂ i₂' h₂
    obtain rfl : i₂' + 1 = i₂ := h₂
    change (ComplexShape.down ℕ).ε (i₁ * (i₂' + 1)) * (ComplexShape.down ℕ).ε i₁ =
      1 * (ComplexShape.down ℕ).ε (i₁ * i₂')
    rw [one_mul, mul_add, mul_one, ComplexShape.ε_add, mul_assoc, Int.units_mul_self, mul_one]

namespace LeanPool.EilenbergZilber

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The intermediate total complex: outer unnormalized and inner normalized. -/
noncomputable abbrev M₁ (X : BisimplicialObject C) : ChainComplex C ℕ :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).obj
    (((normalizedMooreComplex C).mapHomologicalComplex _).obj
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

variable (X : BisimplicialObject C)

/-- The outer normalization inclusion `N₁(X) ⟶ M₁(X)`. -/
noncomputable def inclusionM₁ : N₁.obj X ⟶ M₁ X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    (((normalizedMooreComplex C).mapHomologicalComplex _).map (inclusionOfMooreComplexMap X))

/-- The outer normalization retraction `M₁(X) ⟶ N₁(X)`. -/
noncomputable def retractionM₁ : M₁ X ⟶ N₁.obj X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    (((normalizedMooreComplex C).mapHomologicalComplex _).map (PInftyToNormalizedMooreComplex X))

/-- The inner normalization inclusion `M₁(X) ⟶ F₁(X)`. -/
noncomputable def inclusionF₁ : M₁ X ⟶ F₁.obj X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    ((NatTrans.mapHomologicalComplex mooreInclusion _).app
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

/-- The inner normalization retraction `F₁(X) ⟶ M₁(X)`. -/
noncomputable def retractionF₁ : F₁.obj X ⟶ M₁ X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    ((NatTrans.mapHomologicalComplex mooreRetraction _).app
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

@[reassoc]
lemma inclusionM₁_comp_inclusionF₁ :
    inclusionM₁ X ≫ inclusionF₁ X = inclusionN₁ X := by
  exact ((HomologicalComplex₂.totalFunctor _ _ _ _).map_comp _ _).symm

@[reassoc]
lemma retractionF₁_comp_retractionM₁ :
    retractionF₁ X ≫ retractionM₁ X = retractionN₁ X := by
  exact ((HomologicalComplex₂.totalFunctor _ _ _ _).map_comp _ _).symm

@[reassoc]
lemma inclusionM₁_comp_retractionM₁ :
    inclusionM₁ X ≫ retractionM₁ X = 𝟙 (N₁.obj X) := by
  have h :
      (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inclusionOfMooreComplexMap X) ≫
        ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (PInftyToNormalizedMooreComplex X)) =
      𝟙 _ := by
    rw [← Functor.map_comp]
    change ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (inclusionOfMooreComplexMap X ≫ (splitMonoInclusionOfMooreComplexMap X).retraction) = _
    rw [(splitMonoInclusionOfMooreComplexMap X).id, CategoryTheory.Functor.map_id]
  exact ((HomologicalComplex₂.totalFunctor _ _ _ _).map_comp _ _).symm.trans
    ((congrArg (HomologicalComplex₂.totalFunctor _ _ _ _).map h).trans
        (CategoryTheory.Functor.map_id _ _))

@[reassoc]
lemma inclusionF₁_comp_retractionF₁ :
    inclusionF₁ X ≫ retractionF₁ X = 𝟙 (M₁ X) := by
  have h :
      (NatTrans.mapHomologicalComplex mooreInclusion (ComplexShape.down ℕ)).app
          ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
        (NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
          ((alternatingFaceMapComplex (SimplicialObject C)).obj X) =
      𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      mooreInclusion_comp_mooreRetraction, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  exact ((HomologicalComplex₂.totalFunctor _ _ _ _).map_comp _ _).symm.trans
    ((congrArg (HomologicalComplex₂.totalFunctor _ _ _ _).map h).trans
        (CategoryTheory.Functor.map_id _ _))

namespace HomologicalComplex₂

section OuterLift

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c] [L.HasTotal c]
  {φ ψ : K ⟶ L}

/-- The components `(K.total c).X j ⟶ (L.total c).X j'` of the homotopy on total complexes
induced by a homotopy `h` between maps of bicomplexes that is homotopic in the first
direction. -/
noncomputable def totalMapHomotopyHom (h : Homotopy φ ψ) (j j' : J) :
    (K.total c).X j ⟶ (L.total c).X j' :=
  K.totalDesc (c₁₂ := c)
    (fun i₁ i₂ _ =>
      ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
        (h.hom i₁ (c₁.prev i₁)).f i₂ ≫
          L.ιTotalOrZero c (c₁.prev i₁) i₂ j')

@[reassoc]
private lemma ιTotal_totalMapHomotopyHom (h : Homotopy φ ψ) (i₁ : I₁) (i₂ : I₂) (j j' : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    K.ιTotal c i₁ i₂ j hj ≫ totalMapHomotopyHom h j j' =
      ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
        (h.hom i₁ (c₁.prev i₁)).f i₂ ≫
          L.ιTotalOrZero c (c₁.prev i₁) i₂ j' := by
  simp [totalMapHomotopyHom]

lemma totalMapHomotopy_zero (h : Homotopy φ ψ) (j j' : J)
    (hj : ¬ c.Rel j' j) :
    totalMapHomotopyHom (c := c) h j j' = 0 := by
  apply HomologicalComplex₂.total.hom_ext (c₁₂ := c)
  intro i₁ i₂ hi
  rw [ιTotal_totalMapHomotopyHom]
  by_cases h₁ : c₁.Rel (c₁.prev i₁) i₁
  · rw [L.ιTotalOrZero_eq_zero c (c₁.prev i₁) i₂ j']
    · simp
    · intro h'
      apply hj
      rw [← hi, ← h']
      exact ComplexShape.rel_π₁ c₂ c h₁ i₂
  · rw [h.zero i₁ (c₁.prev i₁) h₁, HomologicalComplex.zero_f, zero_comp,
      smul_zero, comp_zero]

private lemma totalMapHomotopy_comm_aux (h : Homotopy φ ψ)
    {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁')
    {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') (j : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) :
    ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
        (h.hom i₁' i₁).f i₂ ≫ L.d₂ c i₁ i₂ j =
      -(K.d₂ c i₁' i₂ (c.next j) ≫
        totalMapHomotopyHom h (c.next j) j) := by
  have hj' : ComplexShape.π c₁ c₂ c (i₁, i₂') = j := by
    rw [← hj, ← ComplexShape.next_π₂ c₁ c i₁ hi₂,
      ComplexShape.next_π₁ c₂ c hi₁ i₂]
  rw [HomologicalComplex₂.d₂_eq _ c _ hi₂ _ hj', HomologicalComplex₂.d₂_eq _ c _ hi₂ _
        (by rw [← c.next_eq'
          (ComplexShape.rel_π₂ c₁ c i₁' hi₂), hj]),
    Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ιTotal_totalMapHomotopyHom h _ _ _ _
      (by rw [← c.next_eq'
        (ComplexShape.rel_π₂ c₁ c i₁' hi₂), hj]),
    c₁.prev_eq' hi₁,
    HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ hj',
    Linear.comp_units_smul, smul_smul, smul_smul,
    ComplexShape.ε₁_ε₂ c hi₁ hi₂, neg_mul, Units.neg_smul, neg_inj,
    smul_left_cancel_iff, HomologicalComplex.Hom.comm_assoc]

lemma totalMapHomotopy_comm (h : Homotopy φ ψ) (j : J) :
    (HomologicalComplex₂.total.map φ c).f j =
      dNext j (totalMapHomotopyHom h) + prevD j (totalMapHomotopyHom h) +
        (HomologicalComplex₂.total.map ψ c).f j := by
  apply HomologicalComplex₂.total.hom_ext (c₁₂ := c)
  intro i₁ i₂ hj
  simp only [h.comm i₁, dNext_eq_dFrom_fromNext, HomologicalComplex.dFrom, fromNext,
    AddMonoidHom.mk'_apply, prevD_eq_toPrev_dTo, toPrev, HomologicalComplex.dTo,
    Preadditive.add_comp, Preadditive.comp_add, HomologicalComplex₂.total_d,
    HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc]
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, Preadditive.add_comp,
    Category.assoc, add_left_inj]
  have : ∀ {X Y : C} (a b c d e f : X ⟶ Y), a = c → b = e → f = -d →
      a + b = c + d + (e + f) := by
    rintro X Y a b _ d _ _ rfl rfl rfl
    abel
  apply this
  · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
    · rw [HomologicalComplex₂.d₁_eq _ c h₃ _ _
        (by rw [← hj, ComplexShape.next_π₁ c₂ c h₃ i₂]),
        Linear.units_smul_comp, Category.assoc,
        ιTotal_totalMapHomotopyHom h _ _ _ _
          (by
            rw [← ComplexShape.next_π₁ c₂ c h₃ i₂, hj]),
        c₁.prev_eq' h₃, L.ιTotalOrZero_eq c i₁ i₂ j hj,
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
    · rw [K.shape_f _ _ h₃, zero_comp,
        HomologicalComplex₂.d₁_eq_zero _ c _ _ _ h₃, zero_comp]
  · rw [ιTotal_totalMapHomotopyHom_assoc h _ _ _ _ hj]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [L.ιTotalOrZero_eq c (c₁.prev i₁) i₂
          (c.prev j) (by
            rw [← ComplexShape.prev_π₁ c₂ c h₃, hj]),
        Linear.units_smul_comp, Category.assoc, HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.d₁_eq _ c h₃ _ _ hj, Linear.comp_units_smul,
        smul_smul, Int.units_mul_self, one_smul]
    · rw [h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, zero_comp, smul_zero, zero_comp]
  · rw [ιTotal_totalMapHomotopyHom_assoc h _ _ _ _ hj]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [Linear.units_smul_comp, Category.assoc,
        L.ιTotalOrZero_eq c (c₁.prev i₁) i₂
          (c.prev j) (by
            rw [← ComplexShape.prev_π₁ c₂ c h₃, hj]),
        HomologicalComplex₂.ι_D₂]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · exact totalMapHomotopy_comm_aux h h₃ h₄ j hj
      · rw [HomologicalComplex₂.d₂_eq_zero _ c _ _ _ h₄, comp_zero,
          smul_zero, HomologicalComplex₂.d₂_eq_zero _ c _ _ _ h₄,
          zero_comp, neg_zero]
    · rw [h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, smul_zero, zero_comp, zero_eq_neg]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₅ : c.Rel j (c.next j)
        · rw [HomologicalComplex₂.d₂_eq _ c _ h₄ _ (by
              rw [← ComplexShape.next_π₂ c₁ c i₁ h₄, hj]),
            Linear.units_smul_comp, Category.assoc, ιTotal_totalMapHomotopyHom h _ _ _ _
              (by rw [← ComplexShape.next_π₂ c₁ c i₁ h₄,
                hj]),
            h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, smul_zero, comp_zero, smul_zero]
        · rw [totalMapHomotopy_zero h _ _ h₅, comp_zero]
      · rw [HomologicalComplex₂.d₂_eq_zero _ c _ _ _ h₄, zero_comp]

/-- A homotopy of bicomplex morphisms in the outer direction induces a homotopy on total
complexes. -/
noncomputable def totalMapHomotopy (h : Homotopy φ ψ) :
    Homotopy (HomologicalComplex₂.total.map φ c)
      (HomologicalComplex₂.total.map ψ c) where
  hom := totalMapHomotopyHom h
  zero := totalMapHomotopy_zero h
  comm := totalMapHomotopy_comm h

end OuterLift

section InnerLift

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [DecidableEq J] [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]
  {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c] [L.HasTotal c]

/-- The flip of a bicomplex morphism, as a morphism between the flipped bicomplexes. -/
def flipMap (φ : K ⟶ L) : K.flip ⟶ L.flip :=
  (HomologicalComplex₂.flipFunctor C c₁ c₂).map φ

@[simp]
lemma flipMap_f_f (φ : K ⟶ L) (i₂ : I₂) (i₁ : I₁) : ((flipMap φ).f i₂).f i₁ = (φ.f i₁).f i₂ :=
  rfl

/-- Naturality of the flip symmetry isomorphism `totalFlipIso` with respect to a bicomplex
morphism `φ : K ⟶ L`: the totalization of `φ` and of its flip are related by conjugation. -/
@[reassoc]
lemma totalFlipIso_hom_naturality (φ : K ⟶ L) :
    (K.totalFlipIso c).hom ≫ HomologicalComplex₂.total.map φ c =
      HomologicalComplex₂.total.map (flipMap φ) c ≫ (L.totalFlipIso c).hom := by
  ext j i₂ i₁ hj
  simp only [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc,
    HomologicalComplex₂.ιTotal_map_assoc, flipMap_f_f,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  erw [Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map, Linear.comp_units_smul]
  rfl

/-- The totalization of a bicomplex morphism is conjugate to the totalization of its flip by
`totalFlipIso`. -/
lemma total_map_eq_flipConjugate (φ : K ⟶ L) :
    HomologicalComplex₂.total.map φ c =
      (K.totalFlipIso c).inv ≫ HomologicalComplex₂.total.map (flipMap φ) c ≫
        (L.totalFlipIso c).hom := by
  rw [← totalFlipIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- The inner-direction analog of `totalMapHomotopy`.

It is obtained by applying `totalMapHomotopy` to the flipped bicomplex and transporting the result
across `totalFlipIso`. -/
noncomputable def totalMapHomotopy₂ {φ ψ : K ⟶ L}
    (h : Homotopy (flipMap φ) (flipMap ψ)) :
    Homotopy (HomologicalComplex₂.total.map φ c) (HomologicalComplex₂.total.map ψ c) :=
  (Homotopy.ofEq (total_map_eq_flipConjugate φ)).trans
    ((((totalMapHomotopy h).compRight (L.totalFlipIso c).hom).compLeft
        (K.totalFlipIso c).inv).trans (Homotopy.ofEq (total_map_eq_flipConjugate ψ).symm))

end InnerLift

end HomologicalComplex₂

/-- The outer Dold-Kan homotopy equivalence before totalization. -/
noncomputable def outerNormalizationComparisonPreTotal :
    HomotopyEquiv
      (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((normalizedMooreComplex (SimplicialObject C)).obj X))
      (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (SimplicialObject C)).obj X)) :=
  (normalizedMooreComplex C).mapHomotopyEquiv <|
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (A := SimplicialObject C) (Y := X)

/-- The outer half of `normalizationComparison`. -/
noncomputable def outerNormalizationComparison : HomotopyEquiv (N₁.obj X) (M₁ X) where
  hom := inclusionM₁ X
  inv := retractionM₁ X
  homotopyHomInvId := Homotopy.ofEq (inclusionM₁_comp_retractionM₁ X)
  homotopyInvHomId := by
    simpa [retractionM₁, inclusionM₁, M₁, outerNormalizationComparisonPreTotal,
      HomologicalComplex₂.totalFunctor]
      using HomologicalComplex₂.totalMapHomotopy (c := ComplexShape.down ℕ)
        ((outerNormalizationComparisonPreTotal (C := C) X).homotopyInvHomId)

/-- A natural family of homotopies between chain-complex-valued functors lifts, after `flip`, to a
homotopy between the corresponding `mapHomologicalComplex` morphisms. -/
noncomputable def flipMapHomologicalComplexHomotopy {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜]
    {F G : 𝒜 ⥤ ChainComplex C ℕ} [F.Additive] [G.Additive] {α β : F ⟶ G}
    (h : ∀ Y, Homotopy (α.app Y) (β.app Y))
    (hnat : ∀ {Y Z : 𝒜} (f : Y ⟶ Z) (i j : ℕ),
      (F.map f).f i ≫ (h Z).hom i j = (h Y).hom i j ≫ (G.map f).f j)
    (W : HomologicalComplex 𝒜 (ComplexShape.down ℕ)) :
    Homotopy
      (HomologicalComplex₂.flipMap ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app W))
      (HomologicalComplex₂.flipMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.down ℕ)).app W)) where
  hom m m' :=
    { f := fun r => (h (W.X r)).hom m m'
      comm' := fun r r' _ => (hnat (W.d r r') m m').symm }
  zero m m' hmm' := by
    ext r
    exact (h (W.X r)).zero m m' hmm'
  comm m := by
    ext r
    have key := (h (W.X r)).comm m
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at key
    simp only [HomologicalComplex.add_f_apply,
      dNext, prevD, AddMonoidHom.mk'_apply,
      HomologicalComplex.comp_f,
      HomologicalComplex₂.flip_d_f, Functor.mapHomologicalComplex_obj_X]
    exact key

/-- Naturality of the homotopy operator in `homotopyPToId`. -/
lemma alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom {Y Z : SimplicialObject C}
    (f : Y ⟶ Z) (q i j : ℕ) :
    ((alternatingFaceMapComplex C).map f).f i ≫ (homotopyPToId Z q).hom i j =
      (homotopyPToId Y q).hom i j ≫ ((alternatingFaceMapComplex C).map f).f j := by
  simp only [alternatingFaceMapComplex_map_f]
  induction q with
  | zero => simp [homotopyPToId]
  | succ q ih =>
    -- Unfold the inductive step and use naturality of the projection and homotopy operators.
    simp only [homotopyPToId, homotopyHσToZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
      Pi.zero_apply, Homotopy.add_hom,
      add_zero, zero_add]
    rw [Preadditive.comp_add, Preadditive.add_comp, ih]
    congr 1
    erw [Homotopy.compLeft_hom, Homotopy.compLeft_hom]
    simp only [Homotopy.nullHomotopy'_hom]
    split_ifs with h
    · rw [← Category.assoc, P_f_naturality, Category.assoc, hσ'_naturality, Category.assoc]
    · simp

/-- Naturality, in the simplicial object, of the Dold–Kan contraction homotopy operator for
`PInfty ≃ 𝟙` (i.e. `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.homotopyInvHomId`).
This is the `hnat` input to `flipMapHomologicalComplexHomotopy` for the inner normalization
comparison. -/
lemma homotopyInvHomId_hom_naturality {Y Z : SimplicialObject C} (f : Y ⟶ Z) (i j : ℕ) :
    ((alternatingFaceMapComplex C).map f).f i ≫
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (A := C) (Y := Z)).homotopyInvHomId.hom i j =
      (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (A := C) (Y := Y)).homotopyInvHomId.hom i j ≫
        ((alternatingFaceMapComplex C).map f).f j := by
  simp only [homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex_homotopyInvHomId,
    Homotopy.trans_hom,
    homotopyPInftyToId_hom]
  erw [Homotopy.ofEq_hom, Homotopy.ofEq_hom]
  simp only [Pi.zero_apply, zero_add]
  exact alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom f (j + 1) i j

/-- The flipped inner Dold-Kan homotopy used in `innerNormalizationComparison`. -/
noncomputable def retractionF₁InclusionF₁FlipHomotopy :
    Homotopy
      (HomologicalComplex₂.flipMap
        ((NatTrans.mapHomologicalComplex mooreRetraction _).app
            ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
          (NatTrans.mapHomologicalComplex mooreInclusion _).app
            ((alternatingFaceMapComplex (SimplicialObject C)).obj X)))
      (HomologicalComplex₂.flipMap
        (𝟙 (((alternatingFaceMapComplex C).mapHomologicalComplex _).obj
          ((alternatingFaceMapComplex (SimplicialObject C)).obj X)))) :=
  flipMapHomologicalComplexHomotopy
    (α := mooreRetraction ≫ mooreInclusion) (β := 𝟙 (alternatingFaceMapComplex C))
    (fun Y => (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (A := C) (Y := Y)).homotopyInvHomId)
    (fun f i j => homotopyInvHomId_hom_naturality f i j)
    ((alternatingFaceMapComplex (SimplicialObject C)).obj X)

/-- The inner half of `normalizationComparison`. -/
noncomputable def innerNormalizationComparison : HomotopyEquiv (M₁ X) (F₁.obj X) where
  hom := inclusionF₁ X
  inv := retractionF₁ X
  homotopyHomInvId := Homotopy.ofEq (inclusionF₁_comp_retractionF₁ X)
  homotopyInvHomId :=
    (Homotopy.ofEq ((HomologicalComplex₂.totalFunctor _ _ _ _).map_comp _ _).symm).trans <|
      (HomologicalComplex₂.totalMapHomotopy₂ (c := ComplexShape.down ℕ)
        (retractionF₁InclusionF₁FlipHomotopy X)).trans
        (Homotopy.ofEq ((HomologicalComplex₂.totalFunctor _ _ _ _).map_id _))

/-- The full comparison between the normalized and unnormalized total complexes. -/
noncomputable def normalizationComparison : HomotopyEquiv (N₁.obj X) (F₁.obj X) :=
  (outerNormalizationComparison X).trans (innerNormalizationComparison X)

@[reassoc]
lemma normalizationComparison_hom_eq :
    (normalizationComparison X).hom = inclusionN₁ X := by
  change inclusionM₁ X ≫ inclusionF₁ X = inclusionN₁ X
  exact inclusionM₁_comp_inclusionF₁ X

@[reassoc]
lemma normalizationComparison_inv_eq :
    (normalizationComparison X).inv = retractionN₁ X := by
  change retractionF₁ X ≫ retractionM₁ X = retractionN₁ X
  exact retractionF₁_comp_retractionM₁ X

end BisimplicialObject

end LeanPool.EilenbergZilber
