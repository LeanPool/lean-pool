/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Proposition
public import LeanPool.ExtriangulatedRealization.CD.Extensions

/-!
# Transfer of the axioms from the realization (Corollary 2.4)

On `C_J`, a sequence realizes `δ` exactly when its image under the realization functor, with
third morphism `η δ`, is distinguished: realizations go to distinguished triangles, and
conversely a distinguished triangle is compared with the image of a realization of `δ`
(which exists in `C(D)` and lies in `C_J`), and the comparison isomorphism lifts along the fully
faithful realization functor. The axioms of an extriangulated category then follow from those of
the triangulated category `K(Q)` [NP, Remark 2.18].
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory
  Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard HasExt.standard

namespace RealizationData

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] [WellFoundedLT I] [Nonempty I]
  {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I} (R : RealizationData D J) (hR : R.IsCompatible)

/-- A sequence of `C_J` going to a distinguished triangle is a realization. -/
lemma realizes_of_distinguished {A B C : (labelsIn D J).FullSubcategory} {x : A ⟶ B}
    {y : B ⟶ C} {δ : (dataJ (D := D) (J := J)).Ext C A}
    (hT : R.realTriangle hR x y δ ∈ distTriang _) : (dataJ (D := D) (J := J)).Realizes δ x y := by
  obtain ⟨B₀, x₀, y₀, h₀⟩ := cd_exists_realizes D (A := A.obj) (C := C.obj) δ
  have hB₀ : labelsIn D J B₀ := labelsIn_of_realizes D h₀ A.property C.property
  let B₀' : (labelsIn D J).FullSubcategory := ⟨B₀, hB₀⟩
  have hT₀ := R.realTriangle_distinguished hR (B := B₀') (x := ObjectProperty.homMk x₀)
    (y := ObjectProperty.homMk y₀) h₀
  obtain ⟨e, he₁, he₂⟩ := exists_iso_of_distinguished hT₀ hT
  let b : B₀' ≅ B := (R.realP hR).preimageIso e
  have hb₁ : ObjectProperty.homMk x₀ ≫ b.hom = x :=
    (R.realP hR).map_injective (by
      rw [Functor.map_comp]
      exact (congrArg _ ((R.realP hR).map_preimage e.hom)).trans he₁)
  have hb₂ : b.hom ≫ y = ObjectProperty.homMk y₀ :=
    (R.realP hR).map_injective (by
      rw [Functor.map_comp]
      exact (congrArg (· ≫ _) ((R.realP hR).map_preimage e.hom)).trans he₂)
  have h := cdData_realizes_iso D ((labelsIn D J).ι.mapIso b) h₀
  have e₁ : x₀ ≫ b.hom.hom = x.hom := congrArg InducedCategory.Hom.hom hb₁
  have e₂ : b.inv.hom ≫ y₀ = y.hom := by
    have h' : y = b.inv ≫ ObjectProperty.homMk y₀ := by rw [← hb₂, Iso.inv_hom_id_assoc]
    rw [h']
    rfl
  change (cdData D).Realizes δ x.hom y.hom
  rw [← e₁, ← e₂]
  exact h

section Axioms

variable {A B B' C A' C' : (labelsIn D J).FullSubcategory}

include R hR

omit [WellFoundedLT I] [Nonempty I] in
lemma realizes_unique {δ : (dataJ (D := D) (J := J)).Ext C A} {x : A ⟶ B} {y : B ⟶ C}
    {x' : A ⟶ B'} {y' : B' ⟶ C} (h : (dataJ (D := D) (J := J)).Realizes δ x y)
    (h' : (dataJ (D := D) (J := J)).Realizes δ x' y') :
    ∃ b : B ≅ B', x ≫ b.hom = x' ∧ b.hom ≫ y' = y := by
  obtain ⟨e, he₁, he₂⟩ := exists_iso_of_distinguished (R.realTriangle_distinguished hR h)
    (R.realTriangle_distinguished hR h')
  refine ⟨(R.realP hR).preimageIso e, (R.realP hR).map_injective ?_,
    (R.realP hR).map_injective ?_⟩
  · rw [Functor.map_comp]
    exact (congrArg _ ((R.realP hR).map_preimage e.hom)).trans he₁
  · rw [Functor.map_comp]
    exact (congrArg (· ≫ _) ((R.realP hR).map_preimage e.hom)).trans he₂

omit [WellFoundedLT I] [Nonempty I] in
lemma realizes_morphism {δ : (dataJ (D := D) (J := J)).Ext C A}
    {δ' : (dataJ (D := D) (J := J)).Ext C' A'} {x : A ⟶ B} {y : B ⟶ C} {x' : A' ⟶ B'}
    {y' : B' ⟶ C'} (h : (dataJ (D := D) (J := J)).Realizes δ x y)
    (h' : (dataJ (D := D) (J := J)).Realizes δ' x' y') (a : A ⟶ A') (c : C ⟶ C')
    (hac : (dataJ (D := D) (J := J)).push a δ = (dataJ (D := D) (J := J)).pull c δ') :
    ∃ b : B ⟶ B', x ≫ b = a ≫ x' ∧ y ≫ c = b ≫ y' := by
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _
    (R.realTriangle_distinguished hR h) (R.realTriangle_distinguished hR h')
    ((R.realP hR).map a) ((R.realP hR).map c) (by
      change R.eta hR C A δ ≫ _ = _ ≫ R.eta hR C' A' δ'
      erw [← R.eta_push' hR, ← R.eta_pull' hR, hac])
  refine ⟨(R.realP hR).preimage b, (R.realP hR).map_injective ?_,
    (R.realP hR).map_injective ?_⟩
  · rw [Functor.map_comp, Functor.map_comp]
    erw [Functor.map_preimage]
    exact hb₁
  · rw [Functor.map_comp, Functor.map_comp]
    erw [Functor.map_preimage]
    exact hb₂

/-- Realizations are invariant under isomorphisms of the end terms. -/
lemma realizes_transport {δ : (dataJ (D := D) (J := J)).Ext C A} {x : A ⟶ B} {y : B ⟶ C}
    (h : (dataJ (D := D) (J := J)).Realizes δ x y) (a : A' ≅ A) (c : C' ≅ C) :
    (dataJ (D := D) (J := J)).Realizes
      ((dataJ (D := D) (J := J)).pull c.hom ((dataJ (D := D) (J := J)).push a.inv δ))
      (a.hom ≫ x) (y ≫ c.inv) := by
  apply R.realizes_of_distinguished hR
  refine isomorphic_distinguished _ (R.realTriangle_distinguished hR h) _
    (Triangle.isoMk _ _ ((R.realP hR).mapIso a) (Iso.refl _) ((R.realP hR).mapIso c) ?_ ?_ ?_)
  · change (R.realP hR).map (a.hom ≫ x) ≫ 𝟙 _ = (R.realP hR).map a.hom ≫ (R.realP hR).map x
    rw [Category.comp_id, Functor.map_comp]
  · change (R.realP hR).map (y ≫ c.inv) ≫ (R.realP hR).map c.hom = 𝟙 _ ≫ (R.realP hR).map y
    rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · change R.eta hR C' A' _ ≫ ((R.realP hR).map a.hom)⟦(1 : ℤ)⟧' =
      (R.realP hR).map c.hom ≫ R.eta hR C A δ
    rw [R.eta_pull' hR, R.eta_push' hR, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

omit [WellFoundedLT I] [Nonempty I] in
lemma et3 {δ : (dataJ (D := D) (J := J)).Ext C A}
    {δ' : (dataJ (D := D) (J := J)).Ext C' A'} {x : A ⟶ B} {y : B ⟶ C} {x' : A' ⟶ B'}
    {y' : B' ⟶ C'} (h : (dataJ (D := D) (J := J)).Realizes δ x y)
    (h' : (dataJ (D := D) (J := J)).Realizes δ' x' y') (a : A ⟶ A') (b : B ⟶ B')
    (hab : x ≫ b = a ≫ x') :
    ∃ c : C ⟶ C', y ≫ c = b ≫ y' ∧
      (dataJ (D := D) (J := J)).push a δ = (dataJ (D := D) (J := J)).pull c δ' := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _
    (R.realTriangle_distinguished hR h) (R.realTriangle_distinguished hR h')
    ((R.realP hR).map a) ((R.realP hR).map b) (by
      change (R.realP hR).map x ≫ _ = _ ≫ (R.realP hR).map x'
      rw [← Functor.map_comp, ← Functor.map_comp, hab])
  refine ⟨(R.realP hR).preimage c, (R.realP hR).map_injective ?_, (R.eta_bijective hR C A').1 ?_⟩
  · rw [Functor.map_comp, Functor.map_comp]
    erw [Functor.map_preimage]
    exact hc₂
  · rw [R.eta_push' hR, R.eta_pull' hR]
    erw [Functor.map_preimage]
    exact hc₃

omit [WellFoundedLT I] [Nonempty I] in
lemma et3_op {δ : (dataJ (D := D) (J := J)).Ext C A}
    {δ' : (dataJ (D := D) (J := J)).Ext C' A'} {x : A ⟶ B} {y : B ⟶ C} {x' : A' ⟶ B'}
    {y' : B' ⟶ C'} (h : (dataJ (D := D) (J := J)).Realizes δ x y)
    (h' : (dataJ (D := D) (J := J)).Realizes δ' x' y') (b : B ⟶ B') (c : C ⟶ C')
    (hbc : y ≫ c = b ≫ y') :
    ∃ a : A ⟶ A', x ≫ b = a ≫ x' ∧
      (dataJ (D := D) (J := J)).push a δ = (dataJ (D := D) (J := J)).pull c δ' := by
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ _ _
    (R.realTriangle_distinguished hR h) (R.realTriangle_distinguished hR h')
    ((R.realP hR).map b) ((R.realP hR).map c) (by
      change (R.realP hR).map y ≫ _ = _ ≫ (R.realP hR).map y'
      rw [← Functor.map_comp, ← Functor.map_comp, hbc])
  refine ⟨(R.realP hR).preimage a, (R.realP hR).map_injective ?_, (R.eta_bijective hR C A').1 ?_⟩
  · rw [Functor.map_comp, Functor.map_comp]
    erw [Functor.map_preimage]
    exact ha₁
  · rw [R.eta_push' hR, R.eta_pull' hR]
    erw [Functor.map_preimage]
    exact ha₃

/-- A distinguished triangle `F X → Z → F Y → (F X)⟦1⟧` with third morphism `η ε` comes from a
realization of `ε`. -/
lemma exists_realizes_iso {X Y : (labelsIn D J).FullSubcategory}
    (ε : (dataJ (D := D) (J := J)).Ext Y X) {Z : HomotopyCategory R.Q (ComplexShape.up ℤ)}
    {a : (R.realP hR).obj X ⟶ Z} {b : Z ⟶ (R.realP hR).obj Y}
    (hT : Triangle.mk a b (R.eta hR Y X ε) ∈ distTriang _) :
    ∃ (E : (labelsIn D J).FullSubcategory) (d : X ⟶ E) (e : E ⟶ Y)
      (φ : (R.realP hR).obj E ≅ Z), (dataJ (D := D) (J := J)).Realizes ε d e ∧
        (R.realP hR).map d ≫ φ.hom = a ∧ φ.hom ≫ b = (R.realP hR).map e := by
  obtain ⟨B₀, x₀, y₀, h₀⟩ := cd_exists_realizes D (A := X.obj) (C := Y.obj) ε
  let E : (labelsIn D J).FullSubcategory := ⟨B₀, labelsIn_of_realizes D h₀ X.property Y.property⟩
  have hT₀ := R.realTriangle_distinguished hR (B := E) (x := ObjectProperty.homMk x₀)
    (y := ObjectProperty.homMk y₀) h₀
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_iso_of_distinguished hT₀ hT
  exact ⟨E, ObjectProperty.homMk x₀, ObjectProperty.homMk y₀, φ, h₀, hφ₁, hφ₂⟩

/-- (ET4) in `C_J`, from the octahedral axiom in `K(Q)`. -/
lemma et4 {A B C' D' F' : (labelsIn D J).FullSubcategory} {f : A ⟶ B} {f' : B ⟶ D'}
    {g : B ⟶ C'} {g' : C' ⟶ F'} {δ : (dataJ (D := D) (J := J)).Ext D' A}
    {δ' : (dataJ (D := D) (J := J)).Ext F' B} (h : (dataJ (D := D) (J := J)).Realizes δ f f')
    (h' : (dataJ (D := D) (J := J)).Realizes δ' g g') :
    ∃ (E : (labelsIn D J).FullSubcategory) (h'' : C' ⟶ E) (d : D' ⟶ E) (e : E ⟶ F')
      (δ'' : (dataJ (D := D) (J := J)).Ext E A),
      (dataJ (D := D) (J := J)).Realizes δ'' (f ≫ g) h'' ∧ f' ≫ d = g ≫ h'' ∧ h'' ≫ e = g' ∧
      (dataJ (D := D) (J := J)).Realizes ((dataJ (D := D) (J := J)).push f' δ') d e ∧
      (dataJ (D := D) (J := J)).pull d δ'' = δ ∧
      (dataJ (D := D) (J := J)).push f δ'' = (dataJ (D := D) (J := J)).pull e δ' := by
  let F := R.realP hR
  obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (F.map (f ≫ g))
  have h₁₂ : Triangle.mk (F.map f) (F.map f') (R.eta hR D' A δ) ∈ distTriang _ :=
    R.realTriangle_distinguished hR h
  have h₂₃ : Triangle.mk (F.map g) (F.map g') (R.eta hR F' B δ') ∈ distTriang _ :=
    R.realTriangle_distinguished hR h'
  let o := Triangulated.someOctahedron (F.map_comp f g).symm h₁₂ h₂₃ h₁₃
  have hmem : Triangle.mk o.m₁ o.m₃ (R.eta hR F' D' ((dataJ (D := D) (J := J)).push f' δ')) ∈
      distTriang _ := by
    rw [R.eta_push' hR]
    exact o.mem
  obtain ⟨E, d, e, φ, hde, hφ₁, hφ₂⟩ := R.exists_realizes_iso hR _ hmem
  obtain ⟨δ'', hδ''⟩ := (R.eta_bijective hR E A).2 (φ.hom ≫ w₁₃)
  have hc₁ := o.comm₁
  have hc₂ := o.comm₂
  have hc₃ := o.comm₃
  have hc₄ := o.comm₄
  refine ⟨E, F.preimage (v₁₃ ≫ φ.inv), d, e, δ'', ?_, ?_, ?_, hde, ?_, ?_⟩
  · refine R.realizes_of_distinguished hR (isomorphic_distinguished _ h₁₃ _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) φ ?_ ?_ ?_))
    · simp [realTriangle, F]
    · change F.map (F.preimage (v₁₃ ≫ φ.inv)) ≫ φ.hom = 𝟙 _ ≫ v₁₃
      rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    · change R.eta hR E A δ'' ≫ (𝟙 ((R.realP hR).obj A))⟦(1 : ℤ)⟧' = φ.hom ≫ w₁₃
      rw [CategoryTheory.Functor.map_id, Category.comp_id, hδ'']
  · apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, ← Category.assoc, ← hc₁,
      ← hφ₁, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · apply F.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Category.assoc, ← hφ₂, Iso.inv_hom_id_assoc, hc₃]
  · apply (R.eta_bijective hR D' A).1
    rw [R.eta_pull' hR, hδ'', ← Category.assoc, hφ₁, hc₂]
  · apply (R.eta_bijective hR E B).1
    rw [R.eta_push' hR, R.eta_pull' hR, hδ'', Category.assoc]
    exact (congrArg (φ.hom ≫ ·) hc₄).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ R.eta hR F' B δ') hφ₂))

/-- (ET4)ᵒᵖ in `C_J`, from the octahedral axiom in `K(Q)`. -/
lemma et4_op {D' A B F' C' : (labelsIn D J).FullSubcategory} {f' : D' ⟶ A} {f : A ⟶ B}
    {g' : F' ⟶ B} {g : B ⟶ C'} {δ : (dataJ (D := D) (J := J)).Ext B D'}
    {δ' : (dataJ (D := D) (J := J)).Ext C' F'} (h : (dataJ (D := D) (J := J)).Realizes δ f' f)
    (h' : (dataJ (D := D) (J := J)).Realizes δ' g' g) :
    ∃ (E : (labelsIn D J).FullSubcategory) (h'' : E ⟶ A) (d : D' ⟶ E) (e : E ⟶ F')
      (δ'' : (dataJ (D := D) (J := J)).Ext C' E),
      (dataJ (D := D) (J := J)).Realizes δ'' h'' (f ≫ g) ∧ d ≫ h'' = f' ∧ e ≫ g' = h'' ≫ f ∧
      (dataJ (D := D) (J := J)).Realizes ((dataJ (D := D) (J := J)).pull g' δ) d e ∧
      δ' = (dataJ (D := D) (J := J)).push e δ'' ∧
      (dataJ (D := D) (J := J)).push d δ = (dataJ (D := D) (J := J)).pull g δ'' := by
  let F := R.realP hR
  obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle₁ (F.map (f ≫ g))
  have h₁₂ : Triangle.mk (F.map f') (F.map f) (R.eta hR B D' δ) ∈ distTriang _ :=
    R.realTriangle_distinguished hR h
  have h₂₃ : Triangle.mk (F.map g') (F.map g) (R.eta hR C' F' δ') ∈ distTriang _ :=
    R.realTriangle_distinguished hR h'
  let o := Triangulated.someOctahedron' (F.map_comp f g).symm h₁₂ h₂₃ h₁₃
  have hmem : Triangle.mk o.m₁ o.m₃ (R.eta hR F' D' ((dataJ (D := D) (J := J)).pull g' δ)) ∈
      distTriang _ := by
    rw [R.eta_pull' hR]
    exact o.mem
  obtain ⟨E, d, e, φ, hde, hφ₁, hφ₂⟩ := R.exists_realizes_iso hR _ hmem
  obtain ⟨δ'', hδ''⟩ := (R.eta_bijective hR C' E).2 (w₁₃ ≫ φ.inv⟦(1 : ℤ)⟧')
  have hc₁ := o.comm₁
  have hc₂ := o.comm₂
  have hc₃ := o.comm₃
  have hc₄ := o.comm₄
  have hd : F.map d = o.m₁ ≫ φ.inv := by rw [← hφ₁, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  refine ⟨E, F.preimage (φ.hom ≫ v₁₃), d, e, δ'', ?_, ?_, ?_, hde, ?_, ?_⟩
  · refine R.realizes_of_distinguished hR (isomorphic_distinguished _ h₁₃ _
      (Triangle.isoMk _ _ φ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_))
    · change F.map (F.preimage (φ.hom ≫ v₁₃)) ≫ 𝟙 _ = φ.hom ≫ v₁₃
      rw [Functor.map_preimage, Category.comp_id]
    · simp [realTriangle, F]
    · change R.eta hR C' E δ'' ≫ φ.hom⟦(1 : ℤ)⟧' = 𝟙 _ ≫ w₁₃
      rw [hδ'', Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  · apply F.map_injective
    rw [Functor.map_comp, Functor.map_preimage, ← Category.assoc, hφ₁, hc₁]
  · apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, ← hφ₂, Category.assoc, hc₄,
      Category.assoc]
  · apply (R.eta_bijective hR C' F').1
    rw [R.eta_push' hR, hδ'', ← hφ₂, Functor.map_comp, ← Category.assoc, Category.assoc w₁₃,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id, hc₃]
  · apply (R.eta_bijective hR B E).1
    rw [R.eta_push' hR, R.eta_pull' hR, hd, Functor.map_comp, ← Category.assoc, hc₂, hδ'',
      Category.assoc]

/-! ### Direct sums -/

omit R hR in
/-- The direct sum in `C(D)` of two objects of `C_J`, as an object of `C_J`. -/
noncomputable abbrev biprodJ (X Y : (labelsIn D J).FullSubcategory) :
    (labelsIn D J).FullSubcategory :=
  ⟨X.obj ⊞ Y.obj, labelsIn_biprod D X.property Y.property⟩

/-- The realization functor preserves binary direct sums. -/
noncomputable def realBiprodIso (X Y : (labelsIn D J).FullSubcategory) :
    (R.realP hR).obj (biprodJ X Y) ≅ (R.realP hR).obj X ⊞ (R.realP hR).obj Y :=
  isoBiprodOfTotal (R.realMap hR (M := X) (N := biprodJ X Y) biprod.inl)
    (R.realMap hR (M := Y) (N := biprodJ X Y) biprod.inr)
    (R.realMap hR (M := biprodJ X Y) (N := X) biprod.fst)
    (R.realMap hR (M := biprodJ X Y) (N := Y) biprod.snd)
    ((R.realMap_comp_eq hR biprod.inl_fst).trans (R.realMap_id hR _))
    ((R.realMap_comp_eq hR biprod.inr_snd).trans (R.realMap_id hR _))
    ((R.realMap_comp_eq hR biprod.inl_snd).trans (R.realMap_zero hR _ _))
    ((R.realMap_comp_eq hR biprod.inr_fst).trans (R.realMap_zero hR _ _))
    ((congrArg₂ (· + ·) (R.realMap_comp hR _ _).symm (R.realMap_comp hR _ _).symm).trans
      ((R.realMap_add hR _ _).symm.trans
        ((congrArg (R.realMap hR) biprod.total).trans (R.realMap_id hR _))))

omit [WellFoundedLT I] [Nonempty I] in
lemma realMap_inl_comp_realBiprodIso (X Y : (labelsIn D J).FullSubcategory) :
    R.realMap hR (M := X) (N := biprodJ X Y) biprod.inl ≫ (R.realBiprodIso hR X Y).hom =
      biprod.inl := by
  apply biprod.hom_ext
  · simp only [realBiprodIso, isoBiprodOfTotal_hom, Category.assoc, biprod.lift_fst,
      biprod.inl_fst]
    exact (R.realMap_comp_eq hR biprod.inl_fst).trans (R.realMap_id hR _)
  · simp only [realBiprodIso, isoBiprodOfTotal_hom, Category.assoc, biprod.lift_snd,
      biprod.inl_snd]
    exact (R.realMap_comp_eq hR biprod.inl_snd).trans (R.realMap_zero hR _ _)

omit [WellFoundedLT I] [Nonempty I] in
lemma realMap_inr_comp_realBiprodIso (X Y : (labelsIn D J).FullSubcategory) :
    R.realMap hR (M := Y) (N := biprodJ X Y) biprod.inr ≫ (R.realBiprodIso hR X Y).hom =
      biprod.inr := by
  apply biprod.hom_ext
  · simp only [realBiprodIso, isoBiprodOfTotal_hom, Category.assoc, biprod.lift_fst,
      biprod.inr_fst]
    exact (R.realMap_comp_eq hR biprod.inr_fst).trans (R.realMap_zero hR _ _)
  · simp only [realBiprodIso, isoBiprodOfTotal_hom, Category.assoc, biprod.lift_snd,
      biprod.inr_snd]
    exact (R.realMap_comp_eq hR biprod.inr_snd).trans (R.realMap_id hR _)

/-- (ET2) The split sequence realizes the zero extension. -/
lemma realizes_zero (X Y : (labelsIn D J).FullSubcategory) :
    (dataJ (D := D) (J := J)).Realizes (0 : (dataJ (D := D) (J := J)).Ext Y X)
      (ObjectProperty.homMk biprod.inl : X ⟶ biprodJ X Y)
      (ObjectProperty.homMk biprod.snd : biprodJ X Y ⟶ Y) := by
  apply R.realizes_of_distinguished hR
  refine isomorphic_distinguished
    (binaryBiproductTriangle ((R.realP hR).obj X) ((R.realP hR).obj Y))
    (binaryBiproductTriangle_distinguished _ _)
    (R.realTriangle hR (ObjectProperty.homMk biprod.inl : X ⟶ biprodJ X Y)
      (ObjectProperty.homMk biprod.snd : biprodJ X Y ⟶ Y) 0)
    (Triangle.isoMk _ _ (Iso.refl _) (R.realBiprodIso hR X Y) (Iso.refl _) ?_ ?_ ?_)
  · exact (R.realMap_inl_comp_realBiprodIso hR X Y).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (biprod.lift_snd _ _).symm
  · exact (congrArg (· ≫ _) (map_zero (R.eta hR Y X))).trans (zero_comp.trans comp_zero.symm)

omit R hR in
/-- The direct sum of two extensions, between objects of `C_J`. -/
noncomputable abbrev sumJ {A C A' C' : (labelsIn D J).FullSubcategory}
    (δ : (dataJ (D := D) (J := J)).Ext C A) (δ' : (dataJ (D := D) (J := J)).Ext C' A') :
    (dataJ (D := D) (J := J)).Ext (biprodJ C C') (biprodJ A A') :=
  (cdData D).sum (C₁ := C.obj) (A₁ := A.obj) (C₂ := C'.obj) (A₂ := A'.obj) δ δ'

omit [WellFoundedLT I] [Nonempty I] in
lemma realBiprodIso_naturality {X Y X' Y' : (labelsIn D J).FullSubcategory} (f : X ⟶ Y)
    (g : X' ⟶ Y') :
    R.realMap hR (M := biprodJ X X') (N := biprodJ Y Y') (biprod.map f.hom g.hom) ≫
      (R.realBiprodIso hR Y Y').hom =
      (R.realBiprodIso hR X X').hom ≫ biprod.map ((R.realP hR).map f) ((R.realP hR).map g) := by
  apply biprod.hom_ext
  · simp only [realBiprodIso, isoBiprodOfTotal_hom, Category.assoc, biprod.lift_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    exact (R.realMap_comp_eq hR (biprod.map_fst _ _)).trans (R.realMap_comp hR _ _)
  · simp only [realBiprodIso, isoBiprodOfTotal_hom, Category.assoc, biprod.lift_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    exact (R.realMap_comp_eq hR (biprod.map_snd _ _)).trans (R.realMap_comp hR _ _)

/-- (ET2) Direct sums of realizations realize direct sums. -/
lemma realizes_sum {A B C A' B' C' : (labelsIn D J).FullSubcategory}
    {δ : (dataJ (D := D) (J := J)).Ext C A} {δ' : (dataJ (D := D) (J := J)).Ext C' A'}
    {x : A ⟶ B} {y : B ⟶ C} {x' : A' ⟶ B'} {y' : B' ⟶ C'}
    (h : (dataJ (D := D) (J := J)).Realizes δ x y)
    (h' : (dataJ (D := D) (J := J)).Realizes δ' x' y') :
    (dataJ (D := D) (J := J)).Realizes
      (sumJ δ δ')
      (ObjectProperty.homMk (biprod.map x.hom x'.hom) : biprodJ A A' ⟶ biprodJ B B')
      (ObjectProperty.homMk (biprod.map y.hom y'.hom) : biprodJ B B' ⟶ biprodJ C C') := by
  apply R.realizes_of_distinguished hR
  refine isomorphic_distinguished
    (triangleBiprod (R.realTriangle hR x y δ) (R.realTriangle hR x' y' δ'))
    (triangleBiprod_distinguished _ _ (R.realTriangle_distinguished hR h)
      (R.realTriangle_distinguished hR h'))
    (R.realTriangle hR (ObjectProperty.homMk (biprod.map x.hom x'.hom) :
        biprodJ A A' ⟶ biprodJ B B')
      (ObjectProperty.homMk (biprod.map y.hom y'.hom) : biprodJ B B' ⟶ biprodJ C C')
      (sumJ δ δ'))
    (Triangle.isoMk _ _ (R.realBiprodIso hR A A') (R.realBiprodIso hR B B')
      (R.realBiprodIso hR C C') (R.realBiprodIso_naturality hR x x')
      (R.realBiprodIso_naturality hR y y') ?_)
  refine (cancel_epi (R.realBiprodIso hR C C').inv).mp ?_
  erw [Iso.inv_hom_id_assoc]
  apply biprod.hom_ext'
  · have e₁ : biprod.inl ≫ (R.realBiprodIso hR C C').inv =
        R.realMap hR (M := C) (N := biprodJ C C') biprod.inl := biprod.inl_desc _ _
    have e₂ : R.realMap hR (M := C) (N := biprodJ C C') biprod.inl ≫
        R.eta hR (biprodJ C C') (biprodJ A A') (sumJ δ δ') =
        R.eta hR C (biprodJ A A')
          ((dataJ (D := D) (J := J)).push (ObjectProperty.homMk biprod.inl) δ) := by
      exact (R.eta_pull' hR (C'' := C) (C := biprodJ C C') (A := biprodJ A A')
        (ObjectProperty.homMk biprod.inl) (sumJ δ δ')).symm.trans
        (congrArg (R.eta hR C (biprodJ A A')) (cdData_pull_inl_sum D δ δ'))
    change biprod.inl ≫ (R.realBiprodIso hR C C').inv ≫
        R.eta hR (biprodJ C C') (biprodJ A A') (sumJ δ δ') ≫
          (R.realBiprodIso hR A A').hom⟦(1 : ℤ)⟧' =
      biprod.inl ≫ biprod.desc (R.eta hR C A δ ≫ biprod.inl⟦(1 : ℤ)⟧')
        (R.eta hR C' A' δ' ≫ biprod.inr⟦(1 : ℤ)⟧')
    rw [biprod.inl_desc, ← Category.assoc, e₁, ← Category.assoc, e₂, R.eta_push' hR,
      Category.assoc, ← Functor.map_comp]
    exact congrArg (fun φ => R.eta hR C A δ ≫ φ⟦(1 : ℤ)⟧')
      (R.realMap_inl_comp_realBiprodIso hR A A')
  · have e₁ : biprod.inr ≫ (R.realBiprodIso hR C C').inv =
        R.realMap hR (M := C') (N := biprodJ C C') biprod.inr := biprod.inr_desc _ _
    have e₂ : R.realMap hR (M := C') (N := biprodJ C C') biprod.inr ≫
        R.eta hR (biprodJ C C') (biprodJ A A') (sumJ δ δ') =
        R.eta hR C' (biprodJ A A')
          ((dataJ (D := D) (J := J)).push (ObjectProperty.homMk biprod.inr) δ') := by
      exact (R.eta_pull' hR (C'' := C') (C := biprodJ C C') (A := biprodJ A A')
        (ObjectProperty.homMk biprod.inr) (sumJ δ δ')).symm.trans
        (congrArg (R.eta hR C' (biprodJ A A')) (cdData_pull_inr_sum D δ δ'))
    change biprod.inr ≫ (R.realBiprodIso hR C C').inv ≫
        R.eta hR (biprodJ C C') (biprodJ A A') (sumJ δ δ') ≫
          (R.realBiprodIso hR A A').hom⟦(1 : ℤ)⟧' =
      biprod.inr ≫ biprod.desc (R.eta hR C A δ ≫ biprod.inl⟦(1 : ℤ)⟧')
        (R.eta hR C' A' δ' ≫ biprod.inr⟦(1 : ℤ)⟧')
    rw [biprod.inr_desc, ← Category.assoc, e₁, ← Category.assoc, e₂, R.eta_push' hR,
      Category.assoc, ← Functor.map_comp]
    exact congrArg (fun φ => R.eta hR C' A' δ' ≫ φ⟦(1 : ℤ)⟧')
      (R.realMap_inr_comp_realBiprodIso hR A A')

end Axioms

end RealizationData

end ExtriangulatedRealization
