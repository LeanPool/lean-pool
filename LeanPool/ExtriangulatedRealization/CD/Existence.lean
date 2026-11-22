/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Parts
public import Mathlib.Algebra.Homology.ShortComplex.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Every extension class of `C(D)` is realized

A good representation embeds into a finite direct sum of the injectives `k_{[*,t]}`. Hence every
class `ξ ∈ Ext¹(C', A')` between good representations is the pullback of the class of
`A' ↪ J ↠ J/A'` along some `C' ⟶ J/A'`, so it is the class of a short exact sequence whose
middle term is good (Lemma 2.1), hence a finite direct sum of intervals. Lifting the maps along
the fully faithful functor `ρ` gives a realization in `C(D)` (Construction 2.2).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Abelian

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasExt.standard

/-- A good representation embeds into a good injective representation. -/
theorem IsGood.exists_mono_injective {E : Finset I} {M : Rep k I} (hM : IsGood E M) :
    ∃ (J : Rep k I) (_ : Injective J) (j : M ⟶ J), Mono j ∧ IsGood E J := by
  classical
  let T : Finset (WithBot I) := insert ⊥ (E.image (fun e : I => (e : WithBot I)))
  let ι := Σ t : T, Fin (Module.finrank k (M.obj t.1))
  have := fun t => hM.finite t
  let b : ∀ t : T, Module.Basis (Fin (Module.finrank k (M.obj t.1))) k (M.obj t.1) :=
    fun t => Module.finBasis k (M.obj t.1)
  let f : ι → Rep k I := fun p => lowerRep (k := k) p.1.1
  have : ∀ p, Injective (f p) := fun p => lowerRep_injective _
  let j : M ⟶ ⨁ f := biproduct.lift (fun p => toLower M p.1.1 ((b p.1).coord p.2))
  have hgood : ∀ p : ι, IsGood E (f p) := by
    rintro ⟨⟨t, ht⟩, _⟩
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact isGood_rep E IntervalLabel.Y trivial
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht'
      exact isGood_rep E (IntervalLabel.P e) he
  refine ⟨⨁ f, inferInstance, j, ?_, IsGood.biproduct ι f hgood⟩
  rw [NatTrans.mono_iff_mono_app]
  intro s
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro m hm
  have hcomp : ∀ p : ι, ((toLower M p.1.1 ((b p.1).coord p.2)).app s).hom m = 0 := by
    intro p
    have h := congrArg (fun φ => ((biproduct.π f p).app s).hom φ) hm
    simp only [map_zero] at h
    rw [← h, ← ModuleCat.comp_apply, ← NatTrans.comp_app, biproduct.lift_π]
  have hzero : ∀ (t : T) (hst : s ≤ t.1), smap M hst m = 0 := by
    intro t hst
    apply (b t).ext_elem
    intro c
    refine (congrFun (hcomp ⟨t, c⟩) ⟨(), hst⟩).trans ?_
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
  by_contra hm0
  induction s using WithBot.recBotCoe with
  | bot =>
    exact hm0 ((smap_self M ⊥ m).symm.trans (hzero ⟨⊥, Finset.mem_insert_self _ _⟩ le_rfl))
  | coe s =>
    obtain ⟨e, he, hse, hne⟩ := hM.survive m hm0
    exact hne (hzero ⟨(e : WithBot I), Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ he)⟩
      (WithBot.coe_le_coe.mpr hse))

/-- Every class in `Ext¹(C', A')` between good representations is the class of a short exact
sequence with good middle term. -/
theorem exists_shortExact_of_ext {E : Finset I} {A' C' : Rep k I} (hA : IsGood E A')
    (hC : IsGood E C') (ξ : Ext C' A' 1) :
    ∃ (M : Rep k I) (f : A' ⟶ M) (g : M ⟶ C') (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact), hS.extClass = ξ ∧ IsGood E M := by
  obtain ⟨J, hJ, j, hj, -⟩ := hA.exists_mono_injective
  let S₀ := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS₀ : S₀.ShortExact :=
    ShortComplex.ShortExact.mk' (S₀.exact_of_g_is_cokernel (cokernelIsCokernel j)) hj
      inferInstance
  have h0 : ξ.comp (Ext.mk₀ S₀.f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ C' hS₀ ξ h0 (zero_add 1)
  let g := Ext.addEquiv₀ x₃
  have hg : Ext.mk₀ g = x₃ := Ext.mk₀_addEquiv₀_apply x₃
  have hS := hS₀.pull g
  refine ⟨pullback g S₀.g, pullback.lift 0 S₀.f (by simp), pullback.fst _ _, (S₀.pull g).zero,
    hS, ?_, IsGood.of_shortExact E hS hA hC⟩
  let φ : S₀.pull g ⟶ S₀ :=
    { τ₁ := 𝟙 _
      τ₂ := pullback.snd _ _
      τ₃ := g
      comm₁₂ := by simp
      comm₂₃ := by
        change pullback.snd g S₀.g ≫ S₀.g = pullback.fst g S₀.g ≫ g
        exact pullback.condition.symm }
  have h := hS.extClass_naturality hS₀ φ
  rw [hg, hx₃] at h
  exact (Ext.comp_mk₀_id _).symm.trans h

/-! ### Realizations in `C(D)` -/

/-- The indices occurring in a label. -/
def labelIdx : Option (IntervalLabel I) → Finset I
  | none => ∅
  | some Y => ∅
  | some (A i) => {i}
  | some (P i) => {i}

omit [Field k] [LinearOrder I] in
lemma labelIn_of_labelIdx {E : Finset I} (l : Option (IntervalLabel I)) (h : labelIdx l ⊆ E) :
    labelIn (E : Set I) l := by
  rcases l with _ | _ | i | i
  · trivial
  · trivial
  · exact h (Finset.mem_singleton_self i)
  · exact h (Finset.mem_singleton_self i)

variable (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The indices occurring in an object of `C(D)`. -/
noncomputable def objIdx (M : CD D) : Finset I :=
  (Finset.univ : Finset M.ι).biUnion (fun i => labelIdx (M.X i))

lemma labelIn_objIdx {E : Finset I} (M : CD D) (h : objIdx D M ⊆ E) :
    ∀ i, labelIn (E : Set I) (M.X i) := fun i =>
  labelIn_of_labelIdx _ ((Finset.subset_biUnion_of_mem _ (Finset.mem_univ i)).trans h)

lemma isZero_rho_biprod_xParts (A C : CD D) :
    IsZero ((rho D).obj (xPart D A ⊞ xPart D C)) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← biprod.total, Functor.map_add,
    Functor.map_comp, Functor.map_comp, (isZero_rho_xPart D A).eq_of_src ((rho D).map biprod.inl) 0,
    (isZero_rho_xPart D C).eq_of_src ((rho D).map biprod.inr) 0, comp_zero, comp_zero, add_zero]

variable [WellFoundedLT I] [Nonempty I]

/-- A good representation is `ρ` of an object without copies of `X`. -/
lemma exists_xFree_of_isGood {E : Finset I} {M : Rep k I} (hM : IsGood E M) :
    ∃ N : CD D, XFree D N ∧ Nonempty ((rho D).obj N ≅ M) := by
  obtain ⟨ι, _, L, -, ⟨eM⟩⟩ := IsGood.decompose (measure M) M hM le_rfl
  exact ⟨{ ι := ι, X := fun i => some (L i) }, fun _ => rfl, ⟨eM.symm⟩⟩

/-- A short exact sequence `ρA → M → ρC` with good middle term gives a realization of its class
whose middle term has `ρ`-image `M`. -/
theorem exists_realizes_of_shortExact {A C : CD D} {E : Finset I} {M : Rep k I} (hM : IsGood E M)
    (f : (rho D).obj A ⟶ M) (g : M ⟶ (rho D).obj C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    ∃ (B : CD D) (x : A ⟶ B) (y : B ⟶ C),
      (cdData D).Realizes hS.extClass x y ∧ Nonempty ((rho D).obj B ≅ M) := by
  classical
  obtain ⟨N, hN, ⟨eN⟩⟩ := exists_xFree_of_isGood D hM
  obtain ⟨x'', hx''⟩ := (rho_map_bijective D (xFree_bPart D A) hN).2
    ((rhoBPartIso D A).hom ≫ f ≫ eN.inv)
  obtain ⟨y'', hy''⟩ := (rho_map_bijective D hN (xFree_bPart D C)).2
    (eN.hom ≫ g ≫ (rhoBPartIso D C).inv)
  let x' : A ⟶ N := bProj D A ≫ x''
  let y' : N ⟶ C := y'' ≫ bIncl D C
  have hρx' : (rho D).map x' = f ≫ eN.inv := by
    simp only [x', Functor.map_comp, hx'']
    rw [← Category.assoc, rhoBPartIso, ← Functor.map_comp, rho_bProj_bIncl, Category.id_comp]
  have hρy' : (rho D).map y' = eN.hom ≫ g := by
    simp only [y', Functor.map_comp, hy'', Category.assoc]
    rw [rhoBPartIso, ← Functor.map_comp, bProj, bIncl, ← bProj, ← bIncl, rho_bProj_bIncl]
    simp
  have hx''y'' : x'' ≫ y'' = 0 := by
    apply (rho_map_bijective D (xFree_bPart D A) (xFree_bPart D C)).1
    rw [Functor.map_comp, hx'', hy'', Functor.map_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc f, w, zero_comp, comp_zero]
  let B : CD D := N ⊞ (xPart D A ⊞ xPart D C)
  let x : A ⟶ B := biprod.lift x' (biprod.lift (xProj D A) 0)
  let y : B ⟶ C := biprod.desc y' (biprod.desc 0 (xIncl D C))
  have hxy : x ≫ y = 0 := by
    simp only [x, y, biprod.lift_desc, comp_zero, zero_comp, add_zero, x', y',
      Category.assoc]
    rw [← Category.assoc x'', hx''y'', zero_comp, comp_zero]
  have hZ := isZero_rho_biprod_xParts D A C
  have hsnd : (rho D).map (biprod.snd : B ⟶ _) = 0 := hZ.eq_of_tgt _ _
  have hfst_inl : (rho D).map (biprod.fst : B ⟶ N) ≫ (rho D).map biprod.inl = 𝟙 _ := by
    rw [← Functor.map_comp, ← sub_eq_iff_eq_add.mpr (biprod.total (X := N)
      (Y := xPart D A ⊞ xPart D C)).symm, Functor.map_sub, CategoryTheory.Functor.map_id,
      Functor.map_comp, hsnd, zero_comp, sub_zero]
  let e₂ : (rho D).obj B ≅ M :=
    { hom := (rho D).map biprod.fst ≫ eN.hom
      inv := eN.inv ≫ (rho D).map biprod.inl
      hom_inv_id := by
        rw [Category.assoc, Iso.hom_inv_id_assoc, hfst_inl]
      inv_hom_id := by
        rw [Category.assoc, ← Category.assoc ((rho D).map _), ← Functor.map_comp, biprod.inl_fst,
          CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id] }
  let S' := ShortComplex.mk ((rho D).map x) ((rho D).map y)
    (by rw [← Functor.map_comp, hxy, Functor.map_zero])
  let eS : S' ≅ ShortComplex.mk f g w :=
    ShortComplex.isoMk (Iso.refl _) e₂ (Iso.refl _)
      (by
        change 𝟙 _ ≫ f = (rho D).map x ≫ (rho D).map biprod.fst ≫ eN.hom
        rw [Category.id_comp, ← Category.assoc, ← Functor.map_comp, biprod.lift_fst, hρx',
          Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by
        change ((rho D).map biprod.fst ≫ eN.hom) ≫ g = (rho D).map y ≫ 𝟙 _
        rw [Category.comp_id, show (rho D).map y =
            (rho D).map (biprod.desc y' (biprod.desc 0 (xIncl D C))) from rfl, biprod.desc_eq,
          Functor.map_add, (rho D).map_comp biprod.fst y', (rho D).map_comp biprod.snd, hsnd,
          zero_comp, add_zero, hρy', Category.assoc])
  have hS' : S'.ShortExact := ShortComplex.shortExact_of_iso eS.symm hS
  refine ⟨B, x, y, ⟨hxy, ⟨hS', ?_⟩, N, hN, Iso.refl B, x', y', ?_, Category.comp_id x,
    Category.id_comp y⟩, ⟨e₂⟩⟩
  · have h := hS'.extClass_naturality hS eS.hom
    change hS'.extClass.comp (Ext.mk₀ (𝟙 _)) (add_zero 1) =
      (Ext.mk₀ (𝟙 _)).comp hS.extClass (zero_add 1) at h
    rw [Ext.comp_mk₀_id, Ext.mk₀_id_comp] at h
    exact h
  · simp only [x', ← Category.assoc, xIncl_bProj, zero_comp]

/-- **Existence of realizations** for `C(D)` (Construction 2.2, using Lemma 2.1). -/
theorem cd_exists_realizes {A C : CD D} (ξ : (cdData D).Ext C A) :
    ∃ (B : CD D) (x : A ⟶ B) (y : B ⟶ C), (cdData D).Realizes ξ x y := by
  let E := objIdx D A ∪ objIdx D C
  have hA := isGood_rho D E A (labelIn_objIdx D A Finset.subset_union_left)
  have hC := isGood_rho D E C (labelIn_objIdx D C Finset.subset_union_right)
  obtain ⟨M, f, g, w, hS, hcls, hM⟩ := exists_shortExact_of_ext hA hC ξ
  obtain ⟨B, x, y, h, -⟩ := exists_realizes_of_shortExact D hM f g w hS
  exact ⟨B, x, y, hcls ▸ h⟩

end ExtriangulatedRealization
