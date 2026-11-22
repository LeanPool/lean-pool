/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Complexes.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# The homotopy category of an additive category is algebraic

With the degreewise split exact structure, `CochainComplex C ℤ` is a Frobenius exact category
whose projective-injective objects are the contractible complexes (Keller, *Chain complexes and
stable categories*, Section 1). The quotient functor to the homotopy category kills exactly the
morphisms factoring through a contractible complex, which are the null-homotopic ones, and sends
a degreewise split conflation to the distinguished triangle of
`CochainComplex.trianglehOfDegreewiseSplit`, whose connecting morphism is natural. Hence
`HomotopyCategory C (ComplexShape.up ℤ)` is an algebraic triangulated category.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits HomologicalComplex Statement Pretriangulated CochainComplex HomComplex
  Homotopy

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### The connecting morphism is natural -/

/-- The identity behind the naturality of the connecting morphism of degreewise split sequences,
in two consecutive degrees `p → q`. -/
lemma connecting_naturality_aux {X₂p X₃p Y₁p Y₂p Y₃p X₁q X₂q X₃q Y₁q Y₂q : C}
    {f'q : Y₁q ⟶ Y₂q} {fq : X₁q ⟶ X₂q} {f'p : Y₁p ⟶ Y₂p}
    {gp : X₂p ⟶ X₃p} {gq : X₂q ⟶ X₃q} {g'p : Y₂p ⟶ Y₃p}
    {sp : X₃p ⟶ X₂p} {sq : X₃q ⟶ X₂q} {s'p : Y₃p ⟶ Y₂p}
    {rq : X₂q ⟶ X₁q} {r'p : Y₂p ⟶ Y₁p} {r'q : Y₂q ⟶ Y₁q}
    {d₂ : X₂p ⟶ X₂q} {d₃ : X₃p ⟶ X₃q} {d₁' : Y₁p ⟶ Y₁q} {d₂' : Y₂p ⟶ Y₂q}
    {τ₁q : X₁q ⟶ Y₁q} {τ₂p : X₂p ⟶ Y₂p} {τ₂q : X₂q ⟶ Y₂q} {τ₃p : X₃p ⟶ Y₃p}
    (h1 : d₁' ≫ f'q = f'p ≫ d₂') (h2 : f'q ≫ r'q = 𝟙 _) (h3 : r'p ≫ f'p + g'p ≫ s'p = 𝟙 _)
    (h4 : gp ≫ d₃ = d₂ ≫ gq) (h5 : sp ≫ gp = 𝟙 _) (h6 : rq ≫ fq + gq ≫ sq = 𝟙 _)
    (h7 : τ₂p ≫ d₂' = d₂ ≫ τ₂q) (h8 : τ₂p ≫ g'p = gp ≫ τ₃p) (h9 : fq ≫ τ₂q = τ₁q ≫ f'q) :
    (sp ≫ τ₂p ≫ r'p) ≫ d₁' - d₃ ≫ sq ≫ τ₂q ≫ r'q =
      (sp ≫ d₂ ≫ rq) ≫ τ₁q - τ₃p ≫ s'p ≫ d₂' ≫ r'q := by
  have e1 : r'p ≫ d₁' = d₂' ≫ r'q - g'p ≫ s'p ≫ d₂' ≫ r'q := by
    calc r'p ≫ d₁' = r'p ≫ d₁' ≫ f'q ≫ r'q := by rw [h2, Category.comp_id]
      _ = (r'p ≫ f'p + g'p ≫ s'p - g'p ≫ s'p) ≫ d₂' ≫ r'q := by
          rw [add_sub_cancel_right, reassoc_of% h1, Category.assoc]
      _ = _ := by rw [h3, Preadditive.sub_comp, Category.id_comp, Category.assoc]
  have e2 : d₃ ≫ sq = sp ≫ d₂ - sp ≫ d₂ ≫ rq ≫ fq := by
    calc d₃ ≫ sq = sp ≫ gp ≫ d₃ ≫ sq := by rw [reassoc_of% h5]
      _ = sp ≫ d₂ ≫ (rq ≫ fq + gq ≫ sq - rq ≫ fq) := by
          rw [reassoc_of% h4, add_sub_cancel_left]
      _ = _ := by rw [h6, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id]
  have e3 : sp ≫ τ₂p ≫ g'p = τ₃p := by rw [h8, reassoc_of% h5]
  calc (sp ≫ τ₂p ≫ r'p) ≫ d₁' - d₃ ≫ sq ≫ τ₂q ≫ r'q
      = sp ≫ τ₂p ≫ (r'p ≫ d₁') - (d₃ ≫ sq) ≫ τ₂q ≫ r'q := by
        simp only [Category.assoc]
    _ = (sp ≫ d₂ ≫ rq) ≫ τ₁q - τ₃p ≫ s'p ≫ d₂' ≫ r'q := by
        rw [e1, e2, Preadditive.comp_sub, Preadditive.comp_sub, Preadditive.sub_comp,
          reassoc_of% h7]
        simp only [Category.assoc]
        rw [reassoc_of% e3, reassoc_of% h9, h2, Category.comp_id]
        abel

/-! ### Contractible complexes are the projective-injective objects -/

section Frobenius

variable [HasBinaryBiproducts C]

/-- A contractible complex: its identity is null-homotopic. -/
def IsContractible (K : CochainComplex C ℤ) : Prop := Nonempty (Homotopy (𝟙 K) 0)

variable [HasZeroObject C]

omit [HasBinaryBiproducts C] [HasZeroObject C] in
lemma id_eq_nullHomotopicMap {K : CochainComplex C ℤ} (h : Homotopy (𝟙 K) 0) :
    𝟙 K = nullHomotopicMap h.hom := by
  ext n
  rw [h.comm n, HomologicalComplex.zero_f, add_zero]
  rfl

lemma IsContractible.isInjectiveObject {P : CochainComplex C ℤ} (hP : IsContractible P) :
    (degreewiseSplit C).IsInjectiveObject P := by
  obtain ⟨h⟩ := hP
  intro S hS f
  refine ⟨nullHomotopicMap (fun i j => (hS i).some.r ≫ f.f i ≫ h.hom i j), ?_⟩
  rw [comp_nullHomotopicMap]
  conv_rhs => rw [← Category.comp_id f, id_eq_nullHomotopicMap h, comp_nullHomotopicMap]
  congr 1
  funext i j
  exact (hS i).some.f_r_assoc (f.f i ≫ h.hom i j)

lemma IsContractible.isProjectiveObject {P : CochainComplex C ℤ} (hP : IsContractible P) :
    (degreewiseSplit C).IsProjectiveObject P := by
  obtain ⟨h⟩ := hP
  intro S hS f
  refine ⟨nullHomotopicMap (fun i j => h.hom i j ≫ f.f j ≫ (hS j).some.s), ?_⟩
  rw [nullHomotopicMap_comp]
  conv_rhs => rw [← Category.id_comp f, id_eq_nullHomotopicMap h, nullHomotopicMap_comp]
  congr 1
  funext i j
  have e : (hS j).some.s ≫ S.g.f j = 𝟙 _ := (hS j).some.s_g
  rw [Category.assoc, Category.assoc, e]
  exact congrArg _ (Category.comp_id _)

omit [HasZeroObject C] in
/-- The degreewise split conflation `K ⟶ cone(𝟙 K) ⟶ K⟦1⟧`. -/
lemma isDegreewiseSplit_cone (K : CochainComplex C ℤ) :
    IsDegreewiseSplit (mappingCone.triangleRotateShortComplex (𝟙 K)) :=
  fun n => ⟨mappingCone.triangleRotateShortComplexSplitting (𝟙 K) n⟩

omit [HasZeroObject C] in
lemma isContractible_cone (K : CochainComplex C ℤ) : IsContractible (mappingCone (𝟙 K)) :=
  ⟨mappingCone.homotopyToZeroOfId K⟩

lemma IsContractible.of_isInjectiveObject {P : CochainComplex C ℤ}
    (hP : (degreewiseSplit C).IsInjectiveObject P) : IsContractible P := by
  obtain ⟨g, hg⟩ := hP _ (isDegreewiseSplit_cone P) (𝟙 P)
  let g' : mappingCone (𝟙 P) ⟶ P := g
  have hg' : mappingCone.inr (𝟙 P) ≫ g' = 𝟙 P := hg
  refine ⟨(Homotopy.ofEq ?_).trans
    ((((mappingCone.homotopyToZeroOfId P).compRight g').compLeft
      (mappingCone.inr (𝟙 P))).trans (Homotopy.ofEq ?_))⟩
  · rw [Category.id_comp, hg']
  · rw [zero_comp, comp_zero]

lemma IsContractible.of_isProjectiveObject {P : CochainComplex C ℤ}
    (hP : (degreewiseSplit C).IsProjectiveObject P) : IsContractible P := by
  let e : (P⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ P :=
    (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by norm_num)).app P
  obtain ⟨g, hg⟩ := hP _ (isDegreewiseSplit_cone (P⟦(-1 : ℤ)⟧)) e.inv
  let g' : P ⟶ mappingCone (𝟙 (P⟦(-1 : ℤ)⟧)) := g
  let q : mappingCone (𝟙 (P⟦(-1 : ℤ)⟧)) ⟶ P :=
    (mappingCone.triangleRotateShortComplex (𝟙 (P⟦(-1 : ℤ)⟧))).g ≫ e.hom
  have hq : g' ≫ q = 𝟙 P := by
    exact (Category.assoc g _ e.hom).symm.trans ((congrArg (· ≫ e.hom) hg).trans e.inv_hom_id)
  refine ⟨(Homotopy.ofEq ?_).trans
    ((((mappingCone.homotopyToZeroOfId _).compRight q).compLeft g').trans (Homotopy.ofEq ?_))⟩
  · rw [Category.id_comp, hq]
  · rw [zero_comp, comp_zero]

lemma degreewiseSplit_isFrobenius : (degreewiseSplit C).IsFrobenius := by
  refine ⟨fun X => ?_, fun X => ?_, fun P => ⟨fun h =>
    (IsContractible.of_isProjectiveObject h).isInjectiveObject,
    fun h => (IsContractible.of_isInjectiveObject h).isProjectiveObject⟩⟩
  · exact ⟨_, isDegreewiseSplit_cone (X⟦(-1 : ℤ)⟧), (isContractible_cone _).isProjectiveObject,
      ⟨(shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by norm_num)).app X⟩⟩
  · exact ⟨_, isDegreewiseSplit_cone X, (isContractible_cone X).isInjectiveObject, ⟨Iso.refl _⟩⟩

/-- A morphism of complexes is null-homotopic if and only if it factors through a projective
object of the degreewise split exact structure. -/
lemma quotient_map_eq_zero_iff_factors {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f = 0 ↔
      ∃ (P : CochainComplex C ℤ) (_ : (degreewiseSplit C).IsProjectiveObject P) (g : X ⟶ P)
        (h : P ⟶ Y), f = g ≫ h := by
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  constructor
  · rintro ⟨ho⟩
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f 0 ho
    refine ⟨mappingCone (𝟙 X), (isContractible_cone X).isProjectiveObject, mappingCone.inr _,
      mappingCone.desc (𝟙 X) z f (by rw [Category.id_comp, hz, Cochain.ofHom_zero, add_zero]),
      (mappingCone.inr_desc _ _ _ _).symm⟩
  · rintro ⟨P, hP, g, h, rfl⟩
    obtain ⟨c⟩ := IsContractible.of_isProjectiveObject hP
    exact ⟨(Homotopy.ofEq (by rw [Category.id_comp])).trans
      (((c.compRight h).compLeft g).trans (Homotopy.ofEq (by rw [zero_comp, comp_zero])))⟩

/-! ### Connecting morphisms -/

/-- The connecting morphism in the homotopy category of a degreewise split conflation. -/
noncomputable def connecting (S : ShortComplex (CochainComplex C ℤ)) (hS : IsDegreewiseSplit S) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (trianglehOfDegreewiseSplit S fun n => (hS n).some).mor₃

lemma connecting_distinguished (S : ShortComplex (CochainComplex C ℤ)) (hS : IsDegreewiseSplit S) :
    Triangle.mk ((HomotopyCategory.quotient C _).map S.f) ((HomotopyCategory.quotient C _).map S.g)
      (connecting S hS) ∈ distTriang _ :=
  trianglehOfDegreewiseSplit_distinguished S _

omit [HasBinaryBiproducts C] [HasZeroObject C] in
lemma quotient_map_homOfDegreewiseSplit_naturality {S S' : ShortComplex (CochainComplex C ℤ)}
    (σ : ∀ n, (S.map (eval C (ComplexShape.up ℤ) n)).Splitting)
    (σ' : ∀ n, (S'.map (eval C (ComplexShape.up ℤ) n)).Splitting) (φ : S ⟶ S') :
    (HomotopyCategory.quotient C _).map (homOfDegreewiseSplit S σ ≫ φ.τ₁⟦(1 : ℤ)⟧') =
      (HomotopyCategory.quotient C _).map (φ.τ₃ ≫ homOfDegreewiseSplit S' σ') := by
  have h₁ : homOfDegreewiseSplit S σ = Cocycle.equivHomShift.symm (cocycleOfDegreewiseSplit S σ) :=
    rfl
  have h₂ : homOfDegreewiseSplit S' σ' =
      Cocycle.equivHomShift.symm (cocycleOfDegreewiseSplit S' σ') := rfl
  rw [h₁, h₂, ← Cocycle.equivHomShift_symm_postcomp, ← Cocycle.equivHomShift_symm_precomp,
    ← CohomologyClass.toHom_mk, ← CohomologyClass.toHom_mk]
  congr 1
  rw [CohomologyClass.mk_eq_mk_iff, mem_coboundaries_iff _ 0 (by norm_num)]
  refine ⟨Cochain.ofHoms (fun p => (σ p).s ≫ φ.τ₂.f p ≫ (σ' p).r), ?_⟩
  ext p q hpq
  obtain rfl : q = p + 1 := by lia
  rw [δ_v 0 1 (by norm_num) _ p (p + 1) hpq p (p + 1) (by lia) rfl, Cochain.ofHoms_v,
    Cochain.ofHoms_v, Int.negOnePow_one, Units.neg_smul, one_smul, ← sub_eq_add_neg,
    Cocycle.coe_sub, Cochain.sub_v, Cocycle.postcomp_coe, Cocycle.precomp_coe,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  have hc : ∀ (T : ShortComplex (CochainComplex C ℤ))
      (τ : ∀ n, (T.map (eval C (ComplexShape.up ℤ) n)).Splitting),
      (cocycleOfDegreewiseSplit T τ).1.v p (p + 1) hpq =
        (τ p).s ≫ T.X₂.d p (p + 1) ≫ (τ (p + 1)).r :=
    fun T τ => rfl
  rw [hc, hc]
  exact connecting_naturality_aux (S'.f.comm p (p + 1)).symm (σ' (p + 1)).f_r (σ' p).id
    (S.g.comm p (p + 1)) (σ p).s_g (σ (p + 1)).id (φ.τ₂.comm p (p + 1))
    (HomologicalComplex.congr_hom φ.comm₂₃ p) (HomologicalComplex.congr_hom φ.comm₁₂ (p + 1)).symm

omit [HasBinaryBiproducts C] [HasZeroObject C] in
lemma connecting_naturality {S S' : ShortComplex (CochainComplex C ℤ)} (hS : IsDegreewiseSplit S)
    (hS' : IsDegreewiseSplit S') (φ : S ⟶ S') :
    connecting S hS ≫ ((HomotopyCategory.quotient C _).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (HomotopyCategory.quotient C _).map φ.τ₃ ≫ connecting S' hS' := by
  change ((HomotopyCategory.quotient C _).map (homOfDegreewiseSplit S fun n => (hS n).some) ≫
      ((HomotopyCategory.quotient C _).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫ _ =
    _ ≫ (HomotopyCategory.quotient C _).map (homOfDegreewiseSplit S' fun n => (hS' n).some) ≫
      ((HomotopyCategory.quotient C _).commShiftIso (1 : ℤ)).hom.app S'.X₁
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Category.assoc, ← Functor.map_comp,
    ← Category.assoc, ← Functor.map_comp, quotient_map_homOfDegreewiseSplit_naturality]

variable (C) in
/-- **The homotopy category of an additive category is algebraic.** -/
theorem isAlgebraicTriangulated_homotopyCategory :
    IsAlgebraicTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) :=
  ⟨CochainComplex C ℤ, inferInstance, inferInstance, inferInstance, degreewiseSplit C,
    HomotopyCategory.quotient C _, inferInstance, fun S hS => connecting S hS,
    degreewiseSplit_isFrobenius, inferInstance, inferInstance,
    quotient_map_eq_zero_iff_factors, fun S hS => connecting_distinguished S hS,
    fun _ _ hS hS' φ => connecting_naturality hS hS' φ⟩

end Frobenius

end ExtriangulatedRealization
