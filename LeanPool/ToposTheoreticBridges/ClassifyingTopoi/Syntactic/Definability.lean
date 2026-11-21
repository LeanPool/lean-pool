/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Generic
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.NormalForm

/-!
# Definability of subobjects of the generic structure

Every subobject of a power of the generic structure on the Horn category is the interpretation
of a geometric formula (`HornCat.exists_interp_genericPsh_eq`). A subobject `S` of `y ⊤ₙ` is the
union of the images of the morphisms `y c ⟶ y ⊤ₙ` given by its sections `s ∈ S(c)`, that is of
tuples `σ` of terms in the context of `c`; such an image is the interpretation of the formula
`∃ y, c(y) ∧ x = σ(y)` (`HornCat.imageFormula`), as is checked in the term models.

Every subobject of `L X`, for a left exact reflector `L` (a left adjoint with invertible counit),
is the image under `L` of a subobject of `X` (`exists_mapSubobject_eq`). Hence subobjects of
powers of the sheafified generic structure are definable too, for every topology on the Horn
category.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi
  Opposite

section Reflective

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [HasPullbacks 𝒞] [HasPullbacks 𝒟]
  {F : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} [PreservesLimitsOfShape WalkingCospan F]
  [F.PreservesMonomorphisms]

/-- Every subobject of the image of an object under a reflector preserving pullbacks is the
image of a subobject. -/
theorem exists_mapSubobject_eq (adj : F ⊣ R) [IsIso adj.counit] {X : 𝒞} {Y : 𝒟}
    (c : F.obj X ⟶ Y) [IsIso c]
    (S : Subobject Y) : ∃ Q : Subobject X, mapSubobject F c Q = S := by
  have : R.PreservesMonomorphisms := Functor.preservesMonomorphisms_of_adjunction adj
  refine ⟨(Subobject.pullback (adj.unit.app X)).obj
    (Subobject.mk (R.map (S.arrow ≫ inv c))), ?_⟩
  rw [mapSubobject_pullback c (adj.counit.app (F.obj X) ≫ c), mapSubobject_mk]
  have h₁ : inv c ≫ F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) ≫ c = 𝟙 _ := by
    rw [← Category.assoc (F.map _), Adjunction.left_triangle_components, Category.id_comp,
      IsIso.inv_hom_id]
  rw [h₁, Subobject.pullback_id]
  have h₂ : F.map (R.map (S.arrow ≫ inv c)) ≫ adj.counit.app (F.obj X) ≫ c =
      adj.counit.app S ≫ S.arrow := by
    rw [← Category.assoc]
    erw [adj.counit_naturality]
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  conv_rhs => rw [← Subobject.mk_arrow S]
  exact Subobject.mk_eq_mk_of_comm _ _ (asIso (adj.counit.app S)) h₂.symm

end Reflective

variable {L : Language.{u₁, u₂}}

namespace HornCat

/-- The graph of a tuple of terms `σ` in the context of `c`: the Horn formula
`c(y) ∧ x = σ(y)` in the context `(x, y)`. -/
abbrev graph (c : HornCat.{u} L) {n : ℕ} (σ : Fin n → L.Term (Fin c.n)) : HornCat.{u} L :=
  ⟨n + c.n, c.atoms.map (Atom.relabel (Fin.natAdd n)) ++
    List.ofFn fun j => Atom.equal (Term.var (Fin.castAdd c.n j)) ((σ j).relabel (Fin.natAdd n))⟩

/-- Satisfaction of the graph of a tuple of terms. -/
theorem holds_graph {M : Type*} [L.Structure M] (c : HornCat.{u} L) {n : ℕ}
    (σ : Fin n → L.Term (Fin c.n)) (z : Fin (n + c.n) → M) :
    (graph c σ).Holds z ↔ c.Holds (z ∘ Fin.natAdd n) ∧
      ∀ j, z (Fin.castAdd c.n j) = (σ j).realize (z ∘ Fin.natAdd n) := by
  constructor
  · intro h
    refine ⟨fun a ha => (Atom.realize_relabel _ _ _).1
      (h _ (List.mem_append_left _ (List.mem_map_of_mem ha))), fun j => ?_⟩
    have := h _ (List.mem_append_right _ (List.mem_ofFn.2 ⟨j, rfl⟩))
    exact Eq.trans this Term.realize_relabel
  · rintro ⟨h₁, h₂⟩ a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact (Atom.realize_relabel _ _ _).2 (h₁ b hb)
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
      exact (h₂ j).trans Term.realize_relabel.symm

/-- The formula `∃ y, c(y) ∧ x = σ(y)` defining the image of a tuple of terms. -/
def imageFormula (c : HornCat.{u} L) {n : ℕ} (σ : Fin n → L.Term (Fin c.n)) :
    GeometricFormula.{max u₁ u₂ u} L n :=
  GeometricFormula.exs (m := c.n) (graph c σ).toFormula

/-- The image formula in the term models: it holds at a tuple of terms `τ` in the context of `d`
iff `τ` factors through `σ`. -/
theorem realize_imageFormula (c d : HornCat.{u} L) {n : ℕ} (σ : Fin n → L.Term (Fin c.n))
    (τ : Fin n → L.Term (Fin d.n)) :
    @GeometricFormula.Realize L _ ((genericPsh L).fiberStr (op d)) n (imageFormula c σ)
        (fun i => cls d (τ i)) ↔
      ∃ (ρ : Fin c.n → L.Term (Fin d.n)) (hρ : IsMor d c ρ), toTop d τ = mor ρ hρ ≫ toTop c σ := by
  rw [imageFormula,
    @GeometricFormula.realize_exs L _ ((genericPsh L).fiberStr (op d)) n c.n _ _]
  constructor
  · rintro ⟨y, hy⟩
    choose ρ hρ using fun j => exists_eq_cls (y j)
    have e : Fin.append (fun i => cls d (τ i)) y = fun k => cls d (Fin.append τ ρ k) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simp
      · simp [hρ]
    rw [e, realize_toFormula, genericPsh_holds] at hy
    have key := fun M (_ : L.Structure M) x hx => (holds_graph c σ _).1 (hy M x hx)
    refine ⟨ρ, fun M _ x hx => ?_, toTop_eq_toTop_iff.2 fun M _ x hx j => ?_⟩
    · simpa [Function.comp_def] using (key M _ x hx).1
    · have := (key M _ x hx).2 j
      simp only [Fin.append_left, Function.comp_def, Fin.append_right] at this
      simpa [Term.realize_subst] using this
  · rintro ⟨ρ, hρ, h⟩
    refine ⟨fun j => cls d (ρ j), ?_⟩
    have e : Fin.append (fun i => cls d (τ i)) (fun j => cls d (ρ j)) =
        fun k => cls d (Fin.append τ ρ k) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
    rw [e, realize_toFormula, genericPsh_holds]
    intro M _ x hx
    have h' := toTop_eq_toTop_iff.1 h M x hx
    refine (holds_graph c σ _).2 ⟨?_, fun j => ?_⟩
    · simpa [Function.comp_def] using hρ M x hx
    · simp only [Fin.append_left, Function.comp_def, Fin.append_right]
      simpa [Term.realize_subst] using h' j

/-- **Definability in the presheaf topos.** Every subobject of a power of the generic structure
on the Horn category is the interpretation of a geometric formula. -/
theorem exists_interp_genericPsh_eq {n : ℕ} (S : Subobject ((genericPsh.{u} L).pow n)) :
    ∃ ψ : GeometricFormula.{max u₁ u₂ u} L n, (genericPsh L).interp ψ = S := by
  let ι := Σ c : HornCat.{u} L, (S : (HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)).obj (op c)
  let w : ∀ i : ι, i.1 ⟶ top n := fun i =>
    (isoPow (yoneda : HornCat.{u} L ⥤ _) n).inv.app (op i.1) (S.arrow.app (op i.1) i.2)
  choose σ hσ hw using fun i => exists_eq_mor (w i)
  refine ⟨.iSup fun i : ι => imageFormula i.1 (σ i), le_antisymm ?_ ?_⟩ <;>
    rw [le_iff_range_app_subset] <;> intro d <;>
    induction d using Opposite.rec with | op d => ?_
  · intro z hz
    rw [mem_range_interp_app_iff] at hz
    obtain ⟨v, rfl⟩ : ∃ v, (isoPow (yoneda : HornCat.{u} L ⥤ _) n).hom.app (op d) v = z :=
      ⟨(isoPow (yoneda : HornCat.{u} L ⥤ _) n).inv.app (op d) z, by simp⟩
    obtain ⟨τ, hτ, rfl⟩ := exists_eq_mor v
    rw [secEquiv_isoPow_hom] at hz
    obtain ⟨i, hi⟩ := hz
    obtain ⟨ρ, hρ, h⟩ := (realize_imageFormula i.1 d (σ i) τ).1 hi
    refine ⟨(S : (HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)).map (mor ρ hρ).op i.2, ?_⟩
    rw [NatTrans.naturality_apply]
    have e₁ : S.arrow.app (op i.1) i.2 =
        (isoPow (yoneda : HornCat.{u} L ⥤ _) n).hom.app (op i.1) (w i) := by
      simp [w]
    rw [e₁, ← NatTrans.naturality_apply]
    change _ = (isoPow (yoneda : HornCat.{u} L ⥤ _) n).hom.app (op d) (mor τ hτ)
    congr 1
    change mor ρ hρ ≫ w i = mor τ hτ
    rw [hw i]
    exact h.symm
  · rintro _ ⟨s, rfl⟩
    rw [mem_range_interp_app_iff]
    let i : ι := ⟨d, s⟩
    have hz : S.arrow.app (op d) s =
        (isoPow (yoneda : HornCat.{u} L ⥤ _) n).hom.app (op d) (mor (σ i) (hσ i)) := by
      rw [← hw i]
      simp [w, i]
    rw [hz, secEquiv_isoPow_hom]
    refine ⟨i, (realize_imageFormula d d (σ i) (σ i)).2 ⟨fun j => Term.var j, isMor_id d, ?_⟩⟩
    exact toTop_eq_toTop_iff.2 fun _ _ _ _ _ => by simp

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
