/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Statement

/-!
# Functors out of a one-point extension, and out of an additive envelope

A functor out of the one-point extension of `𝒜` by `Ψ` is given by a functor `F` on `𝒜`, an
object `X`, scalars `k → End X`, and maps `Ψ(a) → Hom(X, F a)` natural in `a`.

`matLift` is `Mat_.lift` for target categories in arbitrary universes.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Statement

universe u u₁ u₂ v₂

namespace OnePointExtension

variable {k : Type u} [CommRing k] {𝒜 : Type u₁} [Category.{u} 𝒜] [Preadditive 𝒜] [Linear k 𝒜]
  {Ψ : 𝒜 ⥤ ModuleCat.{u} k} [Ψ.Additive] [Ψ.Linear k]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] [Preadditive 𝒯]

/-- The data of a functor out of the one-point extension. -/
structure LiftData (Ψ : 𝒜 ⥤ ModuleCat.{u} k) (𝒯 : Type u₂) [Category.{v₂} 𝒯]
    [Preadditive 𝒯] where
  /-- The functor on `𝒜`. -/
  FB : 𝒜 ⥤ 𝒯
  [additive : FB.Additive]
  /-- The image of the adjoined object. -/
  Xt : 𝒯
  /-- The action of scalars on the adjoined object. -/
  sc : k → (Xt ⟶ Xt)
  /-- The morphisms out of the adjoined object. -/
  ι : ∀ a : 𝒜, Ψ.obj a → (Xt ⟶ FB.obj a)
  sc_one : sc 1 = 𝟙 Xt
  sc_mul : ∀ c c' : k, sc (c * c') = sc c ≫ sc c'
  sc_add : ∀ c c' : k, sc (c + c') = sc c + sc c'
  ι_add : ∀ (a : 𝒜) (x y : Ψ.obj a), ι a (x + y) = ι a x + ι a y
  ι_nat : ∀ {a b : 𝒜} (g : a ⟶ b) (x : Ψ.obj a), ι b ((Ψ.map g).hom x) = ι a x ≫ FB.map g
  ι_sc : ∀ (c : k) (a : 𝒜) (x : Ψ.obj a), sc c ≫ ι a x = ι a (c • x)

attribute [instance] LiftData.additive

variable (L : LiftData Ψ 𝒯)

omit [Linear k 𝒜] [Ψ.Additive] [Ψ.Linear k] in
lemma LiftData.sc_zero : L.sc 0 = 0 := by
  have h := L.sc_add 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

omit [Linear k 𝒜] [Ψ.Additive] [Ψ.Linear k] in
lemma LiftData.ι_zero (a : 𝒜) : L.ι a 0 = 0 := by
  have h := L.ι_add a 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The object map of the lift. -/
def liftObj : OnePointExtension 𝒜 Ψ → 𝒯
  | none => L.Xt
  | some a => L.FB.obj a

/-- The morphism map of the lift. -/
def liftMap : ∀ {X Y : OnePointExtension 𝒜 Ψ}, (X ⟶ Y) → (liftObj L X ⟶ liftObj L Y)
  | none, none, f => L.sc (show k from f)
  | none, some a, f => L.ι a f
  | some _, none, _ => 0
  | some _, some _, f => L.FB.map f

/-- The functor out of the one-point extension. -/
def lift : OnePointExtension 𝒜 Ψ ⥤ 𝒯 where
  obj := liftObj L
  map := liftMap L
  map_id X := by
    rcases X with _ | a
    · exact L.sc_one
    · exact L.FB.map_id a
  map_comp {X Y Z} f g := by
    rcases X with _ | a <;> rcases Y with _ | b <;> rcases Z with _ | c
    · exact L.sc_mul _ _
    · exact (L.ι_sc _ _ _).symm
    · change L.sc 0 = L.ι b f ≫ 0
      rw [L.sc_zero, comp_zero]
    · exact L.ι_nat _ _
    · exact (zero_comp).symm
    · change L.FB.map 0 = 0 ≫ L.ι _ g
      rw [L.FB.map_zero, zero_comp]
    · exact (comp_zero).symm
    · exact L.FB.map_comp _ _

instance lift_additive : (lift L).Additive where
  map_add {X Y} f g := by
    rcases X with _ | a <;> rcases Y with _ | b
    · exact L.sc_add _ _
    · exact L.ι_add _ _ _
    · exact (add_zero 0).symm
    · exact L.FB.map_add

/-! ### The inclusion of `𝒜`, and change of base -/

variable (Ψ) in
/-- The inclusion of `𝒜` into its one-point extension. -/
def incl : 𝒜 ⥤ OnePointExtension 𝒜 Ψ where
  obj a := some a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (incl Ψ).Additive where

instance : (incl Ψ).Linear k where

instance : (incl Ψ).Full where
  map_surjective f := ⟨f, rfl⟩

instance : (incl Ψ).Faithful where
  map_injective h := h

section Map

variable {𝒜' : Type*} [Category.{u} 𝒜'] [Preadditive 𝒜'] [Linear k 𝒜'] (F : 𝒜' ⥤ 𝒜)
  [F.Additive] [F.Linear k]

/-- The lift data of the functor induced by `F : 𝒜' ⥤ 𝒜` between one-point extensions. -/
def mapData : LiftData (F ⋙ Ψ) (OnePointExtension 𝒜 Ψ) where
  FB := F ⋙ incl Ψ
  Xt := none
  sc c := c
  ι _ x := x
  sc_one := rfl
  sc_mul _ _ := rfl
  sc_add _ _ := rfl
  ι_add _ _ _ := rfl
  ι_nat _ _ := rfl
  ι_sc _ _ _ := rfl

/-- The functor `OnePointExtension 𝒜' (F ⋙ Ψ) ⥤ OnePointExtension 𝒜 Ψ` induced by `F`. -/
def map : OnePointExtension 𝒜' (F ⋙ Ψ) ⥤ OnePointExtension 𝒜 Ψ := lift (mapData F)

instance : (map (Ψ := Ψ) F).Additive := lift_additive _

instance [F.Faithful] : (map (Ψ := Ψ) F).Faithful where
  map_injective {X Y} f g h := by
    rcases X with _ | a <;> rcases Y with _ | b
    · exact h
    · exact h
    · rfl
    · exact F.map_injective h

instance [F.Full] : (map (Ψ := Ψ) F).Full where
  map_surjective {X Y} f := by
    rcases X with _ | a <;> rcases Y with _ | b
    · exact ⟨f, rfl⟩
    · exact ⟨f, rfl⟩
    · exact ⟨PUnit.unit, rfl⟩
    · exact ⟨F.preimage f, F.map_preimage f⟩

end Map

end OnePointExtension

/-! ### `Mat_.lift` in arbitrary universes -/

section MatLift

variable {𝒞 : Type u₁} [Category.{u} 𝒞] [Preadditive 𝒞]
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [Preadditive 𝒟] [HasFiniteBiproducts 𝒟]
  (F : 𝒞 ⥤ 𝒟) [F.Additive]

attribute [local simp] biproduct.lift_desc

/-- An additive functor `𝒞 ⥤ 𝒟` extends to `Mat_ 𝒞 ⥤ 𝒟`. -/
@[simps]
noncomputable def matLift : Mat_ 𝒞 ⥤ 𝒟 where
  obj X := ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h
      simp
    · simp [h, Mat_.id_apply]
  map_comp {X Y Z} f g := by
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    simp [Mat_.comp_apply, Functor.map_sum]

instance matLift_additive : (matLift F).Additive where
  map_add {X Y} f g := by
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι _ i ≫ biproduct.matrix (fun i j => F.map (f i j + g i j)) ≫
      biproduct.π _ j = biproduct.ι _ i ≫ (biproduct.matrix (fun i j => F.map (f i j)) +
        biproduct.matrix (fun i j => F.map (g i j))) ≫ biproduct.π _ j
    rw [Preadditive.add_comp, Preadditive.comp_add, biproduct.matrix_π, biproduct.matrix_π,
      biproduct.matrix_π, biproduct.ι_desc, biproduct.ι_desc, biproduct.ι_desc, F.map_add]

lemma matLift_map_entry {M N : Mat_ 𝒞} (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    biproduct.ι (fun i => F.obj (M.X i)) i ≫ (matLift F).map f ≫
      biproduct.π (fun j => F.obj (N.X j)) j = F.map (f i j) := by
  change biproduct.ι (fun i => F.obj (M.X i)) i ≫
    biproduct.matrix (fun (i : M.ι) (j : N.ι) => F.map (f i j)) ≫
      biproduct.π (fun j => F.obj (N.X j)) j = F.map (f i j)
  simp only [biproduct.matrix_π, biproduct.ι_desc]

instance matLift_faithful [F.Faithful] : (matLift F).Faithful where
  map_injective {M N} f g h := by
    funext i j
    apply F.map_injective
    rw [← matLift_map_entry, ← matLift_map_entry, h]

instance matLift_full [F.Full] : (matLift F).Full where
  map_surjective {M N} h := by
    refine ⟨fun i j => F.preimage (biproduct.ι (fun i => F.obj (M.X i)) i ≫ h ≫
      biproduct.π (fun j => F.obj (N.X j)) j), ?_⟩
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    exact (matLift_map_entry F _ i j).trans (F.map_preimage _)

variable {F} in
/-- `matLift` sends natural isomorphisms to natural isomorphisms. -/
noncomputable def matLiftMapIso {G : 𝒞 ⥤ 𝒟} [G.Additive] (α : F ≅ G) : matLift F ≅ matLift G :=
  NatIso.ofComponents (fun M => biproduct.mapIso fun i => α.app (M.X i)) (by
    intro M N f
    change biproduct.matrix (fun i j => F.map (f i j)) ≫
        biproduct.map (fun b => α.hom.app (N.X b)) =
      biproduct.map (fun b => α.hom.app (M.X b)) ≫ biproduct.matrix (fun i j => G.map (f i j))
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    simp [α.hom.naturality])

/-- `matLift` commutes with additive functors. -/
noncomputable def matLiftCompIso {ℰ : Type*} [Category ℰ] [Preadditive ℰ] [HasFiniteBiproducts ℰ]
    (H : 𝒟 ⥤ ℰ) [H.Additive] : matLift F ⋙ H ≅ matLift (F ⋙ H) :=
  NatIso.ofComponents (fun M => H.mapBiproduct _) (by
    intro M N f
    change H.map (biproduct.matrix (fun i j => F.map (f i j))) ≫
        biproduct.lift (fun j => H.map (biproduct.π (fun i => F.obj (N.X i)) j)) =
      biproduct.lift (fun j => H.map (biproduct.π (fun i => F.obj (M.X i)) j)) ≫
        biproduct.matrix (fun i j => H.map (F.map (f i j)))
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, Category.assoc, biproduct.lift_π, biproduct.matrix_π, biproduct.lift_desc,
      ← H.map_comp, biproduct.matrix_π, biproduct.desc_eq, H.map_sum]
    simp only [Functor.map_comp])

end MatLift

instance mapMat_linear {R : Type u} [CommRing R] {𝒞 𝒟 : Type*} [Category.{u} 𝒞] [Preadditive 𝒞]
    [Linear R 𝒞] [Category.{u} 𝒟] [Preadditive 𝒟] [Linear R 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive]
    [F.Linear R] : F.mapMat_.Linear R where
  map_smul {M N} f c := by
    funext i j
    exact F.map_smul c (f i j)

end ExtriangulatedRealization
