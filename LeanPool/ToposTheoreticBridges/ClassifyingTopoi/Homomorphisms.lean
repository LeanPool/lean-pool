/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.InverseImage

/-!
# Homomorphisms and isomorphisms of structures in a category

Basic facts on `CatStructure.IsHom` and `CatStructure.Isomorphic`, used in Layer 2 to compare
models through the universal property of classifying sites.

## Main results

* `LeanPool.ClassifyingTopoi.CatStructure.IsHom.id`, `IsHom.comp`, and `Isomorphic.refl`,
  `Isomorphic.symm`, `Isomorphic.trans`: isomorphism of structures is an equivalence relation;
* `LeanPool.ClassifyingTopoi.CatStructure.IsHom.interp_le`: a homomorphism `h : M ⟶ N` maps
  the interpretation of every geometric formula into its interpretation,
  `[[φ]]_M ≤ (hⁿ)^* [[φ]]_N`
  (the categorical form of the preservation of geometric formulas by homomorphisms); hence
  isomorphic structures are models of the same theories (`Isomorphic.isModel_iff`);
* `LeanPool.ClassifyingTopoi.CatStructure.isHom_map_app`, `isomorphic_map_of_iso`,
  `isomorphic_map_id`, `isomorphic_map_comp`: the image of a structure under functors is
  functorial up to isomorphism of structures;
* `LeanPool.ClassifyingTopoi.CatStructure.IsHom.map`, `Isomorphic.map`: a functor preserving
  finite limits and epimorphisms, into a strong-epi category, maps homomorphisms to
  homomorphisms.

The proof of `IsHom.interp_le` uses only the adjunction `∃_f ⊣ f^*` on subobjects
(`Subobject.existsPullbackAdj`), by induction on the formula.
-/

@[expose] public section

open CategoryTheory Limits

universe w u₁ u₂ v v' v'' u u' u''

namespace LeanPool.ClassifyingTopoi

variable {E : Type u} [Category.{v} E]

/-- The image of `f` lies in the pullback along `k` of the image of `g` when `f ≫ k` factors
through `g`. -/
theorem imageSubobject_le_pullback [HasImages E] [HasPullbacks E] {A B X Y : E} (f : A ⟶ X)
    (k : X ⟶ Y) (g : B ⟶ Y) (a : A ⟶ B) (w : f ≫ k = a ≫ g) :
    imageSubobject f ≤ (Subobject.pullback k).obj (imageSubobject g) :=
  imageSubobject_le f ((Subobject.isPullback k (imageSubobject g)).lift
    (a ≫ factorThruImageSubobject g) f (by simp [w])) (by simp)

/-- A subobject lies in the pullback of `T` along `k` when its arrow followed by `k` factors
through `T`. -/
theorem le_pullback_of_factors [HasPullbacks E] {X Y : E} (S : Subobject X) (k : X ⟶ Y)
    (T : Subobject Y) (hf : T.Factors (S.arrow ≫ k)) : S ≤ (Subobject.pullback k).obj T :=
  Subobject.le_pullback_of_comm k (T.factorThru _ hf) (by simp)

/-- A subobject below a pullback has its arrow, followed by the morphism, factoring through the
pulled back subobject. -/
theorem exists_comp_of_le_pullback [HasPullbacks E] {X Y : E} {S : Subobject X} {k : X ⟶ Y}
    {T : Subobject Y} (h : S ≤ (Subobject.pullback k).obj T) :
    ∃ a : (S : E) ⟶ T, S.arrow ≫ k = a ≫ T.arrow :=
  ⟨Subobject.ofLE _ _ h ≫ Subobject.pullbackπ k T, by
    rw [Category.assoc, (Subobject.isPullback k T).w, ← Category.assoc, Subobject.ofLE_arrow]⟩

variable {L : FirstOrder.Language.{u₁, u₂}}

namespace CatStructure

section Hom

variable [HasFiniteLimits E] [HasImages E]

/-- Terms commute with homomorphisms. -/
theorem IsHom.termMap {M N : CatStructure L E} {h : M.carrier ⟶ N.carrier} (hh : M.IsHom N h)
    {n : ℕ} (t : L.Term (Fin n)) :
    M.termMap t ≫ h = Limits.Pi.map (fun _ => h) ≫ N.termMap t := by
  induction t with
  | var i => simp [CatStructure.termMap]
  | func f ts ih =>
    simp only [CatStructure.termMap, Category.assoc, hh.funMap]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    ext j
    simp [ih]

/-- The identity is a homomorphism. -/
theorem IsHom.id (M : CatStructure L E) : M.IsHom M (𝟙 _) where
  funMap f := by simp
  relMap R := by simp [Subobject.pullback_id]

/-- Homomorphisms compose. -/
theorem IsHom.comp {M N P : CatStructure L E} {h : M.carrier ⟶ N.carrier}
    {h' : N.carrier ⟶ P.carrier} (hh : M.IsHom N h) (hh' : N.IsHom P h') :
    M.IsHom P (h ≫ h') where
  funMap f := by
    rw [← Category.assoc, hh.funMap, Category.assoc, hh'.funMap, ← Category.assoc]
    congr 1
    ext
    simp
  relMap {k} R := by
    refine (hh.relMap R).trans ?_
    have : (Limits.Pi.map fun _ : Fin k => h ≫ h') =
        Limits.Pi.map (fun _ => h) ≫ Limits.Pi.map (fun _ => h') := by
      ext
      simp
    rw [this, Subobject.pullback_comp]
    exact (Subobject.pullback _).monotone (hh'.relMap R)

/-- Isomorphism of structures is reflexive. -/
theorem Isomorphic.refl (M : CatStructure L E) : M.Isomorphic M :=
  ⟨Iso.refl _, IsHom.id M, IsHom.id M⟩

/-- Isomorphism of structures is symmetric. -/
theorem Isomorphic.symm {M N : CatStructure L E} (h : M.Isomorphic N) : N.Isomorphic M :=
  let ⟨e, h₁, h₂⟩ := h
  ⟨e.symm, h₂, h₁⟩

/-- Isomorphism of structures is transitive. -/
theorem Isomorphic.trans {M N P : CatStructure L E} (h : M.Isomorphic N) (h' : N.Isomorphic P) :
    M.Isomorphic P :=
  let ⟨e, h₁, h₂⟩ := h
  let ⟨e', h₁', h₂'⟩ := h'
  ⟨e ≪≫ e', h₁.comp h₁', h₂'.comp h₂⟩

variable [HasCoproducts.{w} E]

/-- A homomorphism maps the interpretation of a geometric formula into its interpretation. -/
theorem IsHom.interp_le {M N : CatStructure L E} {h : M.carrier ⟶ N.carrier}
    (hh : M.IsHom N h) {n : ℕ} (φ : GeometricFormula.{w} L n) :
    M.interp φ ≤ (Subobject.pullback (Limits.Pi.map fun _ : Fin n => h)).obj (N.interp φ) := by
  induction φ with
  | top => simp [interp, Subobject.pullback_top]
  | and φ ψ ihφ ihψ =>
    rw [interp, interp, Subobject.inf_pullback]
    exact inf_le_inf ihφ ihψ
  | iSup φ ih =>
    rw [interp, interp]
    choose a ha using fun i => exists_comp_of_le_pullback (ih i)
    refine imageSubobject_le_pullback _ _ _
      (Sigma.desc fun i => a i ≫ Sigma.ι (fun i => (N.interp (φ i) : E)) i) ?_
    ext i
    simp [ha]
  | equal t₁ t₂ =>
    rw [interp, interp]
    refine le_pullback_of_factors _ _ _ (equalizerSubobject_factors _ _ _ ?_)
    simp only [Category.assoc, ← hh.termMap]
    rw [← Category.assoc, equalizerSubobject_arrow_comp, Category.assoc]
  | @rel n k R ts =>
    rw [interp, interp, ← Subobject.pullback_comp]
    have : (Limits.Pi.map fun _ : Fin n => h) ≫ Pi.lift (fun i => N.termMap (ts i)) =
        Pi.lift (fun i => M.termMap (ts i)) ≫ Limits.Pi.map fun _ : Fin k => h := by
      ext i
      simp [hh.termMap]
    rw [this, Subobject.pullback_comp]
    exact (Subobject.pullback _).monotone (hh.relMap R)
  | @ex n φ ih =>
    rw [interp, interp]
    refine ((Subobject.existsPullbackAdj _).gc.le_iff_le).2 ?_
    rw [← Subobject.pullback_comp]
    have : (Pi.lift fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => M.carrier) i.castSucc) ≫
        (Limits.Pi.map fun _ : Fin n => h) = (Limits.Pi.map fun _ : Fin (n + 1) => h) ≫
        Pi.lift fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => N.carrier) i.castSucc := by
      ext i
      simp
    rw [this, Subobject.pullback_comp]
    exact ih.trans ((Subobject.pullback _).monotone (Subobject.le_pullback_exists _ _))

/-- Isomorphic structures are models of the same theories. -/
theorem Isomorphic.isModel {M N : CatStructure L E} (h : M.Isomorphic N)
    {T : GeometricTheory.{w} L} (hM : M.IsModel T) : N.IsModel T := by
  obtain ⟨e, h₁, h₂⟩ := h
  intro σ hσ
  refine (h₂.interp_le σ.lhs).trans (((Subobject.pullback _).monotone
    ((hM σ hσ).trans (h₁.interp_le σ.rhs))).trans (le_of_eq ?_))
  rw [← Subobject.pullback_comp]
  have : (Limits.Pi.map fun _ : Fin σ.n => e.inv) ≫ (Limits.Pi.map fun _ => e.hom) = 𝟙 _ := by
    ext
    simp
  rw [this, Subobject.pullback_id]

/-- Isomorphic structures are models of the same theories. -/
theorem Isomorphic.isModel_iff {M N : CatStructure L E} (h : M.Isomorphic N)
    {T : GeometricTheory.{w} L} : M.IsModel T ↔ N.IsModel T :=
  ⟨h.isModel, h.symm.isModel⟩

end Hom

section Map

variable {E' : Type u'} [Category.{v'} E'] {E'' : Type u''} [Category.{v''} E'']

/-- The comparison morphisms `F (Xᵏ) ⟶ (F X)ᵏ` are natural in `X`. -/
theorem map_piMap_comp_piComparison [HasFiniteProducts E] [HasFiniteProducts E'] (F : E ⥤ E')
    {X Y : E} (h : X ⟶ Y) (k : ℕ) :
    F.map (Limits.Pi.map fun _ : Fin k => h) ≫ piComparison F (fun _ => Y) =
      piComparison F (fun _ => X) ≫ Limits.Pi.map fun _ => F.map h := by
  ext j
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, Limits.Pi.map_π, Category.assoc,
    Limits.Pi.map_π, piComparison_comp_π_assoc, F.map_comp]

/-- The comparison morphisms are natural in the functor. -/
theorem app_comp_piComparison [HasFiniteProducts E] [HasFiniteProducts E'] {F G : E ⥤ E'}
    (α : F ⟶ G) (X : E) (k : ℕ) :
    α.app _ ≫ piComparison G (fun _ : Fin k => X) =
      piComparison F (fun _ => X) ≫ Limits.Pi.map fun _ => α.app X := by
  ext j
  simp

/-- The comparison morphism of a composite of functors. -/
theorem piComparison_comp' [HasFiniteProducts E] [HasFiniteProducts E'] [HasFiniteProducts E'']
    (F : E ⥤ E') (G : E' ⥤ E'') (X : E) (k : ℕ) :
    piComparison (F ⋙ G) (fun _ : Fin k => X) =
      G.map (piComparison F fun _ => X) ≫ piComparison G fun _ => F.obj X := by
  ext j
  simp only [piComparison_comp_π, Category.assoc, Functor.comp_obj]
  rw [← G.map_comp, piComparison_comp_π]
  exact piComparison_comp_π (F ⋙ G) (fun _ => X) j

/-- The inverse of the comparison morphism of a composite of functors preserving finite
products. -/
theorem inv_piComparison_comp [HasFiniteProducts E] [HasFiniteProducts E']
    [HasFiniteProducts E''] (F : E ⥤ E') (G : E' ⥤ E'') [PreservesFiniteProducts F]
    [PreservesFiniteProducts G] (X : E) (k : ℕ) :
    inv (piComparison (F ⋙ G) fun _ : Fin k => X) =
      inv (piComparison G fun _ => F.obj X) ≫ G.map (inv (piComparison F fun _ => X)) := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [piComparison_comp']
  simp

/-- The comparison morphism of the identity functor. -/
theorem piComparison_id [HasFiniteProducts E] (X : E) (k : ℕ) :
    piComparison (𝟭 E) (fun _ : Fin k => X) = 𝟙 _ := by
  ext j
  rw [piComparison_comp_π, Category.id_comp]
  rfl

variable [HasFiniteLimits E] [HasImages E] [HasFiniteLimits E'] [HasImages E']
  [HasFiniteLimits E''] [HasImages E'']

omit [HasFiniteLimits E] [HasImages E] in
/-- A natural transformation between functors preserving finite products induces a homomorphism
between the images of a structure. -/
theorem isHom_map_app [HasFiniteProducts E] (M : CatStructure L E) {F G : E ⥤ E'}
    [PreservesFiniteProducts F]
    [PreservesFiniteProducts G] (α : F ⟶ G) : (M.map F).IsHom (M.map G) (α.app M.carrier) where
  funMap {k} f := by
    have : inv (piComparison F fun _ : Fin k => M.carrier) ≫ α.app _ =
        (Limits.Pi.map fun _ => α.app M.carrier) ≫ inv (piComparison G fun _ => M.carrier) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, app_comp_piComparison]
    change (inv (piComparison F _) ≫ F.map (M.funMap f)) ≫ α.app _ =
      _ ≫ inv (piComparison G _) ≫ G.map (M.funMap f)
    rw [Category.assoc, α.naturality, ← Category.assoc, this, Category.assoc]
  relMap {k} R := by
    refine imageSubobject_le_pullback _ _ _ (α.app _) ?_
    change (F.map _ ≫ _) ≫ _ = α.app _ ≫ G.map _ ≫ _
    rw [Category.assoc, ← app_comp_piComparison, ← Category.assoc, α.naturality,
      Category.assoc]

omit [HasFiniteLimits E] [HasImages E] in
/-- The images of a structure under isomorphic functors are isomorphic. -/
theorem isomorphic_map_of_iso [HasFiniteProducts E] (M : CatStructure L E) {F G : E ⥤ E'}
    [PreservesFiniteProducts F]
    [PreservesFiniteProducts G] (α : F ≅ G) : (M.map F).Isomorphic (M.map G) :=
  ⟨α.app M.carrier, M.isHom_map_app α.hom, M.isHom_map_app α.inv⟩

/-- The image of a structure under the identity functor is isomorphic to it. -/
theorem isomorphic_map_id (M : CatStructure L E) : (M.map (𝟭 E)).Isomorphic M := by
  have key : ∀ {k : ℕ} {Y : E} (g : M.pow k ⟶ Y),
      inv (piComparison (𝟭 E) fun _ : Fin k => M.carrier) ≫ g = g := fun g => by
    rw [IsIso.inv_comp_eq, piComparison_id, Category.id_comp]
  refine ⟨Iso.refl _, ⟨fun f => ?_, fun R => ?_⟩, ⟨fun f => ?_, fun R => ?_⟩⟩
  · change (inv (piComparison (𝟭 E) _) ≫ M.funMap f) ≫ 𝟙 _ = _ ≫ M.funMap f
    rw [key]
    simp
  · refine imageSubobject_le_pullback _ _ _ (𝟙 _) ?_
    change ((M.relMap R).hom ≫ piComparison (𝟭 E) _) ≫ _ = _
    rw [piComparison_id]
    simp
  · change M.funMap f ≫ 𝟙 _ = _ ≫ inv (piComparison (𝟭 E) _) ≫ M.funMap f
    rw [key]
    simp
  · refine imageSubobject_le_pullback _ _ _ (𝟙 _) ?_
    change _ = 𝟙 _ ≫ (M.relMap R).hom ≫ piComparison (𝟭 E) _
    rw [piComparison_id]
    simp

section MapComp

omit [HasFiniteLimits E] [HasImages E] [HasFiniteLimits E'] [HasImages E']

variable [HasFiniteProducts E] [HasFiniteProducts E'] (M : CatStructure L E) (F : E ⥤ E')
  (G : E' ⥤ E'') [PreservesFiniteProducts F] [PreservesFiniteProducts G]

/-- The identity of carriers is a homomorphism from the image of a structure under a composite
functor to the iterated image. -/
theorem isHom_map_comp_hom : (M.map (F ⋙ G)).IsHom ((M.map F).map G) (𝟙 _) := by
  refine ⟨fun f => ?_, fun R => ?_⟩
  · change (inv (piComparison (F ⋙ G) _) ≫ G.map (F.map (M.funMap f))) ≫ 𝟙 _ =
      _ ≫ inv (piComparison G _) ≫ G.map (inv (piComparison F _) ≫ F.map (M.funMap f))
    rw [inv_piComparison_comp]
    simp
  · refine imageSubobject_le_pullback _ _ _ (𝟙 _) ?_
    change (G.map (F.map (M.relMap R).hom) ≫ piComparison (F ⋙ G) _) ≫ _ =
      𝟙 _ ≫ G.map (F.map (M.relMap R).hom ≫ piComparison F _) ≫ piComparison G _
    rw [piComparison_comp']
    simp

/-- The identity of carriers is a homomorphism from the iterated image of a structure to its
image under the composite functor. -/
theorem isHom_map_comp_inv : ((M.map F).map G).IsHom (M.map (F ⋙ G)) (𝟙 _) := by
  refine ⟨fun f => ?_, fun R => ?_⟩
  · change (inv (piComparison G _) ≫ G.map (inv (piComparison F _) ≫ F.map (M.funMap f))) ≫
      𝟙 _ = _ ≫ inv (piComparison (F ⋙ G) _) ≫ G.map (F.map (M.funMap f))
    rw [inv_piComparison_comp]
    simp
  · refine imageSubobject_le_pullback _ _ _ (𝟙 _) ?_
    change (G.map (F.map (M.relMap R).hom ≫ piComparison F _) ≫ piComparison G _) ≫ _ =
      𝟙 _ ≫ G.map (F.map (M.relMap R).hom) ≫ piComparison (F ⋙ G) _
    rw [piComparison_comp']
    simp

/-- The image of a structure under a composite functor is isomorphic to the iterated image. -/
theorem isomorphic_map_comp : (M.map (F ⋙ G)).Isomorphic ((M.map F).map G) :=
  ⟨Iso.refl _, M.isHom_map_comp_hom F G, M.isHom_map_comp_inv F G⟩

end MapComp

/-- A functor preserving finite limits and epimorphisms, into a strong-epi category, maps
homomorphisms to homomorphisms. -/
theorem IsHom.map {M N : CatStructure L E} {h : M.carrier ⟶ N.carrier} (hh : M.IsHom N h)
    [StrongEpiCategory E'] (F : E ⥤ E') [PreservesFiniteLimits F] [F.PreservesEpimorphisms] :
    (M.map F).IsHom (N.map F) (F.map h) where
  funMap {k} f := by
    have : inv (piComparison F fun _ : Fin k => M.carrier) ≫ F.map (Limits.Pi.map fun _ => h) =
        (Limits.Pi.map fun _ => F.map h) ≫ inv (piComparison F fun _ => N.carrier) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, map_piMap_comp_piComparison]
    change (inv (piComparison F _) ≫ F.map (M.funMap f)) ≫ F.map h =
      _ ≫ inv (piComparison F _) ≫ F.map (N.funMap f)
    rw [Category.assoc, ← F.map_comp, hh.funMap, F.map_comp, ← Category.assoc, this,
      Category.assoc]
  relMap {k} R := by
    change imageSubobject (F.map (M.relMap R).hom ≫ piComparison F _) ≤
      (Subobject.pullback _).obj (imageSubobject (F.map (N.relMap R).hom ≫ piComparison F _))
    rw [imageSubobject_map_comp, imageSubobject_map_comp]
    refine (mapSubobject_mono _ (hh.relMap R)).trans (le_of_eq ?_)
    rw [mapSubobject_pullback _ (piComparison F fun _ => N.carrier)]
    congr 2
    rw [IsIso.inv_comp_eq, map_piMap_comp_piComparison]

/-- Such a functor maps isomorphic structures to isomorphic structures. -/
theorem Isomorphic.map {M N : CatStructure L E} (hMN : M.Isomorphic N) [StrongEpiCategory E']
    (F : E ⥤ E') [PreservesFiniteLimits F] [F.PreservesEpimorphisms] :
    (M.map F).Isomorphic (N.map F) :=
  let ⟨e, h₁, h₂⟩ := hMN
  ⟨F.mapIso e, h₁.map F, h₂.map F⟩

end Map

end CatStructure

end LeanPool.ClassifyingTopoi
