/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import LeanPool.GrothendieckVanishing.GeneratedSubsheaf
public import Mathlib.Topology.NoetherianSpace
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Diagrams of finitely generated subsheaves

The finite subsheaves of a sheaf on a Noetherian space form a filtered diagram
whose colimit is that sheaf. A finite induction reduces vanishing for the
diagram objects to vanishing for epi-images of extension by zero.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram

variable {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
noncomputable def finsetGenFunctor :
    Finset
        (TopCat.Presheaf.SectionIndex K) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Presheaf.finsetGeneratedSheaf hK S
  map h := TopCat.Presheaf.finsetImageInclGen hK h.le
  map_id S := by
    apply (cancel_mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S))).1
    rw [TopCat.Presheaf.finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃))).1
    rw [Category.assoc, TopCat.Presheaf.finsetImageInclGen_comp_ι,
      TopCat.Presheaf.finsetImageInclGen_comp_ι,
      TopCat.Presheaf.finsetImageInclGen_comp_ι]

attribute [local implicit_reducible] finsetGenFunctor

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor hK) :=
  Cocone.mk (TopCat.Presheaf.sheafOfIsSheaf hK)
    { app := fun S ↦ Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S)
      naturality := fun S S' h ↦ by
        change TopCat.Presheaf.finsetImageInclGen hK h.le ≫
            Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S') =
          Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S) ≫
            𝟙 (TopCat.Presheaf.sheafOfIsSheaf hK)
        rw [TopCat.Presheaf.finsetImageInclGen_comp_ι]
        exact (Category.comp_id _).symm }

attribute [local implicit_reducible] finsetGenCocone

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
noncomputable def finsetGenCoconeIsColimit :
    IsColimit (finsetGenCocone hK) := by
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  haveI hd_mono : Mono d := by
    have : IsConnected
        (Finset (TopCat.Presheaf.SectionIndex K)) := IsFiltered.isConnected _
    have : ∀ j, Mono ((finsetGenCocone hK).ι.app j) := fun j ↦
      show Mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK j)) from inferInstance
    have := NatTrans.mono_of_mono_app (finsetGenCocone hK).ι
    exact colim.map_mono' (finsetGenCocone hK).ι (colimit.isColimit _)
      (isColimitConstCocone _ _) d (fun j ↦ by
        change colimit.ι (finsetGenFunctor hK) j ≫
            colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK) =
          (finsetGenCocone hK).ι.app j
        exact colimit.ι_desc (finsetGenCocone hK) j)
  -- desc is epi: allSectionMap K factors through desc
  haveI hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Presheaf.SectionIndex K ↦ TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor hK) :=
      Sigma.desc fun σ ↦
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
          colimit.ι (finsetGenFunctor hK) {σ}
    have hfac : g ≫ d = TopCat.Presheaf.allSectionMap hK := by
      ext σ
      dsimp only [g, d]
      rw [← Category.assoc, Sigma.ι_comp_desc]
      calc
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
            factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
              colimit.ι (finsetGenFunctor hK) {σ} ≫ d =
          (Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
              TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ})) ≫
            (colimit.ι (finsetGenFunctor hK) {σ} ≫ d) := by
            rw [Category.assoc]
        _ = Sigma.ι (fun σ ↦ TopCat.Sheaf.zeroOutsideInt σ.fst) σ ≫
              TopCat.Presheaf.allSectionMap hK := by
          rw [show d = colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK) from rfl]
          simp_rw [Category.assoc]
          erw [colimit.ι_desc]
          rw [← Category.assoc]
          dsimp only [finsetGenCocone]
          rw [Category.assoc, Limits.image.fac]
          exact (Sigma.ι_comp_desc _ _).trans (Sigma.ι_comp_desc _ _).symm
    exact @epi_of_epi_fac _ _ _ _ _ g d (TopCat.Presheaf.allSectionMap hK)
      (TopCat.Presheaf.allSectionMap_epi (F := K) hK) hfac
  -- mono + epi → iso in abelian category
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor hK)).desc (finsetGenCocone hK)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor hK)).ofPointIso

end FilteredDiagram

section FinsetGenerated

variable {X : TopCat.{u}} {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}}
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (TopCat.Presheaf.sheafOfIsSheaf hG) m))
    (S : Finset
      (TopCat.Presheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := by
  classical
  suffices h : ∀ (T : Finset (TopCat.Presheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK T) m) from h S
  intro T; induction T using Finset.induction with
  | empty =>
    exact sheafH_subsingleton_of_isZero
      (IsZero.of_iso (isZero_zero _) (imageZero' (by
        ext ⟨σ, hσ⟩
        simp at hσ))) m
  | @insert σ₀ S' _ ih =>
    let h_sub := Finset.subset_insert σ₀ S'
    let f := TopCat.Presheaf.finsetImageInclGen hK h_sub
    let qIns := factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))
    let qS := factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK S')
    let g : TopCat.Sheaf.zeroOutsideInt σ₀.1 ⟶ cokernel f :=
      Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫ qIns ≫ cokernel.π f
    have : Epi g := by
      refine epi_of_epi_fac
        (f := Sigma.desc fun σ ↦ if h : σ.1 = σ₀ then eqToHom (by rw [h]) else 0)
        (h := qIns ≫ cokernel.π f) ?_
      ext ⟨σ, hσ⟩
      by_cases h : σ = σ₀
      · subst h
        rw [← Category.assoc, Sigma.ι_comp_desc]
        simp [g]
      · rw [← Category.assoc, Sigma.ι_comp_desc, dite_eq_right h, zero_comp]
        have hfacBase :
            TopCat.Presheaf.finsetCoproductInclGen h_sub ≫ qIns = qS ≫ f := by
          simp [qIns, qS, f, TopCat.Presheaf.finsetImageInclGen]
        have hfac' :=
          congrArg (fun e ↦ Sigma.ι
            (fun τ : {τ // τ ∈ S'} ↦ TopCat.Sheaf.zeroOutsideInt τ.1.1)
            ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫ e ≫ cokernel.π f) hfacBase
        have hzero_rhs :
            Sigma.ι
                (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1)
                ⟨σ, hσ⟩ ≫ qIns ≫ cokernel.π f = 0 := by
          simpa [TopCat.Presheaf.finsetCoproductInclGen, Category.assoc, h,
            cokernel.condition, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using hfac'
        exact hzero_rhs.symm
    exact subsingleton_sheafH_of_shortExact_middle f m ih <|
      hzero (cokernel f).property g.hom
        ((TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance)

end FinsetGenerated
