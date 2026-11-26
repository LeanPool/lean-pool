/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import LeanPool.GrothendieckVanishing.AbelianSheaves
public import LeanPool.GrothendieckVanishing.CohomologyFoundations
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Connecting morphisms and low-degree sheaf cohomology
-/

@[expose] public section

universe w' w v u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

instance {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive D] :
    (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

instance {X : TopCat.{u}} :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
  inferInstanceAs ((Functor.const (Opens X)ᵒᵖ ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive)

-- `TopCat.Sheaf` is a semireducible definition, so instance search cannot see through it to
-- the site sheaves that `Ext` and `Sheaf.H` are stated for. These restate the relevant
-- structures with `TopCat.Sheaf` in the head position.
noncomputable instance sheafHAddCommGroup {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    AddCommGroup (Sheaf.H F n) :=
  Ext.instAddCommGroup

instance sheafPreadditive (X : TopCat.{u}) :
    Preadditive (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Preadditive (CategoryTheory.Sheaf _ _))

/-! ## Internal Ext helpers -/

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- If the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
    connecting morphism `Ext^n(Z, X₃) → Ext^(n+1)(Z, X₁)` is bijective. -/
private theorem extClass_postcomp_bijective_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Function.Bijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hzero : (x - y).comp hS.extClass rfl = 0 := by
      change (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ Z hS (x - y) rfl hzero
    have hz0 : z = 0 := Subsingleton.elim _ _
    apply sub_eq_zero.mp
    rw [← hz, hz0, Ext.zero_comp]
  · intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x
      (@Subsingleton.elim _ h₂succ _ _) rfl
    exact ⟨y, hy⟩

/-- The connecting morphism in the covariant long exact sequence as an additive equivalence,
    assuming the middle cohomology groups in degrees `n` and `n + 1` vanish. -/
noncomputable def extClassPostcompAddEquivOfSubsingletonMiddle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Ext Z S.X₃ n ≃+ Ext Z S.X₁ (n + 1) :=
  AddEquiv.ofBijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1))
    (private_decl% (extClass_postcomp_bijective_of_subsingleton_middle Z hS n h₂n h₂succ))

/-- Naturality of the extension class for a morphism of short exact sequences. -/
private lemma extClass_naturality {S₁ S₂ : ShortComplex C'} (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    (Ext.mk₀ φ.τ₃).comp hS₂.extClass (zero_add 1) =
    hS₁.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) :=
  (ShortComplex.ShortExact.extClass_naturality hS₁ hS₂ φ).symm

end ExtDimShift

/-! ## Connecting maps -/

/-- Naturality of the connecting map on sheaf cohomology for a morphism of short exact
    sequences, with the associativity rewrites needed for nested `comp` expressions. -/
private theorem sheafH_comp_extClass_naturality {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (y : Sheaf.H S₁.X₃ n) :
    (y.comp hS₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hS₂.extClass rfl := by
  refine (Ext.comp_assoc_of_third_deg_zero y hS₁.extClass (Ext.mk₀ φ.τ₁) rfl).trans
    (Eq.trans ?_ (Ext.comp_assoc_of_second_deg_zero y (Ext.mk₀ φ.τ₃) hS₂.extClass rfl).symm)
  exact congrArg (fun t ↦ y.comp t rfl) (extClass_naturality hS₁ hS₂ φ).symm

/-- Successor connecting morphism attached to a short exact sequence of sheaves. -/
noncomputable def sheafHSuccMap {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun y ↦ y.comp hS.extClass rfl)
      (fun a b ↦ Ext.add_comp a b hS.extClass rfl)

theorem sheafH_succ_map_apply {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom (sheafHSuccMap hS n) y = y.comp hS.extClass rfl := rfl

/-- If the middle term has subsingleton cohomology in degree `n + 1`, every
`H^(n+1)(S.X₁)` class comes from some `H^n(S.X₃)` class via the successor map. -/
theorem sheafH_succ_map_exists_preimage_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (h₂H : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (x : Sheaf.H S.X₁ (n + 1)) :
    ∃ y : Sheaf.H S.X₃ n, ConcreteCategory.hom (sheafHSuccMap hS n) y = x := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (@Subsingleton.elim _ h₂H _ _) rfl
  exact ⟨y, (sheafH_succ_map_apply hS n y).trans hy⟩

/-! ## H⁰ ≅ Sections -/

/-- If `F` is a sheaf, then `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H F 0 ≃+ F.obj.obj (op ⊤) :=
  Sheaf.H.equiv₀ F Limits.isTerminalTop

/-- Naturality of `sheafH0EquivSections`: composing `x` with `mk₀ f` at
    degree 0 corresponds to applying `f.app(⊤)` on sections. -/
lemma sheafH0EquivSections_natural {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : Sheaf.H F 0) :
    sheafH0EquivSections G (x.comp (Ext.mk₀ f) (add_zero 0)) =
    ConcreteCategory.hom (f.hom.app (op ⊤)) (sheafH0EquivSections F x) :=
  (Sheaf.H.equiv₀_naturality Limits.isTerminalTop f x).symm

/-- `H¹(S.X₁)` as the cokernel of top sections for a short exact sequence of sheaves,
    assuming `H¹(S.X₂)` is subsingleton. -/
noncomputable def sheafH1CokernelIsoOfSubsingletonMiddle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1)) :
  cokernel (S.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ 1) := by
  let δ : S.X₃.obj.obj (op ⊤) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    AddCommGrpCat.ofHom ((sheafH0EquivSections S.X₃).symm.toAddMonoidHom) ≫
      sheafHSuccMap hS 0
  have hδ : S.g.hom.app (op ⊤) ≫ δ = 0 := by
    ext s
    let y : Sheaf.H S.X₂ 0 := (sheafH0EquivSections S.X₂).symm s
    change ConcreteCategory.hom (sheafHSuccMap hS 0)
      ((sheafH0EquivSections S.X₃).symm
        (ConcreteCategory.hom (S.g.hom.app (op ⊤)) s)) = 0
    rw [← show y.comp (Ext.mk₀ S.g) (add_zero 0) =
        (sheafH0EquivSections S.X₃).symm
          (ConcreteCategory.hom (S.g.hom.app (op ⊤)) s) from
          (sheafH0EquivSections S.X₃).injective (by
            simpa [y] using sheafH0EquivSections_natural (f := S.g) (x := y)),
      sheafH_succ_map_apply]
    rw [show (Ext.comp y (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl =
        Ext.comp y ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) rfl from
      Ext.comp_assoc_of_second_deg_zero y (Ext.mk₀ S.g) hS.extClass rfl]
    rw [hS.comp_extClass]
    exact Ext.comp_zero y S.X₁ 1 1 (zero_add 1)
  let πH : cokernel (S.g.hom.app (op ⊤)) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    cokernel.desc _ δ hδ
  have hπH_epi : Epi πH := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := sheafH_succ_map_exists_preimage_of_subsingleton_middle hS 0 h₂H x
    refine ⟨ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤)))
      (sheafH0EquivSections S.X₃ y), ?_⟩
    refine (cokernel.π_desc_apply _ δ hδ _).trans ?_
    change ConcreteCategory.hom (sheafHSuccMap hS 0)
      ((sheafH0EquivSections S.X₃).symm (sheafH0EquivSections S.X₃ y)) = x
    exact (congrArg (ConcreteCategory.hom (sheafHSuccMap hS 0))
      ((sheafH0EquivSections S.X₃).symm_apply_apply y)).trans hy
  have hπH_mono : Mono πH := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    apply sub_eq_zero.mp
    obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.hom.app (op ⊤)))).mp inferInstance (a - b)
    rw [← hs]
    have hzero :
        ((((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl) :
            Sheaf.H S.X₁ 1) = 0 := by
      have hmap :
          ConcreteCategory.hom (sheafHSuccMap hS 0) ((sheafH0EquivSections S.X₃).symm s) =
            0 := by
        simpa [πH, δ, ← hs] using (by
          rw [map_sub, hab, sub_self] : ConcreteCategory.hom πH (a - b) = 0)
      exact (sheafH_succ_map_apply hS 0 ((sheafH0EquivSections S.X₃).symm s)).symm.trans hmap
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS
      ((sheafH0EquivSections S.X₃).symm s) rfl hzero
    have hy_sec :=
      (sheafH0EquivSections_natural (f := S.g) (x := y)).symm.trans <|
        congrArg (sheafH0EquivSections S.X₃) hy
    simpa using
      congrArg (ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤)))) hy_sec.symm
  haveI : IsIso πH := isIso_of_mono_of_epi πH
  exact asIso πH

@[simp] theorem sheafH1_cokernel_iso_of_subsingleton_middle_hom_π {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (s : S.X₃.obj.obj (op ⊤)) :
    ConcreteCategory.hom
        ((sheafH1CokernelIsoOfSubsingletonMiddle hS h₂H).hom)
        (ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤))) s) =
      ((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl := by
  simpa [sheafH1CokernelIsoOfSubsingletonMiddle] using
    sheafH_succ_map_apply hS 0 ((sheafH0EquivSections S.X₃).symm s)

/-- If a sheaf morphism is surjective on top sections, then every degree-zero cohomology
    class of the target lifts along it. -/
theorem sheafH0_surj_of_epi_app_top {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : Epi (f.hom.app (op ⊤))) :
    ∀ y : Sheaf.H G 0, ∃ z : Sheaf.H F 0, z.comp (Ext.mk₀ f) (add_zero 0) = y := by
  intro y
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hf
    (sheafH0EquivSections G y)
  refine ⟨(sheafH0EquivSections F).symm s, ?_⟩
  apply (sheafH0EquivSections G).injective
  rw [sheafH0EquivSections_natural (f := f), AddEquiv.apply_symm_apply, hs]

/-- Internal helper for `H^1` vanishing via degree-zero surjectivity. -/
private theorem subsingleton_H1_via_surj {C' : Type*} [Category C'] [Abelian C'] [HasExt C']
    (Z : C') {S : ShortComplex C'} (hSE : S.ShortExact)
    (hJ : Subsingleton (Ext Z S.X₂ 1))
    (h_surj : ∀ y : Ext Z S.X₃ 0,
      ∃ z : Ext Z S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Ext Z S.X₁ 1) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨c', hc'⟩ := h_surj c; obtain ⟨d', hd'⟩ := h_surj d
  simp only [← hc, ← hd, ← hc', ← hd', Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g)
    hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]

/-- `H¹` vanishing via degree-zero surjectivity. -/
theorem sheafH_subsingleton_H1_via_surj {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (h_surj : ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  subsingleton_H1_via_surj _ hS h₂H h_surj

/-- `H¹` vanishing criterion from surjective top sections. -/
theorem sheafH_subsingleton_H1_via_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (hg : Epi (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_surj hS h₂H (sheafH0_surj_of_epi_app_top S.g hg)

/-- Positive-degree cohomology of an injective sheaf is subsingleton. -/
theorem sheafH_subsingleton_of_injective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (I : Sheaf J AddCommGrpCat.{w}) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H I (n + 1)) := by
  simpa [Sheaf.H] using
    (Ext.subsingleton_of_injective
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) I n)

/-- `H¹` vanishing criterion with injective middle term. -/
theorem sheafH_subsingleton_H1_of_injective_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    [hI : Injective S.X₂]
    (hg : Epi (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_epi_app_top hS
    (@sheafH_subsingleton_of_injective (Opens X) _ (Opens.grothendieckTopology X)
      _ _ S.X₂ hI 0) hg

/-! ## Sheaf Cohomology Functor -/

/-- The sheaf cohomology functor `H^n : Sheaf(X, Ab) ⥤ Ab`, defined as the covariant
    Ext functor `Ext^n(ℤ_X, −)` where `ℤ_X` is the constant sheaf of integers. -/
noncomputable def sheafCohomologyFunctor (X : TopCat.{u}) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  extFunctorObj ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) n

@[simp]
theorem sheafCohomologyFunctor_map_apply (X : TopCat.{u}) (n : ℕ)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : Sheaf.H F n) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X n).map f) x =
    x.comp (Ext.mk₀ f) (add_zero n) := rfl

/-- Naturality of `sheafH1CokernelIsoOfSubsingletonMiddle` for a morphism between
    two short exact sequences of sheaves. -/
theorem sheafH1_cokernel_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (h₁₂H : Subsingleton (Sheaf.H S₁.X₂ 1))
    (h₂₂H : Subsingleton (Sheaf.H S₂.X₂ 1)) :
    cokernel.map (S₁.g.hom.app (op ⊤)) (S₂.g.hom.app (op ⊤))
        (φ.τ₂.hom.app (op ⊤)) (φ.τ₃.hom.app (op ⊤))
        (by
          change (S₁.g ≫ φ.τ₃).hom.app (op ⊤) =
            (φ.τ₂ ≫ S₂.g).hom.app (op ⊤)
          exact congrArg (fun α : S₁.X₂ ⟶ S₂.X₃ ↦ α.hom.app (op ⊤)) φ.comm₂₃.symm) ≫
      (sheafH1CokernelIsoOfSubsingletonMiddle hS₂ h₂₂H).hom =
    (sheafH1CokernelIsoOfSubsingletonMiddle hS₁ h₁₂H).hom ≫
      (sheafCohomologyFunctor X 1).map φ.τ₁ := by
  apply (cancel_epi (cokernel.π (S₁.g.hom.app (op ⊤)))).mp
  rw [cokernel.π_desc_assoc, Category.assoc]
  ext s
  have hs :
      (((sheafH0EquivSections S₁.X₃).symm s).comp
          (Ext.mk₀ φ.τ₃) (add_zero 0)) =
        (sheafH0EquivSections S₂.X₃).symm
          (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s) := by
    apply (sheafH0EquivSections S₂.X₃).injective
    simpa using
      (sheafH0EquivSections_natural (f := φ.τ₃)
        (x := (sheafH0EquivSections S₁.X₃).symm s))
  change ConcreteCategory.hom (sheafH1CokernelIsoOfSubsingletonMiddle hS₂ h₂₂H).hom
      (ConcreteCategory.hom (cokernel.π (S₂.g.hom.app (op ⊤)))
        (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s)) =
    ConcreteCategory.hom ((sheafCohomologyFunctor X 1).map φ.τ₁)
      (ConcreteCategory.hom (sheafH1CokernelIsoOfSubsingletonMiddle hS₁ h₁₂H).hom
        (ConcreteCategory.hom (cokernel.π (S₁.g.hom.app (op ⊤))) s))
  rw [sheafH1_cokernel_iso_of_subsingleton_middle_hom_π,
    sheafH1_cokernel_iso_of_subsingleton_middle_hom_π]
  change (((sheafH0EquivSections S₂.X₃).symm
        (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s)).comp hS₂.extClass rfl) =
      ((((sheafH0EquivSections S₁.X₃).symm s).comp hS₁.extClass rfl).comp
        (Ext.mk₀ φ.τ₁) (add_zero 1))
  rw [← hs]
  simpa using
    (sheafH_comp_extClass_naturality hS₁ hS₂ φ 0
      ((sheafH0EquivSections S₁.X₃).symm s)).symm

/-- The degree-`0` sheaf cohomology functor is naturally isomorphic to taking sections on `⊤`. -/
noncomputable def sheafH0NatIsoSections {X : TopCat.{u}} :
    sheafCohomologyFunctor X 0 ≅
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ (sheafH0EquivSections F).toAddCommGrpIso)
    fun {F G} f ↦ by
      apply AddCommGrpCat.ext
      intro x
      exact sheafH0EquivSections_natural f x

/-- Higher-degree connecting additive equivalence for a short exact sequence of sheaves:
if the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
connecting morphism induces an additive equivalence `H^n(S.X₃) ≃+ H^(n+1)(S.X₁)`. -/
noncomputable def sheafHExtClassAddEquivOfSubsingletonMiddle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Sheaf.H S.X₃ n ≃+ Sheaf.H S.X₁ (n + 1) :=
  extClassPostcompAddEquivOfSubsingletonMiddle _ hS n h₂n h₂succ

@[simp] private theorem sheafH_extClassAddEquiv_of_subsingleton_middle_apply
    {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    sheafHExtClassAddEquivOfSubsingletonMiddle hS n h₂n h₂succ y =
      y.comp hS.extClass rfl := rfl

/-- Higher-degree connecting isomorphism for a short exact sequence of sheaves: if the
middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the connecting
morphism induces an isomorphism `H^n(S.X₃) ≅ H^(n+1)(S.X₁)`. -/
noncomputable def sheafHSuccIsoOfSubsingletonMiddle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) :=
  (sheafHExtClassAddEquivOfSubsingletonMiddle hS n h₂n h₂succ).toAddCommGrpIso

private theorem sheafH_succ_iso_of_subsingleton_middle_hom_apply {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom
        ((sheafHSuccIsoOfSubsingletonMiddle hS n h₂n h₂succ).hom) y =
      y.comp hS.extClass rfl :=
  sheafH_extClassAddEquiv_of_subsingleton_middle_apply hS n h₂n h₂succ y

/-- Naturality of `sheafHSuccIsoOfSubsingletonMiddle` for a morphism between two
short exact sequences of sheaves. -/
theorem sheafH_succ_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (h₁₂n : Subsingleton (Sheaf.H S₁.X₂ n))
    (h₁₂succ : Subsingleton (Sheaf.H S₁.X₂ (n + 1)))
    (h₂₂n : Subsingleton (Sheaf.H S₂.X₂ n))
    (h₂₂succ : Subsingleton (Sheaf.H S₂.X₂ (n + 1))) :
    (sheafHSuccIsoOfSubsingletonMiddle hS₁ n h₁₂n h₁₂succ).hom ≫
        (sheafCohomologyFunctor X (n + 1)).map φ.τ₁ =
      (sheafCohomologyFunctor X n).map φ.τ₃ ≫
        (sheafHSuccIsoOfSubsingletonMiddle hS₂ n h₂₂n h₂₂succ).hom := by
  ext y
  change
      (ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map φ.τ₁)
        (ConcreteCategory.hom ((sheafHSuccIsoOfSubsingletonMiddle
          hS₁ n h₁₂n h₁₂succ).hom) y)) =
      (ConcreteCategory.hom ((sheafHSuccIsoOfSubsingletonMiddle
        hS₂ n h₂₂n h₂₂succ).hom)
        (ConcreteCategory.hom ((sheafCohomologyFunctor X n).map φ.τ₃) y))
  rw [sheafH_succ_iso_of_subsingleton_middle_hom_apply,
    sheafCohomologyFunctor_map_apply, sheafCohomologyFunctor_map_apply,
    sheafH_succ_iso_of_subsingleton_middle_hom_apply]
  exact sheafH_comp_extClass_naturality hS₁ hS₂ φ n y
