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
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Vanishing from stalks and dimension shifts
-/

@[expose] public section

universe w' w v u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
private theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a (@Subsingleton.elim _ h₂ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b (@Subsingleton.elim _ h₂ _ _) rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
    `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
private theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl (@Subsingleton.elim _ h₁ _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

/-- If both outer terms in an Ext exact sequence vanish, its middle term vanishes. -/
private theorem ext_subsingleton_of_shortExact_middle (Z : C')
    {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Ext Z S.X₁ n)) (h₃ : Subsingleton (Ext Z S.X₃ n)) :
    Subsingleton (Ext Z S.X₂ n) := by
  constructor
  intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ Z hS a (Subsingleton.elim _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ Z hS b (Subsingleton.elim _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₁ c d]

/-- Internal helper: if `Y` is zero in an abelian category, `Ext X Y n` is subsingleton
    for all `X`, `n`.
    Proof: `𝟙 Y = 0` because `Y` is zero, so `x = x ∘ mk₀(𝟙 Y) = x ∘ mk₀(0) = x ∘ 0 = 0`. -/
private theorem ext_subsingleton_of_isZero_tgt {X Y : C'} (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext X Y n) :=
  ⟨fun a b ↦ by
    have eq : ∀ x : Ext X Y n, x = 0 := fun x ↦ by
      have h := Ext.comp_mk₀_id x
      rw [show (𝟙 Y : Y ⟶ Y) = 0 from hY.eq_of_src _ _, Ext.mk₀_zero] at h
      exact h.symm.trans (Ext.comp_zero x Y 0 n (add_zero n))
    exact (eq a).trans (eq b).symm⟩

end ExtDimShift

theorem sheaf_isZero_of_zero_stalks (X : TopCat.{u})
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hstalk : ∀ (x : X)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F), a = 0) :
    IsZero ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
  have hZ : IsZero F := Functor.isZero F (fun ⟨U⟩ ↦
    @AddCommGrpCat.isZero_of_subsingleton _
      ⟨fun s t ↦ by
        apply hF.section_ext
        intro x hx
        obtain ⟨W, hxW, iU, iV, hEq⟩ := F.germ_eq x hx hx s t
          ((hstalk x _).trans (hstalk x _).symm)
        rw [Subsingleton.elim iU iV] at hEq
        have hWU : W ≤ U := leOfHom iV
        rw [Subsingleton.elim iV (homOfLE hWU)] at hEq
        exact ⟨W, hWU, hxW, hEq⟩⟩)
  exact IsZero.of_full_of_faithful_of_isZero (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
    ⟨F, hF⟩ hZ

/-- If a bundled sheaf is zero, then its cohomology is subsingleton in every degree. -/
theorem sheafH_subsingleton_of_isZero {X : TopCat.{u}}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (hzero : IsZero F) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  ext_subsingleton_of_isZero_tgt hzero n

/-- The stalk map of `S.f` at `x` is a monomorphism when `S` is short exact. -/
private theorem stalkFunctor_map_f_mono {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact) (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom) := by
  have : Mono S.f := hS.mono_f
  have := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  exact show Mono ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f) from
    Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) S.f

/-- In a short exact sequence `X₁ → X₂ → X₃`, if the stalk map of `g` at `x` is an
isomorphism, then the stalk of `X₁` at `x` vanishes. -/
theorem stalk_zero_of_ses_g_iso
    {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (x : X)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.obj) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hTf_mono : Mono (T.map S.f.hom) := stalkFunctor_map_f_mono S hS x
  have hf0 : T.map S.f.hom = 0 := by
    have : T.map S.f.hom ≫ T.map S.g.hom = 0 := by
      have hzero : S.f.hom ≫ S.g.hom = 0 := congrArg InducedCategory.Hom.hom S.zero
      have hcomp_map : T.map (S.f.hom ≫ S.g.hom) = 0 :=
        (congrArg (fun h ↦ T.map h) hzero).trans
          (Functor.map_zero T S.X₁.obj S.X₃.obj)
      simpa [Functor.map_comp] using hcomp_map
    simp_all
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    (show ConcreteCategory.hom (T.map S.f.hom) a = ConcreteCategory.hom (T.map S.f.hom) 0 by
      simp [hf0])

/-- In a short exact sequence `X₁ → X₂ → X₃`, if all stalks of `X₂` at `x` vanish, then
    all stalks of `X₁` at `x` vanish (by mono-injectivity of `f`). -/
theorem stalk_zero_of_shortExact_kernel
    {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (x : X)
    (hX₂ : ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.obj), b = 0)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.obj) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hTf_mono : Mono (T.map S.f.hom) := stalkFunctor_map_f_mono S hS x
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    ((hX₂ _).trans (map_zero _).symm)

/-- If `g` is a cokernel of `f` and the stalk map of `f` at `x` is epi, then the stalk
of `S.X₃` at `x` vanishes. -/
theorem stalk_zero_of_g_is_cokernel_of_stalk_epi
    {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg : IsColimit (CokernelCofork.ofπ S.g S.zero))
    (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₃.obj) :
    a = 0 := by
  let T : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : ∀ U : Opens X, Decidable (x ∈ U) := fun _ ↦ Classical.dec _
  have : T.IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := X) (p₀ := x)).isLeftAdjoint
  have : Epi (T.map S.f) :=
    show Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom) from hepi
  have hzero_map : T.map S.f ≫ T.map S.g = 0 := by
    rw [← T.map_comp, S.zero, Functor.map_zero]
  have hzero : IsZero (T.obj S.X₃) :=
    CokernelCofork.IsColimit.isZero_of_epi (CokernelCofork.mapIsColimit _ hg T)
  have := AddCommGrpCat.subsingleton_of_isZero hzero
  change T.obj S.X₃ at a
  change (a : T.obj S.X₃) = 0
  exact Subsingleton.elim _ _

/-- Actual-cokernel specialization of
`stalk_zero_of_g_is_cokernel_of_stalk_epi`: if the stalk map of `f` at `x`
is surjective, then the stalk of `cokernel f` at `x` vanishes. -/
theorem cokernel_stalk_zero_of_stalk_surj
    {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : X)
    (hf : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom)))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel f).obj) :
    a = 0 := by
  let S := ShortComplex.mk f (Limits.cokernel.π f) (Limits.cokernel.condition f)
  have hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
    simpa using (AddCommGrpCat.epi_iff_surjective _).mpr hf
  simpa [S] using stalk_zero_of_g_is_cokernel_of_stalk_epi
    (S := S)
    (by simpa [S] using (cokernelIsCokernel f))
    x hepi a

/-- Forward dimension shift for a short exact sequence of sheaves. -/
theorem sheafH_dimension_shift_of_both {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H S.X₃ n))
    (h₂H : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n h₃H h₂H

/-- Forward dimension shift for a monomorphism of sheaves:
    if `f : F ⟶ G` is mono, the cokernel sheaf has subsingleton `H^n`, and
    `G` has subsingleton `H^(n+1)`, then `F` has subsingleton `H^(n+1)`. -/
theorem sheafH_dimension_shift_of_mono {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₃ : Subsingleton (Sheaf.H (cokernel f) n))
    (h₂ : Subsingleton (Sheaf.H G (n + 1))) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    inferInstance inferInstance
  change Subsingleton (Sheaf.H S.X₁ (n + 1))
  exact sheafH_dimension_shift_of_both hS n h₃ h₂

/-- Forward dimension shifting with injective middle term:
    if `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact, `S.X₂` is injective,
    and `H^n(S.X₃)=0`, then `H^(n+1)(S.X₁)=0`. -/
theorem sheafH_dimension_shift_of_injective {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    [Injective S.X₂]
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n h₃H (Ext.subsingleton_of_injective _ _ n)

/-- Reverse dimension shift for a locally surjective morphism:
    if `f : F ⟶ G` is locally surjective, `H^n(F)` is subsingleton, and
    `H^(n+1)(kernel f)` is subsingleton, then `H^n(G)` is subsingleton. -/
theorem sheafH_dimension_shift_X₃_of_locallySurjective {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (hf : TopCat.Presheaf.IsLocallySurjective f.hom) (n : ℕ)
    (h₂ : Subsingleton (Sheaf.H F n))
    (h₁ : Subsingleton (Sheaf.H (kernel f) (n + 1))) :
    Subsingleton (Sheaf.H G n) := by
  let : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  have : Epi f := by
    rw [← TopCat.Sheaf.isLocallySurjective_iff_epi f]
    simpa using hf
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)) inferInstance inferInstance
  change Subsingleton (Sheaf.H S.X₃ n)
  exact ext_dimension_shift_X₃ _ hS n h₂ h₁

/-- If `X` is empty, then the cohomology of every sheaf on `X` is subsingleton. -/
theorem sheafH_subsingleton_of_isEmpty {X : TopCat.{u}} [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  sheafH_subsingleton_of_isZero
    (sheaf_isZero_of_zero_stalks X F.property (fun x _ ↦ (IsEmpty.false x).elim)) n

-- If both ends of a short exact sequence have vanishing H^n, so does the middle.
/-- Middle-term cohomology vanishing: if `f : F ⟶ G` is mono and the cohomology of `F`
and `cokernel f` are subsingleton in degree `n`, then so is the cohomology of `G`. -/
theorem subsingleton_sheafH_of_shortExact_middle {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H F n))
    (h₃ : Subsingleton (Sheaf.H (cokernel f) n)) :
    Subsingleton (Sheaf.H G n) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    inferInstance inferInstance
  exact ext_subsingleton_of_shortExact_middle _ hS n h₁ h₃
