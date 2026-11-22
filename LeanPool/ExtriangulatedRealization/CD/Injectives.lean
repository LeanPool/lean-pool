/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Existence
public import LeanPool.ExtriangulatedRealization.Extriangulated.Injectives
public import LeanPool.ExtriangulatedRealization.Realization.Extriangulated

/-!
# Enough injectives in `C(D)` (Proposition 4.4)

An object `U` of `C(D)` whose image `ρU` is injective in `Rep k I` satisfies
`E(-, U) = Ext¹(ρ-, ρU) = 0`, hence is injective. For an object `A`, the good representation `ρA`
embeds into a good injective `J`; the cokernel is good, hence `ρ` of some object `C`, and the
resulting short exact sequence `ρA → J → ρC` is realized by a conflation `A → B → C` with
`ρB ≅ J` injective.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Abelian

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)
  [WellFoundedLT I] [Nonempty I]

attribute [local instance] HasExt.standard

/-- An object whose image under `ρ` is injective is injective in `C(D)`. -/
lemma cd_isInjectiveObject (hD : HasSurjectiveTransitions D) {U : CD D}
    (hU : Injective ((rho D).obj U)) : (cdData D).IsInjectiveObject U :=
  isInjectiveObject_of_ext_eq_zero (cdData_isExtriangulated D hD) fun _ δ =>
    Ext.eq_zero_of_injective (n := 0) δ

/-- **Proposition 4.4**: `C(D)` has enough injectives. -/
theorem cd_hasEnoughInjectives (hD : HasSurjectiveTransitions D) :
    (cdData D).HasEnoughInjectives := by
  intro A
  let E := objIdx D A
  have hA := isGood_rho D E A (labelIn_objIdx D A subset_rfl)
  obtain ⟨J, hJ, j, hj, hJg⟩ := hA.exists_mono_injective
  let S₀ := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS₀ : S₀.ShortExact :=
    ShortComplex.ShortExact.mk' (S₀.exact_of_g_is_cokernel (cokernelIsCokernel j)) hj
      inferInstance
  have hL : IsGood E (cokernel j) := IsGood.of_shortExact_right E hS₀ hA hJg
  obtain ⟨C, -, ⟨eC⟩⟩ := exists_xFree_of_isGood D hL
  let g := cokernel.π j ≫ eC.inv
  have w : j ≫ g = 0 := by simp [g]
  have hS : (ShortComplex.mk j g w).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := S₀)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eC.symm (by simp [S₀]) (by simp [S₀, g])) hS₀
  obtain ⟨B, x, y, hr, ⟨eB⟩⟩ := exists_realizes_of_shortExact D hJg j g w hS
  exact ⟨B, C, hS.extClass, x, y, hr, cd_isInjectiveObject D hD (Injective.of_iso eB.symm hJ)⟩

end ExtriangulatedRealization
