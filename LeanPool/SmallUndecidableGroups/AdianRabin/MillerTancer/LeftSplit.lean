/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.LeftNormalForm
public import Mathlib.Tactic.FinCases

/-!
The final, formal bookkeeping step in the left separated-conjugates lemma.

Generator `0` is split off from generators `1, ..., 4`.  Its nonzero powers
have outer normal form from the base factor to the base factor.  The remaining
four generators are assumed to send every nontrivial word to a normal form
from the alpha factor to the alpha factor.  Alternating words in the resulting
two-factor coproduct are therefore reduced.
-/

@[expose] public section

namespace Undecidability.MillerTancer.LeftSplit

open Monoid
open LeftNormalForm

variable {G : Type} [Group G]

/-- The first-generator and four-generator-tail components of the source free group. -/
inductive SplitIndex
  | zero
  | tail
/-- The cyclic first-generator factor or the free four-generator tail factor. -/
@[implicit_reducible] def SplitFactor : SplitIndex → Type
  | .zero => FreeGroup Unit
  | .tail => FreeGroup (Fin 4)

instance splitFactorGroup : ∀ i, Group (SplitFactor i) := fun i => by
  cases i <;> simp only [SplitFactor] <;> infer_instance

/-- The free product separating the first source generator from its four-generator tail. -/
abbrev SplitProduct := CoprodI SplitFactor

/-- The four proposed basis elements remaining after separating the first generator. -/
def tailBasis (w z : G) : Fin 4 → MillerLeft G :=
  fun i => outerLeftBasis w z i.succ

/-- The homomorphism freely extending the four-generator tail basis. -/
def tailMap (w z : G) : FreeGroup (Fin 4) →* MillerLeft G :=
  FreeGroup.lift (tailBasis w z)

/-- The homomorphism sending the first cyclic generator to the base letter `beta`. -/
def zeroMap : FreeGroup Unit →* MillerLeft G :=
  FreeGroup.lift fun _ => baseOf beta

/-- The component homomorphisms from the separated source factors. -/
def splitFactorMap (w z : G) : ∀ i, SplitFactor i →* MillerLeft G
  | .zero => zeroMap
  | .tail => tailMap w z

/-- The homomorphism induced by the separated first-generator and tail maps. -/
def splitLift (w z : G) : SplitProduct →* MillerLeft G :=
  CoprodI.lift (splitFactorMap w z)

/-- The endpoint factor corresponding to a separated source-factor label. -/
def splitSide : SplitIndex → OuterIndex
  | .zero => .base
  | .tail => .alpha

theorem splitSide_ne {i j : SplitIndex} (hij : i ≠ j) :
    splitSide i ≠ splitSide j := by
  cases i <;> cases j <;> simp_all [splitSide]

theorem unitExponent_ne_zero (x : FreeGroup Unit) (hx : x ≠ 1) :
    FreeGroup.freeGroupUnitEquivInt x ≠ 0 := by
  intro hzero
  apply hx
  apply FreeGroup.freeGroupUnitEquivInt.injective
  change FreeGroup.freeGroupUnitEquivInt x = 0
  exact hzero

/-- The reduced image of a nonidentity element of the first cyclic source factor. -/
def zeroImage (x : FreeGroup Unit) (hx : x ≠ 1) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.base :=
  baseSingleton (beta ^ FreeGroup.freeGroupUnitEquivInt x)
    (beta_zpow_ne_one _ (unitExponent_ne_zero x hx))

@[simp] theorem zeroImage_prod (x : FreeGroup Unit) (hx : x ≠ 1) :
    (zeroImage (G := G) x hx).prod = zeroMap x := by
  let k := FreeGroup.freeGroupUnitEquivInt x
  have hxrepr : FreeGroup.of () ^ k = x :=
    FreeGroup.freeGroupUnitEquivInt.symm_apply_apply x
  calc
    (zeroImage (G := G) x hx).prod = baseOf (beta ^ k) := by
      simp [zeroImage, k]
    _ = baseOf beta ^ k := baseOf_zpow beta k
    _ = zeroMap (FreeGroup.of () ^ k) := by simp [zeroMap]
    _ = zeroMap x := congrArg zeroMap hxrepr

private theorem neWord_prod_ne_one
    {I : Type} {H : I → Type} [∀ i, Group (H i)]
    {i j : I} (u : CoprodI.NeWord H i j) : u.prod ≠ 1 := by
  classical
  intro hu
  have heq : u.toWord = (CoprodI.Word.empty : CoprodI.Word H) := by
    apply (CoprodI.Word.equiv (M := H)).symm.injective
    change u.prod = 1
    exact hu
  have hlist := congrArg CoprodI.Word.toList heq
  exact u.toList_ne_nil (by
    simpa [CoprodI.NeWord.toWord] using hlist)

/-- A reduced representative of a mapped word, together with its evaluation and boundary properties.
-/
structure Image (w z : G)
    (tailImage : ∀ x : FreeGroup (Fin 4), x ≠ 1 →
      CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    {i j : SplitIndex} (u : CoprodI.NeWord SplitFactor i j) where
  /-- The reduced-word representative carrying the stated evaluation and boundary properties. -/
  word : CoprodI.NeWord (OuterFactor G) (splitSide i) (splitSide j)
  prod_eq : word.prod = splitLift w z u.prod

/-- Construct the reduced image using the first-factor word and the supplied tail images. -/
noncomputable def image (w z : G)
    (tailImage : ∀ x : FreeGroup (Fin 4), x ≠ 1 →
      CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    (tailImage_prod : ∀ (x : FreeGroup (Fin 4)) (hx : x ≠ 1),
      (tailImage x hx).prod = tailMap w z x)
    {i j : SplitIndex} (u : CoprodI.NeWord SplitFactor i j) :
    Image w z tailImage u := by
  induction u with
  | @singleton i x hx =>
      cases i with
      | zero =>
          refine ⟨zeroImage x hx, ?_⟩
          simp only [CoprodI.NeWord.prod_singleton, splitLift,
            CoprodI.lift_of, splitFactorMap]
          exact zeroImage_prod x hx
      | tail =>
          refine ⟨tailImage x hx, ?_⟩
          simp only [CoprodI.NeWord.prod_singleton, splitLift,
            CoprodI.lift_of, splitFactorMap]
          exact tailImage_prod x hx
  | @append i j k l u₁ hjk u₂ ih₁ ih₂ =>
      let v := CoprodI.NeWord.append ih₁.word (splitSide_ne hjk) ih₂.word
      refine ⟨v, ?_⟩
      rw [show v.prod = ih₁.word.prod * ih₂.word.prod by
        exact CoprodI.NeWord.append_prod]
      rw [ih₁.prod_eq, ih₂.prod_eq]
      simp [splitLift]

theorem splitLift_injective_of_tailImage (w z : G)
    (tailImage : ∀ x : FreeGroup (Fin 4), x ≠ 1 →
      CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    (tailImage_prod : ∀ (x : FreeGroup (Fin 4)) (hx : x ≠ 1),
      (tailImage x hx).prod = tailMap w z x) :
    Function.Injective (splitLift w z) := by
  apply CoprodI.lift_injective_of_neWord_nontrivial
  intro i j u hu
  apply neWord_prod_ne_one (image w z tailImage tailImage_prod u).word
  calc
    (image w z tailImage tailImage_prod u).word.prod =
        splitLift w z u.prod :=
      (image w z tailImage tailImage_prod u).prod_eq
    _ = 1 := by
      change (CoprodI.lift (splitFactorMap w z)) u.prod = 1
      exact hu

/-- The five source generators interpreted in the separated free product. -/
def splitGenerator : Fin 5 → SplitProduct
  | 0 => CoprodI.of (i := SplitIndex.zero) (FreeGroup.of ())
  | ⟨n + 1, h⟩ =>
      CoprodI.of (i := SplitIndex.tail) (FreeGroup.of ⟨n, by omega⟩)

/-- The homomorphism separating the first source generator from the remaining four. -/
def sourceSplit : FreeGroup (Fin 5) →* SplitProduct :=
  FreeGroup.lift splitGenerator

/-- The inclusion of the first cyclic factor into the five-generator free group. -/
def zeroJoin : FreeGroup Unit →* FreeGroup (Fin 5) :=
  FreeGroup.lift fun _ => FreeGroup.of (0 : Fin 5)

/-- The inclusion of the four-generator tail into the five-generator free group. -/
def tailJoin : FreeGroup (Fin 4) →* FreeGroup (Fin 5) :=
  FreeGroup.lift fun i => FreeGroup.of i.succ

/-- The homomorphism recombining the separated source factors. -/
def sourceJoin : SplitProduct →* FreeGroup (Fin 5) :=
  CoprodI.lift fun i => match i with
    | .zero => zeroJoin
    | .tail => tailJoin

theorem sourceJoin_comp_sourceSplit :
    sourceJoin.comp sourceSplit = MonoidHom.id (FreeGroup (Fin 5)) := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp only [sourceJoin, zeroJoin, Fin.isValue, tailJoin, sourceSplit, Fin.zero_eta,
      MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift_apply_of, splitGenerator,
      CoprodI.lift_of, MonoidHom.id_apply, Fin.mk_one, Fin.reduceFinMk] <;>
    exact FreeGroup.lift_apply_of

theorem sourceSplit_injective : Function.Injective sourceSplit := by
  apply Function.LeftInverse.injective (g := sourceJoin)
  intro x
  exact DFunLike.congr_fun sourceJoin_comp_sourceSplit x

theorem splitLift_comp_sourceSplit (w z : G) :
    (splitLift w z).comp sourceSplit =
      FreeGroup.lift (outerLeftBasis w z) := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp only [splitLift, sourceSplit, Fin.zero_eta, Fin.isValue, MonoidHom.coe_comp,
      Function.comp_apply, FreeGroup.lift_apply_of, splitGenerator, CoprodI.lift_of,
      splitFactorMap, zeroMap, outerLeftBasis, Fin.mk_one, tailMap, Fin.reduceFinMk] <;>
    exact FreeGroup.lift_apply_of

/-- Reduce the five-generator left-basis check to normal forms for the tail
four-generator map. -/
theorem outerLeftBasis_injective_of_tailImage (w z : G)
    (tailImage : ∀ x : FreeGroup (Fin 4), x ≠ 1 →
      CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    (tailImage_prod : ∀ (x : FreeGroup (Fin 4)) (hx : x ≠ 1),
      (tailImage x hx).prod = tailMap w z x) :
    Function.Injective (FreeGroup.lift (outerLeftBasis w z)) := by
  intro x y hxy
  apply sourceSplit_injective
  apply splitLift_injective_of_tailImage w z tailImage tailImage_prod
  calc
    splitLift w z (sourceSplit x) =
        FreeGroup.lift (outerLeftBasis w z) x :=
      DFunLike.congr_fun (splitLift_comp_sourceSplit w z) x
    _ = FreeGroup.lift (outerLeftBasis w z) y := hxy
    _ = splitLift w z (sourceSplit y) :=
      (DFunLike.congr_fun (splitLift_comp_sourceSplit w z) y).symm

end Undecidability.MillerTancer.LeftSplit
