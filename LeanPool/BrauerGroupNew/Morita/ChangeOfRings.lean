/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import LeanPool.BrauerGroupNew.MoritaEquivalence
public import Mathlib.RingTheory.Morita.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# LeanPool.BrauerGroupNew.Morita.ChangeOfRings

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Morita.ChangeOfRings`.
-/

@[expose] public section

open CategoryTheory Limits

namespace ModuleCat

universe v u₁ u₂ u₃ w

instance instLinearOfAlgebraLeanPool {R₀ S} [CommRing R₀] [Ring S] [Algebra R₀ S] :
    Linear R₀ (ModuleCat S) := Algebra.instLinear

universe u₀ u u' u''  v'

variable (R : Type u₀) [CommRing R]

suppress_compilation

namespace MoritaEquivalence

variable (A B : Type u) [Ring A] [Ring B] [Algebra R A] [Algebra R B]

instance (n : ℕ) [NeZero n] : Functor.Additive (moritaEquivalentToMatrix A (Fin n)).functor :=
  Functor.additive_of_preserves_binary_products _

instance (n : ℕ) [NeZero n] : Functor.Linear R (moritaEquivalentToMatrix A (Fin n)).functor where
  map_smul {M N} f r := by
    ext m
    apply funext
    intro i
    simp only [hom_smul, LinearMap.smul_apply, moritaEquivalentToMatrix,
      toModuleCatOverMatrix_map]
    change (algebraMap R A r) • (f.hom _) =
      ∑ j : Fin n, (algebraMap R (Matrix (Fin n) (Fin n) A) r) _ _ • _
    simp [Matrix.algebraMap_matrix_apply]
    rfl

/-- The Morita equivalence between a ring and a positive-size matrix ring over it. -/
def matrix (n : ℕ) : MoritaEquivalence R A (Matrix (Fin (n+1)) (Fin (n + 1)) A) :=
  letI : NeZero (n + 1) := ⟨by omega⟩
  { eqv :=
      moritaEquivalentToMatrix A _
    linear := inferInstance}

/-- The Morita equivalence between a ring and an `n × n` matrix ring, for nonzero `n`. -/
def matrix' (n : ℕ) [hn : NeZero n] : MoritaEquivalence R A (Matrix (Fin n) (Fin n) A) where
  eqv := moritaEquivalentToMatrix A _
end  MoritaEquivalence

namespace MoritaEquivalence

variable (A B : Type u) [DivisionRing A] [DivisionRing B] [Algebra R A] [Algebra R B]

instance instAlgebraEndOfLeanPool : Algebra R (End (ModuleCat.of A A)) := inferInstance

/-- Right multiplication identifies the opposite division ring with endomorphisms of its regular
module. -/
@[simps apply]
def mopToEnd : Aᵐᵒᵖ →ₐ[R] End (ModuleCat.of A A) where
  toFun a := .of <| ModuleCat.ofHom <|
    { toFun := fun (x : A) ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := fun x y => by ext; simp [mul_add]
  map_mul' := fun x y => by ext; simp
  commutes' := fun r ↦ by
    apply End.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x * algebraMap R A r = algebraMap R A r * x
    exact (Algebra.commutes r x).symm

lemma moptoend_bij : Function.Bijective (mopToEnd R A) := by
  constructor
  · intro a b h
    apply MulOpposite.unop_injective
    have h1 := congrArg (fun φ : End (ModuleCat.of A A) => φ.asHom.hom (1 : A)) h
    simpa [mopToEnd] using h1
  · intro φ
    refine ⟨MulOpposite.op (φ.asHom.hom (1 : A)), ?_⟩
    apply End.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r * φ.asHom.hom 1 = φ.asHom.hom r
    rw [← smul_eq_mul, ← φ.asHom.hom.map_smul, smul_eq_mul, mul_one]

/-- The opposite division ring is equivalent to endomorphisms of its regular module. -/
noncomputable def mopAlgEquivEnd : Aᵐᵒᵖ ≃ₐ[R] End (ModuleCat.of A A) :=
  AlgEquiv.ofBijective (mopToEnd R A) <| moptoend_bij R A

example : End (ModuleCat.of A A) ≃ₐ[R] Module.End A A :=
  mopAlgEquivEnd R A|>.symm.trans <|
    {__ := RingEquiv.moduleEndSelf A, commutes' r := by ext; simp [Algebra.smul_def]}

variable (e : MoritaEquivalence R A B)

/-- Transport endomorphism algebras along the functor of a Morita equivalence. -/
def aux1 : End (ModuleCat.of A A) ≃ₐ[R] End (e.eqv.functor.obj <| .of A A) where
  toFun f := .of (e.eqv.functor.map f.asHom)
  invFun g := .of (e.eqv.fullyFaithfulFunctor.preimage g.asHom)
  left_inv := by
    intro f
    apply End.ext
    exact e.eqv.fullyFaithfulFunctor.preimage_map f.asHom
  right_inv := by
    intro g
    apply End.ext
    exact e.eqv.fullyFaithfulFunctor.map_preimage g.asHom
  map_mul' x y := by apply End.ext; simp
  map_add' x y := by apply End.ext; simp
  commutes' r := by
    apply End.ext
    simp [Algebra.algebraMap_eq_smul_one]

/-- The target simple module associated to the source regular module under a Morita equivalence. -/
noncomputable def aux20 : (e.eqv.functor.obj (ModuleCat.of A A)) ≅ ModuleCat.of B B := by
  haveI : IsSimpleModule A A := by
    rw [@isSimpleModule_iff_finrank_eq_one, Module.finrank_self]
  have :  IsSimpleModule A (ModuleCat.of A A) := inferInstanceAs <| IsSimpleModule A A
  have : IsSimpleModule B (e.eqv.functor.obj (ModuleCat.of A A)) :=
    IsMoritaEquivalent.division_ring.IsSimpleModule.functor A B e.eqv (ModuleCat.of A A)
  have := IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule B
    (e.eqv.functor.obj <| .of A A)
  exact this.some.toModuleIso
/-- Conjugation by a module isomorphism gives an equivalence of endomorphism algebras. -/
def aux2 (M N : ModuleCat B) (f : M ≅ N) : End M ≃ₐ[R] End N where
  toFun x := .of (f.inv ≫ x.asHom ≫ f.hom)
  invFun x := .of (f.hom ≫ x.asHom ≫ f.inv)
  left_inv x := by apply End.ext; simp
  right_inv x := by apply End.ext; simp
  map_mul' x y := by apply End.ext; simp
  map_add' x y := by apply End.ext; simp
  commutes' r := by
    apply End.ext
    simp [Algebra.algebraMap_eq_smul_one]
/-- A Morita equivalence between division rings induces an equivalence of opposite rings. -/
noncomputable def toRingMopEquiv : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ :=
  mopAlgEquivEnd R A |>.trans <|
    aux1 (R := R) (A := A) (B := B) e |>.trans <|
    aux2 _ _ _ _ (aux20 R A B e ) |>.trans <|
    mopAlgEquivEnd R B |>.symm
/-- A Morita equivalence between division rings induces an algebra equivalence. -/
noncomputable def toRingEquiv : A ≃ₐ[R] B where
  toFun r := toRingMopEquiv (R := R) (A := A) (B := B) e (.op r) |>.unop
  invFun s := toRingMopEquiv (R := R) (A := A) (B := B) e |>.symm (.op s) |>.unop
  left_inv r := by simp [MulOpposite.op_unop, MulOpposite.unop_op]
  right_inv s := by simp [MulOpposite.op_unop, MulOpposite.unop_op]
  map_mul' a b := by simp only [MulOpposite.op_mul, _root_.map_mul, MulOpposite.unop_mul]
  map_add' a b := by simp only [MulOpposite.op_add, map_add, MulOpposite.unop_add]
  commutes' r := by
    rw [show (MulOpposite.op <| algebraMap R A r) = algebraMap R Aᵐᵒᵖ r by rfl]
    rw [AlgEquiv.commutes]
    rfl

/-- Morita-equivalent division algebras over a commutative ring are algebra equivalent. -/
noncomputable def algEquivOfDivisionRing (R : Type u) [CommRing R]
    (D₁ D₂ : Type v) [DivisionRing D₁] [DivisionRing D₂] [Algebra R D₁] [Algebra R D₂]
    (e : MoritaEquivalence R D₁ D₂) : D₁ ≃ₐ[R] D₂ :=
    ModuleCat.MoritaEquivalence.toRingEquiv (R := R) (A := D₁) (B := D₂) e

end MoritaEquivalence
end ModuleCat
