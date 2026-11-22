/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Categories.Mat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Data.Set.Countable
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Extriangulated categories, triangulated embeddings and algebraic realizations

This file uses only Mathlib. It fixes the general vocabulary of the manuscript
*An extriangulated category with no triangulated embedding*:

* `ExtriangulatedData k C`: an extension bifunctor `E` on a `k`-linear category `C`, with values in
  `k`-modules, and a realization predicate `Realizes δ x y` ("the sequence `A -x→ B -y→ C`
  realizes `δ ∈ E(C, A)`").
* `ExtriangulatedData.IsExtriangulated`: the axioms (ET1)–(ET4) and (ET4)ᵒᵖ of Nakaoka and Palu
  [NP, Definition 2.12]. The realization `𝔰` of [NP] is encoded by the predicate: every extension
  is realized, two realizations are equivalent, and realizations are closed under equivalence.
* `ExtriangulatedFunctor`: an extriangulated functor into a pretriangulated category in the sense
  of Bennett-Tennenhaus and Shah [BS, Definition 2.32, `n = 1`], as recalled in the introduction.
* `ExtriangulatedFunctor.IsTriangulatedEmbedding`, `HasAlgebraicRealization`.
* `ExactStructure`, `ExactStructure.IsFrobenius`, `IsAlgebraicTriangulated`.

The definition of an algebraic triangulated category ("triangle equivalent to the stable category
of a Frobenius exact category") is stated through the quotient functor: a Frobenius exact category
`B` and an additive functor `Φ : B ⥤ T` which is full, essentially surjective, kills exactly the
morphisms factoring through a projective object, and carries connecting morphisms natural in
morphisms of conflations which complete the images of conflations to distinguished triangles.
-/

@[expose] public section

namespace ExtriangulatedRealization.Statement

open CategoryTheory Limits Opposite Pretriangulated

universe t w v u v' u'

section Data

variable (k : Type w) [CommRing k] (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- An extension bifunctor with values in `k`-modules together with a realization predicate. -/
structure ExtriangulatedData where
  /-- The extension bifunctor `E(C, A)`, contravariant in `C` and covariant in `A`. -/
  E : Cᵒᵖ ⥤ C ⥤ ModuleCat.{t} k
  /-- `Realizes δ x y`: the sequence `A -x→ B -y→ C` realizes `δ ∈ E(C, A)`. -/
  Realizes : ∀ {A B C' : C}, (E.obj (op C')).obj A → (A ⟶ B) → (B ⟶ C') → Prop

variable {k C}

namespace ExtriangulatedData

variable (𝔼 : ExtriangulatedData.{t} k C)

/-- The `k`-module `E(C, A)`. -/
abbrev Ext (C' A : C) : Type t := (𝔼.E.obj (op C')).obj A

/-- Pushforward `a_*` along `a : A ⟶ A'`. -/
def push {C' A A' : C} (a : A ⟶ A') : 𝔼.Ext C' A →ₗ[k] 𝔼.Ext C' A' :=
  ((𝔼.E.obj (op C')).map a).hom

/-- Pullback `c^*` along `c : C'' ⟶ C'`. -/
def pull {C'' C' A : C} (c : C'' ⟶ C') : 𝔼.Ext C' A →ₗ[k] 𝔼.Ext C'' A :=
  ((𝔼.E.map c.op).app A).hom

section Biproducts

variable [HasBinaryBiproducts C]

/-- The direct sum `δ ⊕ δ'` of two extensions [NP, Definition 2.6]. -/
noncomputable def sum {C₁ A₁ C₂ A₂ : C} (δ : 𝔼.Ext C₁ A₁) (δ' : 𝔼.Ext C₂ A₂) :
    𝔼.Ext (C₁ ⊞ C₂) (A₁ ⊞ A₂) :=
  𝔼.pull biprod.fst (𝔼.push biprod.inl δ) + 𝔼.pull biprod.snd (𝔼.push biprod.inr δ')

/-- The axioms of an extriangulated category [NP, Definition 2.12]. -/
structure IsExtriangulated : Prop where
  /-- (ET1) `E` is biadditive (and `k`-bilinear). -/
  push_add : ∀ {C' A A' : C} (a a' : A ⟶ A') (δ : 𝔼.Ext C' A),
    𝔼.push (a + a') δ = 𝔼.push a δ + 𝔼.push a' δ
  push_smul : ∀ {C' A A' : C} (r : k) (a : A ⟶ A') (δ : 𝔼.Ext C' A),
    𝔼.push (r • a) δ = r • 𝔼.push a δ
  pull_add : ∀ {C'' C' A : C} (c c' : C'' ⟶ C') (δ : 𝔼.Ext C' A),
    𝔼.pull (c + c') δ = 𝔼.pull c δ + 𝔼.pull c' δ
  pull_smul : ∀ {C'' C' A : C} (r : k) (c : C'' ⟶ C') (δ : 𝔼.Ext C' A),
    𝔼.pull (r • c) δ = r • 𝔼.pull c δ
  /-- Every extension is realized. -/
  exists_realizes : ∀ {C' A : C} (δ : 𝔼.Ext C' A), ∃ (B : C) (x : A ⟶ B) (y : B ⟶ C'),
    𝔼.Realizes δ x y
  /-- Two realizations of the same extension are equivalent. -/
  realizes_unique : ∀ {A B B' C' : C} {δ : 𝔼.Ext C' A} {x : A ⟶ B} {y : B ⟶ C'} {x' : A ⟶ B'}
    {y' : B' ⟶ C'}, 𝔼.Realizes δ x y → 𝔼.Realizes δ x' y' →
      ∃ b : B ≅ B', x ≫ b.hom = x' ∧ b.hom ≫ y' = y
  /-- Realizations are closed under equivalence of sequences. -/
  realizes_iso : ∀ {A B B' C' : C} {δ : 𝔼.Ext C' A} {x : A ⟶ B} {y : B ⟶ C'} (b : B ≅ B'),
    𝔼.Realizes δ x y → 𝔼.Realizes δ (x ≫ b.hom) (b.inv ≫ y)
  /-- Condition `(∗)` of a realization [NP, Definition 2.9]. -/
  realizes_morphism : ∀ {A B C' A' B' C'' : C} {δ : 𝔼.Ext C' A} {δ' : 𝔼.Ext C'' A'}
    {x : A ⟶ B} {y : B ⟶ C'} {x' : A' ⟶ B'} {y' : B' ⟶ C''}, 𝔼.Realizes δ x y →
      𝔼.Realizes δ' x' y' → ∀ (a : A ⟶ A') (c : C' ⟶ C''), 𝔼.push a δ = 𝔼.pull c δ' →
        ∃ b : B ⟶ B', x ≫ b = a ≫ x' ∧ y ≫ c = b ≫ y'
  /-- (ET2) The split extension is realized by the split sequence. -/
  realizes_zero : ∀ A C' : C,
    𝔼.Realizes (0 : 𝔼.Ext C' A) (biprod.inl : A ⟶ A ⊞ C') (biprod.snd : A ⊞ C' ⟶ C')
  /-- (ET2) Direct sums of realizations realize direct sums. -/
  realizes_sum : ∀ {A B C' A' B' C'' : C} {δ : 𝔼.Ext C' A} {δ' : 𝔼.Ext C'' A'}
    {x : A ⟶ B} {y : B ⟶ C'} {x' : A' ⟶ B'} {y' : B' ⟶ C''}, 𝔼.Realizes δ x y →
      𝔼.Realizes δ' x' y' → 𝔼.Realizes (𝔼.sum δ δ') (biprod.map x x') (biprod.map y y')
  /-- (ET3) -/
  et3 : ∀ {A B C' A' B' C'' : C} {δ : 𝔼.Ext C' A} {δ' : 𝔼.Ext C'' A'}
    {x : A ⟶ B} {y : B ⟶ C'} {x' : A' ⟶ B'} {y' : B' ⟶ C''}, 𝔼.Realizes δ x y →
      𝔼.Realizes δ' x' y' → ∀ (a : A ⟶ A') (b : B ⟶ B'), x ≫ b = a ≫ x' →
        ∃ c : C' ⟶ C'', y ≫ c = b ≫ y' ∧ 𝔼.push a δ = 𝔼.pull c δ'
  /-- (ET3)ᵒᵖ -/
  et3_op : ∀ {A B C' A' B' C'' : C} {δ : 𝔼.Ext C' A} {δ' : 𝔼.Ext C'' A'}
    {x : A ⟶ B} {y : B ⟶ C'} {x' : A' ⟶ B'} {y' : B' ⟶ C''}, 𝔼.Realizes δ x y →
      𝔼.Realizes δ' x' y' → ∀ (b : B ⟶ B') (c : C' ⟶ C''), y ≫ c = b ≫ y' →
        ∃ a : A ⟶ A', x ≫ b = a ≫ x' ∧ 𝔼.push a δ = 𝔼.pull c δ'
  /-- (ET4) -/
  et4 : ∀ {A B C' D F : C} {f : A ⟶ B} {f' : B ⟶ D} {g : B ⟶ C'} {g' : C' ⟶ F}
    {δ : 𝔼.Ext D A} {δ' : 𝔼.Ext F B}, 𝔼.Realizes δ f f' → 𝔼.Realizes δ' g g' →
      ∃ (E : C) (h' : C' ⟶ E) (d : D ⟶ E) (e : E ⟶ F) (δ'' : 𝔼.Ext E A),
        𝔼.Realizes δ'' (f ≫ g) h' ∧ f' ≫ d = g ≫ h' ∧ h' ≫ e = g' ∧
        𝔼.Realizes (𝔼.push f' δ') d e ∧ 𝔼.pull d δ'' = δ ∧ 𝔼.push f δ'' = 𝔼.pull e δ'
  /-- (ET4)ᵒᵖ, in the form of [NP, Remark 2.22]. -/
  et4_op : ∀ {D A B F C' : C} {f' : D ⟶ A} {f : A ⟶ B} {g' : F ⟶ B} {g : B ⟶ C'}
    {δ : 𝔼.Ext B D} {δ' : 𝔼.Ext C' F}, 𝔼.Realizes δ f' f → 𝔼.Realizes δ' g' g →
      ∃ (E : C) (h' : E ⟶ A) (d : D ⟶ E) (e : E ⟶ F) (δ'' : 𝔼.Ext C' E),
        𝔼.Realizes δ'' h' (f ≫ g) ∧ d ≫ h' = f' ∧ e ≫ g' = h' ≫ f ∧
        𝔼.Realizes (𝔼.pull g' δ) d e ∧ δ' = 𝔼.push e δ'' ∧ 𝔼.push d δ = 𝔼.pull g δ''

end Biproducts

/-! ### Subcategories, injective objects, heredity -/

/-- A full subcategory, given by an object property, is extension-closed. -/
def IsExtensionClosed (P : ObjectProperty C) : Prop :=
  ∀ {A B C' : C} {δ : 𝔼.Ext C' A} {x : A ⟶ B} {y : B ⟶ C'}, 𝔼.Realizes δ x y → P A → P C' → P B

/-- The induced extension bifunctor and realizations on a full subcategory. -/
def restrict (P : ObjectProperty C) : ExtriangulatedData.{t} k P.FullSubcategory where
  E := P.ι.op ⋙ 𝔼.E ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι
  Realizes δ x y := 𝔼.Realizes δ x.hom y.hom

/-- An injective object: morphisms into it extend along the first map of every conflation. -/
def IsInjectiveObject (U : C) : Prop :=
  ∀ {A B C' : C} {δ : 𝔼.Ext C' A} {x : A ⟶ B} {y : B ⟶ C'}, 𝔼.Realizes δ x y →
    ∀ f : A ⟶ U, ∃ g : B ⟶ U, x ≫ g = f

/-- Every object is the first term of a conflation with injective middle term. -/
def HasEnoughInjectives : Prop :=
  ∀ A : C, ∃ (B C' : C) (δ : 𝔼.Ext C' A) (x : A ⟶ B) (y : B ⟶ C'),
    𝔼.Realizes δ x y ∧ 𝔼.IsInjectiveObject B

/-- The generators `α₁ ⊗ ⋯ ⊗ αₙ` of the tensor power `Eⁿ(C, A)` of Gorsky, Nakaoka and Palu
[GNP, Definition 3.1]: `α₁ ∈ E(M₁, A)`, `α₂ ∈ E(M₂, M₁)`, …, `αₙ ∈ E(C, Mₙ₋₁)`. -/
inductive TensorWord : C → C → ℕ → Type (max u t)
  | single {C' A : C} (α : 𝔼.Ext C' A) : TensorWord C' A 1
  | cons {C' M A : C} {n : ℕ} (α : 𝔼.Ext M A) (w : TensorWord C' M n) : TensorWord C' A (n + 1)

/-- Pushforward of the first factor of a word along `f : M ⟶ N`. -/
def TensorWord.push {C' M N : C} (f : M ⟶ N) :
    ∀ {n : ℕ}, 𝔼.TensorWord C' M n → 𝔼.TensorWord C' N n
  | _, .single α => .single (𝔼.push f α)
  | _, .cons α w => .cons (𝔼.push f α) w

/-- The defining relations of `Eⁿ`: additivity in every factor and the balance
`(f^* α) ⊗ w = α ⊗ (f_* w)` at every junction. -/
inductive TensorRel : ∀ {C' A : C} {n : ℕ}, FreeAbelianGroup (𝔼.TensorWord C' A n) → Prop
  | add_single {C' A : C} (α α' : 𝔼.Ext C' A) :
      TensorRel (.of (.single (α + α')) - .of (.single α) - .of (.single α'))
  | add_cons {C' M A : C} {n : ℕ} (α α' : 𝔼.Ext M A) (w : 𝔼.TensorWord C' M n) :
      TensorRel (.of (.cons (α + α') w) - .of (.cons α w) - .of (.cons α' w))
  | balance {C' M N A : C} {n : ℕ} (f : M ⟶ N) (α : 𝔼.Ext N A) (w : 𝔼.TensorWord C' M n) :
      TensorRel (.of (.cons (𝔼.pull f α) w) - .of (.cons α (TensorWord.push 𝔼 f w)))
  | tail {C' M A : C} {n : ℕ} (α : 𝔼.Ext M A) {r : FreeAbelianGroup (𝔼.TensorWord C' M n)} :
      TensorRel r → TensorRel (FreeAbelianGroup.map (.cons α) r)

/-- Heredity: `Eⁿ = 0` for every `n ≥ 2`, that is, every generator of `Eⁿ(C, A)` lies in the
subgroup generated by the relations. -/
def IsHereditary : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (C' A : C) (w : 𝔼.TensorWord C' A n),
    FreeAbelianGroup.of w ∈ AddSubgroup.closure {r | 𝔼.TensorRel r}

section Biproducts

variable [HasBinaryBiproducts C]

/-- A full subcategory closed under binary biproducts has binary biproducts, those of `C`. -/
theorem hasBinaryBiproductsOfClosed (P : ObjectProperty C)
    (hP : ∀ A B : C, P A → P B → P (A ⊞ B)) : HasBinaryBiproducts P.FullSubcategory :=
  ⟨fun A B => HasBinaryBiproduct.mk
    { bicone :=
        { pt := ⟨A.obj ⊞ B.obj, hP _ _ A.property B.property⟩
          fst := ObjectProperty.homMk biprod.fst
          snd := ObjectProperty.homMk biprod.snd
          inl := ObjectProperty.homMk biprod.inl
          inr := ObjectProperty.homMk biprod.inr
          inl_fst := by ext; exact biprod.inl_fst
          inl_snd := by ext; exact biprod.inl_snd
          inr_fst := by ext; exact biprod.inr_fst
          inr_snd := by ext; exact biprod.inr_snd }
      isBilimit := isBinaryBilimitOfTotal _
        (ObjectProperty.hom_ext _ (biprod.total (X := A.obj) (Y := B.obj))) }⟩

/-- A full subcategory closed under extensions and binary biproducts, with the induced extension
bifunctor, realizations and biproducts, is extriangulated. -/
def IsExtriangulatedSubcategory (P : ObjectProperty C) : Prop :=
  ∃ hP : ∀ A B : C, P A → P B → P (A ⊞ B),
    letI := hasBinaryBiproductsOfClosed P hP
    (𝔼.restrict P).IsExtriangulated

end Biproducts

end ExtriangulatedData

end Data

/-! ### Extriangulated functors into triangulated categories -/

section Functors

variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- An extriangulated functor into a pretriangulated category [BS, Definition 2.32 with `n = 1`]:
an additive functor `F` with additive maps `η : E(C, A) → T(FC, FA⟦1⟧)`, natural in both
variables, sending every realization `A -x→ B -y→ C` of `δ` to a distinguished triangle
`FA → FB → FC → FA⟦1⟧` with third morphism `η δ`. -/
structure ExtriangulatedFunctor (𝔼 : ExtriangulatedData.{t} k C)
    (T : Type u') [Category.{v'} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] where
  /-- The underlying functor. -/
  F : C ⥤ T
  additive : F.Additive
  /-- The natural transformation `η : E(C, A) → T(FC, FA⟦1⟧)`. -/
  η : ∀ {C' A : C}, 𝔼.Ext C' A →+ (F.obj C' ⟶ (F.obj A)⟦(1 : ℤ)⟧)
  η_push : ∀ {C' A A' : C} (a : A ⟶ A') (δ : 𝔼.Ext C' A),
    η (𝔼.push a δ) = η δ ≫ (F.map a)⟦(1 : ℤ)⟧'
  η_pull : ∀ {C'' C' A : C} (c : C'' ⟶ C') (δ : 𝔼.Ext C' A),
    η (𝔼.pull c δ) = F.map c ≫ η δ
  distinguished : ∀ {A B C' : C} {δ : 𝔼.Ext C' A} {x : A ⟶ B} {y : B ⟶ C'},
    𝔼.Realizes δ x y → Triangle.mk (F.map x) (F.map y) (η δ) ∈ distTriang T

namespace ExtriangulatedFunctor

variable {𝔼 : ExtriangulatedData.{t} k C}
    {T : Type u'} [Category.{v'} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- A triangulated embedding: the underlying functor is fully faithful. -/
def IsTriangulatedEmbedding (Φ : ExtriangulatedFunctor 𝔼 T) : Prop :=
  Φ.F.Full ∧ Φ.F.Faithful

/-- A triangulated realization: a triangulated embedding all of whose maps `η` are bijective. -/
def IsTriangulatedRealization (Φ : ExtriangulatedFunctor 𝔼 T) : Prop :=
  Φ.IsTriangulatedEmbedding ∧ ∀ C' A : C, Function.Bijective (Φ.η (C' := C') (A := A))

end ExtriangulatedFunctor

end Functors

/-! ### Exact categories, Frobenius categories, algebraic triangulated categories -/

section Exact

variable (B : Type u) [Category.{v} B] [Preadditive B] [HasZeroObject B]

/-- A Quillen exact structure in the form of Bühler [Bü, Definition 2.1]: an
isomorphism-closed class of kernel-cokernel pairs (the conflations) with axioms
[E0], [E0ᵒᵖ], [E1], [E1ᵒᵖ], [E2], [E2ᵒᵖ]. -/
structure ExactStructure where
  /-- The conflations. -/
  Conflation : ShortComplex B → Prop
  conflation_iso : ∀ {S S' : ShortComplex B}, Nonempty (S ≅ S') → Conflation S → Conflation S'
  isLimit_kernelFork : ∀ {S : ShortComplex B}, Conflation S →
    Nonempty (IsLimit (KernelFork.ofι S.f S.zero))
  isColimit_cokernelCofork : ∀ {S : ShortComplex B}, Conflation S →
    Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))
  /-- [E0] Identities are inflations. -/
  id_inflation : ∀ X : B, ∃ (Z : B) (g : X ⟶ Z) (w : 𝟙 X ≫ g = 0),
    Conflation (ShortComplex.mk (𝟙 X) g w)
  /-- [E0ᵒᵖ] Identities are deflations. -/
  id_deflation : ∀ X : B, ∃ (Z : B) (f : Z ⟶ X) (w : f ≫ 𝟙 X = 0),
    Conflation (ShortComplex.mk f (𝟙 X) w)
  /-- [E1] Inflations are closed under composition. -/
  inflation_comp : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z),
    (∃ (W : B) (p : Y ⟶ W) (w : f ≫ p = 0), Conflation (ShortComplex.mk f p w)) →
    (∃ (W : B) (p : Z ⟶ W) (w : g ≫ p = 0), Conflation (ShortComplex.mk g p w)) →
    (∃ (W : B) (p : Z ⟶ W) (w : (f ≫ g) ≫ p = 0), Conflation (ShortComplex.mk (f ≫ g) p w))
  /-- [E1ᵒᵖ] Deflations are closed under composition. -/
  deflation_comp : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z),
    (∃ (W : B) (i : W ⟶ X) (w : i ≫ f = 0), Conflation (ShortComplex.mk i f w)) →
    (∃ (W : B) (i : W ⟶ Y) (w : i ≫ g = 0), Conflation (ShortComplex.mk i g w)) →
    (∃ (W : B) (i : W ⟶ X) (w : i ≫ (f ≫ g) = 0), Conflation (ShortComplex.mk i (f ≫ g) w))
  /-- [E2] Pushouts of inflations along arbitrary morphisms exist and are inflations. -/
  pushout_inflation : ∀ {X Y X' : B} (i : X ⟶ Y) (t : X ⟶ X'),
    (∃ (W : B) (p : Y ⟶ W) (w : i ≫ p = 0), Conflation (ShortComplex.mk i p w)) →
    ∃ (Y' : B) (i' : X' ⟶ Y') (t' : Y ⟶ Y'), IsPushout i t t' i' ∧
      ∃ (W : B) (p : Y' ⟶ W) (w : i' ≫ p = 0), Conflation (ShortComplex.mk i' p w)
  /-- [E2ᵒᵖ] Pullbacks of deflations along arbitrary morphisms exist and are deflations. -/
  pullback_deflation : ∀ {Y Z Z' : B} (p : Y ⟶ Z) (t : Z' ⟶ Z),
    (∃ (W : B) (i : W ⟶ Y) (w : i ≫ p = 0), Conflation (ShortComplex.mk i p w)) →
    ∃ (Y' : B) (p' : Y' ⟶ Z') (t' : Y' ⟶ Y), IsPullback t' p' p t ∧
      ∃ (W : B) (i : W ⟶ Y') (w : i ≫ p' = 0), Conflation (ShortComplex.mk i p' w)

variable {B}

namespace ExactStructure

variable (ℰ : ExactStructure B)

/-- A projective object: morphisms out of it lift along every deflation. -/
def IsProjectiveObject (P : B) : Prop :=
  ∀ (S : ShortComplex B), ℰ.Conflation S → ∀ f : P ⟶ S.X₃, ∃ g : P ⟶ S.X₂, g ≫ S.g = f

/-- An injective object: morphisms into it extend along every inflation. -/
def IsInjectiveObject (I : B) : Prop :=
  ∀ (S : ShortComplex B), ℰ.Conflation S → ∀ f : S.X₁ ⟶ I, ∃ g : S.X₂ ⟶ I, S.f ≫ g = f

/-- A Frobenius exact structure: enough projectives, enough injectives, and the projective
objects are exactly the injective objects. -/
def IsFrobenius : Prop :=
  (∀ X : B, ∃ S : ShortComplex B, ℰ.Conflation S ∧ ℰ.IsProjectiveObject S.X₂ ∧
      Nonempty (S.X₃ ≅ X)) ∧
    (∀ X : B, ∃ S : ShortComplex B, ℰ.Conflation S ∧ ℰ.IsInjectiveObject S.X₂ ∧
      Nonempty (S.X₁ ≅ X)) ∧
    ∀ P : B, ℰ.IsProjectiveObject P ↔ ℰ.IsInjectiveObject P

end ExactStructure

end Exact

/-- A triangulated category is algebraic if it is triangle equivalent to the stable category of a
Frobenius exact category. We state this through the quotient functor `Φ : B ⥤ T`: it is additive,
full and essentially surjective, a morphism goes to zero exactly when it factors through a
projective object, and conflations go to distinguished triangles with connecting morphisms natural
in morphisms of conflations. -/
def IsAlgebraicTriangulated (T : Type u') [Category.{v'} T] [Preadditive T] [HasZeroObject T]
    [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] : Prop :=
  ∃ (B : Type u') (_ : Category.{v'} B) (_ : Preadditive B) (_ : HasZeroObject B)
    (ℰ : ExactStructure B) (Φ : B ⥤ T) (_ : Φ.Additive)
    (δ : ∀ S : ShortComplex B, ℰ.Conflation S → (Φ.obj S.X₃ ⟶ (Φ.obj S.X₁)⟦(1 : ℤ)⟧)),
    ℰ.IsFrobenius ∧ Φ.Full ∧ Φ.EssSurj ∧
    (∀ {X Y : B} (f : X ⟶ Y), Φ.map f = 0 ↔
      ∃ (P : B) (_ : ℰ.IsProjectiveObject P) (g : X ⟶ P) (h : P ⟶ Y), f = g ≫ h) ∧
    (∀ (S : ShortComplex B) (hS : ℰ.Conflation S),
      Triangle.mk (Φ.map S.f) (Φ.map S.g) (δ S hS) ∈ distTriang T) ∧
    (∀ (S S' : ShortComplex B) (hS : ℰ.Conflation S) (hS' : ℰ.Conflation S') (φ : S ⟶ S'),
      δ S hS ≫ (Φ.map φ.τ₁)⟦(1 : ℤ)⟧' = Φ.map φ.τ₃ ≫ δ S' hS')

namespace ExtriangulatedData

variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- `C` has a triangulated embedding into a triangulated category with objects in `Type u'` and
morphisms in `Type v'`. -/
def HasTriangulatedEmbedding (𝔼 : ExtriangulatedData.{t} k C) : Prop :=
  ∃ (T : Type u') (_ : Category.{v'} T) (_ : Preadditive T) (_ : HasZeroObject T)
    (_ : HasShift T ℤ) (_ : ∀ n : ℤ, (shiftFunctor T n).Additive) (_ : Pretriangulated T)
    (_ : IsTriangulated T) (Φ : ExtriangulatedFunctor 𝔼 T), Φ.IsTriangulatedEmbedding

/-- `C` has an algebraic realization: a triangulated realization into an algebraic triangulated
category with objects in `Type u'` and morphisms in `Type v'`. -/
def HasAlgebraicRealization (𝔼 : ExtriangulatedData.{t} k C) : Prop :=
  ∃ (T : Type u') (_ : Category.{v'} T) (_ : Preadditive T) (_ : HasZeroObject T)
    (_ : HasShift T ℤ) (_ : ∀ n : ℤ, (shiftFunctor T n).Additive) (_ : Pretriangulated T)
    (_ : IsTriangulated T), IsAlgebraicTriangulated T ∧
    ∃ Φ : ExtriangulatedFunctor 𝔼 T, Φ.IsTriangulatedRealization

end ExtriangulatedData

universe u₁


/-! ### The one-point extension of a linear category by a linear functor -/

section OnePointExtension

variable {k : Type u} [CommRing k] (𝒜 : Type u₁) [Category.{u} 𝒜] [Preadditive 𝒜] [Linear k 𝒜]
  (Ψ : 𝒜 ⥤ ModuleCat.{u} k)

/-- The objects of the one-point extension: `none` is the adjoined object `X`. -/
def OnePointExtension (_Ψ : 𝒜 ⥤ ModuleCat.{u} k) : Type u₁ := Option 𝒜

namespace OnePointExtension

variable {𝒜 Ψ}

/-- The morphism modules: `Hom(X, X) = k`, `Hom(X, a) = Ψ a`, `Hom(a, X) = 0`, and
`Hom(a, b)` is the morphism module of `𝒜`. -/
def homModule : OnePointExtension 𝒜 Ψ → OnePointExtension 𝒜 Ψ → ModuleCat.{u} k
  | none, none => ModuleCat.of k k
  | none, some a => Ψ.obj a
  | some _, none => ModuleCat.of k PUnit
  | some a, some b => ModuleCat.of k (a ⟶ b)

/-- Composition. -/
def comp : ∀ {X Y Z : OnePointExtension 𝒜 Ψ}, homModule X Y → homModule Y Z → homModule X Z
  | none, none, none, f, g => (show k from f) * (show k from g)
  | none, none, some _, f, g => (show k from f) • g
  | none, some _, none, _, _ => (0 : k)
  | none, some a, some b, f, g => (Ψ.map (show a ⟶ b from g)).hom f
  | some _, none, none, _, _ => PUnit.unit
  | some _, none, some _, _, _ => (0 : _ ⟶ _)
  | some _, some _, none, _, _ => PUnit.unit
  | some a, some b, some c, f, g => (show a ⟶ b from f) ≫ (show b ⟶ c from g)

/-- Identities. -/
def id : ∀ X : OnePointExtension 𝒜 Ψ, homModule X X
  | none => (1 : k)
  | some a => (𝟙 a : a ⟶ a)

variable [Ψ.Additive] [Ψ.Linear k]

instance category : Category.{u} (OnePointExtension 𝒜 Ψ) where
  Hom X Y := homModule X Y
  id := id
  comp := comp
  id_comp {X Y} f := by
    rcases X with _ | a <;> rcases Y with _ | b
    exacts [one_mul (show k from f), one_smul k (show Ψ.obj b from f), rfl,
      Category.id_comp (show a ⟶ b from f)]
  comp_id {X Y} f := by
    rcases X with _ | a <;> rcases Y with _ | b
    exacts [mul_one (show k from f), (by change (Ψ.map (𝟙 b)).hom f = f; rw [Ψ.map_id]; rfl), rfl,
      Category.comp_id (show a ⟶ b from f)]
  assoc {W X Y Z} f g h := by
    rcases W with _ | a <;> rcases X with _ | b <;> rcases Y with _ | c <;> rcases Z with _ | d
    exacts [mul_assoc (show k from f) (show k from g) (show k from h),
      mul_smul (show k from f) (show k from g) (show Ψ.obj d from h),
      (mul_zero (show k from f)).symm,
      map_smul (Ψ.map (show c ⟶ d from h)).hom (show k from f) (show Ψ.obj c from g),
      zero_mul (show k from h),
      (by change (0 : k) • (show Ψ.obj d from h) = (Ψ.map (0 : b ⟶ d)).hom f
          rw [zero_smul, Functor.map_zero]; rfl),
      rfl, (congrArg (fun φ => φ.hom f) (Ψ.map_comp (show b ⟶ c from g) (show c ⟶ d from h))).symm,
      rfl, rfl, rfl, zero_comp, rfl, comp_zero.symm, rfl,
      Category.assoc (show a ⟶ b from f) (show b ⟶ c from g) (show c ⟶ d from h)]

instance preadditive : Preadditive (OnePointExtension 𝒜 Ψ) where
  homGroup X Y := inferInstanceAs (AddCommGroup (homModule X Y))
  add_comp {X Y Z} f f' g := by
    rcases X with _ | a <;> rcases Y with _ | b <;> rcases Z with _ | c
    exacts [add_mul (show k from f) (show k from f') (show k from g),
      add_smul (show k from f) (show k from f') (show Ψ.obj c from g), (add_zero (0 : k)).symm,
      map_add (Ψ.map (show b ⟶ c from g)).hom (show Ψ.obj b from f) f', rfl,
      (add_zero (0 : a ⟶ c)).symm, rfl, Preadditive.add_comp _ _ _ (show a ⟶ b from f) f' g]
  comp_add {X Y Z} f g g' := by
    rcases X with _ | a <;> rcases Y with _ | b <;> rcases Z with _ | c
    exacts [mul_add (show k from f) (show k from g) (show k from g'),
      smul_add (show k from f) (show Ψ.obj c from g) (show Ψ.obj c from g'),
      (add_zero (0 : k)).symm,
      (by have h := congrArg (fun φ => φ.hom f)
            (Ψ.map_add (f := (show b ⟶ c from g)) (g := (show b ⟶ c from g')))
          simp only [ModuleCat.hom_add] at h; exact h),
      rfl, (add_zero (0 : a ⟶ c)).symm, rfl, Preadditive.comp_add _ _ _ (show a ⟶ b from f) g g']

instance linear : Linear k (OnePointExtension 𝒜 Ψ) where
  homModule X Y := inferInstanceAs (Module k (homModule X Y))
  smul_comp {X Y Z} r f g := by
    rcases X with _ | a <;> rcases Y with _ | b <;> rcases Z with _ | c
    exacts [smul_mul_assoc r (show k from f) (show k from g),
      smul_assoc r (show k from f) (show Ψ.obj c from g), (smul_zero (A := k) r).symm,
      map_smul (Ψ.map (show b ⟶ c from g)).hom r (show Ψ.obj b from f), rfl,
      (smul_zero (A := a ⟶ c) r).symm, rfl, Linear.smul_comp _ _ _ r (show a ⟶ b from f) g]
  comp_smul {X Y Z} f r g := by
    rcases X with _ | a <;> rcases Y with _ | b <;> rcases Z with _ | c
    exacts [mul_smul_comm r (show k from f) (show k from g),
      smul_comm (show k from f) r (show Ψ.obj c from g), (smul_zero (A := k) r).symm,
      (by have h := congrArg (fun φ => φ.hom f) (Functor.map_smul Ψ r (show b ⟶ c from g))
          simp only [ModuleCat.hom_smul] at h; exact h),
      rfl, (smul_zero (A := a ⟶ c) r).symm, rfl, Linear.comp_smul _ _ _ (show a ⟶ b from f) r g]

end OnePointExtension

end OnePointExtension

/-! ### Linear structure on the additive envelope -/

section MatLinear

variable {k : Type u} [CommRing k] {𝒞 : Type u₁} [Category.{u} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]

instance Mat_.linear : Linear k (Mat_ 𝒞) where
  homModule M N := inferInstanceAs (Module k (∀ i j, M.X i ⟶ N.X j))
  smul_comp M N K r f g := by
    ext i j; simp only [Mat_.comp_apply]
    change ∑ l, (r • f i l) ≫ g l j = r • ∑ l, f i l ≫ g l j
    simp [Finset.smul_sum, Linear.smul_comp]
  comp_smul M N K f r g := by
    ext i j; simp only [Mat_.comp_apply]
    change ∑ l, f i l ≫ (r • g l j) = r • ∑ l, f i l ≫ g l j
    simp [Finset.smul_sum, Linear.comp_smul]

end MatLinear

/-! ### Interval representations of `I_* = WithBot I` -/

instance Mat_.hasBinaryBiproducts {𝒞 : Type u₁} [Category.{u} 𝒞] [Preadditive 𝒞] :
    HasBinaryBiproducts (Mat_ 𝒞) :=
  hasBinaryBiproducts_of_finite_biproducts _

instance Functor.mapMat_additive {𝒞 𝒟 : Type*} [Category.{u} 𝒞] [Preadditive 𝒞]
    [Category.{u} 𝒟] [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive] : F.mapMat_.Additive where
  map_add {M N} f g := by ext i j; exact F.map_add

section Intervals

variable (k : Type u) [Field k] (I : Type u) [LinearOrder I]

/-- Representations of `I_*`, the ordered set `I` with a new least element `⊥` (written `*` in
the manuscript), in `k`-vector spaces. -/
abbrev Rep := WithBot I ⥤ ModuleCat.{u} k

instance Rep.hasFiniteBiproducts : HasFiniteBiproducts (Rep k I) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {k I}

open Classical in
/-- The interval representation `k_U` of an interval `U ⊆ I_*`: its value at `t` is `k` if
`t ∈ U` and `0` otherwise (modelled as the functions on `{() | t ∈ U}`), with identity structure
maps between points of `U`. -/
noncomputable def intervalRep (U : Set (WithBot I)) [hU : U.OrdConnected] : Rep k I where
  obj t := ModuleCat.of k ({_x : Unit // t ∈ U} → k)
  map {s t} _ := ModuleCat.ofHom
    { toFun := fun f _ => if hs : s ∈ U then f ⟨(), hs⟩ else 0
      map_add' := fun f g => by funext x; split_ifs <;> simp
      map_smul' := fun r f => by funext x; split_ifs <;> simp }
  map_id t := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
    simp only [x.2, ↓reduceDIte]; rfl
  map_comp {s t r} hst htr := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
    change (if hs : s ∈ U then f ⟨(), hs⟩ else 0) =
      if ht : t ∈ U then (if hs : s ∈ U then f ⟨(), hs⟩ else 0) else 0
    by_cases hs : s ∈ U
    · have ht : t ∈ U := hU.out hs x.2 ⟨leOfHom hst, leOfHom htr⟩
      simp [hs, ht]
    · simp [hs]

/-- The labels of the indecomposable interval representations: `Y = k_{{*}}`,
`A i = k_{[0,i]}` and `P i = k_{[*,i]}`. -/
inductive IntervalLabel (I : Type u) : Type u
  | Y : IntervalLabel I
  | A (i : I) : IntervalLabel I
  | P (i : I) : IntervalLabel I

/-- The support of a labelled interval in `I_*`. -/
def IntervalLabel.support : IntervalLabel I → Set (WithBot I)
  | .Y => Set.Iic ⊥
  | .A i => Set.Ioc ⊥ (i : WithBot I)
  | .P i => Set.Iic (i : WithBot I)

instance IntervalLabel.ordConnected (l : IntervalLabel I) : l.support.OrdConnected := by
  cases l <;> dsimp [IntervalLabel.support] <;> infer_instance

variable (k) in
/-- The interval representation with a given label. -/
noncomputable def IntervalLabel.rep (l : IntervalLabel I) : Rep k I := intervalRep l.support

variable (k I) in
/-- The full subcategory of `Rep k I` on the interval representations `Y`, `A i`, `P i`. -/
abbrev IntervalCat := InducedCategory (Rep k I) (IntervalLabel.rep k (I := I))

lemma IntervalLabel.mem_A_self (i : I) : (i : WithBot I) ∈ (IntervalLabel.A i).support :=
  ⟨WithBot.bot_lt_coe i, le_rfl⟩

open Classical in
/-- Naturality of a morphism of interval representations, evaluated at a point. -/
lemma intervalRep_app_map {U V : Set (WithBot I)} [U.OrdConnected] [hV : V.OrdConnected]
    (φ : (intervalRep U : Rep k I) ⟶ intervalRep V) {s t : WithBot I} (hst : s ≤ t)
    (f : (intervalRep U : Rep k I).obj s) (x : {_x : Unit // t ∈ V}) :
    (φ.app t).hom (((intervalRep U : Rep k I).map (homOfLE hst)).hom f) x =
      if hs : s ∈ V then (φ.app s).hom f ⟨(), hs⟩ else 0 := by
  exact congrArg (fun g => (g.hom f) x) (φ.naturality (homOfLE hst))
open Classical in
lemma intervalRep_map_apply {U : Set (WithBot I)} [U.OrdConnected] {s t : WithBot I}
    (hst : s ≤ t) (f : (intervalRep U : Rep k I).obj s) (x : {_x : Unit // t ∈ U}) :
    ((intervalRep U : Rep k I).map (homOfLE hst)).hom f x =
      if hs : s ∈ U then f ⟨(), hs⟩ else 0 := rfl
/-- An element of an interval representation at a point outside the support is zero. -/
lemma intervalRep_obj_eq_zero {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I}
    (ht : t ∉ U) (f : (intervalRep U : Rep k I).obj t) : f = 0 :=
  funext fun x => absurd x.2 ht
/-- An element of an interval representation at a point of the support is determined by its
value. -/
lemma intervalRep_obj_ext {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I} (ht : t ∈ U)
    {f g : (intervalRep U : Rep k I).obj t} (h : f ⟨(), ht⟩ = g ⟨(), ht⟩) : f = g :=
  funext fun _ => h
lemma IntervalLabel.not_bot_mem_A (i : I) : (⊥ : WithBot I) ∉ (IntervalLabel.A i).support :=
  fun h => lt_irrefl _ h.1
lemma IntervalLabel.coe_not_mem_Y (i : I) : (i : WithBot I) ∉ (IntervalLabel.Y (I := I)).support :=
  fun h => WithBot.coe_ne_bot (le_bot_iff.mp (show (i : WithBot I) ≤ ⊥ from h))
lemma IntervalLabel.coe_mem_A {i j : I} : (i : WithBot I) ∈ (IntervalLabel.A j).support ↔ i ≤ j :=
  ⟨fun h => WithBot.coe_le_coe.mp h.2, fun h => ⟨WithBot.bot_lt_coe i, WithBot.coe_le_coe.mpr h⟩⟩
lemma IntervalLabel.coe_mem_P {i j : I} : (i : WithBot I) ∈ (IntervalLabel.P j).support ↔ i ≤ j :=
  WithBot.coe_le_coe
/-- There are no nonzero morphisms `A j ⟶ A i` when `j < i`. -/
lemma app_eq_zero_of_not_le {i j : I} (hij : ¬ i ≤ j)
    (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k) {t : WithBot I}
    (ht : t ∈ (IntervalLabel.A i).support) (f : ((IntervalLabel.A j).rep k).obj t) :
    (φ.app t).hom f = 0 := by
  apply intervalRep_obj_ext ht
  have hle : t ≤ (i : WithBot I) := (show ⊥ < t ∧ t ≤ (i : WithBot I) from ht).2
  have h := intervalRep_app_map φ hle f ⟨(), IntervalLabel.mem_A_self i⟩
  rw [dite_eq_left ht] at h
  have hz : ((intervalRep (IntervalLabel.A j).support : Rep k I).map (homOfLE hle)).hom f = 0 :=
    intervalRep_obj_eq_zero (fun hm => hij (IntervalLabel.coe_mem_A.mp hm)) _
  refine h.symm.trans ?_; simp only [hz, map_zero]; rfl
/-- The scalar by which a morphism `A j ⟶ A i` of representations acts, read off at `i`. -/
noncomputable def coeffRep {i j : I} (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k) :
    k :=
  (φ.app (i : WithBot I)).hom (fun _ => (1 : k)) ⟨(), IntervalLabel.mem_A_self i⟩
/-- A morphism `A j ⟶ A i` acts by its scalar at every common point of the supports. -/
lemma app_one_eq_coeffRep {i j : I} (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k)
    {t : WithBot I} (htj : t ∈ (IntervalLabel.A j).support)
    (hti : t ∈ (IntervalLabel.A i).support) :
    (φ.app t).hom (fun _ => (1 : k)) ⟨(), hti⟩ = coeffRep φ := by
  have hle : t ≤ (i : WithBot I) := (show ⊥ < t ∧ t ≤ (i : WithBot I) from hti).2
  have h := intervalRep_app_map φ hle (fun _ => (1 : k)) ⟨(), IntervalLabel.mem_A_self i⟩
  rw [dite_eq_left hti] at h
  have hm : ((intervalRep (IntervalLabel.A j).support : Rep k I).map (homOfLE hle)).hom
      (fun _ => (1 : k)) = fun _ => (1 : k) := funext fun _ => dite_eq_left htj
  refine h.symm.trans ?_; simp only [hm]; rfl
/-- There are no nonzero morphisms `Y ⟶ A h` (evaluated at `h`). -/
lemma app_Y_eq_zero {h : I} (ψ : (IntervalLabel.Y (I := I)).rep k ⟶ (IntervalLabel.A h).rep k)
    (f : ((IntervalLabel.Y (I := I)).rep k).obj (h : WithBot I)) :
    (ψ.app (h : WithBot I)).hom f = 0 := by
  rw [intervalRep_obj_eq_zero (IntervalLabel.coe_not_mem_Y h) f]
  exact (ψ.app _).hom.map_zero
/-- There are no nonzero morphisms `P i ⟶ A h` (evaluated at `h`). -/
lemma app_P_eq_zero {i h : I} (ψ : (IntervalLabel.P i).rep k ⟶ (IntervalLabel.A h).rep k)
    (f : ((IntervalLabel.P i).rep k).obj (h : WithBot I)) :
    (ψ.app (h : WithBot I)).hom f = 0 := by
  by_cases hhi : h ≤ i
  · have hmem : (h : WithBot I) ∈ (IntervalLabel.P i).support := IntervalLabel.coe_mem_P.mpr hhi
    have hbot : (⊥ : WithBot I) ∈ (IntervalLabel.P i).support :=
      (bot_le : (⊥ : WithBot I) ≤ (i : WithBot I))
    have hf : f = ((intervalRep (IntervalLabel.P i).support : Rep k I).map
        (homOfLE (bot_le : (⊥ : WithBot I) ≤ h))).hom (fun _ => f ⟨(), hmem⟩) := by
      apply intervalRep_obj_ext hmem
      exact ((intervalRep_map_apply (k := k) (U := (IntervalLabel.P i).support)
        (bot_le : (⊥ : WithBot I) ≤ h) (fun _ => f ⟨(), hmem⟩) ⟨(), hmem⟩).trans
        (dite_eq_left hbot)).symm
    apply intervalRep_obj_ext (IntervalLabel.mem_A_self h); rw [hf]
    exact (intervalRep_app_map ψ (bot_le : (⊥ : WithBot I) ≤ h) _ _).trans
      (dite_eq_right (IntervalLabel.not_bot_mem_A h))
  · rw [intervalRep_obj_eq_zero (fun hm => hhi (IntervalLabel.coe_mem_P.mp hm)) f]
    exact (ψ.app _).hom.map_zero
end Intervals
/-! ### The functor `Ψ = C(D)(X, -)` on interval representations -/
section Psi
variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]
lemma coeffRep_comp_of_Y {j h : I}
    (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.Y (I := I)).rep k)
    (ψ : (IntervalLabel.Y (I := I)).rep k ⟶ (IntervalLabel.A h).rep k) : coeffRep (φ ≫ ψ) = 0 :=
  congrFun (app_Y_eq_zero ψ _) _
lemma coeffRep_comp_of_P {i j h : I} (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.P i).rep k)
    (ψ : (IntervalLabel.P i).rep k ⟶ (IntervalLabel.A h).rep k) : coeffRep (φ ≫ ψ) = 0 :=
  congrFun (app_P_eq_zero ψ _) _
lemma coeffRep_comp_of_not_le_left {i j h : I} (hij : ¬ i ≤ j) (hhi : h ≤ i)
    (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k)
    (ψ : (IntervalLabel.A i).rep k ⟶ (IntervalLabel.A h).rep k) : coeffRep (φ ≫ ψ) = 0 := by
  have hz := app_eq_zero_of_not_le hij φ (IntervalLabel.coe_mem_A.mpr hhi) (fun _ => (1 : k))
  change (ψ.app (h : WithBot I)).hom ((φ.app (h : WithBot I)).hom (fun _ => (1 : k))) _ = 0
  rw [hz, map_zero]; rfl
lemma coeffRep_comp_of_not_le_right {i j h : I} (hhi : ¬ h ≤ i)
    (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k)
    (ψ : (IntervalLabel.A i).rep k ⟶ (IntervalLabel.A h).rep k) : coeffRep (φ ≫ ψ) = 0 :=
  congrFun (app_eq_zero_of_not_le hhi ψ (IntervalLabel.mem_A_self h) _) _
lemma coeffRep_comp {i j h : I} (hij : i ≤ j) (hhi : h ≤ i)
    (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k)
    (ψ : (IntervalLabel.A i).rep k ⟶ (IntervalLabel.A h).rep k) :
    coeffRep (φ ≫ ψ) = coeffRep φ * coeffRep ψ := by
  let cj : ((IntervalLabel.A j).rep k).obj (h : WithBot I) := fun _ => 1
  let ci : ((IntervalLabel.A i).rep k).obj (h : WithBot I) := fun _ => 1
  have hφ : (φ.app (h : WithBot I)).hom cj = coeffRep φ • ci := by
    apply intervalRep_obj_ext (IntervalLabel.coe_mem_A.mpr hhi)
    exact (app_one_eq_coeffRep φ (IntervalLabel.coe_mem_A.mpr (hhi.trans hij))
      (IntervalLabel.coe_mem_A.mpr hhi)).trans (mul_one _).symm
  change (ψ.app (h : WithBot I)).hom ((φ.app (h : WithBot I)).hom cj) _ = _
  rw [hφ, map_smul]; rfl
lemma coeffRep_id (i : I) : coeffRep (𝟙 ((IntervalLabel.A i).rep k)) = 1 := rfl
lemma coeffRep_add {i j : I} (φ ψ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k) :
    coeffRep (φ + ψ) = coeffRep φ + coeffRep ψ := rfl
lemma coeffRep_smul {i j : I} (r : k) (φ : (IntervalLabel.A j).rep k ⟶ (IntervalLabel.A i).rep k) :
    coeffRep (r • φ) = r * coeffRep φ := rfl

variable (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- `Ψ` on objects: `Ψ(A i) = D_i`, `Ψ(Y) = Ψ(P i) = 0`, as in (2.3). -/
def psiObj : IntervalCat k I → ModuleCat.{u} k
  | IntervalLabel.Y => ModuleCat.of k PUnit
  | IntervalLabel.A i => D.obj (op i)
  | IntervalLabel.P _ => ModuleCat.of k PUnit

/-- `Ψ` on morphisms: postcomposition with `c • a_{ji} : A j ⟶ A i` acts by `c • π_{ji}`. -/
noncomputable def psiMap : ∀ {l l' : IntervalCat k I}, (l ⟶ l') → (psiObj D l ⟶ psiObj D l')
  | IntervalLabel.A j, IntervalLabel.A i, φ =>
      if h : i ≤ j then coeffRep φ.hom • D.map (homOfLE h).op else 0
  | IntervalLabel.Y, _, _ => 0
  | IntervalLabel.P _, _, _ => 0
  | IntervalLabel.A _, IntervalLabel.Y, _ => 0
  | IntervalLabel.A _, IntervalLabel.P _, _ => 0

lemma psi_hom_ext_of_source_punit {M : ModuleCat.{u} k} (f g : ModuleCat.of k PUnit ⟶ M) :
    f = g := by
  ext x; obtain rfl : x = 0 := Subsingleton.elim _ _; simp

lemma psi_hom_ext_of_target_punit {M : ModuleCat.{u} k} (f g : M ⟶ ModuleCat.of k PUnit) :
    f = g := by
  ext

/-- The functor `Ψ = C(D)(X, -)` on the interval representations. -/
noncomputable def psi : IntervalCat k I ⥤ ModuleCat.{u} k where
  obj := psiObj D
  map := psiMap D
  map_id l := by
    rcases l with _ | i | i <;> try exact psi_hom_ext_of_source_punit _ _
    change (if h : i ≤ i then coeffRep (𝟙 _) • D.map (homOfLE h).op else 0) = 𝟙 _
    rw [dite_eq_left le_rfl, coeffRep_id, one_smul]
    exact (congrArg D.map (Subsingleton.elim _ _)).trans (D.map_id _)
  map_comp {l l' l''} φ ψ := by
    rcases l with _ | j | j <;> try exact psi_hom_ext_of_source_punit _ _
    rcases l'' with _ | h | h <;> try exact psi_hom_ext_of_target_punit _ _
    rcases l' with _ | i | i
    · change (if hh : h ≤ j then coeffRep (φ.hom ≫ ψ.hom) • D.map (homOfLE hh).op else 0) =
        0 ≫ 0
      simp [coeffRep_comp_of_Y]
    · change (if hh : h ≤ j then coeffRep (φ.hom ≫ ψ.hom) • D.map (homOfLE hh).op else 0) =
        (if hi : i ≤ j then coeffRep φ.hom • D.map (homOfLE hi).op else 0) ≫
          (if hh : h ≤ i then coeffRep ψ.hom • D.map (homOfLE hh).op else 0)
      by_cases hij : i ≤ j
      · by_cases hhi : h ≤ i
        · rw [dite_eq_left (hhi.trans hij), dite_eq_left hij, dite_eq_left hhi,
            coeffRep_comp hij hhi,
            Linear.smul_comp, Linear.comp_smul, smul_smul, ← D.map_comp]
          rfl
        · simp [coeffRep_comp_of_not_le_right hhi, hhi]
      · rw [dite_eq_right hij, zero_comp]
        by_cases hhi : h ≤ i
        · simp [coeffRep_comp_of_not_le_left hij hhi]
        · simp [coeffRep_comp_of_not_le_right hhi]
    · change (if hh : h ≤ j then coeffRep (φ.hom ≫ ψ.hom) • D.map (homOfLE hh).op else 0) =
        0 ≫ 0
      simp [coeffRep_comp_of_P]

instance psi_additive : (psi D).Additive where
  map_add {l l'} φ ψ := by
    rcases l with _ | j | j <;> try exact psi_hom_ext_of_source_punit _ _
    rcases l' with _ | i | i <;> try exact psi_hom_ext_of_target_punit _ _
    change (if h : i ≤ j then coeffRep (φ.hom + ψ.hom) • D.map (homOfLE h).op else 0) =
      (if h : i ≤ j then coeffRep φ.hom • D.map (homOfLE h).op else 0) +
        (if h : i ≤ j then coeffRep ψ.hom • D.map (homOfLE h).op else 0)
    split_ifs
    exacts [by rw [coeffRep_add, add_smul], by rw [add_zero]]

instance psi_linear : (psi D).Linear k where
  map_smul {l l'} φ r := by
    rcases l with _ | j | j <;> try exact psi_hom_ext_of_source_punit _ _
    rcases l' with _ | i | i <;> try exact psi_hom_ext_of_target_punit _ _
    change (if h : i ≤ j then coeffRep (r • φ.hom) • D.map (homOfLE h).op else 0) =
      r • (if h : i ≤ j then coeffRep φ.hom • D.map (homOfLE h).op else 0)
    split_ifs
    exacts [by rw [coeffRep_smul, smul_smul], by rw [smul_zero]]

end Psi

/-! ### The category `C(D)` (Construction 2.2) -/

section CD

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The indecomposable objects of `C(D)`: the adjoined object `X` (`none`) and the interval
representations `Y`, `A i`, `P i`, with morphisms (2.2) and (2.3). -/
abbrev IndCat := OnePointExtension (IntervalCat k I) (psi D)

/-- The category `C(D)`: finite direct sums of `X`, `Y`, `A i`, `P i` (Construction 2.2). -/
abbrev CD := Mat_ (IndCat D)

open ZeroObject in
/-- The functor `ρ` on indecomposables: `X ↦ 0`, and an interval object to its representation. -/
noncomputable def rho0 : IndCat D ⥤ Rep k I where
  obj X := match X with
    | none => 0
    | some l => l.rep k
  map {X Y} f := match X, Y, f with
    | some _, some _, f => InducedCategory.Hom.hom f
    | none, _, _ => 0
    | some _, none, _ => 0
  map_id X := by
    rcases X with _ | l
    exacts [(isZero_zero _).eq_of_src _ _, rfl]
  map_comp {X Y Z} f g := by
    rcases X with _ | a; · exact (isZero_zero _).eq_of_src _ _
    rcases Z with _ | c; · exact (isZero_zero _).eq_of_tgt _ _
    rcases Y with _ | b
    exacts [(zero_comp (f := (0 : (0 : Rep k I) ⟶ c.rep k))).symm, rfl]

instance rho0_additive : (rho0 D).Additive where
  map_add {X Y} f g := by
    rcases X with _ | a; · exact (isZero_zero _).eq_of_src _ _
    rcases Y with _ | b
    exacts [(isZero_zero _).eq_of_tgt _ _, rfl]

/-- The functor `ρ : C(D) ⥤ Rep k I`, killing `X` (Construction 2.2). -/
noncomputable def rho : CD D ⥤ Rep k I := (rho0 D).mapMat_ ⋙ Mat_.lift (𝟭 (Rep k I))

instance rho_additive : (rho D).Additive := by unfold rho; infer_instance

attribute [local instance] HasExt.standard

/-- The extension bifunctor `E(C, A) = Ext¹(ρC, ρA)`, computed in `Rep k I`. -/
noncomputable def extE : (CD D)ᵒᵖ ⥤ CD D ⥤ ModuleCat.{u + 1} k :=
  (rho D).op ⋙ Abelian.linearExtFunctor.{u + 1} k (Rep k I) 1 ⋙
    (Functor.whiskeringLeft _ _ _).obj (rho D)

/-- The summand of an object of `C(D)` formed by its copies of `X`. -/
def xPart (M : CD D) : CD D := subObj M fun i => (M.X i).isNone

/-- The inclusion of the `X`-part. -/
noncomputable def xIncl (M : CD D) : xPart D M ⟶ M := subIncl M fun i => (M.X i).isNone

/-- The projection onto the `X`-part. -/
noncomputable def xProj (M : CD D) : M ⟶ xPart D M := subProj M fun i => (M.X i).isNone

/-- The realizations of Construction 2.2: `A -x→ B -y→ C` realizes `ξ ∈ Ext¹(ρC, ρA)` when
`ρA → ρB → ρC` is a short exact sequence of class `ξ` and the sequence is equivalent to the
direct sum of a sequence `A → N → C` between the interval parts (killing the `X`-part of `A`)
and the split sequence `X^a → X^a ⊕ X^c → X^c` of the `X`-parts. -/
def Realizes {A B C : CD D} (ξ : ((extE D).obj (op C)).obj A) (x : A ⟶ B) (y : B ⟶ C) : Prop :=
  ∃ w : x ≫ y = 0,
    (∃ hS : (ShortComplex.mk ((rho D).map x) ((rho D).map y)
        (by rw [← Functor.map_comp, w, Functor.map_zero])).ShortExact, hS.extClass = ξ) ∧
    ∃ (N : CD D) (_ : ∀ i, (N.X i).isSome) (θ : B ≅ N ⊞ (xPart D A ⊞ xPart D C))
      (x' : A ⟶ N) (y' : N ⟶ C),
      xIncl D A ≫ x' = 0 ∧ x ≫ θ.hom = biprod.lift x' (biprod.lift (xProj D A) 0) ∧
      θ.hom ≫ biprod.desc y' (biprod.desc 0 (xIncl D C)) = y

/-- The extriangulated data of `C(D)` (Construction 2.2). -/
noncomputable def cdData : ExtriangulatedData.{u + 1} k (CD D) where
  E := extE D
  Realizes := Realizes D

/-- Whether a label has its index in `J` (the labels `X` and `Y` always do). -/
def labelIn (J : Set I) : Option (IntervalLabel I) → Prop
  | none => True
  | some IntervalLabel.Y => True
  | some (IntervalLabel.A i) => i ∈ J
  | some (IntervalLabel.P i) => i ∈ J

/-- The full subcategory `C_J` of `C(D)`: finite direct sums of `X`, `Y` and `A i`, `P i` with
`i ∈ J`. -/
def subcatJ (J : Set I) : ObjectProperty (CD D) := fun M => ∀ i, labelIn J (M.X i)

/-- The label predicate defining the full subcategory `C_J`. -/
abbrev labelsIn (J : Set I) : ObjectProperty (CD D) := subcatJ D J

/-- The single object of `C(D)` given by a label (`none` is `X`). -/
noncomputable abbrev single (l : IndCat D) : CD D := (Mat_.embedding (IndCat D)).obj l

end CD

/-! ### Krull–Schmidt categories and indecomposable objects -/

section KrullSchmidt

variable (𝒞 : Type*) [Category 𝒞] [Preadditive 𝒞] [HasFiniteBiproducts 𝒞]

/-- A Krull–Schmidt category: every object is a finite direct sum of objects with local
endomorphism rings. -/
def IsKrullSchmidt : Prop :=
  ∀ X : 𝒞, ∃ (n : ℕ) (Y : Fin n → 𝒞), (∀ i, IsLocalRing (End (Y i))) ∧ Nonempty (X ≅ ⨁ Y)

/-- The isomorphism classes of indecomposable objects. -/
def IndecomposableClasses [HasBinaryBiproducts 𝒞] : Type _ :=
  {s : Set 𝒞 // ∃ X : 𝒞, Indecomposable X ∧ s = {Y | Nonempty (Y ≅ X)}}

end KrullSchmidt

/-! ### Inverse systems -/

section InverseSystems

variable {k : Type u} [Ring k] {I : Type u} [Preorder I]

/-- The transition maps `π_{ji} : D_j → D_i` of the inverse system are surjective. -/
def HasSurjectiveTransitions (D : Iᵒᵖ ⥤ ModuleCat.{u} k) : Prop :=
  ∀ {i j : I} (h : i ≤ j), Function.Surjective (D.map (homOfLE h).op).hom

/-- Every projection `lim D → D_i` is surjective: every `u ∈ D_i` is the `i`-th component of a
compatible family. -/
def ProjectionsSurjective (D : Iᵒᵖ ⥤ ModuleCat.{u} k) : Prop :=
  ∀ (i : I) (x : D.obj (op i)), ∃ y : ∀ j : I, D.obj (op j),
    (∀ {j j' : I} (h : j ≤ j'), (D.map (homOfLE h).op).hom (y j') = y j) ∧ y i = x

end InverseSystems

/-! ### The endpoints -/

/-- The nonzero first extension spaces between indecomposables in (4.1):
`E(Y, A i)` and `E(P j, A i)` with `j < i`. -/
def IsExtPair {k : Type u} [Field k] {I : Type u} [LinearOrder I] {D : Iᵒᵖ ⥤ ModuleCat.{u} k} :
    IndCat D → IndCat D → Prop
  | some IntervalLabel.Y, some (IntervalLabel.A _) => True
  | some (IntervalLabel.P j), some (IntervalLabel.A i) => j < i
  | _, _ => False

/-- Algebraic-realization consequence of Proposition 2.3. If a vector space `W` maps compatibly and
surjectively onto the `D_i`, `i ∈ J`, then `C_J`, with the induced structure, is extriangulated
and has an algebraic realization. The paper constructs the realization in the bounded
homotopy category. The formal construction uses the homotopy category of all cochain complexes. -/
def Proposition23 : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k), HasSurjectiveTransitions D →
    ∀ (J : Set I) (W : ModuleCat.{u} k) (q : ∀ i ∈ J, W ⟶ D.obj (op i)),
      (∀ i (hi : i ∈ J), Function.Surjective (q i hi).hom) →
      (∀ (i j : I) (hi : i ∈ J) (hj : j ∈ J) (h : i ≤ j), q j hj ≫ D.map (homOfLE h).op = q i hi) →
      (cdData D).IsExtriangulatedSubcategory (subcatJ D J) ∧
      ((cdData D).restrict (subcatJ D J)).HasAlgebraicRealization.{_, _, _, _, u, max 1 u}

/-- **Corollary 2.4.** `C(D)` is an essentially small `k`-linear extriangulated category; each
`C_J` is a full extension-closed subcategory, extriangulated with the induced structure; and
`C_J` has an algebraic realization when `J` has a largest element. -/
def Corollary24 : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k), HasSurjectiveTransitions D →
    (cdData D).IsExtriangulated ∧ EssentiallySmall.{u} (CD D) ∧
    ∀ J : Set I, (subcatJ D J).IsClosedUnderIsomorphisms ∧
      (cdData D).IsExtensionClosed (subcatJ D J) ∧
      (cdData D).IsExtriangulatedSubcategory (subcatJ D J) ∧
      ((∃ m ∈ J, ∀ i ∈ J, i ≤ m) →
        ((cdData D).restrict (subcatJ D J)).HasAlgebraicRealization.{_, _, _, _, u, max 1 u})

/-- **Theorem B (= Theorem 3.1).** `C(D)` admits a triangulated embedding if and only if every
projection `lim D → D_i` is surjective, if and only if `C(D)` has an algebraic realization. The
triangulated and algebraic targets have objects in `Type (max 1 u)` and morphisms in `Type u`,
the universes of `C(D)` itself. -/
def TheoremB : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k), HasSurjectiveTransitions D →
    ((cdData D).HasTriangulatedEmbedding.{_, _, _, _, u, max 1 u} ↔ ProjectionsSurjective D) ∧
    (ProjectionsSurjective D ↔ (cdData D).HasAlgebraicRealization.{_, _, _, _, u, max 1 u})

/-- **Theorem B, (1) ⇒ (2), in all universes.** A triangulated embedding of `C(D)` into a
triangulated category in any universes forces every projection `lim D → D_i` to be
surjective. -/
def TheoremBNecessity : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [LinearOrder I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k),
    (cdData D).HasTriangulatedEmbedding.{_, _, _, _, v', u'} → ProjectionsSurjective D

open Classical in
/-- **Proposition 4.4.** For every system `D`, `C(D)` is idempotent complete and Krull–Schmidt;
`X`, `Y`, `A i`, `P i` form a complete list of pairwise nonisomorphic indecomposables, each with
endomorphism ring `k`; the only nonzero first extension spaces between them are
`E(Y, A i) ≃ k` and `E(P j, A i) ≃ k` for `j < i` (4.1); `C(D)` has enough injectives; and
`Eⁿ = 0` for all `n ≥ 2`. -/
def Proposition44 : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k), HasSurjectiveTransitions D →
    IsIdempotentComplete (CD D) ∧ IsKrullSchmidt (CD D) ∧
    (∀ X : CD D, Indecomposable X → ∃ l : IndCat D, Nonempty (X ≅ single D l)) ∧
    (∀ l : IndCat D, Indecomposable (single D l)) ∧
    (∀ l l' : IndCat D, Nonempty (single D l ≅ single D l') → l = l') ∧
    (∀ (l : IndCat D) (f : single D l ⟶ single D l), ∃! c : k, f = c • 𝟙 _) ∧
    (∀ c a : IndCat D, Module.rank k ((cdData D).Ext (single D c) (single D a)) =
      if IsExtPair c a then 1 else 0) ∧
    (cdData D).HasEnoughInjectives ∧ (cdData D).IsHereditary

/-- **Proposition 4.6 (1), (2).** `C(D)` has an algebraic realization if `I` has a countable
cofinal subset, or if every `D_i` is finite-dimensional. -/
def Proposition46 : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    (D : Iᵒᵖ ⥤ ModuleCat.{u} k), HasSurjectiveTransitions D →
    ((∃ S : Set I, S.Countable ∧ ∀ i, ∃ j ∈ S, i ≤ j) →
        (cdData D).HasAlgebraicRealization.{_, _, _, _, u, max 1 u}) ∧
    ((∀ i, FiniteDimensional k (D.obj (op i))) →
        (cdData D).HasAlgebraicRealization.{_, _, _, _, u, max 1 u})

/-- **Theorem A (= Theorem 4.5).** Over every field `k` there is an inverse system `D` of
`k`-vector spaces with surjective transition maps over a nonempty well-ordered set such that the
essentially small `k`-linear extriangulated category `C(D)` satisfies:
(1) `C(D)` has no triangulated embedding. Not every projection `lim D → D_i` is surjective, so
by `TheoremBNecessity`, which holds for triangulated targets in all universes, this one
category has no triangulated embedding into a triangulated category in any universes; the
nonembedding is also stated directly for targets in the universes of `C(D)`;
(2) every countable family of objects of `C(D)` lies in a full extension-closed subcategory
having an algebraic realization;
(3) `C(D)` is hereditary, Krull–Schmidt, has enough injectives and `ℵ₁` isomorphism classes of
indecomposables, each with endomorphism ring `k`; `dim_k E(C, A) ≤ 1` for indecomposables
`A, C`; and every morphism space has at most countable dimension. -/
def TheoremA : Prop :=
  ∀ (k : Type u) [Field k], ∃ (I : Type u) (_ : LinearOrder I) (_ : WellFoundedLT I)
    (_ : Nonempty I) (D : Iᵒᵖ ⥤ ModuleCat.{u} k),
    HasSurjectiveTransitions D ∧ ¬ ProjectionsSurjective D ∧
    (cdData D).IsExtriangulated ∧ EssentiallySmall.{u} (CD D) ∧
    ¬ (cdData D).HasTriangulatedEmbedding.{_, _, _, _, u, max 1 u} ∧
    (∀ S : Set (CD D), S.Countable → ∃ P : ObjectProperty (CD D), P.IsClosedUnderIsomorphisms ∧
      (∀ X ∈ S, P X) ∧ (cdData D).IsExtensionClosed P ∧
      ((cdData D).restrict P).HasAlgebraicRealization.{_, _, _, _, u, max 1 u}) ∧
    (cdData D).IsHereditary ∧ IsKrullSchmidt (CD D) ∧ (cdData D).HasEnoughInjectives ∧
    Cardinal.mk (IndecomposableClasses (CD D)) = Cardinal.aleph 1 ∧
    (∀ X : CD D, Indecomposable X → ∀ f : X ⟶ X, ∃! c : k, f = c • 𝟙 X) ∧
    (∀ A C' : CD D, Indecomposable A → Indecomposable C' →
      Module.rank k ((cdData D).Ext C' A) ≤ 1) ∧
    (∀ X Y : CD D, Module.rank k (X ⟶ Y) ≤ Cardinal.aleph0)

end ExtriangulatedRealization.Statement
