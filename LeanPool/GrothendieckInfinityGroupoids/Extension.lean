/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckInfinityGroupoids.GlobularSum
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda

/-!
# Globular extensions, pseudo-coherators and ∞-groupoids of type `C` (roadmap 2.1, 2.2, 3.1)

Globular extensions (`GlobularExtension`, D. Ara, « On the homotopy theory of Grothendieck
∞-groupoids », J. Pure Appl. Algebra 217 (2013), 1237–1278, 1.4), globular functors
(`IsGlobularFunctor`), admissible pairs, liftings and contractibility (Ara 2013, 2.1–2.4), the
contractible globular extensions called pseudo-coherators by Maltsiniotis (`PseudoCoherator`),
and ∞-groupoids of type `C`, the presheaves sending globular sums to globular products
(`IsGlobularPresheaf`, `InfinityGroupoid`, Ara 2013, 1.8 and 2.5).

`TopCat` with the coglobular space of disks is a globular extension (`topCatExtension`, Ara 2013,
Examples 1.5.1–1.5.2); the pair `(1_{D_n}, 1_{D_n})` is admissible (`GlobularExtension.idPair`);
the terminal presheaf and every representable presheaf send globular sums to globular products
(`isGlobularPresheaf_terminal`, `isGlobularPresheaf_yoneda`, Ara 2013, 5.4).
-/

@[expose] public section

namespace LeanPool.GrothendieckInfinityGroupoids

open CategoryTheory Limits Opposite

universe u v w

/-- **Layer 2.1.** A globular extension (Ara 2013, 1.4): a category with a coglobular object and
a chosen globular sum for every table. No condition is put on the objects: `TopCat` with its
disks is one, and so is every free globular extension. -/
structure GlobularExtension where
  /-- The objects. -/
  Obj : Type u
  [cat : Category.{v} Obj]
  /-- The disks. -/
  disks : CoglobularObject Obj
  /-- The chosen globular sums. -/
  sums : GlobularSums disks

attribute [instance] GlobularExtension.cat

namespace GlobularExtension

variable (C : GlobularExtension)

/-- The globular sum of a table. -/
abbrev ofTable (T : Table) : C.Obj := C.sums.sum T

/-- The inclusion of the `k`-th disk of a table into its globular sum. -/
abbrev incl (T : Table) (k : Fin (T.width + 1)) : C.disks.disk (T.top k) ⟶ C.ofTable T :=
  C.sums.incl T k

/-- The globular sum of the one-disk table `(n)` is the disk `D_n`. -/
theorem ofTable_globe (n : ℕ) : C.ofTable (Table.globe n) = C.disks.disk n :=
  C.sums.sum_globe n

/-- Two maps `D_n ⟶ S` are parallel: equal sources and targets (no condition for `n = 0`). -/
def Parallel : (n : ℕ) → {S : C.Obj} → (C.disks.disk n ⟶ S) → (C.disks.disk n ⟶ S) → Prop
  | 0, _, _, _ => True
  | n + 1, _, f, g => C.disks.σ n ≫ f = C.disks.σ n ≫ g ∧ C.disks.τ n ≫ f = C.disks.τ n ≫ g

/-- Every map is parallel to itself. -/
theorem parallel_refl : ∀ (n : ℕ) {S : C.Obj} (f : C.disks.disk n ⟶ S), C.Parallel n f f
  | 0, _, _ => True.intro
  | _ + 1, _, _ => And.intro rfl rfl

/-- An admissible pair (Ara 2013, 2.3): parallel `f, g : D_n ⟶ S` with `S` the globular sum of a
table of dimension at most `n + 1`. -/
structure AdmissiblePair where
  /-- The dimension `n`. -/
  n : ℕ
  /-- The arity table. -/
  T : Table
  dim_le : T.dim ≤ n + 1
  /-- The first map. -/
  f : C.disks.disk n ⟶ C.ofTable T
  /-- The second map. -/
  g : C.disks.disk n ⟶ C.ofTable T
  parallel : C.Parallel n f g

/-- A lifting of an admissible pair. -/
def IsLifting (p : C.AdmissiblePair) (h : C.disks.disk (p.n + 1) ⟶ C.ofTable p.T) : Prop :=
  C.disks.σ p.n ≫ h = p.f ∧ C.disks.τ p.n ≫ h = p.g

/-- Contractibility (Ara 2013, 2.4): every admissible pair has a lifting. -/
def IsContractible : Prop := ∀ p : C.AdmissiblePair, ∃ h, C.IsLifting p h

/-- The admissible pair `(1_{D_n}, 1_{D_n})`, whose liftings give the identity cells. -/
abbrev idPair (n : ℕ) : C.AdmissiblePair where
  n := n
  T := Table.globe n
  dim_le := show Finset.univ.sup (fun _ : Fin 1 => n) ≤ n + 1 from
    Finset.sup_le fun _ _ => Nat.le_succ n
  f := eqToHom (C.ofTable_globe n).symm
  g := eqToHom (C.ofTable_globe n).symm
  parallel := C.parallel_refl n _

end GlobularExtension

/-- **Layer 2.1.** A globular functor from a globular extension `C` to a category `K` with a
coglobular object `D` (Ara 2013, 1.4): `R` sends the disks and faces of `C` to those of `D`, and
the image of each globular sum of `C` is a globular sum in `K`. -/
structure IsGlobularFunctor {K : Type u} [Category.{v} K] (C : GlobularExtension)
    (D : CoglobularObject K) (R : C.Obj ⥤ K) : Prop where
  obj_disk : ∀ n, R.obj (C.disks.disk n) = D.disk n
  map_σ : ∀ n, R.map (C.disks.σ n) =
    eqToHom (obj_disk n) ≫ D.σ n ≫ eqToHom (obj_disk (n + 1)).symm
  map_τ : ∀ n, R.map (C.disks.τ n) =
    eqToHom (obj_disk n) ≫ D.τ n ≫ eqToHom (obj_disk (n + 1)).symm
  isGlobularSum : ∀ (T : Table) (Y : K) (φ : ∀ k, D.disk (T.top k) ⟶ Y), D.Compatible T φ →
    ∃! u : R.obj (C.ofTable T) ⟶ Y,
      ∀ k, R.map (C.incl T k) ≫ u = eqToHom (obj_disk (T.top k)) ≫ φ k

/-- A contractible globular extension, called a pseudo-coherator by Maltsiniotis (2010) and in
Ara's thesis, as Ara 2013, 2.4, recalls. A coherator is a pseudo-coherator with a defining
cellular tower (Ara 2013, 2.10–2.11); the tower is Layer 2.4's `CellularTower` and is not
prototyped here, so this structure omits freeness. -/
structure PseudoCoherator extends GlobularExtension where
  contractible : toGlobularExtension.IsContractible
  /-- The lifting of `(1_{D_n}, 1_{D_n})` chosen once as data, from which the identity cells are
  built (it exists by `contractible`). -/
  idLift : ∀ n : ℕ, disks.disk ((toGlobularExtension.idPair n).n + 1) ⟶
    toGlobularExtension.ofTable (toGlobularExtension.idPair n).T
  isLifting_idLift :
    ∀ n : ℕ, toGlobularExtension.IsLifting (toGlobularExtension.idPair n) (idLift n)

/-! ## Layer 3: ∞-groupoids of type `C` -/

/-- A presheaf on `C` sends globular sums to globular products: every compatible family of
elements on the disks of a table comes from a unique element on the table (Ara 2013, 1.8). -/
def IsGlobularPresheaf (C : GlobularExtension) (X : C.Objᵒᵖ ⥤ Type w) : Prop :=
  ∀ (T : Table) (v : ∀ k, X.obj (op (C.disks.disk (T.top k)))),
    (∀ j, X.map (C.disks.faceTo (T.bot_lt_left j) false).op (v j.castSucc) =
      X.map (C.disks.faceTo (T.bot_lt_right j) true).op (v j.succ)) →
    ∃! a : X.obj (op (C.ofTable T)), ∀ k, X.map (C.incl T k).op a = v k

/-- **Layer 3.1.** The category `∞-Gpd_C` of ∞-groupoids of type `C` (Ara 2013, 2.5). -/
abbrev InfinityGroupoid (C : PseudoCoherator) :=
  ObjectProperty.FullSubcategory
    (fun X : C.Objᵒᵖ ⥤ Type w => IsGlobularPresheaf C.toGlobularExtension X)


/-- **Roadmap 2.1.** `TopCat` with the coglobular space of disks and its iterated pushouts is a
globular extension (Ara 2013, Examples 1.5.1–1.5.2). -/
noncomputable def topCatExtension : GlobularExtension.{1, 0} where
  Obj := TopCat.{0}
  disks := stdDisks
  sums := stdDisks.globularSums

/-- **Roadmap 3.1.** The terminal presheaf, with one cell in each dimension, sends globular sums
to globular products. -/
theorem isGlobularPresheaf_terminal (C : GlobularExtension.{u, v}) :
    IsGlobularPresheaf C ((Functor.const _).obj PUnit.{w + 1}) :=
  fun _ _ _ => ⟨PUnit.unit, fun _ => rfl, fun _ _ => rfl⟩

/-- **Roadmap 3.1.** Every representable presheaf `C(−, S)` sends globular sums to globular
products: this is the universal property of the globular sums (Ara 2013, 5.4). -/
theorem isGlobularPresheaf_yoneda (C : GlobularExtension.{u, v}) (S : C.Obj) :
    IsGlobularPresheaf C (yoneda.obj S) :=
  fun T v hv => C.sums.isGlobularSum T S v fun j => (hv j)

end LeanPool.GrothendieckInfinityGroupoids
