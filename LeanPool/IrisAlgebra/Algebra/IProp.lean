/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Janine Lohse
-/
module

-- Adapted for Lean Pool from Iris-Lean.

public import LeanPool.IrisAlgebra.Algebra.CMRA
public import LeanPool.IrisAlgebra.Algebra.OFE
public import LeanPool.IrisAlgebra.Algebra.UPred
public import LeanPool.IrisAlgebra.Algebra.GenMap
public import LeanPool.IrisAlgebra.Algebra.COFESolver
public import Init.Data.Vector

/-! The recursive Iris proposition model over ordered ghost resources.

Copyright (c) The Iris-Lean Contributors.
-/

@[expose] public section

namespace Iris

open COFE

/-- The index type for the global family of ghost-resource functors. -/
abbrev GType := Nat

universe u v w

/-- A resource functor admissible in the global ghost state: contractive, with affine algebras. -/
structure GFunctor where
  /-- The underlying mixed-variance family of resource carriers. -/
  F : ∀ (α : Type u) (β : Type v), [COFE α] → [COFE β] → Type w
  /-- Contractiveness of the resource functor action. -/
  [contractive : RFunctorContractive F]
  [affine : RFunctorAffine F]

/-- A global family of admissible ghost-resource functors. -/
structure BundledGFunctors where
  /-- The resource functor assigned to each ghost-resource index. -/
  get : GType → GFunctor.{u, v, w}

instance : CoeFun BundledGFunctors.{u, v, w} (fun _ => GType → GFunctor.{u, v, w}) :=
    ⟨BundledGFunctors.get⟩

/-- The global family assigning the constant unit resource to every index. -/
def BundledGFunctors.default : BundledGFunctors := ⟨fun _ => ⟨constOF Unit⟩⟩

/-- Replace the resource functor at one global index. -/
def BundledGFunctors.set (GF : BundledGFunctors) (i : Nat) (FB : GFunctor) :
    BundledGFunctors :=
  ⟨fun j => if j = i then FB else GF j⟩

/-- The natural-number names used for ghost-resource allocations. -/
abbrev GName := Nat

/-- The global ghost-resource functor, built from finite-support maps. -/
abbrev IResF (GF : BundledGFunctors) : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β]
    → Type _) := DiscreteFunOF (fun i => GenMapOF (GF i).F)

instance (GF : BundledGFunctors) (i : GType) : RFunctorContractive (GF i).F := (GF i).contractive

instance instRFunctorAffineGF (GF : BundledGFunctors) (i : GType) : RFunctorAffine (GF i).F := (GF
    i).affine

section IProp
open ORA

variable (GF : BundledGFunctors.{u, u, u})

/-- The complete recursive domain used to define Iris propositions. -/
def IPre : Type _ := OFunctor.Fix (UPredOF (IResF GF))

instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Fix _))

/-- The global unital ordered resource algebra over the recursive pre-propositions. -/
def IResUR : Type u := (i : GType) → GenMap ((GF i).F (IPre GF) (IPre GF))

instance : UORA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GenMap ((GF i).F (IPre GF) (IPre GF)))

instance instIncOrdIResUR : IncOrd (IResUR GF) :=
  inferInstanceAs (IncOrd ((i : GType) → GenMap ((GF i).F (IPre GF) (IPre GF))))

/-- Monotone step-indexed predicates over the global ghost-resource algebra. -/
abbrev IProp : Type u := UPred (IResUR GF)

/-- Map a proposition to its recursive pre-proposition representation. -/
def IProp.unfold : IProp GF -n> IPre GF :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

/-- Map a recursive pre-proposition back to its proposition representation. -/
def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

theorem IProp.fold_unfold (P : IProp GF) : IProp.fold GF (IProp.unfold GF P) = P :=
  OFunctor.Fix.iso (F := UPredOF (IResF GF)) |>.inv_hom

theorem IProp.unfold_fold (P : IPre GF) : IProp.unfold GF (IProp.fold GF P) = P :=
  OFunctor.Fix.iso (F := UPredOF (IResF GF)) |>.hom_inv

end IProp

end Iris
