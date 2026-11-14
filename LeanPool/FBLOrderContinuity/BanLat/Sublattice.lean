/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Substructures.Sublattice
public import LeanPool.OrderClosures.BanLat.Operators.Hom

/-!
# Subtype algebra and homomorphisms for vector sublattices

Extends the shared BanLat core with its carrier-based algebra and the canonical inclusions.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

namespace VectorSublattice

/-- Vector sublattices are determined by their members. -/
@[ext] theorem ext {Y Z : VectorSublattice X} (h : ∀ x, x ∈ Y ↔ x ∈ Z) : Y = Z :=
  SetLike.ext h

/-- Vector sublattices are additive subgroups of their ambient vector lattice. -/
instance addSubgroupClass :
    AddSubgroupClass (VectorSublattice X) X where
  zero_mem := fun Y => Y.toSubmodule.zero_mem
  add_mem := fun {Y _ _} hx hy => Y.toSubmodule.add_mem hx hy
  neg_mem := fun {Y _} hx => Y.toSubmodule.neg_mem hx

/-- Vector sublattices are closed under real scalar multiplication. -/
instance smulMemClass :
    SMulMemClass (VectorSublattice X) ℝ X where
  smul_mem := fun {Y} r _ hx => Y.toSubmodule.smul_mem r hx


variable (Y : VectorSublattice X)

/-- A vector sublattice contains zero. -/
protected theorem zero_mem : (0 : X) ∈ Y := by
  exact Y.toSubmodule.zero_mem

/-- A vector sublattice is closed under addition. -/
protected theorem add_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x + y ∈ Y := by
  exact Y.toSubmodule.add_mem hx hy

/-- A vector sublattice is closed under negation. -/
protected theorem neg_mem {x : X} (hx : x ∈ Y) :
    -x ∈ Y := by
  exact Y.toSubmodule.neg_mem hx

/-- A vector sublattice is closed under subtraction. -/
protected theorem sub_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x - y ∈ Y := by
  exact Y.toSubmodule.sub_mem hx hy

/-- A vector sublattice is closed under real scalar multiplication. -/
protected theorem smul_mem (c : ℝ) {x : X} (hx : x ∈ Y) :
    c • x ∈ Y := by
  exact Y.toSubmodule.smul_mem c hx


/-- A vector sublattice inherits supremum from its ambient vector lattice. -/
instance instSupCoe : Max Y where
  max x y := ⟨x ⊔ y, Y.sup_mem x.2 y.2⟩

/-- A vector sublattice inherits infimum from its ambient vector lattice. -/
instance instInfCoe : Min Y where
  min x y := ⟨x ⊓ y, Y.inf_mem x.2 y.2⟩

/-- Suprema in a vector sublattice are computed in the ambient vector lattice. -/
@[simp, norm_cast]
theorem coe_sup (x y : Y) :
    ((x ⊔ y : Y) : X) = (x : X) ⊔ (y : X) := by
  rfl

/-- Infima in a vector sublattice are computed in the ambient vector lattice. -/
@[simp, norm_cast]
theorem coe_inf (x y : Y) :
    ((x ⊓ y : Y) : X) = (x : X) ⊓ (y : X) := by
  rfl

/-- The supremum of two explicitly constructed sublattice elements is computed
in the ambient vector lattice. -/
@[simp]
theorem mk_sup_mk (x y : X) (hx : x ∈ Y) (hy : y ∈ Y) :
    (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Y) =
      ⟨x ⊔ y, Y.sup_mem hx hy⟩ := by
  rfl

/-- The infimum of two explicitly constructed sublattice elements is computed
in the ambient vector lattice. -/
@[simp]
theorem mk_inf_mk (x y : X) (hx : x ∈ Y) (hy : y ∈ Y) :
    (⟨x, hx⟩ ⊓ ⟨y, hy⟩ : Y) =
      ⟨x ⊓ y, Y.inf_mem hx hy⟩ := by
  rfl

/-- The lattice structure on the subtype of a vector sublattice. -/
noncomputable instance instLatticeCoe : Lattice Y := instLatticeSubtype Y

/-- The inherited additive order agrees with the shared submodule model. -/
instance instIsOrderedAddMonoidCoe :
    @IsOrderedAddMonoid Y inferInstance
      (instLatticeCoe Y).toPartialOrder.toPreorder := instIsOrderedAddMonoidSubtype Y

/-- Nonnegative scalar multiplication is monotone in a vector sublattice. -/
instance instPosSMulMonoCoe : PosSMulMono ℝ Y := instPosSMulMonoSubtype Y

/-- The carrier and submodule models use the same vector-lattice structure. -/
instance instVectorLatticeCoe :
    @VectorLattice Y inferInstance (instLatticeCoe Y)
      (instIsOrderedAddMonoidCoe Y) := instVectorLatticeSubtype Y


end VectorSublattice

namespace VectorSublattice

/-- The canonical inclusion of a vector sublattice into its ambient vector lattice. -/
def subtype (Y : VectorSublattice X) : VecLatHom Y X where
  toFun y := y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- The canonical inclusion maps a vector-sublattice element to its underlying value. -/
@[simp]
theorem subtype_apply (Y : VectorSublattice X) (y : Y) :
    Y.subtype y = (y : X) := rfl

/-- The canonical inclusion of a vector sublattice is injective. -/
theorem subtype_injective (Y : VectorSublattice X) :
    Function.Injective Y.subtype :=
  Subtype.coe_injective

/-- The inclusion of a vector sublattice into a larger vector sublattice. -/
def inclusion {Y Z : VectorSublattice X} (h : Y ≤ Z) :
    VecLatHom Y Z where
  toFun := Set.inclusion h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- Sublattice inclusion agrees with the corresponding set inclusion. -/
theorem inclusion_apply {Y Z : VectorSublattice X} (h : Y ≤ Z) (y : Y) :
    inclusion h y = Set.inclusion h y := rfl

/-- Inclusion into a larger vector sublattice is injective. -/
theorem inclusion_injective {Y Z : VectorSublattice X} (h : Y ≤ Z) :
    Function.Injective (inclusion h) :=
  Set.inclusion_injective h

end VectorSublattice

namespace LLexpr

/-- Evaluation in a vector sublattice agrees with evaluation in the ambient lattice. -/
theorem coe_eval_vectorSublattice {n : ℕ} (Y : VectorSublattice X)
    (y : Fin n → Y) (e : LLexpr n) :
    ((eval y e : Y) : X) = eval (fun i ↦ (y i : X)) e := by
  simpa using map_eval Y.subtype y e


end LLexpr

section Normed

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

namespace VectorSublattice

variable (Y : VectorSublattice X)

/-- A vector sublattice of a normed vector lattice is itself a normed vector
lattice under the induced norm and lattice operations. -/
instance instNormedVectorLatticeCoe :
    @NormedVectorLattice Y inferInstance (instLatticeCoe Y)
      (instIsOrderedAddMonoidCoe Y) := instNormedVectorLatticeSubtype Y

/-- The underlying set of the topological closure of a vector sublattice is
the closure of its underlying set. -/
@[simp]
theorem topologicalClosure_coe (Y : VectorSublattice X) :
    (Y.topologicalClosure : Set X) = closure (Y : Set X) :=
  Submodule.topologicalClosure_coe Y.toSubmodule

/-- A vector sublattice is contained in its topological closure. -/
theorem le_topologicalClosure (Y : VectorSublattice X) :
    Y ≤ Y.topologicalClosure :=
  Y.toSubmodule.le_topologicalClosure

/-- The topological closure of a vector sublattice is closed. -/
theorem isClosed_topologicalClosure (Y : VectorSublattice X) :
    IsClosed (Y.topologicalClosure : Set X) :=
  Y.toSubmodule.isClosed_topologicalClosure

/-- The topological closure of a vector sublattice is contained in every
closed vector sublattice containing it. -/
theorem topologicalClosure_minimal {Y Z : VectorSublattice X}
    (hYZ : Y ≤ Z) (hZ : IsClosed (Z : Set X)) :
    Y.topologicalClosure ≤ Z := by
  change closure (Y : Set X) ⊆ (Z : Set X)
  exact closure_minimal hYZ hZ



end VectorSublattice

end Normed

section Banach

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

namespace VectorSublattice

/-- A closed vector sublattice of a Banach lattice is a Banach lattice. -/
@[reducible]
noncomputable def banachLatticeCoe (Y : VectorSublattice X)
    (hclosed : IsClosed (Y : Set X)) :
    @BanachLattice Y inferInstance (instLatticeCoe Y)
      (instIsOrderedAddMonoidCoe Y) where
  toCompleteSpace := hclosed.completeSpace_coe

end VectorSublattice

end Banach
