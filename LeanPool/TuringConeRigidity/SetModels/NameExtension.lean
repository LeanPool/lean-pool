/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Data.Set.Countable

public import LeanPool.TuringConeRigidity.SetModels.RecursiveNames
public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing

/-!
# Name Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u}

/-- The first name occurs as an immediate child of the second name. -/
def Name.Child : Name P → Name P → Prop
  | σ, .mk _ child _ => ∃ i, child i = σ

/-- The set of values of all names in `M` under the condition family `G`. -/
noncomputable def extension (M : Set (Name P)) (G : Set P) : Set ZFSet.{u} := Name.val G '' M

/-- The name family contains every immediate child of each of its members. -/
def ChildClosed (M : Set (Name P)) : Prop :=
  ∀ τ ∈ M, ∀ σ, Name.Child σ τ → σ ∈ M

theorem extension_transitive (M : Set (Name P)) (hM : ChildClosed M) (G : Set P) :
    ∀ x ∈ extension M G, ∀ y ∈ x, y ∈ extension M G := by
  rintro x ⟨τ,hτ,rfl⟩ y hy
  cases τ with
  | mk ι child tag =>
    obtain ⟨i,_,hi⟩ := (Name.mem_val G ι child tag y).mp hy
    exact ⟨child i,hM _ hτ _ ⟨i,rfl⟩,hi⟩

theorem extension_countable (M : Set (Name P)) (hM : M.Countable) (G : Set P) :
    (extension M G).Countable := hM.image (Name.val G)

theorem ground_subset_extension [Top P] (M : Set (Name P)) (V : Set ZFSet.{u})
    (hM : ∀ x ∈ V, Name.check x ∈ M) (G : Set P) (hG : ⊤ ∈ G) :
    V ⊆ extension M G := fun x hx => ⟨Name.check x,hM x hx,Name.val_check G hG x⟩

namespace Name

/-- The unordered-pair name with the two supplied children tagged by top. -/
def pair [Top P] (σ τ : Name P) : Name P :=
  .mk (ULift Bool) (fun i => if i.down then σ else τ) (fun _ => ⊤)

theorem val_pair [Top P] (G : Set P) (hG : ⊤ ∈ G) (σ τ : Name P) :
    val G (pair σ τ) = ({val G σ,val G τ} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro x
  simp only [pair,mem_val,hG,true_and,ZFSet.mem_pair]
  constructor
  · rintro ⟨⟨b⟩,hb⟩
    cases b
    · exact Or.inr hb.symm
    · exact Or.inl hb.symm
  · rintro (h|h)
    · exact ⟨⟨true⟩,h.symm⟩
    · exact ⟨⟨false⟩,h.symm⟩

/-- The index type of immediate children of a name. -/
def arity : Name P → Type u
  | .mk ι _ _ => ι

/-- The immediate child at the specified name index. -/
def child : (τ : Name P) → arity τ → Name P
  | .mk _ c _, i => c i

/-- The forcing condition tagging the specified name child. -/
def tag : (τ : Name P) → arity τ → P
  | .mk _ _ t, i => t i

/-- The union name, tagged by common extensions of parent and child conditions. -/
def union [Preorder P] (τ : Name P) : Name P :=
  .mk (Σ i : arity τ, Σ j : arity (child τ i),
      {p : P // p ≤ tag τ i ∧ p ≤ tag (child τ i) j})
    (fun t => child (child τ t.1) t.2.1) (fun t => t.2.2.val)

theorem mem_val_children (G : Set P) (τ : Name P) (x : ZFSet.{u}) :
    x ∈ val G τ ↔ ∃ i, tag τ i ∈ G ∧ val G (child τ i) = x := by
  cases τ
  exact mem_val _ _ _ _ _

theorem val_union [Preorder P] (G : GenericFilter P) (τ : Name P) :
    val G.carrier (union τ) = ZFSet.sUnion (val G.carrier τ) := by
  apply ZFSet.ext
  intro x
  rw [union,mem_val,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨⟨i,j,p,hpi,hpj⟩,hp,hx⟩
    refine ⟨val G.carrier (child τ i),?_,?_⟩
    · exact (mem_val_children _ _ _).mpr ⟨i,G.upper hpi hp,rfl⟩
    · exact (mem_val_children _ _ _).mpr ⟨j,G.upper hpj hp,hx⟩
  · rintro ⟨y,hy,hx⟩
    obtain ⟨i,hi,rfl⟩ := (mem_val_children _ _ _).mp hy
    obtain ⟨j,hj,hx⟩ := (mem_val_children _ _ _).mp hx
    obtain ⟨p,hp,hpi,hpj⟩ := G.directed hi hj
    exact ⟨⟨i,j,p,hpi,hpj⟩,hp,hx⟩

end Name

theorem extension_pair_closed [Top P] (M : Set (Name P))
    (hM : ∀ σ ∈ M, ∀ τ ∈ M, Name.pair σ τ ∈ M) (G : Set P) (hG : ⊤ ∈ G) :
    ∀ x ∈ extension M G, ∀ y ∈ extension M G, ({x,y} : ZFSet.{u}) ∈ extension M G := by
  rintro x ⟨σ,hσ,rfl⟩ y ⟨τ,hτ,rfl⟩
  exact ⟨Name.pair σ τ,hM σ hσ τ hτ,Name.val_pair G hG σ τ⟩

end TuringRigidity.RecursiveNames

end OAI
