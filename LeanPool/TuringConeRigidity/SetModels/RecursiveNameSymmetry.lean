/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RecursiveNameSymmetry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameExtension
public import LeanPool.TuringConeRigidity.Representation.AutomorphismName

/-!
# Recursive Name Symmetry
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u} [Preorder P]

theorem val_mapFilter (e : P ≃o P) (G : GenericFilter P) (τ : Name P) :
    Name.val (AutomorphismName.mapFilter e G).carrier (Name.rename e τ) =
      Name.val G.carrier τ :=
  Name.val_rename e G.carrier (AutomorphismName.mapFilter e G).carrier
    (fun p => by simp [AutomorphismName.mapFilter]) τ

theorem extension_mapFilter (M : Set (Name P)) (e : P ≃o P)
    (hf : ∀ τ ∈ M, Name.rename e τ ∈ M)
    (hb : ∀ τ ∈ M, Name.rename e.symm τ ∈ M) (G : GenericFilter P) :
    extension M (AutomorphismName.mapFilter e G).carrier = extension M G.carrier := by
  ext x
  constructor
  · rintro ⟨τ,hτ,rfl⟩
    refine ⟨Name.rename e.symm τ,hb τ hτ,?_⟩
    exact Name.val_rename e.symm (AutomorphismName.mapFilter e G).carrier G.carrier
      (fun _ => Iff.rfl) τ
  · rintro ⟨τ,hτ,rfl⟩
    exact ⟨Name.rename e τ,hf τ hτ,val_mapFilter e G τ⟩

def reals (U : Set ZFSet.{u}) : Set ZFSet.{u} := {x | x ∈ U ∧ x ⊆ ZFSet.omega}

theorem reals_mapFilter (M : Set (Name P)) (e : P ≃o P)
    (hf : ∀ τ ∈ M, Name.rename e τ ∈ M)
    (hb : ∀ τ ∈ M, Name.rename e.symm τ ∈ M) (G : GenericFilter P) :
    reals (extension M (AutomorphismName.mapFilter e G).carrier) =
      reals (extension M G.carrier) := by rw [extension_mapFilter M e hf hb G]

inductive Formula where
  | equal (i j : ℕ)
  | member (i j : ℕ)
  | conj (φ ψ : Formula)
  | neg (φ : Formula)
  | existsSet (φ : Formula)

def Formula.Realize (U : Set ZFSet.{u}) (env : ℕ → ZFSet.{u}) : Formula → Prop
  | .equal i j => env i = env j
  | .member i j => env i ∈ env j
  | .conj φ ψ => Realize U env φ ∧ Realize U env ψ
  | .neg φ => ¬ Realize U env φ
  | .existsSet φ => ∃ x ∈ U, Realize U (fun n => if n = 0 then x else env (n-1)) φ

theorem realize_mapFilter (M : Set (Name P)) (e : P ≃o P)
    (hf : ∀ τ ∈ M, Name.rename e τ ∈ M)
    (hb : ∀ τ ∈ M, Name.rename e.symm τ ∈ M) (G : GenericFilter P)
    (env : ℕ → ZFSet.{u}) (φ : Formula) :
    φ.Realize (extension M (AutomorphismName.mapFilter e G).carrier) env ↔
      φ.Realize (extension M G.carrier) env := by rw [extension_mapFilter M e hf hb G]

theorem definable_subset_mapFilter (M : Set (Name P)) (e : P ≃o P)
    (hf : ∀ τ ∈ M, Name.rename e τ ∈ M)
    (hb : ∀ τ ∈ M, Name.rename e.symm τ ∈ M) (G : GenericFilter P)
    (env : ℕ → ZFSet.{u}) (φ : Formula) :
    {x | x ∈ extension M (AutomorphismName.mapFilter e G).carrier ∧
      φ.Realize (extension M (AutomorphismName.mapFilter e G).carrier)
        (fun n => if n = 0 then x else env (n-1))} =
    {x | x ∈ extension M G.carrier ∧
      φ.Realize (extension M G.carrier) (fun n => if n = 0 then x else env (n-1))} := by
  rw [extension_mapFilter M e hf hb G]

noncomputable def extensionSet (M : ℕ → Name P) (G : Set P) : ZFSet.{u} :=
  ZFSet.range (fun n => Name.val G (M n))

omit [Preorder P] in
theorem extensionSet_coe (M : ℕ → Name P) (G : Set P) :
    (extensionSet M G : Set ZFSet.{u}) = extension (Set.range M) G := by
  ext x
  change x ∈ ZFSet.range (fun n => Name.val G (M n)) ↔ _
  rw [ZFSet.mem_range]
  simp only [extension,Set.mem_image,Set.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨M n,⟨n,rfl⟩,hn⟩,
    fun ⟨τ,⟨n,hn⟩,hx⟩ => ⟨n,hn ▸ hx⟩⟩

noncomputable def definedSet (U : ZFSet.{u}) (env : ℕ → ZFSet.{u}) (φ : Formula) :
    ZFSet.{u} := ZFSet.sep
      (fun x => φ.Realize (U : Set ZFSet) (fun n => if n = 0 then x else env (n-1))) U

theorem mem_definedSet (U : ZFSet.{u}) (env : ℕ → ZFSet.{u}) (φ : Formula)
    (x : ZFSet.{u}) : x ∈ definedSet U env φ ↔ x ∈ U ∧
      φ.Realize (U : Set ZFSet) (fun n => if n = 0 then x else env (n-1)) :=
  ZFSet.mem_sep

theorem definedSet_mapFilter (M : ℕ → Name P) (e : P ≃o P)
    (hf : ∀ τ ∈ Set.range M, Name.rename e τ ∈ Set.range M)
    (hb : ∀ τ ∈ Set.range M, Name.rename e.symm τ ∈ Set.range M)
    (G : GenericFilter P) (env : ℕ → ZFSet.{u}) (φ : Formula) :
    definedSet (extensionSet M (AutomorphismName.mapFilter e G).carrier) env φ =
      definedSet (extensionSet M G.carrier) env φ := by
  have hU : extensionSet M (AutomorphismName.mapFilter e G).carrier =
      extensionSet M G.carrier := by
    apply SetLike.coe_injective
    rw [extensionSet_coe,extensionSet_coe,extension_mapFilter _ e hf hb G]
  rw [hU]

end TuringRigidity.RecursiveNames

end OAI
