/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericTopology.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ShuffleRequirements

/-!
# Generic Topology
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericTopology
open FiniteShuffle ShuffleRequirements GenericCoding Set

theorem cylinder_basis (U : Set Oracle) (hu : IsOpen U) (G : Oracle) (hg : G ∈ U) :
    ∃ n, ∀ H, Agree n G H → H ∈ U := by
  classical
  obtain ⟨I,u,huI,hsub⟩ := isOpen_pi_iff.mp hu G hg
  refine ⟨I.sup id + 1,?_⟩
  intro H hH
  apply hsub
  intro i hi
  have hl : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [←hH i (by omega)]
  exact (huI i hi).2

theorem openSet_dense (D : List Bool → Prop) (hd : DenseOpen D) : Dense (OpenSet D) := by
  apply dense_iff_inter_open.mpr
  rintro U hu ⟨G,hG⟩
  obtain ⟨n,hn⟩ := cylinder_basis U hu G hG
  obtain ⟨s,hs,hD⟩ := hd.1 (initial G n)
  exact ⟨fun i => s.getD i false,hn _ (agree_of_prefix hs),s,hD,realizes_default s⟩

theorem requirements_topology (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n)) (n : ℕ) :
    Dense (OpenSet (Requirements D n)) ∧ IsOpen (OpenSet (Requirements D n)) ∧
      MeasurableSet (OpenSet (Requirements D n)) :=
  ⟨openSet_dense _ (requirements_denseOpen D hd n),openSet_isOpen _,openSet_measurable _⟩

def Combined {X : Type*} (D : ℕ → List Bool → Prop) (R : X → ℕ → ℕ → Prop)
    (x : X) (n t : ℕ) : Prop :=
  if n % 2 = 0 then Requirements D (n/2) (BorelGeneric.word t) else R x (n/2) t

theorem borel_selection_with_requirements {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n))
    (R : X → ℕ → ℕ → Prop)
    (hRd : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ R x n t)
    (hRm : ∀ n t, MeasurableSet {x | R x n t}) :
    ∃ G : X → Oracle, Measurable G ∧ ∀ x,
      (GenericFor D (G x) ∧ InfiniteOdd (G x) ∧ ∀ A, GenericFor D (code A (G x))) ∧
      ∀ n, ∃ t, R x n t ∧ BorelGeneric.Meets (G x) t := by
  have hc : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ Combined D R x n t := by
    intro x n s
    unfold Combined
    split
    · exact coded_dense _ (requirements_denseOpen D hd _) s
    · exact hRd x _ s
  have hm : ∀ n t, MeasurableSet {x | Combined D R x n t} := by
    intro n t
    unfold Combined
    split
    · exact requirements_borel D _ _
    · exact hRm _ _
  obtain ⟨G,hG,hreq⟩ := BorelGeneric.borel_generic_selection (Combined D R) hc hm
  refine ⟨G,hG,?_⟩
  intro x
  constructor
  · apply requirements_spec
    intro n
    obtain ⟨t,ht,hGt⟩ := hreq x (2*n)
    exact ⟨BorelGeneric.word t,by simpa [Combined] using ht,(realizes_iff_meets _ _).mpr hGt⟩
  · intro n
    obtain ⟨t,ht,hGt⟩ := hreq x (2*n+1)
    exact ⟨t,by simpa [Combined,Nat.add_div] using ht,hGt⟩

end TuringRigidity.GenericTopology

end OAI
