/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteJoinSections.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPrefixForcing

/-!
# Finite Join Sections
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FiniteJoinSections
open FiniteShuffle ShuffleRequirements ArithmeticPrefixForcing

def Cover (s t u : List Bool) : Prop :=
  u.length ≤ 2 * s.length ∧ u.length ≤ 2 * t.length ∧
    Realizes u (join (fun i => s.getD i false) (fun i => t.getD i false))

theorem cover_realizes {s t u : List Bool} {A B : Oracle}
    (h : Cover s t u) (hs : Realizes s A) (ht : Realizes t B) :
    Realizes u (join A B) := by
  have hlenS := h.1
  have hlenT := h.2.1
  intro i hi
  rw [h.2.2 i hi]
  simp only [join]
  split
  · exact ht (i / 2) (by omega)
  · exact hs (i / 2) (by omega)

theorem cover_mono {s t u s' t' : List Bool} (h : Cover s t u)
    (hs : s <+: s') (ht : t <+: t') : Cover s' t' u := by
  have hlenS := h.1
  have hlenT := h.2.1
  refine ⟨by have := hs.length_le; omega, by have := ht.length_le; omega, ?_⟩
  exact cover_realizes h (realizes_mono hs (realizes_default s'))
    (realizes_mono ht (realizes_default t'))

def Product (D : List Bool → Prop) (s t : List Bool) : Prop :=
  ∃ u, D u ∧ Cover s t u

theorem product_mono {D : List Bool → Prop} {s t s' t' : List Bool}
    (h : Product D s t) (hs : s <+: s') (ht : t <+: t') : Product D s' t' := by
  obtain ⟨u,hu,hc⟩ := h
  exact ⟨u,hu,cover_mono hc hs ht⟩

theorem product_realizes {D : List Bool → Prop} {s t : List Bool} {A B : Oracle}
    (h : Product D s t) (hs : Realizes s A) (ht : Realizes t B) :
    join A B ∈ OpenSet D := by
  obtain ⟨u,hu,hc⟩ := h
  exact ⟨u,hu,cover_realizes hc hs ht⟩

theorem product_dense {D : List Bool → Prop} (hD : DenseOpen D)
    (s t : List Bool) :
    ∃ s' t', s <+: s' ∧ t <+: t' ∧ Product D s' t' := by
  let A : Oracle := fun i => s.getD i false
  let B : Oracle := fun i => t.getD i false
  let n := max s.length t.length
  obtain ⟨u,hu,hDu⟩ := hD.1 (initial (join A B) (2 * n))
  let C : Oracle := fun i => u.getD i false
  let A' : Oracle := fun i => C (2 * i)
  let B' : Oracle := fun i => C (2 * i + 1)
  have hc : Agree (2 * n) (join A B) C := agree_of_prefix hu
  have hlen : 2 * n ≤ u.length := by simpa using hu.length_le
  have hjoin : join A' B' = C := by
    funext i
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · have he : i = 2 * (i / 2) := by omega
      rw [he, join_even]
    · have he : i = 2 * (i / 2) + 1 := by omega
      rw [he, join_odd]
  refine ⟨initial A' u.length, initial B' u.length, ?_, ?_, u, hDu, ?_⟩
  · rw [←prefix_default s]
    apply initial_prefix (by dsimp [n] at hlen; omega)
    intro i hi
    exact (join_even A B i).symm.trans (hc (2 * i) (by dsimp [n]; omega))
  · rw [←prefix_default t]
    apply initial_prefix (by dsimp [n] at hlen; omega)
    intro i hi
    exact (join_odd A B i).symm.trans (hc (2 * i + 1) (by dsimp [n]; omega))
  · refine ⟨by simp; omega, by simp; omega, ?_⟩
    have hr : Realizes u (join A' B') := hjoin ▸ realizes_default u
    intro i hi
    rw [hr i hi]
    simp only [join]
    split <;> exact (prefix_getD _ _ _ (by omega)).symm

def Section (D : List Bool → Prop) (t s : List Bool) : Prop :=
  ∃ t', t <+: t' ∧ Product D s t'

theorem section_dense {D : List Bool → Prop} (hD : DenseOpen D) (t : List Bool) :
    DenseOpen (Section D t) := by
  constructor
  · intro s
    obtain ⟨s',t',hs,ht,h⟩ := product_dense hD s t
    exact ⟨s',hs,t',ht,h⟩
  · rintro s s' hs ⟨t',ht,h⟩
    exact ⟨t',ht,product_mono h hs List.prefix_rfl⟩

def Fiber (D : List Bool → Prop) (A : Oracle) (t : List Bool) : Prop :=
  ∃ s, Realizes s A ∧ Product D s t

theorem fiber_dense {D : List Bool → Prop} {A : Oracle}
    (hA : ∀ t, A ∈ OpenSet (Section D t)) : DenseOpen (Fiber D A) := by
  constructor
  · intro t
    obtain ⟨s,⟨t',ht,h⟩,hs⟩ := hA t
    exact ⟨t',ht,s,hs,h⟩
  · rintro t t' ht ⟨s,hs,h⟩
    exact ⟨s,hs,product_mono h List.prefix_rfl ht⟩

end TuringRigidity.FiniteJoinSections

end OAI
