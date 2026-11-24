/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs

/-!
# Boundary vertices among the terms of a disc chain

In the VI (3.6) chain reduction used by XII (3.2), pages 247--248,
only the first and last terms can be peripheral. Thus any vertex
term on the surface boundary is one of the two chain endpoints.
This ensures that the normal carrier built from internal region
curves meets the surface boundary only at those endpoints.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06

/-- Boundary vertices occurring in a VI chain are its endpoints. -/
theorem disc_chain_boundary_vertex_eq_endpoint
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y v : S}
    {A : List (ChainTerm S)} (hA : IsXYChain G x y A)
    (hv : Sum.inl v ∈ A) (hvb : v ∈ bd S) : v = x ∨ v = y := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hv
  have hper : (A[i]).IsPeripheral G := by
    rw [he]
    exact ⟨hA.valid (.inl v) hv, hvb⟩
  rcases (hA.peripheral_iff ⟨i, hi⟩).mp hper with hfirst | hlast
  · change i = 0 at hfirst
    have hhead : A.head hA.ne_nil = Sum.inl v := by
      rw [List.head_eq_getElem_zero]
      simpa only [hfirst] using he
    have h := hA.head_matches
    rw [hhead] at h
    exact Or.inl h
  · change i + 1 = A.length at hlast
    have hlast' : A.getLast hA.ne_nil = Sum.inl v := by
      rw [List.getLast_eq_getElem]
      have hi' : i = A.length - 1 := by omega
      simpa only [hi'] using he
    have h := hA.last_matches
    rw [hlast'] at h
    exact Or.inr h

end GraphMinor.GM12
