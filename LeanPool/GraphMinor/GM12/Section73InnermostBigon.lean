/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73BigonChord
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Choosing an innermost radial bigon

For XII (7.3), page 261, choose a bigon inside a given parallel-spoke
disc with the fewest contained edges. A third parallel spoke cuts off
a new bigon with strictly fewer edges, which contradicts minimality.
Thus the chosen disc contains no other parallel spoke.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Inside any parallel-spoke bigon there is a bigon containing no
third parallel spoke. This is the finite minimality step in the
cleanup of XII (7.3), page 261. -/
theorem exists_innermost_parallel_bigon
    {S : Type*} [TopologicalSpace S] [T2Space S] {H : Drawing S}
    {g h Q : Set S} {v u : S} (hg : g ∈ H.E) (hh : h ∈ H.E)
    (hgh : g ≠ h) (hvu : v ≠ u)
    (hcg : closure g ∩ H.V = {v, u}) (hch : closure h ∩ H.V = {v, u})
    (hQ : IsClosedDisc Q) (hbd : discBd Q = closure g ∪ closure h) :
    ∃ (P a b : Set S), IsClosedDisc P ∧ P ⊆ Q ∧ a ∈ H.E ∧ b ∈ H.E ∧
      a ≠ b ∧ closure a ∩ H.V = {v, u} ∧ closure b ∩ H.V = {v, u} ∧
      discBd P = closure a ∪ closure b ∧
      (∀ k ∈ H.E, closure k ∩ H.V = {v, u} → k ⊆ P → k = a ∨ k = b) := by
  classical
  let count : Set S → ℕ := fun P => {e ∈ H.E | e ⊆ P}.ncard
  let good : ℕ → Prop := fun n => ∃ (P a b : Set S), IsClosedDisc P ∧ P ⊆ Q ∧
    a ∈ H.E ∧ b ∈ H.E ∧ a ≠ b ∧ closure a ∩ H.V = {v, u} ∧
    closure b ∩ H.V = {v, u} ∧ discBd P = closure a ∪ closure b ∧ count P = n
  have hex : ∃ n, good n :=
    ⟨count Q, Q, g, h, hQ, Subset.rfl, hg, hh, hgh, hcg, hch, hbd, rfl⟩
  obtain ⟨P, a, b, hP, hPQ, ha, hb, hab, hca, hcb, hbdP, hcount⟩ := Nat.find_spec hex
  refine ⟨P, a, b, hP, hPQ, ha, hb, hab, hca, hcb, hbdP, ?_⟩
  intro k hk hck hkP
  by_contra hnot
  have hka : k ≠ a := fun h => hnot (Or.inl h)
  have hkb : k ≠ b := fun h => hnot (Or.inr h)
  have hkcl : closure k ⊆ P := closure_minimal hkP hP.isClosed
  obtain ⟨P', hP', hP'P, hbdP', hmiss⟩ := exists_bigon_from_third_spoke
    ha hb hk hab hka hkb hvu hca hcb hck hP hbdP hkcl
  have hgood : good (count P') := by
    rcases hbdP' with hbdP' | hbdP'
    · exact ⟨P', a, k, hP', hP'P.trans hPQ, ha, hk, hka.symm, hca, hck, hbdP', rfl⟩
    · exact ⟨P', b, k, hP', hP'P.trans hPQ, hb, hk, hkb.symm, hcb, hck, hbdP', rfl⟩
  have hmin : count P ≤ count P' := by
    rw [hcount]
    exact Nat.find_min' hex hgood
  have hsub : {e ∈ H.E | e ⊆ P'} ⊆ {e ∈ H.E | e ⊆ P} :=
    fun _ he => ⟨he.1, he.2.trans hP'P⟩
  have habP : a ⊆ P ∧ b ⊆ P := by
    constructor
    · intro x hx
      exact Surface.discBd_subset P (hbdP ▸ Or.inl (subset_closure hx))
    · intro x hx
      exact Surface.discBd_subset P (hbdP ▸ Or.inr (subset_closure hx))
  have hnotback : ¬ {e ∈ H.E | e ⊆ P} ⊆ {e ∈ H.E | e ⊆ P'} := by
    intro hback
    rcases hmiss with han | hbn
    · exact han (hback ⟨ha, habP.1⟩).2
    · exact hbn (hback ⟨hb, habP.2⟩).2
  have hlt : count P' < count P := ncard_lt_ncard ⟨hsub, hnotback⟩
    (H.finite_edges.subset fun _ he => he.1)
  exact (Nat.not_le_of_gt hlt) hmin

end GraphMinor.GM12
