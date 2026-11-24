/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM14.Section5
import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# The nest between the battlefield circuit and its boundary

In XVI (8.1), Claim (11), the regional distance in a battlefield
supplies the breadth needed by IX (10.5). Apply XIV (5.5) in the
closed battlefield disc to its inner circuit. The resulting circuits
are disjoint and nested, and all their closed discs lie in the open
battlefield disc.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- A circle is arc-connected: either of the two arcs between distinct
points lies in the circle. -/
theorem oArc_isArcConnected {F : Set S} (hF : IsOArc F) : IsArcConnected F := by
  intro x hx y hy hxy
  obtain ⟨A, B, hA, _, hAB, _⟩ := hF.lines hx hy hxy
  exact ⟨A, fun _ ha => hAB ▸ Or.inl ha, hA⟩

/-- The nested circuits used to obtain the breadth in XVI (8.1),
Claim (11), page 74, follow from XIV (5.5). -/
theorem section9_battlefield_nest (hS : IsClosedSurface S)
    {H C : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β : ℕ} {z Λ X : Set S}
    (hB : IsBattlefield H T d θ β z Λ C X) :
    ∃ (K : Fin (β / 2) → Drawing S) (A : Fin (β / 2) → Set S),
      (∀ i, (K i).IsSubdrawing H ∧ (K i).IsCircuit ∧
        (K i).U ⊆ Λ ∧ IsOpenDisc (A i) ∧ closure (A i) ⊆ Λ ∧
        IsClosedDisc (closure (A i)) ∧ subBd (A i) = (K i).U ∧
        subBd (closure (A i)) = (K i).U ∧
        closure (A i) \ (K i).U = A i ∧ C.U ⊆ A i) ∧
      (∀ i j, i < j → closure (A i) ⊆ A j) ∧
      Pairwise (fun i j => Disjoint (K i).U (K j).U) := by
  have hbd : subBd (closure Λ) = subBd Λ :=
    subBd_closure_eq_subBd_of_isOpenDisc hS hB.isZone.isOpenDisc
      hB.isZone.isOArc_bd hB.isZone.isClosedDisc_closure
  have hdiff : closure Λ \ subBd (closure Λ) = Λ := by
    rw [hbd, subBd_eq_frontier, closure_sdiff_frontier, hB.isZone.isOpenDisc.1.interior_eq]
  have hCU : C.U ⊆ closure Λ \ subBd (closure Λ) := hdiff.symm ▸ hB.circuit_and_paths.2.2.1
  have hCo : IsOArc C.U := IsCircuit.isOArc_U hB.circuit_and_paths.1
  have hCne : C.U.Nonempty := by
    obtain ⟨φ⟩ := hCo
    exact ⟨(φ 1).val, (φ 1).prop⟩
  have hDist : β / 2 + 1 ≤ regionalDistance H C.U (subBd (closure Λ)) := by
    rw [hbd, Nat.add_comm]
    exact hB.regionalDistance_ge
  obtain ⟨K, A, hK, hnest, hdis⟩ := theorem_5_5_proof hS H hB.isZone.isClosedDisc_closure
    hCU hCne (oArc_isArcConnected hCo) (Nat.succ_le_succ (Nat.zero_le _)) hDist
  refine ⟨K, A, ?_, hnest, hdis⟩
  intro i
  obtain ⟨hKH, hKC, hKU, hAo, hAcl, hAd, hAb, hAcb, hAdiff, hCA⟩ := hK i
  exact ⟨hKH, hKC, hdiff ▸ hKU, hAo, hdiff ▸ hAcl,
    hAd, hAb, hAcb, hAdiff, hCA⟩

end GraphMinor.GM16
