/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM16.Section9BattlefieldNest
import LeanPool.GraphMinor.GM16.NestedDiscContainment
import LeanPool.GraphMinor.GM16.AnnulusPresentation
import LeanPool.GraphMinor.GM16.AnnulusBreadth
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# The rural neighborhood supplied by a battlefield

For XVI (8.1), Claim (11), restrict the drawing to the annulus
between the inner battlefield circuit and the outer zone boundary.
The regional-distance bound gives nested circuits by XIV (5.5).
Uniqueness of the inside of a circle puts the inner disc inside all
of their discs. Transporting this annulus to the plane therefore gives
a rural neighborhood with breadth at least half the battlefield size.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The rural neighborhood and its breadth in XVI (8.1), Claim (11),
page 74. Its outer order consists of all vertices on the zone boundary. -/
theorem section9_battlefield_neighborhood (hS : IsClosedSurface S)
    {H C : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β : ℕ} {z Λ X : Set S}
    (hB : IsBattlefield H T d θ β z Λ C X) :
    ∃ (D₀ : Set S) (N : Neighborhood S (Set S)),
      IsClosedDisc D₀ ∧ D₀ ⊆ closure Λ ∧ discBd D₀ = C.U ∧
      N.G = (H.interSet (closure Λ \ discInt D₀)).toGraph ∧
      N.Ω.bar = H.V ∩ subBd Λ ∧
      N.Ω₀.bar = (H.interSet (closure Λ \ discInt D₀)).V ∩ C.U ∧
      N.IsRural ∧ N.HasBreadthGe (β / 2) := by
  classical
  let : CompactSpace S := hS.1
  have hD := hB.isZone.isClosedDisc_closure
  have hbd : subBd (closure Λ) = subBd Λ :=
    subBd_closure_eq_subBd_of_isOpenDisc hS hB.isZone.isOpenDisc
      hB.isZone.isOArc_bd hD
  have hCU : C.U ⊆ closure Λ := hB.circuit_and_paths.2.2.1.trans subset_closure
  have hCo := IsCircuit.isOArc_U hB.circuit_and_paths.1
  obtain ⟨D₀, hD₀, _⟩ := disc_oArc (closure Λ) C.U hD hCU hCo
  have hInt (E : Set S) (hE : IsClosedDisc E) : discInt E = interior E := by
    change E \ discBd E = interior E
    rw [← IsClosedDisc.subBd_eq_discBd hS hE, subBd_eq_frontier, self_sdiff_frontier]
  have hInt₀ := hInt D₀ hD₀.2.1
  let A := closure Λ \ discInt D₀
  have hAc : IsClosed A := by
    change IsClosed (closure Λ \ discInt D₀)
    rw [hInt₀]
    exact isClosed_closure.sdiff isOpen_interior
  let Q := H.interSet A
  have hQV : ∀ x, x ∈ Q.V ↔ x ∈ H.V ∧ x ∈ A := fun _ => mem_interSet_V_iff hAc
  have hOuterA : subBd Λ ⊆ A := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [hInt₀]
    intro hxInt
    have hxi := interior_mono hD₀.1 hxInt
    have hxb : x ∈ subBd (closure Λ) := hbd.symm ▸ hx
    rw [subBd_eq_frontier] at hxb
    exact hxb.2 hxi
  have hInnerA : C.U ⊆ A := by
    intro x hx
    have hxb : x ∈ discBd D₀ := hD₀.2.2.1.symm ▸ hx
    exact ⟨hD₀.1 (Surface.discBd_subset D₀ hxb), fun h => h.2 hxb⟩
  have hOuterEq : Q.V ∩ discBd (closure Λ) = H.V ∩ subBd Λ := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hD, hbd]
    ext x
    exact ⟨fun h => ⟨(hQV x).mp h.1 |>.1, h.2⟩,
      fun h => ⟨(hQV x).mpr ⟨h.1, hOuterA h.2⟩, h.2⟩⟩
  have hXfin : X.Finite := H.finite_V.subset (fun _ hx => (hB.isFree_X.1 hx).1)
  have hXne : X.Nonempty := by
    apply (ncard_pos hXfin).mp
    rw [hB.isFree_X.2.1]
    exact lt_of_lt_of_le (by decide : 0 < 4) hB.params_valid.1
  have hne : (Q.V ∩ discBd (closure Λ)).Nonempty := by
    rw [hOuterEq]
    exact hXne.mono hB.isFree_X.1
  have hne₀ : (Q.V ∩ discBd D₀).Nonempty := by
    obtain ⟨c, W, _, _, hCV, _⟩ := hB.circuit_and_paths.1
    have hc : c ∈ C.V := hCV.symm ▸ W.start_mem_support
    have hcU := C.V_subset_U hc
    exact ⟨c, (hQV c).mpr ⟨hB.circuit_and_paths.2.1.1 hc, hInnerA hcU⟩,
      hD₀.2.2.1.symm ▸ hcU⟩
  obtain ⟨N, P, f, hG, hΩ, hΩ₀, _, _, hΔ, hΔ₀, hdisc, hpoints⟩ :=
    exists_annular_presentation Q hD hD₀.2.1 hD₀.1 (interSet_U_subset hAc) hne hne₀
  obtain ⟨K, B, hK, hNest, hDis⟩ := section9_battlefield_nest hS hB
  have hE (i : Fin (β / 2)) : D₀ ⊆ closure (B i) :=
    closedDisc_subset_of_boundary_subset hD (hK i).2.2.2.2.2.1 hD₀.2.1
      ((hK i).2.2.2.2.1.trans subset_closure) hD₀.1
      (hD₀.2.2.1 ▸ ((hK i).2.2.2.2.2.2.2.2.2.trans subset_closure))
  have hKQ (i : Fin (β / 2)) : (K i).IsSubdrawing Q ∧ (K i).IsCircuit := by
    refine ⟨subdrawing_interSet_of_U_subset (hK i).1 ?_, (hK i).2.1⟩
    intro x hx
    refine ⟨subset_closure ((hK i).2.2.1 hx), ?_⟩
    rw [hInt₀]
    intro hxi
    have hxb : x ∈ subBd (closure (B i)) := (hK i).2.2.2.2.2.2.2.1.symm ▸ hx
    rw [subBd_eq_frontier] at hxb
    exact hxb.2 (interior_mono (hE i) hxi)
  have hBreadth : N.HasBreadthGe (β / 2) := by
    apply hasBreadthGe_of_drawing_nest P Q hG hΔ hΔ₀ hdisc hpoints K
      (fun i => closure (B i)) hKQ hDis
    · intro i
      refine ⟨(hK i).2.2.2.2.2.1, ?_, hE i,
        (hK i).2.2.2.2.1.trans subset_closure⟩
      rw [← IsClosedDisc.subBd_eq_discBd hS (hK i).2.2.2.2.2.1]
      exact (hK i).2.2.2.2.2.2.2.1
    · intro i j hij
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact Subset.rfl
      · exact (hNest i j hlt).trans subset_closure
  refine ⟨D₀, N, hD₀.2.1, hD₀.1, hD₀.2.2.1, hG,
    hΩ.trans hOuterEq, ?_, ?_, hBreadth⟩
  · exact hΩ₀.trans (by rw [hD₀.2.2.1])
  · exact ⟨P.Γ, P.Δ, P.Δ₀, P.isClosedDisc_Δ, P.Δ₀_subset_Δ,
      P.U_subset, P.mem_bd_Δ_iff, P.mem_bd_Δ₀_iff, P.agrees_Δ, P.agrees_Δ₀⟩

end GraphMinor.GM16
