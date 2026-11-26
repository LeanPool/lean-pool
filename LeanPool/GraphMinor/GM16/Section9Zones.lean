/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.GM11.NiceStatements
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM14.Section3

/-!
# Disjoint battlefield zones

In the proof of XVI (8.1), distant centres have disjoint battlefield discs.
To apply the zone distance bound to a point in both closures, first show that
the whole atom containing the point lies in both closures. A zone boundary
lies in the drawing, so an edge or region cannot cross it.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- An atom meeting the closure of a zone lies wholly in that closure. -/
theorem zone_atom_subset_closure {H : Drawing S} {d : Set S → Set S → ℕ}
    {lam : ℕ} {z Λ a : Set S} (h : IsLambdaZoneAround H d lam z Λ)
    (ha : a ∈ H.A) (hmeet : (a ∩ closure Λ).Nonempty) : a ⊆ closure Λ := by
  have hfront : frontier (closure Λ) ⊆ subBd Λ := by
    rw [subBd_eq_frontier]
    exact frontier_closure_subset
  have hpre : ∀ {A : Set S}, IsPreconnected A → Disjoint A (frontier (closure Λ)) →
      (A ∩ closure Λ).Nonempty → A ⊆ closure Λ := by
    intro A hA hdis ⟨x, hxA, hxΛ⟩
    exact (subset_or_disjoint_of_frontier isClosed_closure hA hdis).resolve_right
      (fun hd => hd.notMem_of_mem_left hxA hxΛ)
  rcases ha with (⟨x, hx, rfl⟩ | he) | hr
  · obtain ⟨y, hy, hyΛ⟩ := hmeet
    rw [mem_singleton_iff] at hy
    exact singleton_subset_iff.mpr (hy ▸ hyΛ)
  · by_cases hbd : (a ∩ subBd Λ).Nonempty
    · exact (edge_subset_of_oArc h.isOArc_bd h.bd_subset_U he hbd).trans
        (fun _ hx => hx.1)
    · apply hpre he.2.2.1.isConnected.isPreconnected _ hmeet
      exact disjoint_left.mpr fun x hxa hxfr => hbd ⟨x, hxa, hfront hxfr⟩
  · apply hpre (region_isPreconnected hr) _ hmeet
    exact disjoint_left.mpr fun x hxr hxfr =>
      region_subset hr hxr (h.bd_subset_U (hfront hxfr))

/-- Graph Minors XVI, proof of (8.1), page 71: battlefield closures around
centres at distance greater than `2γ` are disjoint. -/
theorem section9_disjoint_zones {H : Drawing S} {d : Set S → Set S → ℕ}
    {γ θ : ℕ} {z₁ z₂ Λ₁ Λ₂ : Set S}
    (h₁ : IsLambdaZoneAround H d γ z₁ Λ₁) (h₂ : IsLambdaZoneAround H d γ z₂ Λ₂)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    (hsep : θ ≤ d z₁ z₂) (hθ : 2 * γ < θ) :
    Disjoint (closure Λ₁) (closure Λ₂) := by
  apply disjoint_left.mpr
  intro x hx₁ hx₂
  obtain ⟨a, ha, hxa⟩ := exists_atom H x
  have hd₁ := h₁.dist_le a ha (zone_atom_subset_closure h₁ ha ⟨x, hxa, hx₁⟩)
  have hd₂ := h₂.dist_le a ha (zone_atom_subset_closure h₂ ha ⟨x, hxa, hx₂⟩)
  have hb := htri z₁ h₁.z_mem a ha z₂ h₂.z_mem
  rw [hsymm a ha z₂ h₂.z_mem] at hb
  omega

omit [ConnectedSpace S] in
/-- A subdrawing contained in a set survives restriction to that set. -/
theorem subdrawing_interSet_of_U_subset {H K : Drawing S} {T : Set S}
    (hKH : K.IsSubdrawing H) (hKT : K.U ⊆ T) : K.IsSubdrawing (H.interSet T) := by
  constructor
  · intro x hx
    exact Or.inl ⟨⟨hKH.1 hx, hKT (K.V_subset_U hx)⟩, hKH.1 hx⟩
  · intro e he
    change e ∈ (H.span _ _).E
    rw [H.span_E]
    exact ⟨⟨hKH.2 he, (fun x hx => hKT (K.closure_subset_U he (subset_closure hx)))⟩, hKH.2 he⟩

/-- A circle in the old drawing survives restriction whenever its point set
does. In particular, battlefield boundaries survive clearing other zones. -/
theorem oArc_subset_interSet_U {H : Drawing S} {F T : Set S}
    (hF : IsOArc F) (hFH : F ⊆ H.U) (hFT : F ⊆ T) : F ⊆ (H.interSet T).U := by
  obtain ⟨C, _, hCH, hCF⟩ := exists_circuit_of_oArc hF hFH
  have hCT : C.U ⊆ T := hCF ▸ hFT
  exact hCF ▸ (subdrawing_interSet_of_U_subset hCH hCT).U_subset

/-- Clearing a family of disjoint zones retains every zone boundary. -/
theorem zone_boundary_subset_clearFamily {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {γ : ℕ} {Λ : S → Set S}
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → Disjoint (closure (Λ y₁)) (closure (Λ y₂)))
    {y : S} (hy : y ∈ Y) : subBd (Λ y) ⊆ (clearEnvelopeDrawing H Y Λ).U := by
  apply oArc_subset_interSet_U (hZone y hy).isOArc_bd (hZone y hy).bd_subset_U
  intro x hx
  refine ⟨mem_univ _, ?_⟩
  intro hxUnion
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hxUnion
  by_cases heq : y = z
  · subst z
    have hclosed : IsClosed (univ \ Λ y) := isClosed_univ.sdiff (hZone y hy).isOpenDisc.1
    have hxOut := hx.2
    rw [hclosed.closure_eq] at hxOut
    exact hxOut.2 hxz
  · exact (hdis y hy z hz heq).notMem_of_mem_left hx.1 (subset_closure hxz)

omit [ConnectedSpace S] in
/-- The point set left after clearing a family of zones is the old point
set outside their union. This is used in XVI (8.1), Claim (2), page 71. -/
theorem clearFamily_U {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {γ : ℕ} {Λ : S → Set S}
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y)) :
    (clearEnvelopeDrawing H Y Λ).U = H.U \ (⋃ y ∈ Y, Λ y) := by
  have hclosed : IsClosed (univ \ (⋃ y ∈ Y, Λ y)) :=
    isClosed_univ.sdiff (isOpen_iUnion fun y => isOpen_iUnion fun hy => (hZone y hy).isOpenDisc.1)
  apply subset_antisymm
  · intro x hx
    exact ⟨interSet_isSub.U_subset hx, (interSet_U_subset hclosed hx).2⟩
  · rintro x ⟨hxH, hxOut⟩
    by_cases hxV : x ∈ H.V
    · exact (clearEnvelopeDrawing H Y Λ).V_subset_U
        ((mem_interSet_V_iff hclosed).mpr ⟨hxV, mem_univ _, hxOut⟩)
    · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxH hxV
      have heOut : e ⊆ univ \ (⋃ y ∈ Y, Λ y) := by
        intro z hz
        refine ⟨mem_univ _, ?_⟩
        intro hzUnion
        obtain ⟨y, hyY, hzy⟩ := mem_iUnion₂.mp hzUnion
        rcases edge_subset_or_subset_compl_of_zone (hZone y hyY) he with heIn | heNot
        · exact hxOut (mem_iUnion₂.mpr ⟨y, hyY, heIn hxe⟩)
        · exact (heNot hz).2 hzy
      exact (clearEnvelopeDrawing H Y Λ).closure_subset_U
        (mem_interSet_E_iff.mpr ⟨he, heOut⟩) (subset_closure hxe)

/-- The drawing on a circle contained in a drawing is a circuit.
This gives the boundary circuits used in XVI (8.1), Claim (4). -/
theorem interSet_isCircuit_of_oArc {H : Drawing S} {F : Set S}
    (hF : IsOArc F) (hFH : F ⊆ H.U) : (H.interSet F).IsCircuit := by
  obtain ⟨C, hC, hCH, hCF⟩ := exists_circuit_of_oArc hF hFH
  have hclosed : IsClosed F := (isCompact_of_isOArc hF).isClosed
  have hHC : (H.interSet F).IsSubdrawing C :=
    interSet_isSubdrawing hCH hclosed hCF.symm.subset
  have hCH' : C.IsSubdrawing (H.interSet F) :=
    subdrawing_interSet_of_U_subset hCH hCF.subset
  have heq : H.interSet F = C := Drawing.ext_of_V_E
    (subset_antisymm hHC.1 hCH'.1) (subset_antisymm hHC.2 hCH'.2)
  exact heq.symm ▸ hC

/-- Every boundary circuit remains a circuit after the whole family is
cleared, as required in XVI (8.1), Claim (4), page 72. -/
theorem zone_boundary_isCircuit_clearFamily {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {γ : ℕ} {Λ : S → Set S}
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    {y : S} (hy : y ∈ Y) :
    ((clearEnvelopeDrawing H Y Λ).interSet (subBd (Λ y))).IsCircuit :=
  interSet_isCircuit_of_oArc (hZone y hy).isOArc_bd (zone_boundary_subset_clearFamily hZone hdis hy)

end GraphMinor.GM16
