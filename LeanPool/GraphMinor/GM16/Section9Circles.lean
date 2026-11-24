/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.GM11.Section7

/-!
# A circle crossing a zone boundary

In Claim (2) of the proof of XVI (8.1), a normal circle meets at most two
vertices of the cleared drawing. A circle entering and leaving an open disc
must meet its boundary twice, since removing one point from a circle leaves
a connected set. This is the first step of the rigidity argument there.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
private theorem preconnected_meets_boundary {F Δ : Set S} (hF : IsPreconnected F)
    (hΔ : IsOpen Δ) (hin : (F ∩ Δ).Nonempty) (hout : (F \ closure Δ).Nonempty) :
    (F ∩ subBd Δ).Nonempty := by
  by_contra hn
  have hcover : F ⊆ Δ ∪ (closure Δ)ᶜ := by
    intro x hx
    by_cases hxΔ : x ∈ Δ
    · exact Or.inl hxΔ
    · right
      intro hxcl
      have hxBd : x ∈ subBd Δ := by
        rw [subBd_eq_frontier]
        exact ⟨hxcl, by simpa only [hΔ.interior_eq] using hxΔ⟩
      exact hn ⟨x, hx, hxBd⟩
  obtain ⟨x, hxF, hxΔ⟩ := hin
  obtain ⟨y, hyF, hyΔ⟩ := hout
  obtain ⟨z, _, hzΔ, hzout⟩ := hF Δ (closure Δ)ᶜ hΔ isClosed_closure.isOpen_compl hcover
    ⟨x, hxF, hxΔ⟩ ⟨y, hyF, hyΔ⟩
  exact hzout (subset_closure hzΔ)

omit [T2Space S] in
/-- A circle meeting an open disc and the outside of its closure has at least
two boundary points. This is used in XVI, proof of (8.1), Claim (2), page 71. -/
theorem oArc_crosses_boundary_twice {F Δ : Set S} (hF : IsOArc F) (hΔ : IsOpen Δ)
    (hin : (F ∩ Δ).Nonempty) (hout : (F \ closure Δ).Nonempty)
    (hfin : (F ∩ subBd Δ).Finite) : 2 ≤ (F ∩ subBd Δ).ncard := by
  by_contra hn
  have hsmall : (F ∩ subBd Δ).ncard ≤ 1 := by omega
  obtain ⟨p, hpF, hpBd⟩ := preconnected_meets_boundary hF.isPreconnected hΔ hin hout
  have hall := (Set.ncard_le_one hfin).mp hsmall
  have hcl : closure (univ \ Δ) = univ \ Δ := (isClosed_univ.sdiff hΔ).closure_eq
  have hpOut : p ∉ Δ := by
    have hp := hpBd.2
    rw [hcl] at hp
    exact hp.2
  obtain ⟨x, hxF, hxΔ⟩ := hin
  obtain ⟨y, hyF, hyOut⟩ := hout
  have hxp : x ≠ p := fun heq => hpOut (heq ▸ hxΔ)
  have hyp : y ≠ p := fun heq => hyOut (heq ▸ hpBd.1)
  have hpre := (isPathConnected_oArc_diff hF hpF).isConnected.isPreconnected
  obtain ⟨q, hq, hqBd⟩ := preconnected_meets_boundary hpre hΔ
    ⟨x, ⟨hxF, hxp⟩, hxΔ⟩ ⟨y, ⟨hyF, hyp⟩, hyOut⟩
  have hqp : q = p := hall q ⟨hq.1, hqBd⟩ p ⟨hpF, hpBd⟩
  exact hq.2 hqp

omit [T2Space S] in
/-- In XVI, proof of (8.1), Claim (2), a normal circle meeting at most two
vertices cannot enter two of the pairwise disjoint battlefield discs. -/
theorem oArc_not_meet_two_discs {K : Drawing S} {F Δ₁ Δ₂ : Set S}
    (hF : IsOArc F) (hΔ₁ : IsOpen Δ₁) (hΔ₂ : IsOpen Δ₂)
    (hdis : Disjoint (closure Δ₁) (closure Δ₂))
    (hbd₁ : subBd Δ₁ ⊆ K.U) (hbd₂ : subBd Δ₂ ⊆ K.U)
    (hnormal : F ∩ K.U ⊆ K.V) (hcard : (F ∩ K.V).ncard ≤ 2) :
    ¬ ((F ∩ Δ₁).Nonempty ∧ (F ∩ Δ₂).Nonempty) := by
  rintro ⟨⟨x₁, hx₁F, hx₁⟩, ⟨x₂, hx₂F, hx₂⟩⟩
  have hsub₁ : F ∩ subBd Δ₁ ⊆ F ∩ K.V := by
    rintro x ⟨hxF, hxBd⟩
    exact ⟨hxF, hnormal ⟨hxF, hbd₁ hxBd⟩⟩
  have hsub₂ : F ∩ subBd Δ₂ ⊆ F ∩ K.V := by
    rintro x ⟨hxF, hxBd⟩
    exact ⟨hxF, hnormal ⟨hxF, hbd₂ hxBd⟩⟩
  have hcapFin : (F ∩ K.V).Finite := K.finite_V.subset inter_subset_right
  have hfin₁ := hcapFin.subset hsub₁
  have hfin₂ := hcapFin.subset hsub₂
  have hcross₁ := oArc_crosses_boundary_twice hF hΔ₁ ⟨x₁, hx₁F, hx₁⟩
    ⟨x₂, hx₂F, hdis.notMem_of_mem_right (subset_closure hx₂)⟩ hfin₁
  have hcross₂ := oArc_crosses_boundary_twice hF hΔ₂ ⟨x₂, hx₂F, hx₂⟩
    ⟨x₁, hx₁F, hdis.notMem_of_mem_left (subset_closure hx₁)⟩ hfin₂
  have hdisCap : Disjoint (F ∩ subBd Δ₁) (F ∩ subBd Δ₂) :=
    disjoint_left.mpr fun x hx hy => hdis.notMem_of_mem_left hx.2.1 hy.2.1
  have hcount := ncard_le_ncard (union_subset hsub₁ hsub₂) hcapFin
  rw [ncard_union_eq hdisCap hfin₁ hfin₂] at hcount
  omega

end GraphMinor.GM16
