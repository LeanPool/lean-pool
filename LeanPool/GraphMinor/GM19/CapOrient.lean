/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.DiscRealize
public import LeanPool.GraphMinor.GM19.CutFragment

/-!
# Orienting the capped surface

The hypothesis of Graph Minors XIX, (15.2) gives an orientation of `Σ`. Steps (2) and (3) of its
proof work on the closed surface `Σ̂`, so we carry the orientation over (`exists_cap_orientation`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]

/-- The left inverse of the embedding of `Σ` into `Σ̂`. -/
noncomputable def capBack [Nonempty S] (cap : IsCappedSurface S Shat) : Shat → S
  := Function.invFun cap.emb

omit [T2Space S] [T2Space Shat] in
theorem capBack_emb [Nonempty S] (cap : IsCappedSurface S Shat) (x : S) : capBack cap (cap.emb x)
  = x :=
  Function.leftInverse_invFun cap.isEmbedding.injective x

omit [T2Space S] [T2Space Shat] in
theorem continuousOn_capBack [Nonempty S] (cap : IsCappedSurface S Shat) : ContinuousOn
  (capBack cap) (range cap.emb) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Continuous fun x : range cap.emb => cap.isEmbedding.toHomeomorph.symm x
    := cap.isEmbedding.toHomeomorph.symm.continuous
  convert h using 2 with x
  obtain ⟨_, ⟨y, rfl⟩⟩ := x
  change capBack cap (cap.emb y) = _
  rw [capBack_emb]
  exact (cap.isEmbedding.toHomeomorph.symm_apply_apply y).symm

/-- **An orientation of `Σ` extends to `Σ̂`.** On each disc of `Σ` the extension agrees with the
given orientation. -/
theorem exists_cap_orientation [Nonempty S] (hS : IsSurface S) (cap : IsCappedSurface S Shat)
  (o : SurfaceOrientation S) :
    ∃ ω : SurfaceOrientation Shat, ∀ Δ, IsClosedDisc Δ → Δ ⊆ range cap.emb → SameOn ω.pos (pullPos
      (capBack cap) o.pos) Δ := by
  have hT := cap.isClosedSurface
  have := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  let 𝓙 : Set (Set Shat) := {Δ | Δ ⊆ range cap.emb}
  have hJ : IsPartialOrientation 𝓙 (pullPos (capBack cap) o.pos) := (o.isPartial univ).pull fun Δ
    hΔ =>
    ⟨(continuousOn_capBack cap).mono hΔ, fun x hx y hy he => by
      obtain ⟨x, rfl⟩ := hΔ hx
      obtain ⟨y, rfl⟩ := hΔ hy
      rw [capBack_emb, capBack_emb] at he
      rw [he], mem_univ _⟩
  have hhered : ∀ Δ ∈ 𝓙, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓙 := fun Δ hΔ Δ' hs => hs.trans hΔ
  let G : Set Shat := (⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ))ᶜ
  obtain ⟨hGo, hGc⟩ := cap.isPreconnected_compl (cuff_statement S hS).2.1 subset_rfl
  have hGJ : {Δ | Δ ⊆ G} ⊆ 𝓙 := fun Δ hΔ x hx => by
    by_contra hn
    have hn' : x ∈ (range cap.emb)ᶜ := hn
    rw [cap.compl_eq] at hn'
    obtain ⟨Θ, hΘ⟩ := mem_iUnion.mp hn'
    obtain ⟨hΘ', hxΘ⟩ := mem_iUnion.mp hΘ
    exact hΔ hx (mem_biUnion hΘ' (subset_closure hxΘ))
  have hint : ∀ x ∈ G, IsInteriorPoint x := fun x _ => hT.2.2 x
  obtain ⟨e, P, hP, hs, ht, -⟩ := exists_cap_chart hS cap
  obtain ⟨ω₂⟩ := isOrientable_of_inside hT hP e hs ht (o.isPartial _)
  obtain ⟨x₀, hx₀⟩ : G.Nonempty := by
    have : Finite {Θ : Set S // Θ ∈ cuffs S} := (cuff_statement S hS).2.1
    obtain ⟨x, hx⟩ := nonempty_compl_iUnion hT (D := fun Θ : {Θ : Set S // Θ ∈ cuffs S} => closure
      (cap.cuffDisc Θ.1)) (fun Θ => cap.cuffDisc_closedDisc Θ.1 Θ.2)
      (fun Θ Θ' h => cap.cuffDisc_disjoint _ Θ.2 _ Θ'.2 fun he => h (Subtype.ext he))
    refine ⟨x, fun hu => hx ?_⟩
    obtain ⟨Θ, hΘ⟩ := mem_iUnion.mp hu
    obtain ⟨hΘ', hxΘ⟩ := mem_iUnion.mp hΘ
    exact mem_iUnion.mpr ⟨⟨Θ, hΘ'⟩, hxΘ⟩
  obtain ⟨E, hE, -, hEs⟩ := exists_small_disc (hint x₀ hx₀) hGo hx₀
  have hdir₂ := (ω₂.isPartial 𝓙).dir E (hGJ hEs) hE
  have hdirJ := hJ.dir E (hGJ hEs) hE
  obtain ⟨pos₁, hpos₁, hE₁⟩ : ∃ pos₁, IsPartialOrientation univ pos₁ ∧ SameOn pos₁ (pullPos
    (capBack cap) o.pos) E := by
    by_cases hs : SameOn ω₂.pos (pullPos (capBack cap) o.pos) E
    · exact ⟨ω₂.pos, ω₂.isPartial univ, hs⟩
    · exact ⟨revPos ω₂.pos, (ω₂.isPartial univ).rev, sameOn_rev_left (sameOn_of_notSame hdir₂ hdirJ
      hs)⟩
  refine ⟨orientationOfPartial hpos₁, fun Δ hΔ hsub a b c ha hb hc hab hbc hac => ?_⟩
  have hP' : IsPartialOrientation 𝓙 pos₁ := hpos₁.mono (subset_univ _)
  obtain ⟨y, hyΔ⟩ := hΔ.nonempty_discInt
  have hyG : ∀ y ∈ discInt Δ, y ∈ G := fun y hy hu => by
    obtain ⟨Θ, hΘ⟩ := mem_iUnion.mp hu
    obtain ⟨hΘ', hyΘ⟩ := mem_iUnion.mp hΘ
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hyΘ _ (hΔ.isOpen_discInt hman) hy
    have : z ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_biUnion hΘ' hz2
    exact this (hsub (discInt_subset _ hz1))
  obtain ⟨D, hD, -, hDs⟩ := exists_small_disc (hint y (hyG y hyΔ)) (hΔ.isOpen_discInt hman) hyΔ
  have hDG : D ⊆ G := hDs.trans hyG
  have hG : SameOn pos₁ (pullPos (capBack cap) o.pos) D :=
    (sameOn_const hman hGo hGc hint (hP'.mono hGJ) (hJ.mono hGJ) hE hD hEs hDG).1 hE₁
  exact (sameOn_of_subset hman hhered hP' hJ hsub hD hΔ (hDs.trans (discInt_subset Δ))).1 hG a b c
    ha hb hc hab hbc hac

end GraphMinor.GM19
