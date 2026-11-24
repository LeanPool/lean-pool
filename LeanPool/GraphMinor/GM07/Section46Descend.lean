/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PushForest
import LeanPool.GraphMinor.GM07.PullForest
import LeanPool.GraphMinor.GM07.Section46CentralLift

/-!
# Feasibility descends along the two cuts

Page 227: "Thus, to show that $H$ is $G$-feasible it suffices to show that
$\phi^{-1}(H)$ is $\phi^{-1}(G)$-feasible." We apply (4.5) twice, first to `ψ` and then
to `θ`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

variable {S S' D : Type} [TopologicalSpace S] [TopologicalSpace S'] [TopologicalSpace D]

/-- The image of a subgraph of `φ⁻¹(G)` is a subgraph of `G`. -/
theorem isSubdrawing_of_image {G : Drawing S} {Gd Hd : Drawing D} {P : Drawing S} {φ : D → S}
    (hPU : P.U = φ '' Hd.U) (hPV : P.V = φ '' Hd.V) (hV : Gd.V = φ ⁻¹' G.V)
    (hsub : Hd.IsSubdrawing Gd) (hE : ∀ e' ∈ Gd.E, ∃ e ∈ G.E, φ '' e' = e) :
    P.IsSubdrawing G := by
  have hVG : P.V ⊆ G.V := by
    rw [hPV]
    rintro _ ⟨v, hv, rfl⟩
    have := hsub.1 hv
    rw [hV] at this
    exact this
  refine ⟨hVG, fun e he => ?_⟩
  have hcover : ∀ {z : S}, z ∈ P.U \ P.V → ∃ g ∈ G.E, z ∈ g ∧ g ⊆ P.U \ P.V := by
    rintro z ⟨hzU, hzV⟩
    rw [hPU] at hzU
    obtain ⟨z', hz', rfl⟩ := hzU
    have hz'V : z' ∉ Hd.V := fun h => hzV (hPV ▸ mem_image_of_mem φ h)
    rcases (mem_U_iff_edge Hd).mp hz' with h | ⟨e', he', hze'⟩
    · exact (hz'V h).elim
    · obtain ⟨g, hg, rfl⟩ := hE e' (hsub.2 he')
      refine ⟨_, hg, mem_image_of_mem φ hze', ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hPU ▸ mem_image_of_mem φ (he'.2.1 hy).1, fun h => ?_⟩
      exact (hg.2.1 ⟨y, hy, rfl⟩).2 (hVG h)
  obtain ⟨x, hx⟩ := he.1
  obtain ⟨g, hg, hxg, hgsub⟩ := hcover (he.2.1 hx)
  have hesub : e ⊆ G.U \ G.V := by
    intro z hz
    obtain ⟨g', hg', hzg', -⟩ := hcover (he.2.1 hz)
    exact hg'.2.1 hzg'
  have hconn : IsPathConnected (e ∪ g) := he.2.2.1.union hg.2.2.1 ⟨x, hx, hxg⟩
  have h1 : e ∪ g = e := he.2.2.2 _ (union_subset he.2.1 hgsub) hconn subset_union_left
  have h2 : e ∪ g = g := hg.2.2.2 _ (union_subset hesub hg.2.1) hconn subset_union_right
  have : e = g := h1.symm.trans h2
  rwa [this]

/-- Page 227: feasibility of the pullback to the disc gives feasibility of `H`. -/
theorem isGFeasible_of_pullback (hS : IsSurface S) {L G H : Drawing S}
    {K' G' H' : Drawing S'} {Gd Hd : Drawing D}
    {θ : S' → S} {ψ : D → S'} (hθ : IsCutAlongGraph L S' θ) (hψ : IsCutAlongGraph K' D ψ)
    (hH : IsSurfaceForest H) (hnL : H.IsNormal L.U) (hH' : IsSurfaceForest H')
    (hnK : H'.IsNormal K'.U) (hp : IsPullbackDrawing θ H H') (hpd : IsPullbackDrawing ψ H' Hd)
    (hG' : IsPullbackDrawing θ G G') (hGd : IsPullbackDrawing ψ G' Gd)
    (hE : ∀ e' ∈ Gd.E, ∃ e ∈ G.E, (θ ∘ ψ) '' e' = e) (hfe : IsGFeasible Gd Hd) :
    IsGFeasible G H := by
  have hS' := hθ.isSurface
  obtain ⟨Hd', hF, hhom, hsub⟩ := hfe
  obtain ⟨Hq, hq, -, hpush⟩ := theorem_4_5_proof hS' K' H' ψ hψ hH' hnK
  have hqeq : Hq = Hd := drawing_eq (hq.1.trans hpd.1.symm) (hq.2.trans hpd.2.symm)
  subst hqeq
  obtain ⟨P₁, hi₁, hF₁, hh₁⟩ := hpush Hd' hF hhom.symm
  obtain ⟨Hr, hr, -, hpush₂⟩ := theorem_4_5_proof hS L H θ hθ hH hnL
  have hreq : Hr = H' := drawing_eq (hr.1.trans hp.1.symm) (hr.2.trans hp.2.symm)
  subst hreq
  obtain ⟨P₂, hi₂, hF₂, hh₂⟩ := hpush₂ P₁ hF₁ hh₁
  refine ⟨P₂, hF₂, hh₂.symm, ?_⟩
  refine isSubdrawing_of_image
    (by rw [hi₂.1, hi₁.1, image_comp]) (by rw [hi₂.2, hi₁.2, image_comp]) ?_ hsub hE
  rw [hGd.2, hG'.2]
  rfl

end GraphMinor.GM07
