/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12e
public import LeanPool.GraphMinor.GM11.OArcCircuit
public import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Graph Minors XIX, Section 12: three vertices on the boundary of a wheel

The proof of (13.1) says that `bd(W)` has at least six vertices of `Γ*`. The paper gives one line
for this. Here is the
proof. If at most two vertices of `Γ` lie on `bd(W)`, then internal 3-connectivity gives a disc `Δ ⊆
Σ` with this
boundary and no other vertex of `Γ`. The disc `W` has a vertex inside, so `W ≠ Δ`, and `W ∪ Δ = Σ̂`.
By the first condition
in the definition of a wheel, `W` is the inside of its boundary circuit. So the tangle has a member
`(A, B)` with
`V(A) = V(Γ)`, against the third tangle axiom.

The result is `TangleDatum.three_le_ncard_bd`, and it also gives the frame `Φ'` of page 377 its
vertices.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

/-- **At least three vertices of `Γ` lie on the boundary of a wheel**, if the boundary misses
`bd(Σ)` and the wheel has
a vertex of `Γ` inside. -/
theorem three_le_ncard_bd (h : D.IsWheelHubOfRadius W H ρ) (hbd : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) :
    3 ≤ (discBd W ∩ D.P.Γ.hatV cap).ncard := by
  classical
  have hT := cap.isClosedSurface
  have hS := χ.isSurface
  have : ConnectedSpace Shat := cap.connected
  have hO : IsOArc (discBd W) := h.is_disc.isOArc_discBd
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc hO h.bd_sub
  by_contra hlt
  push Not at hlt
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  have hVG : Sk.V ⊆ D.rad.G.V := by
    rw [hSk.hV]
    exact D.rad.isPreRadial.2.1
  have hw : IsWeighting D.rad.G (2 * 3) Sk.V 3 :=
    isWeighting_radial (Γ := PaintingOrDrawing.drawing Sk) (by omega) hVG (D.rad.bipartite hSk.hV)
  have hsame : Sk.V ∩ F.V ⊆ discBd W ∩ D.P.Γ.hatV cap := by
    rintro x ⟨hx, hxF⟩
    rw [hSk.hV] at hx
    exact ⟨hFU ▸ F.V_subset_U hxF, hx⟩
  have hfin : (discBd W ∩ D.P.Γ.hatV cap).Finite := D.P.Γ.finite_V.image _ |>.subset
    inter_subset_right
  have hlen : F.E.ncard < 6 := by
    by_contra hge
    have := hw.le_ncard F hFc hFs (by rw [Drawing.length]; omega)
    have := ncard_le_ncard hsame hfin
    omega
  have hρ := h.pos_ρ
  have hrep := h.rep_ge
  have hF : Drawing.IsCircuitOf F D.rad.G := ⟨hFs, hFc⟩
  have hi := D.ins_spec hF (by omega)
  have hFW : F.U ⊆ W := hFU ▸ Surface.discBd_subset W
  have hsubW : D.ins F ⊆ W := h.ins_sub F hF (by omega) hFW
  have heq : D.ins F = W := by
    obtain ⟨Δ₀, -, hu⟩ := disc_oArc W F.U h.is_disc hFW (hFU ▸ hO)
    rw [hu _ hsubW hi.2.2.1 hi.2.2.2.1, hu W subset_rfl h.is_disc hFU.symm]
  -- the preimage of the boundary in `Σ`
  let F₀ : Set S := cap.emb ⁻¹' discBd W
  have hF₀im : cap.emb '' F₀ = discBd W := by
    rw [image_preimage_eq_iff]
    exact fun x hx ↦ by
      obtain ⟨y, -, rfl⟩ := hbd hx
      exact mem_range_self y
  have hF₀O : IsOArc F₀ := isOArc_of_image cap.isEmbedding (hF₀im ▸ hO)
  have hF₀U : F₀ ∩ D.P.Γ.U ⊆ D.P.Γ.V := by
    rintro x ⟨hx, hxU⟩
    have hxG : cap.emb x ∈ D.rad.G.U := h.bd_sub hx
    have hm : cap.emb x ∈ D.P.Γ.hatV cap := D.rad.isPreRadial.1 ▸ ⟨mem_image_of_mem _ hxU, hxG⟩
    obtain ⟨y, hy, hyx⟩ := hm
    exact cap.isEmbedding.injective hyx ▸ hy
  have hF₀b : F₀ ∩ bd S = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxb⟩
    obtain ⟨y, hy, hyx⟩ := hbd hx
    obtain rfl := cap.isEmbedding.injective hyx
    exact hy.2 hxb
  have hF₀V : (F₀ ∩ D.P.Γ.V).ncard ≤ 2 := by
    have hsub : cap.emb '' (F₀ ∩ D.P.Γ.V) ⊆ discBd W ∩ D.P.Γ.hatV cap := by
      rintro _ ⟨x, ⟨hx, hxV⟩, rfl⟩
      exact ⟨hx, mem_image_of_mem _ hxV⟩
    have := ncard_le_ncard hsub hfin
    rw [ncard_image_of_injective _ cap.isEmbedding.injective] at this
    omega
  obtain ⟨Δ, hΔ, hΔb, hΔV⟩ := D.P.fits.internally_three_connected.2 F₀ hF₀O hF₀U
    (by rw [hF₀b]; exact finite_empty)
    (by rw [hF₀b, ncard_empty]; omega)
  obtain ⟨hE, hEb⟩ := isClosedDisc_image hΔ cap.isEmbedding
  have hbeq : discBd W = discBd (cap.emb '' Δ) := by rw [hEb, hΔb, hF₀im]
  obtain ⟨_, ⟨hv₀W, hv₀b⟩, v₀, hv₀, rfl⟩ := hin
  have hne : W ≠ cap.emb '' Δ := fun hne ↦ by
    obtain ⟨y, hy, hyv⟩ := hne ▸ hv₀W
    obtain rfl := cap.isEmbedding.injective hyv
    exact hv₀b (hΔV ⟨hy, hv₀⟩)
  have hcov := cover_of_discBd_eq hT h.is_disc hE hbeq hne
  have hm := hi.2.2.2.2
  rw [heq] at hm
  refine D.isTangle.axiom3 hm ?_
  apply subset_antisymm inter_subset_left
  intro v hv
  refine ⟨hv, ?_⟩
  have hx : cap.emb v ∈ W ∪ cap.emb '' Δ := hcov ▸ mem_univ _
  rcases hx with hx | ⟨y, hy, hyv⟩
  · exact hx
  · obtain rfl := cap.isEmbedding.injective hyv
    exact Surface.discBd_subset W (hΔV ⟨hy, hv⟩)

end TangleDatum

end GraphMinor.GM19
