/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceGerms
public import LeanPool.GraphMinor.GM12.Section2TerminalSectors
import LeanPool.GraphMinor.GM12.Section2SectorEntryEquality
import LeanPool.GraphMinor.GM12.Section2PeriodGermSelection
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.Walks

/-!
# An accumulating corner is recorded by the trace

For the image restriction in XII (2.1), pages 243--244, lift the
subcurve's corner approach to a parameter of the original curve.
At an interior parameter its two recorded region visits enter two
sectors. Distinct sectors meet only in the drawing, so accumulation
in the chosen corner forces one of these two sectors to be that
corner. The common-sector entry comparison identifies the edge.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- At an interior trace parameter, an accumulating corner determines
an edge already in the trace. The incoming comparison curve may be
different from the original curve. -/
theorem traceSteps_mem_edges_of_corner_accumulation
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {γ : Set S → unitInterval → S} {v : S} (hv : v ∈ Γ.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {N : Set S}
    {τ : halfEdges Γ γ v → unitInterval}
    (hsec : IsSectors Γ γ v next ρ P N Q τ)
    (hcover : N \ Γ.U ⊆ ⋃ k, Q k) (k : halfEdges Γ γ v)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} {u z : S} (W : GraphWalk K.toGraph u z)
    (hW : TraceSteps Γ K f a b W) {s : ℝ} (hs : s ∈ Ioo a b) (hfs : f s = v)
    (hscl : s ∈ closure (Icc a b ∩ f ⁻¹' (Q k \ Γ.U)))
    {c d c₀ : ℝ} (hcc₀ : c ≤ c₀) (hc₀d : c₀ < d) (hgd : g d = v)
    {e : Set S} {w : S} (hw : w ∈ ρ k ∩ K.V) (he : e ∈ K.E)
    (hgr : ∀ t ∈ Ioo c d, g t ∈ ρ k)
    (hgQ : ∀ t ∈ Ioo c₀ d, g t ∈ Q k \ discBd (Q k))
    (hentry : EntersLike g c d e (ρ k) v w) : e ∈ W.edges := by
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hrk : ρ k ∈ Γ.R := hsec.corners.region k
  have hregion : (Q k \ discBd (Q k)) ∩ N ⊆ ρ k := by
    intro x hx
    exact hsec.sub k (hsec.inside k ⟨⟨hx.2, hx.1.1⟩, hx.1.2⟩)
  have compare : ∀ (F : ℝ → S), Continuous F → ∀ (p q h : ℝ), p < h → h < q →
      F q = v → ∀ (r₀ e₀ : Set S) (w₀ : S), r₀ ∈ Γ.R → w₀ ∈ r₀ ∩ K.V → e₀ ∈ K.E →
      (∀ t ∈ Ioo p q, F t ∈ r₀) → EntersLike F p q e₀ r₀ v w₀ →
      (∀ t ∈ Ico h q, F t ∈ ρ k ∩ (Q k \ discBd (Q k))) → e = e₀ := by
    intro F hF p q h hph hhq hFq r₀ e₀ w₀ hr₀ hw₀ he₀ hFr hentry₀ hFQ
    let m := (h + q) / 2
    have hhm : h < m := by dsimp [m]; linarith
    have hmq : m < q := by dsimp [m]; linarith
    have hrr : r₀ = ρ k := region_eq_of_mem hr₀ hrk
      (hFr m ⟨hph.trans hhm, hmq⟩) (hFQ m ⟨hhm.le, hmq⟩).1
    subst r₀
    have hww := hub_unique hrad hrk hw.1 hw.2 hw₀.1 hw₀.2
    subst w₀
    exact entersLike_edge_eq_of_common_sector hS hConn hK hrk hv hw he he₀
      (hsec.disc k) (hsec.bd k) hsec.isOpen hsec.mem hregion hg hF
      hcc₀ hc₀d hph.le hhq hgd hFq hgr hFr hgQ
      (fun t ht => (hFQ t ⟨ht.1.le, ht.2⟩).2) hentry hentry₀
  obtain ⟨p, wL, rL, eL, _, hps, hwL, hrL, hwLr, heLW, hfL, hentryL⟩ :=
    traceSteps_exists_incoming_germ W hW ⟨hs.1, hs.2.le⟩ (hfs.symm ▸ hv)
  obtain ⟨q, wR, rR, eR, _, hsq, hwR, hrR, hwRr, heRW, hfR, hentryR⟩ :=
    traceSteps_exists_outgoing_germ W hW ⟨hs.1.le, hs.2⟩ (hfs.symm ▸ hv)
  rw [hfs] at hentryL hentryR
  obtain ⟨i, hL, hpL, hLi⟩ := exists_terminal_sector_of_approach hsec hcover hf hps hfs
    (fun t ht => region_subset hrL (hfL t ht))
  have hneg : Continuous (fun t => f (-t)) := hf.comp continuous_neg
  have hfneg : (fun t => f (-t)) (-s) = v := by simpa only [neg_neg] using hfs
  have hfRneg : ∀ t ∈ Ioo (-q) (-s), f (-t) ∈ rR := by
    intro t ht
    exact hfR (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨j, hR, hqR, hRj⟩ := exists_terminal_sector_of_approach hsec hcover hneg
    (neg_lt_neg hsq) hfneg (fun t ht => region_subset hrR (hfRneg t ht))
  let ε := min ((s - hL) / 2) ((-hR - s) / 2)
  have hε : 0 < ε := lt_min (by linarith [hpL.2]) (by linarith [hqR.2])
  have hεL : ε ≤ (s - hL) / 2 := min_le_left _ _
  have hεR : ε ≤ (-hR - s) / 2 := min_le_right _ _
  have hdis : Pairwise (fun i j => Disjoint (Q i \ Γ.U) (Q j \ Γ.U)) := by
    intro i j hij
    exact disjoint_left.mpr (fun x hxi hxj => hxi.2 (hsec.inter i j hij ⟨hxi.1, hxj.1⟩))
  have hnot : f s ∉ Q k \ Γ.U := fun hx => hx.2 (hfs.symm ▸ Γ.V_subset_U hv)
  have hlabel : k = i ∨ k = j := side_label_of_closure_preimage hdis hε hnot hscl
    (fun t _ ht => by
      have hh : hL < t := by linarith [ht.1]
      exact ⟨(hLi t ⟨hh.le, ht.2⟩).2.1,
        region_subset hrL (hfL t ⟨hpL.1.trans hh, ht.2⟩)⟩)
    (fun t _ ht => by
      have hh : hR < -t := by linarith [ht.2]
      have hts : -t < -s := neg_lt_neg ht.1
      exact ⟨by simpa only [neg_neg] using (hRj (-t) ⟨hh.le, hts⟩).2.1,
        region_subset hrR (hfR t ⟨ht.1, by linarith [hqR.1]⟩)⟩)
  have edge_mem : ∀ e₀ ∈ W.edges, e₀ ∈ K.E := by
    intro e₀ he₀
    exact (walkDrawing_isSubdrawing K W).2 (by rw [walkDrawing_E]; exact he₀)
  rcases hlabel with hki | hkj
  · subst i
    have heq := compare f hf p s hL hpL.1 hpL.2 hfs rL eL wL hrL
      ⟨hwLr, hwL⟩ (edge_mem eL heLW) hfL hentryL hLi
    exact heq.symm ▸ heLW
  · subst j
    have heq := compare (fun t => f (-t)) hneg (-q) (-s) hR hqR.1 hqR.2 hfneg rR eR wR hrR
      ⟨hwRr, hwR⟩ (edge_mem eR heRW) hfRneg hentryR hRj
    exact heq.symm ▸ heRW

end GraphMinor.GM12
