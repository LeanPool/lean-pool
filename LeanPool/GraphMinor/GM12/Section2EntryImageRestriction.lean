/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2CornerAccumulation
public import LeanPool.GraphMinor.GM12.Section2LeafTraceRestriction
import LeanPool.GraphMinor.GM12.Section2TraceTranslation
import LeanPool.GraphMinor.GM12.Section2SectorCover
import LeanPool.GraphMinor.GM12.Section2PeriodGermSelection
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# Entry edges are preserved by inclusion of curve images

For XII (2.1), pages 243--244, an approach in the smaller curve
image enters a corner at its limiting vertex. Compactness lifts
this corner's accumulation to an original parameter. Read two
periods of the original trace and choose the lifted parameter in
the middle period, so both adjacent visits are available. The
corner-accumulation lemma identifies a recorded edge. Leaves have
only one corner and are covered by the leaf restriction lemma.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Every entry along an approach contained in a traced curve image
uses one of that trace's edges, for a drawing with an edge. This is
the edge part of the restriction step of XII (2.1), pages 243--244. -/
theorem trace_mem_edges_of_entry_in_image
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {v w : S} (hv : v ∈ Γ.V) {r e : Set S} (hr : r ∈ Γ.R)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E)
    {g : ℝ → S} (hg : Continuous g) {c d : ℝ} (hcd : c < d) (hgd : g d = v)
    (hgr : ∀ t ∈ Ioo c d, g t ∈ r) (himage : ∀ t ∈ Icc c d, g t ∈ range φ)
    (hentry : EntersLike g c d e r v w) : e ∈ W.edges := by
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ v)
  · obtain ⟨next, ρ, P, N, Q, τ, hsec, hcover⟩ :=
      exists_sectors_with_cover hS Γ hγ hv h2
    obtain ⟨k, c₀, hcc₀, hgQ⟩ := exists_terminal_sector_of_approach hsec hcover hg hcd hgd
      (fun t ht => region_subset hr (hgr t ht))
    let m := (c₀ + d) / 2
    have hm : m ∈ Ioo c₀ d := ⟨by dsimp [m]; linarith [hcc₀.2], by dsimp [m]; linarith [hcc₀.2]⟩
    have hrρ : r = ρ k := region_eq_of_mem hr (hsec.corners.region k)
      (hgr m ⟨hcc₀.1.trans hm.1, hm.2⟩) (hgQ m ⟨hm.1.le, hm.2⟩).1
    subst r
    rcases hW.2 with ⟨_, _, _, r₀, hr₀, hφr₀, _⟩ | ⟨_, _, a, hsteps⟩
    · exact (region_subset hr₀ (hφr₀ (himage d ⟨hcd.le, le_rfl⟩))
        (hgd.symm ▸ Γ.V_subset_U hv)).elim
    · have htwo := traceSteps_two_periods (periodicCurve_periodic φ) W hsteps
      have hfiniteImage : ∀ t ∈ Ioo c₀ d,
          g t ∈ periodicCurve φ '' Icc (a + 1 / 2) (a + 3 / 2) ∩ (Q k \ Γ.U) := by
        intro t ht
        obtain ⟨z, hz⟩ := himage t ⟨(hcc₀.1.trans ht.1).le, ht.2.le⟩
        obtain ⟨p, hp, hpz⟩ := (circle_parameter_bijOn (a + 1 / 2)).surjOn (mem_univ z)
        refine ⟨⟨p, ⟨hp.1, by linarith [hp.2]⟩, (congrArg φ hpz).trans hz⟩,
          (hgQ t ⟨ht.1.le, ht.2⟩).2.1, ?_⟩
        exact region_subset (hsec.corners.region k) (hgr t ⟨hcc₀.1.trans ht.1, ht.2⟩)
      obtain ⟨s, hs, hfs, hscl⟩ := exists_period_parameter_of_approach
        (periodicCurve_continuous φ) hg hcc₀.2 hgd hfiniteImage
      have hscl' : s ∈ closure (Icc a (a + 2) ∩ periodicCurve φ ⁻¹' (Q k \ Γ.U)) := by
        apply closure_mono (s := Icc (a + 1 / 2) (a + 3 / 2) ∩ periodicCurve φ ⁻¹'
          (Q k \ Γ.U)) _ hscl
        intro t ht
        exact ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩
      have heW := traceSteps_mem_edges_of_corner_accumulation hS inferInstance hK hv hsec hcover k
        (periodicCurve_continuous φ) hg (W.append W) htwo
        ⟨by linarith [hs.1], by linarith [hs.2]⟩ hfs hscl'
        hcc₀.1.le hcc₀.2 hgd hw he hgr (fun t ht => (hgQ t ⟨ht.1.le, ht.2⟩).2) hentry
      simpa only [GraphWalk.edges_append, List.mem_append, or_self] using heW
  · obtain ⟨e₀, he₀, hvcl⟩ := exists_edge_at (show PreRad (.drawing Γ) K from ⟨hK.1, hK.2.1⟩) hS hE
      hv
    obtain ⟨b, hb⟩ := exists_end_eq hγ he₀ hv hvcl
    let : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
    let : Nonempty (halfEdges Γ γ v) := ⟨⟨(e₀, b), he₀, hb⟩⟩
    have hpos : 0 < Nat.card (halfEdges Γ γ v) := Nat.card_pos
    have hcard : Nat.card (halfEdges Γ γ v) = 1 := by omega
    have hvφ : v ∈ range φ := hgd ▸ himage d ⟨hcd.le, le_rfl⟩
    exact trace_mem_edges_of_entry_at_leaf hS inferInstance hK hγ hv hcard W hW hvφ
      hg hcd hgd hr hw he hgr hentry

/-- The outgoing version of image restriction follows by reversing
the approaching function and its real interval. -/
theorem trace_mem_edges_of_leaving_in_image
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {v w : S} (hv : v ∈ Γ.V) {r e : Set S} (hr : r ∈ Γ.R)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E)
    {g : ℝ → S} (hg : Continuous g) {c d : ℝ} (hcd : c < d) (hgc : g c = v)
    (hgr : ∀ t ∈ Ioo c d, g t ∈ r) (himage : ∀ t ∈ Icc c d, g t ∈ range φ)
    (hleave : LeavesLike g c d e r v w) : e ∈ W.edges := by
  apply trace_mem_edges_of_entry_in_image hS hK hE W hW hv hr hw he
    (hg.comp continuous_neg) (neg_lt_neg hcd)
    (by simpa only [Function.comp_apply, neg_neg] using hgc) _ _ hleave
  · intro t ht
    exact hgr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro t ht
    exact himage (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩

end GraphMinor.GM12
