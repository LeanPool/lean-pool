/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.RuralClean
public import LeanPool.GraphMinor.Surface.EdgeLens
public import LeanPool.GraphMinor.Surface.ArcTools
public import LeanPool.GraphMinor.Surface.ChartCells
public import LeanPool.GraphMinor.Surface.SurfacePull
public import LeanPool.GraphMinor.Surface.Jordan

/-!
# Free curves near a drawing

Here we find room for one more edge in a clean presentation. Beside an edge there is a thin disc
that meets the rest of the drawing only in the ends of the edge (`exists_edge_lens`, which works in
a closed surface, so we use it in the sphere and come back to the plane). This gives a second line
parallel to the edge, and, at any vertex that is not on the inner disc, an `O`-arc that meets the
drawing only in that vertex.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11
open scoped unitInterval

universe u v

variable {α : Type u} {β : Type v}

/-- The sphere is a closed surface. -/
theorem isClosedSurface_sphere : IsClosedSurface (OnePoint EuclideanPlane) := by
  refine ⟨inferInstance, inferInstance, fun x => ?_⟩
  obtain ⟨h, hh⟩ := exists_homeomorph_onePoint x
  obtain ⟨k, hk⟩ := exists_homeomorph_onePoint ((0 : EuclideanPlane) : OnePoint EuclideanPlane)
  let g := h.trans k.symm
  have hgx : g x = ((0 : EuclideanPlane) : OnePoint EuclideanPlane) := by
    simp only [g, Homeomorph.trans_apply, hh, ← hk, Homeomorph.symm_apply_apply]
  have hemb : IsOpenEmbedding ((↑) : EuclideanPlane → OnePoint EuclideanPlane) :=
    OnePoint.isOpenEmbedding_coe
  let U₀ : Set (OnePoint EuclideanPlane) := (↑) '' OpenUnitDisc
  have hopen : IsOpen OpenUnitDisc := Metric.isOpen_ball
  refine ⟨g ⁻¹' U₀, (hemb.isOpenMap _ hopen).preimage g.continuous, ?_, ?_⟩
  · rw [mem_preimage, hgx]
    exact ⟨0, Metric.mem_ball_self one_pos, rfl⟩
  · exact ⟨(g.sets rfl).trans (hemb.isEmbedding.homeomorphImage OpenUnitDisc).symm⟩

/-- A thin disc around a line of the plane, which meets the closed set `Z` only in the ends of the
line, with a second line with the same ends that lies in the disc and misses the first. -/
theorem exists_plane_lens {L Z : Set EuclideanPlane} {u v : EuclideanPlane}
    (hL : IsLineWithEnds L u v) (huv : u ≠ v) (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ D K : Set EuclideanPlane, IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧ u ∈ discBd D ∧
      v ∈ discBd D ∧ IsPreconnected (D \ {u, v}) ∧ IsLineWithEnds K u v ∧ K ⊆ D ∧
      Disjoint (K \ {u, v}) L := by
  classical
  let c : EuclideanPlane → OnePoint EuclideanPlane := (↑)
  have hc : IsOpenEmbedding c := OnePoint.isOpenEmbedding_coe
  let r : OnePoint EuclideanPlane → EuclideanPlane := invFun c
  have hrc : ∀ x, r (c x) = x := leftInverse_invFun hc.injective
  have hcr : ∀ p ∈ range c, c (r p) = p := by
    rintro _ ⟨x, rfl⟩
    rw [hrc]
  have hrcont : ContinuousOn r (range c) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous fun y : range c => r y.1
    have : (fun y : range c => r y.1) = hc.isEmbedding.toHomeomorph.symm := by
      funext y
      obtain ⟨_, x, rfl⟩ := y
      apply hc.isEmbedding.toHomeomorph.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext (hcr _ ⟨x, rfl⟩)
    rw [this]
    exact Homeomorph.continuous _
  have hL' : IsLineWithEnds (c '' L) (c u) (c v) := hL.map_of_embedding hc.isEmbedding
  have hne : c u ≠ c v := fun h => huv (hc.injective h)
  let Z' : Set (OnePoint EuclideanPlane) := c '' Z ∪ {OnePoint.infty}
  have hZ' : IsClosed Z' := by
    rw [← isOpen_compl_iff]
    have : Z'ᶜ = c '' Zᶜ := by
      ext p
      induction p using OnePoint.rec with
      | infty =>
        constructor
        · intro h
          exact (h (Or.inr rfl)).elim
        · rintro ⟨x, -, hx⟩
          exact (OnePoint.coe_ne_infty x hx).elim
      | coe x =>
        constructor
        · intro h
          exact ⟨x, fun hz => h (Or.inl ⟨x, hz, rfl⟩), rfl⟩
        · rintro ⟨y, hy, hxy⟩ (⟨z, hz, hzx⟩ | h)
          · obtain rfl := hc.injective (hzx.trans hxy.symm)
            exact hy hz
          · exact (OnePoint.coe_ne_infty x h).elim
    rw [this]
    exact hc.isOpenMap _ hZ.isOpen_compl
  have hLZ' : c '' L ∩ Z' ⊆ {c u, c v} := by
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩ | h⟩
    · obtain rfl := hc.injective hxy
      rcases hLZ ⟨hx, hy⟩ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact (OnePoint.coe_ne_infty x h).elim
  obtain ⟨D₀, A, B, hD₀, hLD₀, hD₀Z, hub, hvb, -, hDe, hAc, hBc, -, -, hAL, hBL, hLA, hLB,
    ⟨p, hpD, hpA⟩, -⟩ := exists_edge_lens isClosedSurface_sphere hL' hne hZ' hLZ'
  have hD₀c : D₀ ⊆ range c := by
    intro q hq
    induction q using OnePoint.rec with
    | infty =>
      have := hD₀Z ⟨hq, Or.inr rfl⟩
      rcases this with h | h
      · exact (OnePoint.coe_ne_infty _ h.symm).elim
      · exact (OnePoint.coe_ne_infty _ (mem_singleton_iff.mp h).symm).elim
    | coe x => exact ⟨x, rfl⟩
  have hrD := hrcont.mono hD₀c
  have hcD : ContinuousOn c (r '' D₀) := hc.continuous.continuousOn
  have hleft : LeftInvOn c r D₀ := fun q hq => hcr q (hD₀c hq)
  obtain ⟨hD, hDb⟩ := hD₀.image hrD hcD hleft
  have hLA' : c '' L \ {c u, c v} ⊆ closure A ∩ closure B := fun x hx => ⟨hLA hx.1, hLB hx.1⟩
  have hdiffc := hL'.isPreconnected_diff
  have hcl := hL'.subset_closure_diff
  have hnonempty : (c '' L \ {c u, c v}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hcl
    exact hcl hL'.left_mem
  have hAL₀ : IsPreconnected (A ∪ (c '' L \ {c u, c v})) :=
    hAc.subset_closure subset_union_left (union_subset subset_closure fun x hx => hLA hx.1)
  have hBL₀ : IsPreconnected (B ∪ (c '' L \ {c u, c v})) :=
    hBc.subset_closure subset_union_left (union_subset subset_closure fun x hx => hLB hx.1)
  have hun : IsPreconnected ((A ∪ (c '' L \ {c u, c v})) ∪ (B ∪ (c '' L \ {c u, c v}))) := by
    obtain ⟨w, hw⟩ := hnonempty
    exact IsPreconnected.union w (Or.inr hw) (Or.inr hw) hAL₀ hBL₀
  have hset : (A ∪ (c '' L \ {c u, c v})) ∪ (B ∪ (c '' L \ {c u, c v})) = D₀ \ {c u, c v} := by
    have huL : c u ∈ c '' L := hL'.left_mem
    have hvL : c v ∈ c '' L := hL'.right_mem
    ext x
    constructor
    · rintro ((h | h) | (h | h))
      · refine ⟨hDe ▸ Or.inl (Or.inl h), ?_⟩
        rintro (rfl | rfl)
        · exact disjoint_left.mp hAL h huL
        · exact disjoint_left.mp hAL h hvL
      · exact ⟨hDe ▸ Or.inr h.1, h.2⟩
      · refine ⟨hDe ▸ Or.inl (Or.inr h), ?_⟩
        rintro (rfl | rfl)
        · exact disjoint_left.mp hBL h huL
        · exact disjoint_left.mp hBL h hvL
      · exact ⟨hDe ▸ Or.inr h.1, h.2⟩
    · rintro ⟨hx, hn⟩
      rw [hDe] at hx
      rcases hx with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨h, hn⟩)
  rw [hset] at hun
  have hru : r (c u) = u := hrc u
  have hrv : r (c v) = v := hrc v
  have himg : r '' (D₀ \ {c u, c v}) = r '' D₀ \ {u, v} := by
    ext x
    constructor
    · rintro ⟨q, ⟨hq, hn⟩, rfl⟩
      refine ⟨⟨q, hq, rfl⟩, ?_⟩
      rintro (h | h)
      · exact hn (Or.inl (by rw [← hcr q (hD₀c hq), h]))
      · exact hn (Or.inr (by rw [← hcr q (hD₀c hq), h]; rfl))
    · rintro ⟨⟨q, hq, rfl⟩, hn⟩
      refine ⟨q, ⟨hq, ?_⟩, rfl⟩
      rintro (rfl | rfl)
      · exact hn (Or.inl hru)
      · exact hn (Or.inr hrv)
  have hprange : range p ⊆ range c := hpD.trans hD₀c
  have hγ : Continuous fun t : I => r (p t) := by
    refine hrcont.comp_continuous p.continuous fun t => hprange ⟨t, rfl⟩
  obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path hγ (by
    simp only [Path.source, Path.target, hru, hrv]
    exact huv)
  simp only [Path.source, hru] at he0
  simp only [Path.target, hrv] at he1
  have hK : IsLineWithEnds (range e) u v := by
    have := IsArcMap.isLineWithEnds (⟨hec, hei⟩ : IsArcMap e)
    rwa [he0, he1] at this
  refine ⟨r '' D₀, range e, hD, ?_, ?_, ?_, ?_, ?_, hK, ?_, ?_⟩
  · intro x hx
    exact ⟨c x, hLD₀ ⟨x, hx, rfl⟩, hrc x⟩
  · rintro _ ⟨⟨q, hq, rfl⟩, hz⟩
    have hq' : q ∈ Z' := Or.inl ⟨_, hz, hcr q (hD₀c hq)⟩
    rcases hD₀Z ⟨hq, hq'⟩ with rfl | rfl
    · exact Or.inl hru
    · exact Or.inr hrv
  · rw [hDb]
    exact ⟨c u, hub, hru⟩
  · rw [hDb]
    exact ⟨c v, hvb, hrv⟩
  · rw [← himg]
    exact hun.image r (hrD.mono sdiff_subset)
  · intro x hx
    obtain ⟨t, rfl⟩ := her hx
    exact ⟨p t, hpD ⟨t, rfl⟩, rfl⟩
  · rw [disjoint_left]
    rintro x ⟨hx, hn⟩ hxL
    obtain ⟨t, rfl⟩ := her hx
    have ht0 : t ≠ 0 := fun h => hn (Or.inl (by change r (p t) = u; rw [h, Path.source]; exact hru))
    have ht1 : t ≠ 1 := fun h => hn (Or.inr (by change r (p t) = v; rw [h, Path.target]; exact hrv))
    have hA := hpA t (unitInterval.pos_iff_ne_zero.mpr ht0) (unitInterval.lt_one_iff_ne_one.mpr ht1)
    refine disjoint_left.mp hAL hA ⟨_, hxL, ?_⟩
    exact hcr _ (hprange ⟨t, rfl⟩)

/-- In a disc, at any point `x`, there is an `O`-arc through `x` as close to `x` as we like which
otherwise stays off the boundary of the disc. -/
theorem exists_oArc_in_disc {S : Type*} [TopologicalSpace S] [T2Space S] {D W : Set S}
    (hD : IsClosedDisc D) {x : S} (hx : x ∈ D) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ F : Set S, IsOArc F ∧ x ∈ F ∧ F ⊆ D ∩ W ∧ F \ {x} ⊆ D \ discBd D := by
  obtain ⟨h, g, cc⟩ := hD.exists_isChart
  let w : ℂ := h x
  have hw : w ∈ Metric.closedBall (0 : ℂ) 1 := cc.hm hx
  have hgw : g w = x := cc.gh hx
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, dist z w < ε → g z ∈ W := by
    have := (cc.gc w hw).preimage_mem_nhdsWithin (hW.mem_nhds (hgw ▸ hxW))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp this
    exact ⟨ε, hε, fun z hz hd => hsub ⟨hd, hz⟩⟩
  obtain ⟨F₀, hF₀, hwF, hsubB, hsph, hnear⟩ : ∃ F₀ : Set ℂ, IsOArc F₀ ∧ w ∈ F₀ ∧
      F₀ ⊆ Metric.closedBall (0 : ℂ) 1 ∧ F₀ ∩ Metric.sphere (0 : ℂ) 1 ⊆ {w} ∧
      ∀ z ∈ F₀, dist z w < ε := by
    by_cases hw1 : ‖w‖ = 1
    · have hws : w ∈ Metric.sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hw1
      let ρ : ℝ := min (ε / 3) (1 / 2)
      have hρ : 0 < ρ := lt_min (by linarith) (by norm_num)
      have hρ1 : ρ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hρε : ρ ≤ ε / 3 := min_le_left _ _
      refine ⟨loopCircle w ρ, isOArc_loopCircle w hρ, mem_loopCircle_self hws ρ,
        loopCircle_subset_closedBall hws hρ hρ1, ?_, ?_⟩
      · rw [loopCircle_inter_sphere hws hρ hρ1]
      · rintro _ ⟨c, rfl⟩
        have heq : (1 - (ρ : ℂ)) * w + (ρ : ℂ) * (c : ℂ) - w = (ρ : ℂ) * ((c : ℂ) - w) := by ring
        rw [dist_eq_norm]
        simp only [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
        have : ‖(c : ℂ) - w‖ ≤ 2 := by
          calc ‖(c : ℂ) - w‖ ≤ ‖(c : ℂ)‖ + ‖w‖ := norm_sub_le _ _
            _ = 2 := by rw [Circle.norm_coe, hw1]; norm_num
        nlinarith
    · have hlt : ‖w‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp hw) hw1
      let ρ : ℝ := min (ε / 3) ((1 - ‖w‖) / 3)
      have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
      have hρ1 : ρ ≤ (1 - ‖w‖) / 3 := min_le_right _ _
      have hρε : ρ ≤ ε / 3 := min_le_left _ _
      let m : Circle → ℂ := fun c => w + (ρ : ℂ) + (ρ : ℂ) * (c : ℂ)
      have hmc : Continuous m := by fun_prop
      have hmi : Injective m := by
        intro c c' hcc
        have h₁ : (ρ : ℂ) * (c : ℂ) = (ρ : ℂ) * (c' : ℂ) := add_left_cancel hcc
        have h₂ : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
        exact Circle.ext (mul_left_cancel₀ h₂ h₁)
      have hmn : ∀ c, ‖m c - w‖ ≤ 2 * ρ := by
        intro c
        have heq : m c - w = (ρ : ℂ) + (ρ : ℂ) * (c : ℂ) := by simp only [m]; ring
        rw [heq]
        calc ‖(ρ : ℂ) + (ρ : ℂ) * (c : ℂ)‖ ≤ ‖(ρ : ℂ)‖ + ‖(ρ : ℂ) * (c : ℂ)‖ := norm_add_le _ _
          _ = 2 * ρ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
              Circle.norm_coe]
            ring
      have hmb : ∀ c, ‖m c‖ < 1 := by
        intro c
        have h₁ : ‖m c‖ ≤ ‖m c - w‖ + ‖w‖ := by
          simpa using norm_add_le (m c - w) w
        linarith [hmn c]
      have hw0 : ∃ c : Circle, m c = w := by
        refine ⟨Circle.exp Real.pi, ?_⟩
        simp only [m, Circle.coe_exp, Complex.exp_pi_mul_I]
        ring
      obtain ⟨c₀, hc₀⟩ := hw0
      refine ⟨range m, ⟨(hmc.isClosedEmbedding hmi).isEmbedding.toHomeomorph⟩, ⟨c₀, hc₀⟩, ?_, ?_,
        ?_⟩
      · rintro _ ⟨c, rfl⟩
        exact mem_closedBall_zero_iff.mpr (hmb c).le
      · rintro _ ⟨⟨c, rfl⟩, hs⟩
        exact absurd (mem_sphere_zero_iff_norm.mp hs) (hmb c).ne
      · rintro _ ⟨c, rfl⟩
        rw [dist_eq_norm]
        linarith [hmn c]
  obtain ⟨ψ⟩ := hF₀
  have hgF : ContinuousOn g F₀ := cc.gc.mono hsubB
  have hinj : InjOn g F₀ := cc.hg.injOn.mono hsubB
  let m : Circle → S := fun c => g (ψ c).1
  have hmc : Continuous m :=
    hgF.comp_continuous (continuous_subtype_val.comp ψ.continuous) fun c => (ψ c).2
  have hmi : Injective m := fun c c' hcc =>
    ψ.injective (Subtype.ext (hinj (ψ c).2 (ψ c').2 hcc))
  have hrange : range m = g '' F₀ := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, (ψ c).2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ψ.symm ⟨z, hz⟩, by simp [m]⟩
  refine ⟨g '' F₀, ?_, ⟨w, hwF, hgw⟩, ?_, ?_⟩
  · rw [← hrange]
    exact ⟨(hmc.isClosedEmbedding hmi).isEmbedding.toHomeomorph⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨cc.gm (hsubB hz), hball z (hsubB hz) (hnear z hz)⟩
  · rintro _ ⟨⟨z, hz, rfl⟩, hne⟩
    refine ⟨cc.gm (hsubB hz), fun hb => hne ?_⟩
    have hzs : z ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [← cc.bd]
      exact ⟨g z, hb, cc.hg (hsubB hz)⟩
    rw [mem_singleton_iff.mp (hsph ⟨hz, hzs⟩)]
    exact hgw

/-- The boundary of a closed set in the plane. -/
theorem subBd_eq_of_isClosed {S : Type*} [TopologicalSpace S] {X : Set S} (h : IsClosed X) :
    subBd X = X \ interior X := by
  rw [subBd, h.closure_eq, ← compl_eq_univ_sdiff, closure_compl]
  rfl

/-- A connected set off both boundaries that meets the region between them stays in it. -/
theorem subset_region_of_isPreconnected {X X₀ T : Set EuclideanPlane} (hX : IsClosed X)
    (hX₀ : IsClosed X₀) (hT : IsPreconnected T) (hb : Disjoint T (subBd X ∪ subBd X₀)) {y :
      EuclideanPlane}
    (hy : y ∈ T) (hyr : y ∈ interior X \ X₀) : T ⊆ interior X \ X₀ := by
  have hY : IsOpen (interior X \ X₀) := isOpen_interior.sdiff hX₀
  have hW : IsOpen (Xᶜ ∪ interior X₀) := hX.isOpen_compl.union isOpen_interior
  refine hT.subset_left_of_subset_union hY hW ?_ ?_ ⟨y, hy, hyr⟩
  · rw [disjoint_left]
    rintro x ⟨hx, hx₀⟩ (h | h)
    · exact h (interior_subset hx)
    · exact hx₀ (interior_subset h)
  · intro x hx
    have hn : x ∉ subBd X ∪ subBd X₀ := disjoint_left.mp hb hx
    rw [subBd_eq_of_isClosed hX, subBd_eq_of_isClosed hX₀] at hn
    by_cases h₁ : x ∈ X
    · have h₂ : x ∈ interior X := by
        by_contra h
        exact hn (Or.inl ⟨h₁, h⟩)
      by_cases h₃ : x ∈ X₀
      · have h₄ : x ∈ interior X₀ := by
          by_contra h
          exact hn (Or.inr ⟨h₃, h⟩)
        exact Or.inr (Or.inr h₄)
      · exact Or.inl ⟨h₂, h₃⟩
    · exact Or.inr (Or.inl h₁)

/-- The region between the boundaries misses both boundaries. -/
theorem disjoint_region_subBd {X X₀ : Set EuclideanPlane} (hX : IsClosed X) (hX₀ : IsClosed X₀) :
    Disjoint (interior X \ X₀) (subBd X ∪ subBd X₀) := by
  rw [subBd_eq_of_isClosed hX, subBd_eq_of_isClosed hX₀, disjoint_left]
  rintro x ⟨hx, hx₀⟩ (h | h)
  · exact h.2 hx
  · exact hx₀ h.1

section Region

variable {D : Drawing EuclideanPlane} {X X₀ : Set EuclideanPlane}

theorem exists_edge_of_mem' {x : EuclideanPlane} (hx : x ∈ D.U) (hxV : x ∉ D.V) :
    ∃ e ∈ D.E, x ∈ e := by
  have hxF : x ∈ D.U \ D.V := ⟨hx, hxV⟩
  refine ⟨pathComponentIn (D.U \ D.V) x, ⟨⟨x, mem_pathComponentIn_self hxF⟩,
    pathComponentIn_subset, isPathConnected_pathComponentIn hxF, ?_⟩,
    mem_pathComponentIn_self hxF⟩
  intro C hC hconn hsub
  exact subset_antisymm (hconn.subset_pathComponentIn (hsub (mem_pathComponentIn_self hxF)) hC) hsub

/-- Beside a part `L` of an edge there is a thin disc whose part off the ends of `L` lies in the
region between the two boundaries, and in it a line with the ends of `L` that is off the drawing. -/
theorem exists_lens_of_subline (hX : IsClosed X) (hX₀ : IsClosed X₀)
    (hU : D.U ⊆ X \ interior X₀) (hclean : D.U ∩ (subBd X ∪ subBd X₀) ⊆ D.V)
    {e : Set EuclideanPlane} (he : e ∈ D.E) {L : Set EuclideanPlane} {a b : EuclideanPlane}
    (hL : IsLineWithEnds L a b) (hab : a ≠ b) (hLe : L \ {a, b} ⊆ e)
    (hrest : IsClosed (closure e \ (L \ {a, b}))) :
    ∃ B K : Set EuclideanPlane, IsClosedDisc B ∧ a ∈ discBd B ∧ b ∈ discBd B ∧
      B \ {a, b} ⊆ interior X \ X₀ ∧ IsLineWithEnds K a b ∧ K ⊆ B ∧ Disjoint (K \ {a, b}) D.U := by
  classical
  have heV : e ⊆ D.U \ D.V := he.2.1
  let Zb : Set EuclideanPlane := subBd X ∪ subBd X₀
  have hZbc : IsClosed Zb := (isClosed_subBd X).union (isClosed_subBd X₀)
  let Z : Set EuclideanPlane :=
    (D.V ∪ ⋃ f ∈ D.E \ {e}, closure f) ∪ (closure e \ (L \ {a, b})) ∪ Zb
  have hZ : IsClosed Z := ((D.finite_V.isClosed.union ((D.finite_edges.subset
    sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)).union hrest).union hZbc
  have hoff : ∀ x ∈ L \ {a, b}, x ∉ Z := by
    intro x hx hxZ
    have hxe := hLe hx
    have hxU := (heV hxe).1
    have hxV := (heV hxe).2
    rcases hxZ with ((h | h) | h) | h
    · exact hxV h
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp h
      have hxf' : x ∈ f := D.closure_diff_V hf.1 ▸ ⟨hxf, hxV⟩
      have hu : IsPathConnected (f ∪ e) := hf.1.2.2.1.union he.2.2.1 ⟨x, hxf', hxe⟩
      have h₁ := hf.1.2.2.2 (f ∪ e) (union_subset hf.1.2.1 he.2.1) hu subset_union_left
      have h₂ := he.2.2.2 (f ∪ e) (union_subset hf.1.2.1 he.2.1) hu subset_union_right
      exact hf.2 (h₁.symm.trans h₂)
    · exact h.2 hx
    · exact hxV (hclean ⟨hxU, h⟩)
  have hLZ : L ∩ Z ⊆ {a, b} := by
    rintro x ⟨hxL, hxZ⟩
    by_contra hn
    exact hoff x ⟨hxL, hn⟩ hxZ
  have hUZ : D.U ⊆ Z ∪ (L \ {a, b}) := by
    intro x hx
    by_cases hxV : x ∈ D.V
    · exact Or.inl (Or.inl (Or.inl (Or.inl hxV)))
    obtain ⟨f, hf, hxf⟩ := exists_edge_of_mem' hx hxV
    by_cases hfe : f = e
    · by_cases hxL : x ∈ L \ {a, b}
      · exact Or.inr hxL
      · exact Or.inl (Or.inl (Or.inr ⟨subset_closure (hfe ▸ hxf), hxL⟩))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hxf⟩))))
  obtain ⟨B, K, hB, hLB, hBZ, haB, hbB, hconn, hK, hKB, hKL⟩ := exists_plane_lens hL hab hZ hLZ
  have hL₀ : (L \ {a, b}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have hcl := hL.subset_closure_diff
    rw [h, closure_empty] at hcl
    exact hcl hL.left_mem
  obtain ⟨y, hy⟩ := hL₀
  have hyr : y ∈ interior X \ X₀ := by
    have hyU := (heV (hLe hy)).1
    have hyV := (heV (hLe hy)).2
    have hyb : y ∉ Zb := fun h => hyV (hclean ⟨hyU, h⟩)
    have hyX := hU hyU
    change y ∉ subBd X ∪ subBd X₀ at hyb
    rw [subBd_eq_of_isClosed hX, subBd_eq_of_isClosed hX₀] at hyb
    refine ⟨by_contra fun h => hyb (Or.inl ⟨hyX.1, h⟩), fun h => hyb (Or.inr ⟨h, hyX.2⟩)⟩
  have hreg : B \ {a, b} ⊆ interior X \ X₀ := by
    refine subset_region_of_isPreconnected hX hX₀ hconn ?_ ⟨hLB hy.1, hy.2⟩ hyr
    rw [disjoint_left]
    rintro x ⟨hxB, hxn⟩ hxb
    exact hxn (hBZ ⟨hxB, Or.inr hxb⟩)
  refine ⟨B, K, hB, haB, hbB, hreg, hK, hKB, ?_⟩
  rw [disjoint_left]
  rintro x ⟨hxK, hxn⟩ hxU
  rcases hUZ hxU with h | h
  · exact hxn (hBZ ⟨hKB hxK, h⟩)
  · exact disjoint_left.mp hKL ⟨hxK, hxn⟩ h.1

/-- A line that is off the drawing except at its ends, and lies in the region between the two
boundaries, gives an `O`-arc at its first end with the same properties. -/
theorem exists_oArc_of_line (hX : IsClosed X) (hX₀ : IsClosed X₀)
    {K : Set EuclideanPlane} {a b : EuclideanPlane} (hK : IsLineWithEnds K a b)
    (hKr : K \ {a, b} ⊆ interior X \ X₀) (hKU : Disjoint (K \ {a, b}) D.U) :
    ∃ F : Set EuclideanPlane, IsOArc F ∧ a ∈ F ∧ F \ {a} ⊆ interior X \ X₀ ∧
      Disjoint (F \ {a}) D.U := by
  classical
  have hK₀ : (K \ {a, b}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have hcl := hK.subset_closure_diff
    rw [h, closure_empty] at hcl
    exact hcl hK.left_mem
  obtain ⟨z, hz⟩ := hK₀
  have hza : z ≠ a := fun h => hz.2 (Or.inl h)
  have hzb : z ≠ b := fun h => hz.2 (Or.inr h)
  obtain ⟨K₁, K₂, hK₁, hK₂, hu, hi⟩ := hK.split hz.1 hza hzb
  let Z : Set EuclideanPlane := D.U ∪ (subBd X ∪ subBd X₀)
  have hZ : IsClosed Z := D.isClosed_U.union ((isClosed_subBd X).union (isClosed_subBd X₀))
  have hoff : ∀ x ∈ K \ {a, b}, x ∉ Z := by
    rintro x hx (h | h)
    · exact disjoint_left.mp hKU hx h
    · exact disjoint_left.mp (disjoint_region_subBd hX hX₀) (hKr hx) h
  have hKsub : K₁ ⊆ K := hu ▸ subset_union_left
  have hbK₁ : ∀ x ∈ K₁, x = b → x = z := by
    rintro x hx rfl
    have : x ∈ K₁ ∩ K₂ := ⟨hx, hK₂.right_mem⟩
    rw [hi] at this
    exact this
  have hK₁Z : K₁ ∩ Z ⊆ {a, z} := by
    rintro x ⟨hx, hxZ⟩
    by_contra hn
    have hxa : x ≠ a := fun h => hn (Or.inl h)
    have hxz : x ≠ z := fun h => hn (Or.inr h)
    have hxb : x ≠ b := fun h => hxz (hbK₁ x hx h)
    exact hoff x ⟨hKsub hx, by rintro (h | h) <;> simp_all⟩ hxZ
  obtain ⟨B, -, hB, hK₁B, hBZ, haB, hzB, hconn, -⟩ :=
    exists_plane_lens hK₁ (Ne.symm hza) hZ hK₁Z
  have hK₁₀ : (K₁ \ {a, z}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have hcl := hK₁.subset_closure_diff
    rw [h, closure_empty] at hcl
    exact hcl hK₁.left_mem
  obtain ⟨y, hy⟩ := hK₁₀
  have hyb : y ≠ b := fun h => hy.2 (Or.inr (hbK₁ y hy.1 h))
  have hyr : y ∈ interior X \ X₀ :=
    hKr ⟨hKsub hy.1, by
      rintro (h | h)
      · exact hy.2 (Or.inl h)
      · exact hyb h⟩
  have hreg : B \ {a, z} ⊆ interior X \ X₀ := by
    refine subset_region_of_isPreconnected hX hX₀ hconn ?_ ⟨hK₁B hy.1, hy.2⟩ hyr
    rw [disjoint_left]
    rintro x ⟨hxB, hxn⟩ hxb
    exact hxn (hBZ ⟨hxB, Or.inr hxb⟩)
  obtain ⟨F, hF, haF, hFs, hFb⟩ := exists_oArc_in_disc hB (Surface.discBd_subset _ haB)
    (isOpen_compl_singleton (x := z)) (show a ∈ ({z} : Set EuclideanPlane)ᶜ from Ne.symm hza)
  have hmem : ∀ p ∈ F \ {a}, p ∈ B \ {a, z} := by
    intro p hp
    refine ⟨(hFs hp.1).1, ?_⟩
    rintro (h | h)
    · exact hp.2 h
    · exact (hFs hp.1).2 h
  refine ⟨F, hF, haF, fun p hp => hreg (hmem p hp), ?_⟩
  rw [disjoint_left]
  intro p hp hpU
  exact (hmem p hp).2 (hBZ ⟨(hmem p hp).1, Or.inl hpU⟩)

/-- A line parallel to an edge with two ends, off the drawing and in the region between the
boundaries. -/
theorem exists_parallel_line (hX : IsClosed X) (hX₀ : IsClosed X₀)
    (hU : D.U ⊆ X \ interior X₀) (hclean : D.U ∩ (subBd X ∪ subBd X₀) ⊆ D.V)
    {e : Set EuclideanPlane} (he : e ∈ D.E) {a b : EuclideanPlane} (hab : a ≠ b)
    (hcap : closure e ∩ D.V = {a, b}) :
    ∃ K : Set EuclideanPlane, IsLineWithEnds K a b ∧ K \ {a, b} ⊆ interior X \ X₀ ∧
      Disjoint (K \ {a, b}) D.U := by
  classical
  have hline : IsLineWithEnds (closure e) a b := by
    rcases D.edge_cond e he with ⟨u, v, -, hc, hL⟩ | ⟨u, hc, -⟩
    · have hpair : ({u, v} : Set EuclideanPlane) = {a, b} := hc.symm.trans hcap
      have hau : a ∈ ({u, v} : Set EuclideanPlane) := hpair ▸ Or.inl rfl
      have hbu : b ∈ ({u, v} : Set EuclideanPlane) := hpair ▸ Or.inr rfl
      rcases hau with rfl | rfl
      · rcases hbu with rfl | rfl
        · exact (hab rfl).elim
        · exact hL
      · rcases hbu with rfl | rfl
        · exact hL.symm
        · exact (hab rfl).elim
    · have ha : a ∈ ({u} : Set EuclideanPlane) := hc ▸ hcap ▸ Or.inl rfl
      have hb : b ∈ ({u} : Set EuclideanPlane) := hc ▸ hcap ▸ Or.inr rfl
      exact (hab (ha.trans hb.symm)).elim
  have hLe : closure e \ {a, b} ⊆ e := by
    rw [← hcap]
    rintro x ⟨hx, hn⟩
    exact D.closure_diff_V he ▸ ⟨hx, fun hV => hn ⟨hx, hV⟩⟩
  have hrest : IsClosed (closure e \ (closure e \ {a, b})) := by
    rw [sdiff_sdiff_right_self]
    exact isClosed_closure.inter ((finite_singleton b).insert a).isClosed
  obtain ⟨B, K, -, -, -, hreg, hK, hKB, hKU⟩ :=
    exists_lens_of_subline hX hX₀ hU hclean he hline hab hLe hrest
  exact ⟨K, hK, fun x hx => hreg ⟨hKB hx.1, hx.2⟩, hKU⟩

/-- At any vertex that lies on an edge there is an `O`-arc off the drawing and in the region. -/
theorem exists_oArc_of_edge (hX : IsClosed X) (hX₀ : IsClosed X₀)
    (hU : D.U ⊆ X \ interior X₀) (hclean : D.U ∩ (subBd X ∪ subBd X₀) ⊆ D.V)
    {e : Set EuclideanPlane} (he : e ∈ D.E) {a : EuclideanPlane} (ha : a ∈ closure e ∩ D.V) :
    ∃ F : Set EuclideanPlane, IsOArc F ∧ a ∈ F ∧ F \ {a} ⊆ interior X \ X₀ ∧
      Disjoint (F \ {a}) D.U := by
  classical
  rcases D.edge_cond e he with ⟨u, v, huv, hc, hL⟩ | ⟨u, hc, ⟨φ⟩⟩
  · have haV : a ∈ ({u, v} : Set EuclideanPlane) := hc ▸ ha
    rcases haV with rfl | rfl
    · obtain ⟨K, hK, hr, hd⟩ := exists_parallel_line hX hX₀ hU hclean he huv hc
      exact exists_oArc_of_line hX hX₀ hK hr hd
    · have hc' : closure e ∩ D.V = {a, u} := by rw [hc, pair_comm]
      obtain ⟨K, hK, hr, hd⟩ := exists_parallel_line hX hX₀ hU hclean he (Ne.symm huv) hc'
      exact exists_oArc_of_line hX hX₀ hK hr hd
  · have hau : a = u := by
      have : a ∈ ({u} : Set EuclideanPlane) := hc ▸ ha
      exact this
    subst hau
    obtain ⟨b, hb⟩ := he.1
    have hbV := (he.2.1 hb).2
    have hab : a ≠ b := fun h => hbV (h ▸ ha.2)
    obtain ⟨I₁, I₂, -, -, hd, hun, -, -, hl₁, hl₂⟩ := exists_open_arcs φ ha.1
      (subset_closure hb) hab
    have hI₁ : I₁ ⊆ closure e \ {a, b} := hun ▸ subset_union_left
    have hI₂ : I₂ ⊆ closure e \ {a, b} := hun ▸ subset_union_right
    have hL₀ : (I₁ ∪ {a, b}) \ {a, b} = I₁ := by
      ext x
      constructor
      · rintro ⟨h | h, hn⟩
        · exact h
        · exact (hn h).elim
      · intro h
        exact ⟨Or.inl h, (hI₁ h).2⟩
    have hrest : IsClosed (closure e \ I₁) := by
      have : closure e \ I₁ = I₂ ∪ {a, b} := by
        ext x
        constructor
        · rintro ⟨hx, hn⟩
          by_cases hxab : x ∈ ({a, b} : Set EuclideanPlane)
          · exact Or.inr hxab
          · have : x ∈ I₁ ∪ I₂ := hun ▸ ⟨hx, hxab⟩
            exact Or.inl (this.resolve_left hn)
        · rintro (h | rfl | rfl)
          · exact ⟨(hI₂ h).1, fun h' => disjoint_left.mp hd h' h⟩
          · exact ⟨ha.1, fun h' => (hI₁ h').2 (Or.inl rfl)⟩
          · exact ⟨subset_closure hb, fun h' => (hI₁ h').2 (Or.inr rfl)⟩
      rw [this]
      exact hl₂.isCompact.isClosed
    have hLe : (I₁ ∪ {a, b}) \ {a, b} ⊆ e := by
      rw [hL₀]
      intro x hx
      refine D.closure_diff_V he ▸ ⟨(hI₁ hx).1, fun hV => (hI₁ hx).2 (Or.inl ?_)⟩
      exact (hc ▸ (⟨(hI₁ hx).1, hV⟩ : x ∈ closure e ∩ D.V) : x ∈ ({a} : Set EuclideanPlane))
    obtain ⟨B, K, -, -, -, hreg, hK, hKB, hKU⟩ :=
      exists_lens_of_subline hX hX₀ hU hclean he hl₁ hab hLe (by rwa [hL₀])
    exact exists_oArc_of_line hX hX₀ hK (fun x hx => hreg ⟨hKB hx.1, hx.2⟩) hKU

/-- At a vertex with no edge, in `X` and off `X₀`, there is an `O`-arc off the drawing and in the
region. -/
theorem exists_oArc_of_isolated (hX : IsClosedDisc X) (hX₀ : IsClosed X₀) {a : EuclideanPlane}
    (haX : a ∈ X) (haX₀ : a ∉ X₀) (hno : ∀ e ∈ D.E, a ∉ closure e) :
    ∃ F : Set EuclideanPlane, IsOArc F ∧ a ∈ F ∧ F \ {a} ⊆ interior X \ X₀ ∧
      Disjoint (F \ {a}) D.U := by
  classical
  let R : Set EuclideanPlane := (D.V \ {a}) ∪ (⋃ e ∈ D.E, closure e) ∪ X₀
  have hR : IsClosed R := (((D.finite_V.subset sdiff_subset).isClosed.union
    (D.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure))).union hX₀
  have haR : a ∉ R := by
    rintro ((h | h) | h)
    · exact h.2 rfl
    · obtain ⟨e, he, hae⟩ := mem_iUnion₂.mp h
      exact hno e he hae
    · exact haX₀ h
  obtain ⟨F, hF, haF, hs, hb⟩ := exists_oArc_in_disc hX haX hR.isOpen_compl haR
  refine ⟨F, hF, haF, fun p hp => ⟨?_, fun h => (hs hp.1).2 (Or.inr h)⟩, ?_⟩
  · rw [interior_eq_discInt_plane hX]
    exact hb hp
  · rw [disjoint_left]
    intro p hp hpU
    refine (hs hp.1).2 ?_
    by_cases hpV : p ∈ D.V
    · exact Or.inl (Or.inl ⟨hpV, hp.2⟩)
    · obtain ⟨e, he, hpe⟩ := exists_edge_of_mem' hpU hpV
      exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hpe⟩))

end Region

end GraphMinor.GM09
