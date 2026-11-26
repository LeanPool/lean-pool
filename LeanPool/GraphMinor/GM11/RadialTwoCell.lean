/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.GlueFaces
public import LeanPool.GraphMinor.GM11.RadialFacts

/-!
# A radial drawing is 2-cell

Graph Minors XI, Section 3 (page 75): "$\Gamma'$ is 2-cell". We prove this here for drawings.

Each region `p` of `H = Γ ∪ Γ'` lies in a region `r` of `Γ`, and `r` is an open disc. An `O`-arc in
`p`
bounds a closed disc in `r`. This disc holds no point of `Γ'`, since each edge of `Γ'` in `r`
reaches the
frontier of `r` (`face_isOpenDisc`). So `p` is an open disc, by `open_disc`.

A region of `Γ'` is an edge `e` of `Γ` with the two regions of `H` on the two sides of `e`
(`edge_two_faces`), and `theorem_glue_regions` shows that this is an open disc.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric

universe u

variable {S : Type u} [TopologicalSpace S] {Γ Γ' : Drawing S} [T2Space S] [ConnectedSpace S]
  (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
  (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')

include hrad hS

omit [T2Space S] [ConnectedSpace S] hrad in
/-- A region of a closed surface is not the whole surface, if it is an open disc. -/
theorem openDisc_ne_univ {r : Set S} (hr : IsOpenDisc r) : r ≠ univ := by
  rintro rfl
  obtain ⟨-, ⟨φ⟩⟩ := hr
  have hc : CompactSpace S := hS.1
  have h₁ : CompactSpace (univ : Set S) := isCompact_iff_compactSpace.mp isCompact_univ
  have h₂ : CompactSpace OpenUnitDisc := φ.symm.compactSpace
  have h₃ : IsCompact (OpenUnitDisc : Set EuclideanPlane) := isCompact_iff_compactSpace.mpr h₂
  have h₄ : IsClosed (OpenUnitDisc : Set EuclideanPlane) := h₃.isClosed
  have h₅ : IsClopen (OpenUnitDisc : Set EuclideanPlane) := ⟨h₄, isOpen_ball⟩
  have h₆ := h₅.eq_univ ⟨0, by simp [OpenUnitDisc]⟩
  obtain ⟨v, hv⟩ : ∃ v : EuclideanPlane, ‖v‖ = 2 := by
    have := exists_norm_eq EuclideanPlane (by norm_num : (0 : ℝ) ≤ 2)
    simpa using this
  have h₇ : v ∈ (OpenUnitDisc : Set EuclideanPlane) := h₆ ▸ mem_univ v
  have h₈ : ‖v‖ < 1 := by simpa [OpenUnitDisc] using h₇
  linarith

omit [T2Space S] [ConnectedSpace S] in
/-- Each edge of `Γ'` that meets `r` joins the vertex of `r` to a vertex off `r`. -/
theorem spoke_in_region {r s : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V)
    (hs : s ∈ Γ'.E) {y : S} (hys : y ∈ s) (hyr : y ∈ r) :
    c ∈ closure s ∧ ∃ v ∈ closure s, v ∉ r := by
  obtain ⟨v, hv, r', hr', w, hwr, hwV, hcap, hsubr⟩ := spoke_ends hrad hS hs
  have hr'r : r' = r := region_eq_of_mem hr' hr (hsubr hys) hyr
  subst hr'r
  have hwc : w = c := hub_unique hrad hr hc hcV hwr hwV
  have hmem : ∀ z ∈ ({v, w} : Set S), z ∈ closure s := fun z hz => by
    rw [← hcap] at hz
    exact hz.1
  refine ⟨hwc ▸ hmem w (by simp), v, hmem v (by simp), ?_⟩
  exact fun h => region_subset hr h (Γ.V_subset_U hv)

include hmax in
/-- **Each vertex of `Γ'` in a region of `Γ` has an edge of `Γ'`.** -/
theorem hub_has_spoke {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) :
    ∃ s ∈ Γ'.E, c ∈ closure s := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_cases hE : Γ.E.Nonempty
  · obtain ⟨x, hx, hxr⟩ := exists_vertex_at_region hS hE hr
    obtain ⟨h, hh, hcap⟩ := exists_spoke_at hrad hmax hS hE hr hc hcV hx hxr
    have : c ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
    exact ⟨h, hh, this.1⟩
  by_contra hno
  push Not at hno
  have hE₀ : Γ.E = ∅ := not_nonempty_iff_eq_empty.mp hE
  have hUV : Γ.U = Γ.V := by
    rw [Γ.U_eq, hE₀]
    simp
  have hrU : ∀ y ∈ r, y ∈ Γ'.U → y = c := by
    intro y hy hyU
    by_cases hyV : y ∈ Γ'.V
    · exact hub_unique hrad hr hc hcV hy hyV
    rw [Γ'.U_eq] at hyU
    rcases hyU with h | hyE
    · exact (hyV h).elim
    obtain ⟨g, hg, hyg'⟩ := mem_iUnion₂.mp hyE
    have hyg : y ∈ g := Γ'.closure_diff_V hg ▸ ⟨hyg', hyV⟩
    exact absurd (spoke_in_region hrad hS hr hc hcV hg hyg hy).1 (hno g hg)
  have hrd : IsOpenDisc r := hrad.1.2 r hr
  have hro := region_isOpen hr
  -- A vertex on the frontier of `r`.
  obtain ⟨x, hxfr⟩ : (frontier r).Nonempty := by
    by_contra hn
    have hcl : IsClopen r := isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    exact openDisc_ne_univ hS hrd (hcl.eq_univ ⟨c, hc⟩)
  have hxcl : x ∈ closure r := frontier_subset_closure hxfr
  have hxr : x ∉ r := fun h => by
    rw [hro.frontier_eq] at hxfr
    exact hxfr.2 h
  have hxV : x ∈ Γ.V := by
    rw [← hUV]
    by_contra hxU
    obtain ⟨r', hr', hxr'⟩ := exists_region_of_notMem hxU
    obtain ⟨y, hy', hy⟩ := mem_closure_iff.mp hxcl r' (region_isOpen hr') hxr'
    exact hxr (region_eq_of_mem hr' hr hy' hy ▸ hxr')
  have hcx : c ≠ x := fun h => hxr (h ▸ hc)
  -- A path from `x` into `r`.
  have hW : IsOpen (Γ.V \ {x})ᶜ := (Γ.finite_V.subset sdiff_subset).isClosed.isOpen_compl
  obtain ⟨U₀, h, g, hch, hU₀, hg0⟩ := (hS.2.2 x).exists_ballChart hW (fun h => h.2 rfl) one_pos
  obtain ⟨y, hyU, hyr⟩ := mem_closure_iff.mp hxcl U₀ hch.isOpen (hg0 ▸ hch.gm (by simp))
  have hzb : h y ∈ ball (0 : ℂ) 1 := hch.hm hyU
  have hgy : g (h y) = y := hch.gh hyU
  have htz : ∀ t : I, (t.1 : ℂ) * h y ∈ ball (0 : ℂ) 1 := fun t => by
    have hn : ‖h y‖ < 1 := by simpa using hzb
    have h₁ : |t.1| ≤ 1 := abs_le.mpr ⟨by linarith [t.2.1], t.2.2⟩
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (h y), abs_nonneg t.1]
  let g₁ : I → S := fun t => g ((t.1 : ℂ) * h y)
  have hg₁ : Continuous g₁ := hch.gc.comp_continuous (by fun_prop) htz
  have h₁0 : g₁ 0 = x := by simp [g₁, hg0]
  have h₁1 : g₁ 1 = y := by simp [g₁, hgy]
  have hzne : h y ≠ 0 := fun h0 => hxr (by
    have : y = x := by rw [← hgy, h0, hg0]
    exact this ▸ hyr)
  have hoff : ∀ t : I, 0 < t → g₁ t ∉ Γ.U := by
    intro t ht hU
    rw [hUV] at hU
    have hmem : g₁ t ∈ U₀ := hch.gm (htz t)
    have heq : g₁ t = x := by
      by_contra hn
      exact hU₀ hmem ⟨hU, hn⟩
    have h₂ : (t.1 : ℂ) * h y = 0 := by
      have h₃ := hch.hg (htz t)
      have h₄ := hch.hg (show (0 : ℂ) ∈ ball (0 : ℂ) 1 by simp)
      change h (g₁ t) = _ at h₃
      rw [heq, ← hg0, h₄] at h₃
      exact h₃.symm
    have h₃ : (t.1 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show (0 : ℝ) < t.1 from ht))
    exact (mul_ne_zero h₃ hzne) h₂
  have h₁ : ∀ t : I, 0 < t → g₁ t ∈ r := by
    have hconn : IsPreconnected (g₁ '' Ioi 0) := by
      refine IsPreconnected.image ?_ _ hg₁.continuousOn
      exact isPreconnected_Ioi
    have hdis : Disjoint (g₁ '' Ioi 0) Γ.U := by
      refine disjoint_left.mpr ?_
      rintro _ ⟨t, ht, rfl⟩
      exact hoff t ht
    have hsub := subset_region hr hconn hdis (x := y) ⟨1, unitInterval.pos_iff_ne_zero.mpr
      one_ne_zero, h₁1⟩ hyr
    exact fun t ht => hsub ⟨t, ht, rfl⟩
  have hrpath : IsPathConnected r := isPathConnected_of_isOpen hS hro
    (region_isPreconnected hr) ⟨c, hc⟩
  obtain ⟨u, hu, hui, hu0, hu1, hup, -⟩ := exists_chord_to_point hrpath hxr hc hg₁ h₁0 h₁
  have hline : IsLineWithEnds (range u) c x := by
    have := isLine_range hu hui
    rw [hu0, hu1] at this
    exact GraphMinor.GM11.IsLineWithEnds.symm this
  have hsubp : range u \ {c, x} ⊆ r := by
    rintro _ ⟨⟨t, rfl⟩, hn⟩
    exact hup t fun h => hn (Or.inr (by rw [h, hu0]; rfl))
  obtain ⟨s, hs, hcap, -⟩ := parallel_of_line hrad hmax hS hr hc hcV hxV hline hcx hsubp
    (disjoint_left.mpr fun z hz hzU => hz.2 (Or.inl (hrU z (hsubp hz) hzU)))
  have : c ∈ closure s ∩ Γ'.V := by rw [hcap]; simp
  exact hno s hs this.1

omit hrad hS [ConnectedSpace S] in
/-- A connected set that misses the boundary of a closed disc and has a point outside misses the
disc. -/
theorem disjoint_disc_of_outside (hman : ∀ x : S, IsManifoldPoint x) {Δ K : Set S}
  (hΔ : IsClosedDisc Δ)
    (hK : IsPreconnected K) (hKb : Disjoint K (discBd Δ)) {v : S} (hv : v ∈ K) (hvΔ : v ∉ Δ) :
    Disjoint K Δ := by
  refine disjoint_left.mpr fun x hxK hxΔ => ?_
  have hi : IsOpen (discInt Δ) := hΔ.isOpen_discInt hman
  have hc : IsOpen Δᶜ := hΔ.isClosed.isOpen_compl
  have hdis : Disjoint (discInt Δ) Δᶜ := disjoint_left.mpr fun y hy hy' => hy' hy.1
  have hsub : K ⊆ discInt Δ ∪ Δᶜ := fun y hy => by
    by_cases hyΔ : y ∈ Δ
    · exact Or.inl ⟨hyΔ, disjoint_left.mp hKb hy⟩
    · exact Or.inr hyΔ
  have hne : (K ∩ discInt Δ).Nonempty := ⟨x, hxK, hxΔ, disjoint_left.mp hKb hxK⟩
  exact hvΔ (hK.subset_left_of_subset_union hi hc hdis hsub hne hv).1

include hmax in
/-- **Each region of `Γ ∪ Γ'` is an open disc.** -/
theorem face_isOpenDisc {p : Set S} (hp : p ∈ (radialUnion hrad).R) : IsOpenDisc p := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨r, hr, hpr⟩ := exists_region_of_sub hrad hp
  have hrd : IsOpenDisc r := hrad.1.2 r hr
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  have hc' : c ∈ r := hc
  have hcV' : c ∈ Γ'.V := hcV
  refine isOpenDisc_of_bound hS (region_isOpen hp) ⟨region_nonempty hp, region_isPreconnected hp⟩
    (fun h => openDisc_ne_univ hS hrd (subset_antisymm (subset_univ _) (h ▸ hpr))) ?_
  intro F hFp hF
  obtain ⟨Δ, hΔr, hΔ, hb⟩ := exists_disc_in_openDisc hrd hF (hFp.trans hpr)
  have hFdis : Disjoint F (radialUnion hrad).U :=
    disjoint_left.mpr fun x hx hxU => region_subset hp (hFp hx) hxU
  -- Each spoke with a point in `r` misses `Δ`.
  have hspoke : ∀ s ∈ Γ'.E, (s ∩ r).Nonempty → Disjoint (closure s) Δ ∧ c ∈ closure s := by
    rintro s hs ⟨y, hys, hyr⟩
    obtain ⟨h₁, v, hv, hvr⟩ := spoke_in_region hrad hS hr hc' hcV' hs hys hyr
    have hconn : IsPreconnected (closure s) := by
      have : IsPreconnected s := hs.2.2.1.isConnected.isPreconnected
      exact this.closure
    have hKb : Disjoint (closure s) (discBd Δ) := by
      rw [hb]
      refine disjoint_right.mpr fun x hx hxs => ?_
      exact disjoint_left.mp hFdis hx (Or.inr (Γ'.closure_subset_U hs hxs))
    exact ⟨disjoint_disc_of_outside hman hΔ hconn hKb hv fun h => hvr (hΔr h), h₁⟩
  have hΔU : Disjoint Δ (radialUnion hrad).U := by
    refine disjoint_left.mpr fun x hx hxU => ?_
    have hxr := hΔr hx
    rcases hxU with h | h
    · exact region_subset hr hxr h
    by_cases hxV : x ∈ Γ'.V
    · have hxc : x = c := hub_unique hrad hr hc' hcV' hxr hxV
      obtain ⟨s, hs, hcs⟩ := hub_has_spoke hrad hS hmax hr hc' hcV'
      obtain ⟨z, hzc, hzs⟩ := mem_closure_iff.mp hcs r (region_isOpen hr) hc'
      exact disjoint_left.mp (hspoke s hs ⟨z, hzs, hzc⟩).1 hcs (hxc ▸ hx)
    · rw [Γ'.U_eq] at h
      rcases h with h | hyE
      · exact hxV h
      obtain ⟨g, hg, hxg'⟩ := mem_iUnion₂.mp hyE
      have hxg : x ∈ g := Γ'.closure_diff_V hg ▸ ⟨hxg', hxV⟩
      exact disjoint_left.mp (hspoke g hg ⟨x, hxg, hxr⟩).1 hxg' hx
  obtain ⟨z, hz⟩ : F.Nonempty := by
    obtain ⟨φ⟩ := hF
    exact ⟨_, (φ 1).2⟩
  have hconn : IsPreconnected Δ := by
    obtain ⟨h, g, c'⟩ := hΔ.exists_isChart
    rw [← c'.g_closedBall]
    exact (convex_closedBall _ _).isPreconnected.image _ c'.gc
  have hzΔ : z ∈ Δ := discBd_subset Δ (hb.symm.subset hz)
  exact ⟨Δ, subset_region hp hconn hΔU hzΔ (hFp hz), hΔ, hb⟩

include hmax in
/-- **An edge of `Γ` has exactly two regions of `Γ ∪ Γ'` beside it.** The proof compares the two
corners of `Γ ∪ Γ'` beside one end of `e`, and uses `hub_sides`, which says that a region has at
most
two spokes. -/
theorem exists_two_faces (hE : Γ.E.Nonempty) {e : Set S} (he : e ∈ Γ.E) :
    ∃ p ∈ (radialUnion hrad).R, ∃ q ∈ (radialUnion hrad).R, p ≠ q ∧ e ⊆ closure p ∧ e ⊆ closure q ∧
      ∀ p' ∈ (radialUnion hrad).R, e ⊆ closure p' → p' = p ∨ p' = q := by
  classical
  obtain ⟨y₀, hy₀⟩ := he.1
  have hne : Nonempty S := ⟨y₀⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  have hsec : ∀ x : Γ.V, ∃ next ρ P W Q τ, IsSectors (radialUnion hrad) γ x.1 next ρ P W Q τ :=
    fun x => exists_sectors hS _ hγ
      (by rw [radialUnion_V]; exact radial_V hrad x.2) (two_half_edges hrad hS hmax hE hγ x.2)
  choose next ρ P W Q τ hs using hsec
  have hcor : ∀ x, IsCorners (radialUnion hrad) γ x.1 (next x) (ρ x) := fun x =>
    IsSectors.corners (hs x)
  have hsurj : ∀ x, Function.Surjective (next x) := fun x => next_surjective (hcor x)
  have hsidecl : ∀ x i, i.1.1 ⊆ closure (ρ x i) := fun x i => by
    obtain ⟨l, hl⟩ := hsurj x i
    have := IsCorners.right (hcor x) l
    rwa [hl] at this
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he
  have hend : ∀ b, γ e (endOf b) ∈ Γ.V := fun b => by
    have hxU : γ e (endOf b) ∈ Γ.U := Γ.closure_subset_U he (end_mem_closure hγ heH b)
    have hxV' : γ e (endOf b) ∈ Γ'.V := by
      have := end_mem_V hγ heH b
      rwa [radialUnion_V] at this
    exact radial_inter hrad ▸ ⟨hxU, Γ'.V_subset_U hxV'⟩
  let x : Γ.V := ⟨_, hend false⟩
  let y : Γ.V := ⟨_, hend true⟩
  let i : halfEdges (radialUnion hrad) γ x.1 := ⟨(e, false), heH, rfl⟩
  let i' : halfEdges (radialUnion hrad) γ y.1 := ⟨(e, true), heH, rfl⟩
  obtain ⟨l, hl⟩ := hsurj x i
  have hli : (next x l).1.1 = e := by rw [hl]
  refine ⟨ρ x i, IsCorners.region (hcor x) i, ρ x l, IsCorners.region (hcor x) l, ?_,
    hsidecl x i, ?_, ?_⟩
  rotate_left
  · have := IsCorners.left (hcor x) l
    rwa [hli] at this
  · intro p' hp' hep'
    rcases IsCorners.sides (hcor x) l p' hp' (by rw [hli]; exact hep') with h | h
    · exact Or.inr h
    · rw [hl] at h
      exact Or.inl h
  -- Suppose that the two corners lie in one region `p`.
  intro hpq
  set p := ρ x l with hp_def
  have hpR : p ∈ (radialUnion hrad).R := IsCorners.region (hcor x) l
  have hip : i.1.1 ⊆ closure p := hpq ▸ hsidecl x i
  have hspoke₁ : (next x i).1.1 ∈ Γ'.E := by
    rcases corner_alternates hrad hS hmax hE hγ x.2 (hs x) i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact (edge_not_both hrad he h₁).elim
    · exact h₂
  have hspoke₂ : l.1.1 ∈ Γ'.E := by
    rcases corner_alternates hrad hS hmax hE hγ x.2 (hs x) l with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact h₁
    · exact (edge_not_both hrad he (by rw [← hli]; exact h₂)).elim
  have hcl₁ : (next x i).1.1 ⊆ closure p := by
    have := IsCorners.left (hcor x) i
    rwa [hpq] at this
  have hcl₂ : l.1.1 ⊆ closure p := hsidecl x l
  obtain ⟨r, hr, hpr⟩ := exists_region_of_sub hrad hpR
  obtain ⟨f, g, hf, hg, hfp, hgp, hall, hsides⟩ := hub_sides hrad hS hmax hE hr hpR hpr
  obtain ⟨φ, hφ, hφp, hadj⟩ := exists_adj hrad hS hmax hE hγ y.2 (hs y) i' he hpR hip
  have hadj₁ : IsAdj (next x) (ρ x) p (next x i) i := Or.inr ⟨rfl, hpq⟩
  have hadj₂ : IsAdj (next x) (ρ x) p l i := Or.inl ⟨hl, rfl⟩
  -- A half-edge of a spoke is determined by the spoke.
  have hsame : ∀ (u : Γ.V) (φ a : halfEdges (radialUnion hrad) γ u.1)
      (m : halfEdges (radialUnion hrad) γ x.1), a.1 = (e, true) → φ.1.1 ∈ Γ'.E → φ.1.1 = m.1.1 →
      IsAdj (next u) (ρ u) p φ a →
      ∃ a' : halfEdges (radialUnion hrad) γ x.1, a'.1 = (e, true) ∧ IsAdj (next x) (ρ x) p m a'
        := by
    intro u φ a m ha hk hkm hadj
    obtain ⟨x₀, φ₀, -, huniq⟩ := spoke_half_unique hrad hS hk hγ
    obtain ⟨e₁, e₂⟩ := huniq u φ rfl
    obtain ⟨e₃, e₄⟩ := huniq x m hkm.symm
    have hux : u = x := e₁.trans e₃.symm
    subst hux
    have hk' : φ = m := Subtype.ext (e₂.trans e₄.symm)
    subst hk'
    exact ⟨a, ha, hadj⟩
  have hyx : ∀ (a : halfEdges (radialUnion hrad) γ x.1), a.1 = (e, true) → a ≠ i := by
    intro a ha hai
    have := congrArg (fun z : halfEdges (radialUnion hrad) γ x.1 => z.1.2) hai
    simp [ha, i] at this
  by_cases hφeq : next x i = l
  · -- The spoke beside `i` is the same on both sides, so `p` is on both sides of this spoke.
    have hone : ∀ A ∈ (radialUnion hrad).R, l.1.1 ⊆ closure A → A = p := by
      intro A hA hAl
      rcases IsCorners.sides (hcor x) i A hA (by rw [hφeq]; exact hAl) with h | h
      · exact h.trans hpq
      · rw [hφeq] at h
        exact h
    by_cases hφl : φ.1.1 = l.1.1
    · obtain ⟨a, ha, hadj'⟩ := hsame y φ i' l rfl hφ hφl hadj
      rcases hadj' with ⟨h, -⟩ | ⟨h, -⟩
      · exact hyx a ha (h.symm.trans hl)
      · exact hyx a ha (IsCorners.inj (hcor x) (h.trans hφeq.symm))
    · have hfg : f ≠ g := by
        rintro rfl
        have h₁ := hall _ hspoke₂ hcl₂
        have h₂ := hall _ hφ hφp
        simp only [or_self] at h₁ h₂
        exact hφl (h₂.trans h₁.symm)
      have hsd := hsides.resolve_left hfg
      obtain ⟨A₁, hA₁, A₂, hA₂, hA, h₁, h₂⟩ := hsd _ (hall _ hspoke₂ hcl₂)
      exact hA ((hone A₁ hA₁ h₁).trans (hone A₂ hA₂ h₂).symm)
  · have hneq : (next x i).1.1 ≠ l.1.1 := by
      intro h
      obtain ⟨x₀, φ₀, -, huniq⟩ := spoke_half_unique hrad hS hspoke₁ hγ
      exact hφeq (Subtype.ext ((huniq x _ rfl).2.trans (huniq x l h.symm).2.symm))
    have hfg : f ≠ g := by
      rintro rfl
      have h₁ := hall _ hspoke₂ hcl₂
      have h₂ := hall _ hspoke₁ hcl₁
      simp only [or_self] at h₁ h₂
      exact hneq (h₂.trans h₁.symm)
    have hsd := hsides.resolve_left hfg
    have hcover : φ.1.1 = (next x i).1.1 ∨ φ.1.1 = l.1.1 := by
      rcases hall _ hφ hφp with h₀ | h₀ <;> rcases hall _ hspoke₁ hcl₁ with h₁ | h₁ <;>
        rcases hall _ hspoke₂ hcl₂ with h₂ | h₂
      all_goals first
        | exact Or.inl (h₀.trans h₁.symm)
        | exact Or.inr (h₀.trans h₂.symm)
        | exact (hneq (h₁.trans h₂.symm)).elim
    have key : ∀ m : halfEdges (radialUnion hrad) γ x.1, φ.1.1 = m.1.1 → m.1.1 ∈ Γ'.E →
        IsAdj (next x) (ρ x) p m i → False := by
      intro m hm hm' hadjm
      obtain ⟨a, ha, hadj'⟩ := hsame y φ i' m rfl hφ hm hadj
      obtain ⟨A₁, hA₁, A₂, hA₂, hA, h₁, h₂⟩ := hsd m.1.1 (hall _ hm' (hm ▸ hφp))
      exact hyx a ha (adj_unique (hcor x) hA₁ hA₂ hA h₁ h₂ hadj' hadjm)
    rcases hcover with h | h
    · exact key _ h hspoke₁ hadj₁
    · exact key _ h hspoke₂ hadj₂

include hmax in
/-- A region of `Γ'` is an edge of `Γ` with the two regions of `Γ ∪ Γ'` beside it. -/
theorem region_eq_two_faces (hE : Γ.E.Nonempty) {s e : Set S} (hs : s ∈ Γ'.R) (he : e ∈ Γ.E)
    (hes : e ⊆ s) :
    ∃ p ∈ (radialUnion hrad).R, ∃ q ∈ (radialUnion hrad).R, p ≠ q ∧ e ⊆ closure p ∧ e ⊆ closure q ∧
      s = p ∪ q ∪ e := by
  obtain ⟨p, hp, q, hq, hpq, hep, heq, hall⟩ := exists_two_faces hrad hS hmax hE he
  obtain ⟨y, hy⟩ := he.1
  refine ⟨p, hp, q, hq, hpq, hep, heq, subset_antisymm ?_ ?_⟩
  · intro x hx
    rcases region_eq_faceUnion hrad hS hmax hE hs he hes hx with h | h
    · exact Or.inr h
    · obtain ⟨p', ⟨hp', -, hc⟩, hxp'⟩ := mem_iUnion₂.mp h
      rcases hall p' hp' hc with rfl | rfl
      · exact Or.inl (Or.inl hxp')
      · exact Or.inl (Or.inr hxp')
  · refine union_subset (union_subset ?_ ?_) hes
    · exact region_sub_of_mem hrad hS hs hp (hep hy) (hes hy)
    · exact region_sub_of_mem hrad hS hs hq (heq hy) (hes hy)

include hmax in
/-- **Each region of a radial drawing of a 2-cell drawing is an open disc.** If `Γ` has an edge, a
region of `Γ'` is an edge of `Γ` with the two regions of `Γ ∪ Γ'` beside it, so
`theorem_glue_regions`
applies. If `Γ` has no edge, each region of `Γ'` is a region of `Γ ∪ Γ'`. -/
theorem radial_region_isOpenDisc {s : Set S} (hs : s ∈ Γ'.R) : IsOpenDisc s := by
  by_cases hE : Γ.E.Nonempty
  · obtain ⟨hex, -, -⟩ := regionFacts_of_radial hrad hS hmax hE
    obtain ⟨e, he, hes⟩ := hex s hs
    obtain ⟨p, hp, q, hq, hpq, hep, heq, heqs⟩ := region_eq_two_faces hrad hS hmax hE hs he hes
    rw [heqs]
    have heH : e ∈ (radialUnion hrad).E := by
      rw [radialUnion_E]
      exact Or.inl he
    exact theorem_glue_regions hS heH hp hq hpq (face_isOpenDisc hrad hS hmax hp)
      (face_isOpenDisc hrad hS hmax hq) hep heq
  · have hE₀ : Γ.E = ∅ := not_nonempty_iff_eq_empty.mp hE
    have hUU : (radialUnion hrad).U = Γ'.U := by
      apply subset_antisymm
      · rintro x (h | h)
        · rw [Γ.U_eq, hE₀] at h
          simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, union_empty] at h
          exact Γ'.V_subset_U (radial_V hrad h)
        · exact h
      · exact fun x h => Or.inr h
    have hsH : s ∈ (radialUnion hrad).R := by
      change s ∈ componentsIn (univ \ (radialUnion hrad).U)
      rw [hUU]
      exact hs
    exact face_isOpenDisc hrad hS hmax hsH

omit hrad hS in
/-- **A radial drawing of a 2-cell drawing is 2-cell.** Graph Minors XI, Section 3 (page 75). -/
theorem radial_isTwoCell_of_drawing (hS : IsClosedSurface S)
    (h : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') : Γ'.IsTwoCell := by
  have hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ' := ⟨h.1, h.2.1⟩
  exact ⟨inferInstance, fun _ hs => radial_region_isOpenDisc hrad hS h.2.2 hs⟩

end GraphMinor.GM11
