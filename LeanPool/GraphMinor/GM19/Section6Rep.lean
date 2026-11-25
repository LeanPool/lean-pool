/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Block
public import LeanPool.GraphMinor.GM19.Section6Walk
public import LeanPool.GraphMinor.GM19.Section8e
public import LeanPool.GraphMinor.GM19.Poles

/-!
# Graph Minors XIX, (6.7): a curve of `sk(Γ)` gives a walk of `Γ*`

The paper's proof of (6.7), page 342, ends with "The second claim is clear". Here is one way to see
that `rep(sk(Γ)) ≥ rep(Γ)`. Let `F` be a non-null-homotopic `O`-arc that meets `sk(Γ)` only in `m`
vertices. Then `F` is a closed curve made of `m` paths between vertices, each in a region of
`sk(Γ)`.
We replace each by a homotopic path of length 2 in `Γ*` (`segment_walk`), and we get a closed walk
of
`Γ*` of length at most `2m` that is not null-homotopic. So `Γ*` has a circuit that is not
null-homotopic
with at most `2m` edges (`exists_circuit_of_walk`).

If the region is a region of `Γ` in `Σ̂`, the path of length 2 goes through the vertex of `Γ*` in
the
region. The two paths are homotopic since the region together with one vertex is simply connected,
which
is `sector_homotopic`. If the region is inside the disc of an edge of size 3, we first move the path
across an edge of `sk(Γ)` on the boundary of the disc, into a region of `Γ` beside that edge.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

/-- The skeleton edge along a three-ended cell joining two of its vertices, with a point in
the open edge. -/
theorem exists_sk_boundary_with_point {S : Type}
    [TopologicalSpace S] [T2Space S] (Γ : Painting S) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.E)
    (h3c : (tilde c₀).ncard = 3) {u₀ v₀ : S}
    (hut : u₀ ∈ tilde c₀) (hvt : v₀ ∈ tilde c₀) (huv₀ : u₀ ≠ v₀) :
    ∃ f ∈ arcComponentsIn (Γ.skU \ Γ.V), f ⊆ discBd (closure c₀) ∧ f ⊆ c₀ ∧
      tilde f = {u₀, v₀} ∧ ∃ x ∈ f, x ∈ c₀ ∧ x ∉ Γ.V := by
  classical
  obtain ⟨hdisc, hT', -⟩ := Γ.isDisc_of_three hc₀ h3c
  have htil : ∀ {x₀ : S}, x₀ ∈ closure c₀ → x₀ ∈ Γ.V → x₀ ∈ tilde c₀ := fun hx hxV =>
    ⟨hx, fun h => Γ.disjoint_V hc₀ h hxV⟩
  have hu₀ : u₀ ∈ Γ.V := Γ.tilde_subset_V hc₀ hut
  have hv₀ : v₀ ∈ Γ.V := Γ.tilde_subset_V hc₀ hvt
  obtain ⟨w₀, hw₀, hwu, hwv⟩ : ∃ w₀ ∈ tilde c₀, w₀ ≠ u₀ ∧ w₀ ≠ v₀ := by
    by_contra hn
    push Not at hn
    have hsub : tilde c₀ ⊆ {u₀, v₀} := fun x hx => by
      by_cases hxu : x = u₀
      · exact .inl hxu
      · exact .inr (hn x hx hxu)
    have := ncard_le_ncard hsub (toFinite _)
    have h2 := ncard_pair huv₀
    omega
  have htri : tilde c₀ = {u₀, v₀, w₀} := by
    refine (eq_of_subset_of_ncard_le (s := {u₀, v₀, w₀}) ?_ ?_ (Γ.isDisc_of_three hc₀ h3c).2.2).symm
    · rintro x (rfl | rfl | rfl)
      · exact hut
      · exact hvt
      · exact hw₀
    · rw [h3c, ncard_eq_toFinset_card', Set.toFinset_insert, Set.toFinset_insert]
      simp [Finset.card_insert_of_notMem, huv₀, hwu.symm, hwv.symm]
  obtain ⟨A₁, A₂, hA₁, hA₂, hAU, hAI⟩ := hdisc.isOArc_discBd.lines (hT' hut) (hT' hvt) huv₀
  obtain ⟨A₀, hA₀, hAw, hAB⟩ : ∃ A₀, IsLineWithEnds A₀ u₀ v₀ ∧ w₀ ∉ A₀ ∧ A₀ ⊆ discBd (closure c₀)
    := by
    by_cases hw₁ : w₀ ∈ A₁
    · refine ⟨A₂, hA₂, fun hw₂ => ?_, hAU ▸ subset_union_right⟩
      have : w₀ ∈ A₁ ∩ A₂ := ⟨hw₁, hw₂⟩
      rw [hAI] at this
      rcases this with h | h
      · exact hwu h
      · exact hwv h
    · exact ⟨A₁, hA₁, hw₁, hAU ▸ subset_union_left⟩
  have hint₀ : ∀ {x}, x ∈ A₀ \ {u₀, v₀} → x ∈ c₀ ∧ x ∈ Γ.skU \ Γ.V := by
    intro x hx
    have hxB := hAB hx.1
    have hxcl : x ∈ closure c₀ := Surface.discBd_subset _ hxB
    have hxV : x ∉ Γ.V := fun h => by
      have h₁ := htil hxcl h
      rw [htri] at h₁
      rcases h₁ with h₁ | h₁ | h₁
      · exact hx.2 (.inl h₁)
      · exact hx.2 (.inr h₁)
      · exact hAw (h₁ ▸ hx.1)
    refine ⟨by_contra fun h => hxV (Γ.tilde_subset_V hc₀ ⟨hxcl, h⟩), ?_, hxV⟩
    exact Or.inr (mem_iUnion₂.2 ⟨c₀, ⟨hc₀, h3c⟩, hxB⟩)
  have hpc := isPathConnected_sdiff_pair hA₀
  obtain ⟨f, hf, hsubf⟩ := exists_arcComp_superset hpc fun x hx => (hint₀ hx).2
  obtain ⟨x₀, hx₀⟩ := hpc.nonempty
  have hx₀f := hsubf hx₀
  obtain ⟨p, q, hpq, ht, htV, hline⟩ := Γ.sk_line hf
  have hclf : A₀ ⊆ closure f := hA₀.subset_closure_diff.trans (closure_mono hsubf)
  have htf : ∀ {y}, y ∈ A₀ → y ∈ Γ.V → y ∈ tilde f := fun hy hyV =>
    ⟨hclf hy, fun h => (hf.2.1 h).2 hyV⟩
  have ht' : tilde f = {u₀, v₀} := by
    refine (eq_of_subset_of_ncard_le (s := {u₀, v₀}) ?_ ?_ (by rw [ht]; exact toFinite _)).symm
    · rintro y (rfl | rfl)
      · exact htf hA₀.left_mem hu₀
      · exact htf hA₀.right_mem hv₀
    · rw [ht, ncard_pair hpq, ncard_pair huv₀]
  rcases Γ.sk_cases hf with ⟨hfE, h2⟩ | ⟨c, hc, -, hfc, hfB⟩
  · have := arcComp_eq_of_mem hfE hc₀ hx₀f (hint₀ hx₀).1
    rw [this, h3c] at h2
    omega
  · obtain rfl := arcComp_eq_of_mem hc hc₀ (hfc hx₀f) (hint₀ hx₀).1
    exact ⟨f, hf, hfB, hfc, ht', x₀, hx₀f, (hint₀ hx₀).1, (hint₀ hx₀).2.2⟩

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}

omit [T2Space S] [T2Space Shat] in
/-- Each region of `sk(Γ)` in `Σ̂` is an open disc. -/
theorem sk_region_disc (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) {r : Set Shat} (hr : r ∈ D.R) : IsOpenDisc r := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  rcases hD.region_cases hr with hh | ⟨c₀, hc₀, h3c, hrs⟩
  · exact h3.hatRegions_isOpenDisc hS cap r hh
  · obtain ⟨hΔ, hint, hU⟩ := cell_facts hD hr hc₀ h3c rfl hrs
    have hdis : Disjoint (discInt (cap.emb '' closure c₀)) D.U :=
      disjoint_left.mpr fun x hx hxU => hx.2 (hU ⟨hx.1, hxU⟩)
    obtain ⟨y, hy⟩ := region_nonempty hr
    have hsub := subset_region hr hΔ.isPreconnected_discInt hdis (hint hy) hy
    rw [Subset.antisymm hint hsub]
    exact isOpenDisc_discInt hman hΔ

/-- An `O`-arc through a vertex `v` that otherwise lies in a region of `sk(Γ)` bounds a disc that
meets
`sk(Γ)` only at `v`. -/
theorem sk_pinch (hS : IsSurface S) (hD : IsSkHat cap Γ D) (h3 : Γ.IsInternallyThreeConnected)
    {r : Set Shat} (hr : r ∈ D.R) {v : Shat} (hv : v ∈ D.V) :
    ∀ F : Set Shat, IsOArc F → v ∈ F → v ∈ closure (F \ {v}) → F \ {v} ⊆ r →
      ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ D.U ⊆ {v} := by
  intro F hF hvF hcl hsub
  have hT := cap.isClosedSurface
  rcases hD.region_cases hr with hh | ⟨c₀, hc₀, h3c, hrs⟩
  · rw [hD.hV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    exact pinch hS hD h3 hh hv₀ hF hvF hcl hsub
  · obtain ⟨hΔ, hint, hU⟩ := cell_facts hD hr hc₀ h3c rfl hrs
    have hrΔ : closure r ⊆ cap.emb '' closure c₀ := closure_minimal hrs hΔ.isClosed
    refine pinch_of_cell hT hΔ hF (fun x hx ↦ ?_) (fun x hx ↦ hint (hsub hx)) hU
    by_cases hxv : x = v
    · exact hrΔ (closure_mono hsub (hxv ▸ hcl))
    · exact (hint (hsub ⟨hx, hxv⟩)).1

omit [T2Space S] [T2Space Shat] in
/-- `Γ*` has no loops. -/
theorem rad_loopFree (rad : RadialDrawing cap Γ) : LoopFree rad.G := by
  intro e he
  obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends he
  have hne : cap.emb v ≠ w := fun h => hw.2 (h ▸ mem_image_of_mem _ hv)
  exact ⟨_, _, hne, by rw [tilde_eq_inter_V rad.G he, hset], isLine_closure he hne hset⟩

theorem cancel_mid {X : Type} [TopologicalSpace X] {x y z w : X} (a : Path x y) (l : Path y z)
  (b : Path y w) :
    ((a.trans l).trans (b.symm.trans l).symm).Homotopic (a.trans b) := by
  rw [Path.trans_symm, Path.symm_symm]
  have h₁ := Path.Homotopic.trans_assoc a l (l.symm.trans b)
  have h₂ := (Path.Homotopic.trans_assoc l l.symm b).symm
  have h₃ := ((Path.Homotopic.trans_symm l).hcomp (Path.Homotopic.refl b)).trans
    (Path.Homotopic.refl_trans b)
  exact h₁.trans ((Path.Homotopic.refl a).hcomp (h₂.trans h₃))

/-- The start of a path off a closed set lies in the closure of the region. -/
theorem start_mem_closure {X : Type} [TopologicalSpace X] {u v : X} (g : Path u v) {r : Set X}
    (hg : ∀ t : 𝕀, 0 < t → t < 1 → g t ∈ r) : u ∈ closure r := by
  rw [_root_.mem_closure_iff]
  intro O hO huO
  obtain ⟨t, ht, hs⟩ := exists_time g.continuous hO (by simpa using huO)
  have h₀ : (0 : ℝ) < min t.1 (1 / 2) := lt_min ht (by norm_num)
  let s : 𝕀 := ⟨min t.1 (1 / 2), h₀.le, (min_le_right _ _).trans (by norm_num)⟩
  have hs₁ : s ≤ t := (show min t.1 (1 / 2) ≤ t.1 from min_le_left _ _)
  have hs₂ : s < 1 := by
    change min t.1 (1 / 2) < 1
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  exact ⟨g s, hs s hs₁, hg s h₀ hs₂⟩

theorem symm_mem {X : Type} [TopologicalSpace X] {u v : X} (g : Path u v) {r : Set X}
    (hg : ∀ t : 𝕀, 0 < t → t < 1 → g t ∈ r) : ∀ t : 𝕀, 0 < t → t < 1 → g.symm t ∈ r := by
  intro t h₀ h₁
  rw [Path.symm_apply]
  refine hg _ ?_ ?_
  · rw [unitInterval.pos_iff_ne_zero, Ne, unitInterval.symm_eq_zero]
    exact h₁.ne
  · rw [unitInterval.lt_one_iff_ne_one, Ne, unitInterval.symm_eq_one]
    exact h₀.ne'

/-- The time `1/2`. -/
noncomputable def half : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩

theorem half_pos : 0 < half := by
  change (0 : ℝ) < 1 / 2
  norm_num

theorem half_lt : half < 1 := by
  change (1 / 2 : ℝ) < 1
  norm_num

section Walks

variable (rad : RadialDrawing cap Γ)

omit [T2Space S] in
/-- A point of a step with an end `c` in `R*`, other than the other end, lies in the region of `c`.
-/
theorem step_mem' {a b : rad.G.V} (h : (rad.G.adj.induce rad.G.V).Adj a b) {x c : Shat}
    (hc : c ∈ rad.Rstar) (hset : ({a.1, b.1} : Set Shat) = {x, c}) (t : 𝕀)
    (ht : stepP (rad_loopFree rad) h t ≠ x) : stepP (rad_loopFree rad) h t ∈ rad.regionOf c := by
  have hl := rad_loopFree rad
  have hE := stepE_mem hl h
  have hset' : closure (stepE hl h) ∩ rad.G.V = {x, c} := by
    rw [← tilde_eq_inter_V rad.G hE, stepE_tilde, hset]
  have hsub := rad.edge_subset_region hE hc hset'
  have hy : stepP hl h t ∈ closure (stepE hl h) := by
    rw [← stepP_range]
    exact mem_range_self t
  by_cases hyV : stepP hl h t ∈ rad.G.V
  · have hy' : stepP hl h t ∈ closure (stepE hl h) ∩ rad.G.V := ⟨hy, hyV⟩
    rw [hset'] at hy'
    rcases hy' with hy' | hy'
    · exact absurd hy' ht
    · rw [show stepP hl h t = c from hy']
      exact mem_connectedComponentIn (connectedComponentIn_subset _ _ (rad.regionOf_mem hc).2)
  · exact hsub ((closure_edge_subset hE hy).resolve_right hyV)

omit [T2Space S] in
/-- A step that ends at a vertex of `R*` lies in the region of that vertex, after its start. -/
theorem step_mem {a b : rad.G.V} (h : (rad.G.adj.induce rad.G.V).Adj a b) (hb : b.1 ∈ rad.Rstar) :
    ∀ t : 𝕀, 0 < t → stepP (rad_loopFree rad) h t ∈ rad.regionOf b.1 := fun t ht =>
  step_mem' rad h hb rfl t fun he =>
    ht.ne' (stepP_injective (rad_loopFree rad) h (he.trans (stepP (rad_loopFree rad)
      h).source.symm))

omit [T2Space S] in
/-- A step that starts at a vertex of `R*`, run backwards, lies in the region of that vertex after
its
start. -/
theorem step_symm_mem {a b : rad.G.V} (h : (rad.G.adj.induce rad.G.V).Adj a b)
  (ha : a.1 ∈ rad.Rstar) :
    ∀ t : 𝕀, 0 < t → (stepP (rad_loopFree rad) h).symm t ∈ rad.regionOf a.1 := fun t ht => by
  change stepP (rad_loopFree rad) h (unitInterval.symm t) ∈ _
  refine step_mem' rad h ha (pair_comm _ _) _ fun he => ht.ne' ?_
  have := stepP_injective (rad_loopFree rad) h (he.trans (stepP (rad_loopFree rad) h).target.symm)
  exact unitInterval.symm_eq_one.mp this

omit [T2Space S] [T2Space Shat] in
/-- The vertex of `Γ*` in a region. -/
theorem exists_hub {r : Set Shat} (hr : r ∈ Γ.hatRegions cap) :
    ∃ c ∈ rad.Rstar, rad.regionOf c = r ∧ c ∈ r := by
  obtain ⟨c, ⟨hcr, hcV⟩, -⟩ := rad.isPreRadial.2.2.1 r hr
  obtain ⟨y, hy, rfl⟩ := hr
  have hc : c ∉ Γ.hatV cap := fun h => (connectedComponentIn_subset _ _ hcr)
    (image_mono Γ.V_subset h)
  exact ⟨c, ⟨hcV, hc⟩, (connectedComponentIn_eq hcr).symm, hcr⟩

variable [ConnectedSpace Shat] (hS : IsSurface S) (hD : IsSkHat cap Γ D)
  (h3 : Γ.IsInternallyThreeConnected) {γ : Set Shat → 𝕀 → Shat} (hγ : EdgePar D γ)
  (hval : ∀ v ∈ D.V, 2 ≤ Nat.card (halfEdges D γ v))

include hS hD h3 hγ hval

omit [ConnectedSpace Shat] in
/-- A path from a vertex to itself, otherwise in a region of `sk(Γ)`, is null-homotopic. -/
theorem segment_loop {ρ : Set Shat} (hρ : ρ ∈ D.R) {u : Shat} (hu : u ∈ D.V) (g : Path u u)
    (hg : ∀ t : 𝕀, 0 < t → t < 1 → g t ∈ ρ) : g.Homotopic (Path.refl u) := by
  obtain ⟨g₁, g₂, hg₀, hg₁, hg₂⟩ := path_split g half
  have h₁ : g₁.Homotopic g₂.symm := by
    refine sector_homotopic cap.isClosedSurface D hγ hu (hval u hu) hρ (sk_region_disc hS hD h3 hρ)
      (sk_pinch hS hD h3 hρ hu) g₁ g₂.symm (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨s, hs, he, hp⟩ := hg₁ t
      rw [he]
      exact hg s (hp ht half_pos) (lt_of_le_of_lt hs half_lt)
    · obtain ⟨s, hs, he, hp⟩ := hg₂ (unitInterval.symm t)
      change g₂ (unitInterval.symm t) ∈ ρ
      rw [he]
      refine hg s (lt_of_lt_of_le half_pos hs) (hp ?_ half_lt)
      rw [unitInterval.lt_one_iff_ne_one, Ne, unitInterval.symm_eq_one]
      exact ht.ne'
  exact hg₀.trans ((h₁.hcomp (Path.Homotopic.refl g₂)).trans (Path.Homotopic.symm_trans g₂))

omit [ConnectedSpace Shat] in
/-- **A path across a region of `Γ`.** It is homotopic to a walk of length 2 through the vertex of
`Γ*`
in the region. -/
theorem segment_hat {r : Set Shat} (hr : r ∈ Γ.hatRegions cap) {u v : Shat} (huV : u ∈ D.V)
    (hvV : v ∈ D.V) (huG : u ∈ rad.G.V) (hvG : v ∈ rad.G.V) (g : Path u v)
    (hg : ∀ t : 𝕀, 0 < t → t < 1 → g t ∈ r) :
    ∃ w : (rad.G.adj.induce rad.G.V).Walk ⟨u, huG⟩ ⟨v, hvG⟩, w.length ≤ 2 ∧
      g.Homotopic (walkP (rad_loopFree rad) w) := by
  have hl := rad_loopFree rad
  have hrD := hD.hatRegion_mem_R hr
  have hρd := sk_region_disc hS hD h3 hrD
  have h2 := h3.hatRegions_isOpenDisc hS cap
  obtain ⟨c, hcR, hcr, hc⟩ := exists_hub rad hr
  have huc : ∀ {x : Shat}, x ∈ D.V → x ≠ c := fun hx he =>
    region_subset hrD hc (he ▸ D.V_subset_U hx)
  have hspoke : ∀ {x : Shat} (hx : x ∈ D.V), x ∈ closure r → ∃ e ∈ rad.G.E, closure e ∩ rad.G.V
    = {x, c} := by
    intro x hx hxr
    rw [hD.hV] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    exact rad.exists_spoke hS h2 h3.1 hcR hx₀ (by rwa [hcr])
  have hadj : ∀ {x : Shat} (hx : x ∈ D.V) (hxG : x ∈ rad.G.V), x ∈ closure r →
      (rad.G.adj.induce rad.G.V).Adj ⟨x, hxG⟩ ⟨c, hcR.1⟩ := by
    intro x hx hxG hxr
    obtain ⟨e, he, hset⟩ := hspoke hx hxr
    have ht : tilde e = {x, c} := by rw [tilde_eq_inter_V rad.G he, hset]
    exact ⟨huc hx, hxG, hcR.1, e, he, by rw [ht]; exact .inl rfl, by rw [ht]; exact .inr rfl⟩
  have h₁ := hadj huV huG (start_mem_closure g hg)
  have h₂ := (hadj hvV hvG (start_mem_closure g.symm (symm_mem g hg))).symm
  obtain ⟨g₁, g₂, hg₀, hg₁, hg₂⟩ := path_split g half
  have hp : g half ∈ r := hg _ half_pos half_lt
  have hJ : JoinedIn r c (g half) := hρd.isPathConnected.joinedIn _ hc _ hp
  have hlam : ∀ t, hJ.somePath t ∈ r := hJ.somePath_mem
  have hs₁ : ∀ t : 𝕀, 0 < t → stepP hl h₁ t ∈ r := by
    rw [← hcr]
    exact step_mem rad h₁ hcR
  have hs₂ : ∀ t : 𝕀, 0 < t → (stepP hl h₂).symm t ∈ r := by
    rw [← hcr]
    exact step_symm_mem rad h₂ hcR
  have hh₁ : g₁.Homotopic ((stepP hl h₁).trans hJ.somePath) := by
    refine sector_homotopic cap.isClosedSurface D hγ huV (hval u huV) hrD hρd
      (sk_pinch hS hD h3 hrD huV) g₁ _ (fun t ht => ?_) (trans_mem_of_pos hs₁ hlam)
    obtain ⟨s, hs, he, hp⟩ := hg₁ t
    rw [he]
    exact hg s (hp ht half_pos) (lt_of_le_of_lt hs half_lt)
  have hh₂ : g₂.symm.Homotopic ((stepP hl h₂).symm.trans hJ.somePath) := by
    refine sector_homotopic cap.isClosedSurface D hγ hvV (hval v hvV) hrD hρd
      (sk_pinch hS hD h3 hrD hvV) g₂.symm _ (fun t ht => ?_) (trans_mem_of_pos hs₂ hlam)
    obtain ⟨s, hs, he, hp⟩ := hg₂ (unitInterval.symm t)
    change g₂ (unitInterval.symm t) ∈ r
    rw [he]
    refine hg s (lt_of_lt_of_le half_pos hs) (hp ?_ half_lt)
    rw [unitInterval.lt_one_iff_ne_one, Ne, unitInterval.symm_eq_one]
    exact ht.ne'
  refine ⟨.cons h₁ (.cons h₂ .nil), by simp, ?_⟩
  have hh₂' := hh₂.symm₂
  rw [Path.symm_symm] at hh₂'
  simp only [walkP]
  refine hg₀.trans (((hh₁.hcomp hh₂').trans (cancel_mid _ _ _)).trans ?_)
  exact (Path.Homotopic.refl _).hcomp (Path.Homotopic.trans_refl _).symm

omit [TopologicalSpace S] [T2Space S] [T2Space Shat] [ConnectedSpace Shat] hS hD h3 hγ hval in
private theorem homotopy_in_closed_cell
    {X : Type}
    {Y : Type}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {cap : IsCappedSurface X Y}
    {ρ : Set Y}
    {c₀ : Set X}
    (hrs : ρ ⊆ cap.emb '' closure c₀)
    (hC : IsClosedDisc (cap.emb '' closure c₀))
    (u₀ : X)
    (hu₁ : cap.emb u₀ ∈ cap.emb '' closure c₀)
    (v₀ : X)
    (hv₁ : cap.emb v₀ ∈ cap.emb '' closure c₀)
    (g : Path (cap.emb u₀) (cap.emb v₀))
    (hg : ∀ (t : 𝕀), 0 < t → t < 1 → g t ∈ ρ)
    (e : Set Y)
    (hLC : closure e ⊆ cap.emb '' closure c₀)
    (ε : Path (cap.emb u₀) (cap.emb v₀))
    (hεr : range ⇑ε ⊆ closure e) :
    g.Homotopic ε := by
  refine paths_homotopic_in_disc hC g ε ?_ (hεr.trans hLC)
  rintro _ ⟨t, rfl⟩
  by_cases h0 : t = 0
  · rw [h0, g.source]
    exact hu₁
  by_cases h1 : t = 1
  · rw [h1, g.target]
    exact hv₁
  exact hrs (hg t (unitInterval.pos_iff_ne_zero.mpr h0) (unitInterval.lt_one_iff_ne_one.mpr h1))

omit hγ hval in
omit [ConnectedSpace Shat] h3 in
/-- **A path across the disc of an edge of size 3.** It is homotopic to a path across a region of
`Γ`,
beside an edge of `sk(Γ)` on the boundary of the disc. -/
theorem segment_cell {ρ : Set Shat} (hρ : ρ ∈ D.R) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.E)
    (h3c : (tilde c₀).ncard = 3) (hrs : ρ ⊆ cap.emb '' closure c₀) {u v : Shat} (huV : u ∈ D.V)
    (hvV : v ∈ D.V) (huv : u ≠ v) (g : Path u v) (hg : ∀ t : 𝕀, 0 < t → t < 1 → g t ∈ ρ) :
    ∃ r ∈ Γ.hatRegions cap, ∃ g' : Path u v, g.Homotopic g' ∧ ∀ t : 𝕀, 0 < t → t < 1 → g' t ∈ r
      := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hinj := cap.isEmbedding.injective
  obtain ⟨hΔ, hint, hU⟩ := cell_facts hD hρ hc₀ h3c rfl hrs
  obtain ⟨hdisc, -, -⟩ := Γ.isDisc_of_three hc₀ h3c
  obtain ⟨hC, hbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
  have hclρ : closure ρ ⊆ cap.emb '' closure c₀ := closure_minimal hrs hΔ.isClosed
  have hu₁ := hclρ (start_mem_closure g hg)
  have hv₁ := hclρ (start_mem_closure g.symm (symm_mem g hg))
  have htil : ∀ {x₀ : S}, x₀ ∈ closure c₀ → x₀ ∈ Γ.V → x₀ ∈ tilde c₀ := fun hx hxV =>
    ⟨hx, fun h => Γ.disjoint_V hc₀ h hxV⟩
  rw [hD.hV] at huV hvV
  obtain ⟨u₀, hu₀, rfl⟩ := huV
  obtain ⟨v₀, hv₀, rfl⟩ := hvV
  have hu₂ : u₀ ∈ closure c₀ := by
    obtain ⟨x, hx, he⟩ := hu₁
    exact hinj he ▸ hx
  have hv₂ : v₀ ∈ closure c₀ := by
    obtain ⟨x, hx, he⟩ := hv₁
    exact hinj he ▸ hx
  have huv₀ : u₀ ≠ v₀ := fun h => huv (congrArg _ h)
  have hut := htil hu₂ hu₀
  have hvt := htil hv₂ hv₀
  obtain ⟨f, hf, hfb, hfc, ht', x₀, hx₀f, hx₀c, hx₀V⟩ :=
    exists_sk_boundary_with_point Γ hc₀ h3c hut hvt huv₀
  have htV : tilde f ⊆ Γ.V := by
    rw [ht']
    exact pair_subset hu₀ hv₀
  let e : Set Shat := cap.emb '' f
  have he : e ∈ D.E := hD.edge_iff.mpr ⟨f, hf, rfl⟩
  have hcle : closure e = cap.emb '' closure f := (cap.isClosedEmbedding hS).closure_image_eq f
  have hsetV : closure f ∩ Γ.V = {u₀, v₀} := by
    rw [← ht']
    ext y
    exact ⟨fun h => ⟨h.1, fun hc => (hf.2.1 hc).2 h.2⟩, fun h => ⟨h.1, htV h⟩⟩
  have hset : closure e ∩ D.V = {cap.emb u₀, cap.emb v₀} := by
    rw [hcle, hD.hV, ← image_inter hinj, hsetV, image_pair]
  have hL : IsLineWithEnds (closure e) (cap.emb u₀) (cap.emb v₀) := isLine_closure he huv hset
  have hLC : closure e ⊆ cap.emb '' closure c₀ :=
    closure_minimal (image_mono (hfc.trans subset_closure)) hΔ.isClosed
  have hLB : closure e ⊆ discBd (cap.emb '' closure c₀) := by
    rw [hbd, hcle]
    exact image_mono (closure_minimal hfb (isCompact_of_isOArc hdisc.isOArc_discBd).isClosed)
  let Z : Set Shat := D.V ∪ ⋃ f' ∈ D.E \ {e}, closure f'
  have hZ : IsClosed Z := D.finite_V.isClosed.union
    ((D.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  have hLZ : closure e ∩ Z ⊆ {cap.emb u₀, cap.emb v₀} := by
    rintro y ⟨hye, hyV | hyf⟩
    · rw [← hset]
      exact ⟨hye, hyV⟩
    · obtain ⟨f', hf', hyf'⟩ := mem_iUnion₂.mp hyf
      by_cases hyV : y ∈ D.V
      · rw [← hset]
        exact ⟨hye, hyV⟩
      · exact absurd (edge_eq_of_mem D hf'.1 he hyf' hye hyV) hf'.2
  have hUZ : D.U ⊆ closure e ∪ Z := fun y hy => by
    by_cases hyV : y ∈ D.V
    · exact .inr (.inl hyV)
    obtain ⟨f', hf', hyf'⟩ := exists_edge_of_mem D hy hyV
    by_cases hfe : f' = e
    · exact .inl (subset_closure (hfe ▸ hyf'))
    · exact .inr (.inr (mem_biUnion (x := f') ⟨hf', hfe⟩ (subset_closure hyf')))
  obtain ⟨D₀, A, B, hD₀, hLD, hDZ, -, -, hbL, hDe, hAc, hBc, hAn, hBn, hAL, hBL, hLA, hLB', hpA,
    hpB⟩ :=
    exists_edge_lens hT hL huv hZ hLZ
  have hside : ∀ Y : Set Shat, IsPreconnected Y → Y.Nonempty → Y ⊆ D₀ → Disjoint Y (closure e) →
      closure e ⊆ closure Y → (∃ r ∈ Γ.hatRegions cap, Y ⊆ r) ∨ Y ⊆ cap.emb '' closure c₀ := by
    intro Y hYc ⟨y₀, hy₀⟩ hYD hYL hLY
    have hYU : Disjoint Y D.U := disjoint_left.mpr fun y hy hyU => by
      rcases hUZ hyU with h | h
      · exact disjoint_left.mp hYL hy h
      · refine disjoint_left.mp hYL hy ?_
        rcases hDZ ⟨hYD hy, h⟩ with hm | hm
        · exact hm ▸ hL.left_mem
        · exact hm ▸ hL.right_mem
    obtain ⟨a, ha, hy₀a⟩ := exists_region_of_notMem (disjoint_left.mp hYU hy₀)
    have hYa := subset_region ha hYc hYU hy₀ hy₀a
    rcases hD.region_cases ha with hh | ⟨c', hc', h3', hac⟩
    · exact .inl ⟨a, hh, hYa⟩
    · refine .inr ?_
      obtain ⟨hΔ', -, -⟩ := cell_facts hD ha hc' h3' rfl hac
      have hm : cap.emb x₀ ∈ cap.emb '' closure c' :=
        closure_minimal (hYa.trans hac) hΔ'.isClosed (hLY (subset_closure
          (mem_image_of_mem _ hx₀f)))
      obtain ⟨z, hz, hze⟩ := hm
      obtain rfl := hinj hze
      have hzV : z ∉ Γ.V := hx₀V
      have hzc' : z ∈ c' := by_contra fun h => hzV (Γ.tilde_subset_V hc' ⟨hz, h⟩)
      obtain rfl := arcComp_eq_of_mem hc' hc₀ hzc' hx₀c
      exact hYa.trans hac
  have hAD : A ⊆ D₀ := by
    rw [hDe]
    exact subset_union_left.trans subset_union_left
  have hBD : B ⊆ D₀ := by
    rw [hDe]
    exact subset_union_right.trans subset_union_left
  have hboth : ¬ (A ⊆ cap.emb '' closure c₀ ∧ B ⊆ cap.emb '' closure c₀) := by
    rintro ⟨h₁, h₂⟩
    have hxe : cap.emb x₀ ∈ closure e := subset_closure (mem_image_of_mem _ hx₀f)
    have hxV : cap.emb x₀ ∉ D.V := by
      rw [hD.hV]
      rintro ⟨z, hz, hze⟩
      exact hx₀V (hinj hze ▸ hz)
    have hxb : cap.emb x₀ ∈ discInt D₀ := ⟨hLD hxe, fun hb => by
      have := hbL ⟨hb, hxe⟩
      rw [← hset] at this
      exact hxV this.2⟩
    have hsub : discInt D₀ ⊆ cap.emb '' closure c₀ := fun y hy => by
      have hy₁ := hy.1
      rw [hDe] at hy₁
      rcases hy₁ with (hy₁ | hy₁) | hy₁
      · exact h₁ hy₁
      · exact h₂ hy₁
      · exact hLC hy₁
    have hin : cap.emb x₀ ∈ interior (cap.emb '' closure c₀) :=
      mem_interior.mpr ⟨_, hsub, hD₀.isOpen_discInt hman, hxb⟩
    have hfr := hLB hxe
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hT hC] at hfr
    exact hfr.2 hin
  obtain ⟨f₂, f₀, f₁⟩ := id hL
  let ε : Path (cap.emb u₀) (cap.emb v₀) := ⟨⟨fun t => (f₂ t).1, by fun_prop⟩, f₀, f₁⟩
  have hεr : range ε ⊆ closure e := by
    rintro _ ⟨t, rfl⟩
    exact (f₂ t).2
  have hgC : g.Homotopic ε := by
    exact homotopy_in_closed_cell (cap := cap) (ρ := ρ) (c₀ := c₀) hrs hC
      u₀ hu₁ v₀ hv₁ g hg e hLC ε hεr
  have hfin : ∀ {Y : Set Shat}, (∃ r ∈ Γ.hatRegions cap, Y ⊆ r) →
      (∃ p : Path (cap.emb u₀) (cap.emb v₀), range p ⊆ D₀ ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ Y) →
      ∃ r ∈ Γ.hatRegions cap, ∃ g' : Path (cap.emb u₀) (cap.emb v₀), g.Homotopic g' ∧
        ∀ t : 𝕀, 0 < t → t < 1 → g' t ∈ r := by
    rintro Y ⟨r, hr, hYr⟩ ⟨p, hpD, hpY⟩
    exact ⟨r, hr, p, hgC.trans (paths_homotopic_in_disc hD₀ ε p (hεr.trans hLD) hpD),
      fun t h0 h1 => hYr (hpY t h0 h1)⟩
  by_cases hAh : A ⊆ cap.emb '' closure c₀
  · have hBh : ¬ B ⊆ cap.emb '' closure c₀ := fun h => hboth ⟨hAh, h⟩
    exact hfin ((hside B hBc hBn hBD hBL hLB').resolve_right hBh) hpB
  · exact hfin ((hside A hAc hAn hAD hAL hLA).resolve_right hAh) hpA

omit [ConnectedSpace Shat] in
/-- **A path across a region of `sk(Γ)`**, between two vertices, is homotopic to a walk of `Γ*` of
length at most 2. -/
theorem segment_walk {u v : Shat} (huV : u ∈ D.V) (hvV : v ∈ D.V) (huG : u ∈ rad.G.V)
    (hvG : v ∈ rad.G.V) (g : Path u v) (hg : ∀ t : 𝕀, 0 < t → t < 1 → g t ∉ D.U) :
    ∃ w : (rad.G.adj.induce rad.G.V).Walk ⟨u, huG⟩ ⟨v, hvG⟩, w.length ≤ 2 ∧
      g.Homotopic (walkP (rad_loopFree rad) w) := by
  have hlc : LocallyConnectedSpace Shat :=
    IsClosedSurface.locallyConnectedSpace cap.isClosedSurface
  let I : Set Shat := g '' Ioo 0 1
  have hIc : IsPreconnected I := by
    have : IsPreconnected (Ioo (0 : 𝕀) 1) := ordConnected_Ioo.isPreconnected
    exact this.image _ g.continuous.continuousOn
  have hIU : Disjoint I D.U := disjoint_left.mpr fun _ ⟨t, ht, he⟩ => he ▸ hg t ht.1 ht.2
  obtain ⟨ρ, hρ, hhalf⟩ := exists_region_of_notMem (hg half half_pos half_lt)
  have hIρ := subset_region hρ hIc hIU (mem_image_of_mem _ ⟨half_pos, half_lt⟩) hhalf
  have hgρ : ∀ t : 𝕀, 0 < t → t < 1 → g t ∈ ρ := fun t h0 h1 =>
    hIρ (mem_image_of_mem _ ⟨h0, h1⟩)
  by_cases huv : u = v
  · subst huv
    exact ⟨.nil, by simp, segment_loop hS hD h3 hγ hval hρ huV g hgρ⟩
  rcases hD.region_cases hρ with hh | ⟨c₀, hc₀, h3c, hrs⟩
  · exact segment_hat rad hS hD h3 hγ hval hh huV hvV huG hvG g hgρ
  · obtain ⟨r, hr, g', hh', hg'⟩ := segment_cell hS hD hρ hc₀ h3c hrs huV hvV huv g hgρ
    obtain ⟨w, hw, hhw⟩ := segment_hat rad hS hD h3 hγ hval hr huV hvV huG hvG g' hg'
    exact ⟨w, hw, hh'.trans hhw⟩

omit hS hD h3 hγ hval in
theorem circuit_of_closed {G : Drawing Shat} (hl : LoopFree G) {n : ℕ} {a b : G.V} (h : a = b)
    (w : (G.adj.induce G.V).Walk a b) (hlen : w.length ≤ n) (q : Path a.1 b.1)
    (hq : q.Homotopic (walkP hl w))
    (hnn : ¬ (q.cast rfl (congrArg Subtype.val h)).Homotopic (Path.refl _)) :
    ∃ C : Drawing Shat, C.IsCircuitOf G ∧ ¬ IsNullHomotopicOArc C.U ∧ C.E.ncard ≤ n := by
  subst h
  have e : q.cast rfl rfl = q := by
    ext
    rfl
  rw [e] at hnn
  exact exists_circuit_of_walk hl w hlen fun hc => hnn (hq.trans hc)

omit hS hD h3 hγ hval [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
theorem subP_self (f : C(𝕀, Shat)) (s : 𝕀) : subP f s s = Path.refl (f s) := by
  ext x
  change f (seg s s x) = f s
  congr 1
  ext
  simp only [seg]
  change (1 - x.1) * s.1 + x.1 * s.1 = s.1
  ring

/-- **A curve gives a circuit of `Γ*`.** An `O`-arc that is not null-homotopic and meets `sk(Γ)`
only in
`m` vertices gives a circuit of `Γ*` with at most `2m` edges that is not null-homotopic. -/
theorem exists_circuit_of_curve {F : Set Shat} (hF : IsOArc F) (hn : D.IsNormal F)
    (hnn : ¬ IsNullHomotopicOArc F) :
    ∃ C : Drawing Shat, C.IsCircuitOf rad.G ∧ ¬ IsNullHomotopicOArc C.U ∧
      C.E.ncard ≤ 2 * (F ∩ D.V).ncard := by
  classical
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hl := rad_loopFree rad
  have hDG : ∀ x ∈ D.V, x ∈ rad.G.V := fun x hx => rad.isPreRadial.2.1 (by
    rw [hD.hV] at hx
    exact hx)
  by_cases hne : (F ∩ D.V).Nonempty
  swap
  · exfalso
    obtain ⟨φ⟩ := id hF
    have hFU : Disjoint F D.U := disjoint_left.mpr fun x hx hxU => hne ⟨x, hx, hn ⟨hx, hxU⟩⟩
    have hFr : F = range fun z : Circle => (φ z).1 := by
      ext x
      constructor
      · intro hx
        exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
      · rintro ⟨z, rfl⟩
        exact (φ z).2
    have hFc : IsPreconnected F := by
      rw [hFr]
      exact (isPreconnected_range (by fun_prop))
    have hy := (φ 1).2
    obtain ⟨ρ, hρ, hyρ⟩ := exists_region_of_notMem (disjoint_left.mp hFU hy)
    have hsub := subset_region hρ hFc hFU hy hyρ
    obtain ⟨x, hx, H, -, h0, h1⟩ := (sk_region_disc hS hD h3 hρ).isSimplyConnectedSet.2
      ⟨fun z => (φ z).1, by fun_prop⟩ (by
        rintro _ ⟨z, rfl⟩
        exact hsub (φ z).2)
    exact hnn ⟨φ, x, mem_univ _, H, fun _ => mem_univ _, h0, h1⟩
  obtain ⟨a, ha, haV⟩ := hne
  obtain ⟨φ₀⟩ := id hF
  obtain ⟨z₀, hz₀⟩ := φ₀.surjective ⟨a, ha⟩
  let φ : Circle ≃ₜ F := (Homeomorph.mulLeft z₀).trans φ₀
  have hφ1 : (φ 1).1 = a := by
    change (φ₀ (z₀ * 1)).1 = a
    rw [mul_one, hz₀]
  let γ : C(Circle, Shat) := ⟨fun z => (φ z).1, by fun_prop⟩
  let f : C(𝕀, Shat) := γ.comp (arcParam 1)
  have hf0 : f 0 = a := by
    change γ (arcParam 1 0) = a
    rw [arcParam_zero]
    exact hφ1
  have hf1 : f 1 = a := by
    change γ (arcParam 1 1) = a
    rw [arcParam_one]
    exact hφ1
  have hfF : ∀ t, f t ∈ F := fun t => (φ _).2
  have hfeq : ∀ {s t : 𝕀}, f s = f t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := fun {s t} h =>
    arcParam_eq_iff 1 (φ.injective (Subtype.ext h))
  let T₀ : Set 𝕀 := {t | 0 < t ∧ f t ∈ D.V}
  have hinj : InjOn f T₀ := by
    intro s hs t ht he
    rcases hfeq he with h | ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h hs.1.ne'
    · exact absurd h ht.1.ne'
  have himg : f '' T₀ ⊆ F ∩ D.V := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hfF t, ht.2⟩
  have hVfin : (F ∩ D.V).Finite := D.finite_V.subset inter_subset_right
  have hT₀ : T₀.Finite := Set.Finite.of_finite_image (hVfin.subset himg) hinj
  have hcard : T₀.ncard ≤ (F ∩ D.V).ncard := by
    rw [← hinj.ncard_image]
    exact ncard_le_ncard himg hVfin
  have h0V : f 0 ∈ D.V := hf0 ▸ haV
  let a₀ : rad.G.V := ⟨f 0, hDG _ h0V⟩
  have key : ∀ (n : ℕ) (t : 𝕀) (ht : t ∈ T₀), {s ∈ T₀ | s ≤ t}.ncard ≤ n →
      ∃ w : (rad.G.adj.induce rad.G.V).Walk a₀ ⟨f t, hDG _ ht.2⟩, w.length ≤ 2 * n ∧
        (subP f 0 t).Homotopic (walkP hl w) := by
    intro n
    induction n with
    | zero =>
      intro t ht hc
      have hsub : {s ∈ T₀ | s ≤ t}.Finite := hT₀.subset fun _ h => h.1
      have := (ncard_eq_zero hsub).mp (Nat.le_zero.mp hc)
      exact absurd (show t ∈ {s ∈ T₀ | s ≤ t} from ⟨ht, le_rfl⟩) (this ▸ notMem_empty t)
    | succ n ih =>
      intro t ht hc
      have hprev : ∃ s₀ : 𝕀, s₀ < t ∧ (∃ hs₀ : f s₀ ∈ D.V, ∃ w₀ :
          (rad.G.adj.induce rad.G.V).Walk a₀ ⟨f s₀, hDG _ hs₀⟩, w₀.length ≤ 2 * n ∧
            (subP f 0 s₀).Homotopic (walkP hl w₀)) ∧ ∀ s, s₀ < s → s < t → f s ∉ D.V := by
        by_cases hS₀ : {s ∈ T₀ | s < t}.Nonempty
        · have hfin_lt : {s ∈ T₀ | s < t}.Finite := hT₀.subset fun _ hs => hs.1
          obtain ⟨s₀, hs₀, hmax⟩ := Set.exists_max_image _ id hfin_lt hS₀
          have hlt : {s ∈ T₀ | s ≤ s₀}.ncard < {s ∈ T₀ | s ≤ t}.ncard := by
            refine ncard_lt_ncard ⟨fun x hx => ⟨hx.1, hx.2.trans hs₀.2.le⟩, fun hsub => ?_⟩
              (hT₀.subset fun _ h => h.1)
            exact absurd (hsub ⟨ht, le_rfl⟩).2 (not_le.mpr hs₀.2)
          obtain ⟨w₀, hw₀, hh₀⟩ := ih s₀ hs₀.1 (by omega)
          exact ⟨s₀, hs₀.2, ⟨hs₀.1.2, w₀, hw₀, hh₀⟩, fun s h₁ h₂ hV =>
            absurd (hmax s ⟨⟨lt_of_le_of_lt (unitInterval.nonneg s₀) h₁ |>.trans_le le_rfl, hV⟩,
              h₂⟩)
              (not_le.mpr h₁)⟩
        · refine ⟨0, ht.1, ⟨h0V, .nil, by simp, ?_⟩, fun s h₁ h₂ hV => hS₀ ⟨s, ⟨h₁, hV⟩, h₂⟩⟩
          rw [subP_self]
          exact Path.Homotopic.refl _
      obtain ⟨s₀, hst, ⟨hs₀, w₀, hw₀, hh₀⟩, hnone⟩ := hprev
      have hseg : ∀ x : 𝕀, 0 < x → x < 1 → subP f s₀ t x ∉ D.U := by
        intro x h0 h1 hU
        have hx0 : 0 < x.1 := h0
        have hx1 : x.1 < 1 := h1
        have hst' : s₀.1 < t.1 := hst
        have hlo : s₀ < seg s₀ t x := by
          change s₀.1 < (1 - x.1) * s₀.1 + x.1 * t.1
          nlinarith
        have hhi : seg s₀ t x < t := by
          change (1 - x.1) * s₀.1 + x.1 * t.1 < t.1
          nlinarith
        exact hnone _ hlo hhi (hn ⟨hfF _, hU⟩)
      obtain ⟨w₂, hw₂, hh₂⟩ := segment_walk rad hS hD h3 hγ hval hs₀ ht.2 (hDG _ hs₀) (hDG _ ht.2)
        (subP f s₀ t) hseg
      refine ⟨w₀.append w₂, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_append]
        omega
      · exact (subP_trans f 0 s₀ t).trans ((hh₀.hcomp hh₂).trans (walkP_append hl w₀ w₂).symm)
  have h1T : (1 : 𝕀) ∈ T₀ := ⟨unitInterval.pos_iff_ne_zero.mpr one_ne_zero, hf1 ▸ haV⟩
  obtain ⟨w, hw, hhw⟩ := key _ 1 h1T le_rfl
  have hsub : {s ∈ T₀ | s ≤ (1 : 𝕀)} ⊆ T₀ := fun _ h => h.1
  have hle : {s ∈ T₀ | s ≤ (1 : 𝕀)}.ncard ≤ (F ∩ D.V).ncard :=
    (ncard_le_ncard hsub hT₀).trans hcard
  have hclosed : a₀ = (⟨f 1, hDG _ h1T.2⟩ : rad.G.V) := Subtype.ext (hf0.trans hf1.symm)
  refine circuit_of_closed hl hclosed w (hw.trans (Nat.mul_le_mul_left 2 hle)) _ hhw fun hc
    => hnn ?_
  have hv01 : f 0 = f 1 := hf0.trans hf1.symm
  have hγP : ∀ t, γ (arcParam 1 t) = ((subP f 0 1).cast rfl hv01) t := by
    intro t
    change f t = f (seg 0 1 t)
    congr 1
    ext
    change t.1 = (1 - t.1) * (0 : ℝ) + t.1 * 1
    ring
  exact ⟨φ, null_of_path_refl _ hγP hc⟩

/-- `rep(Γ) ≤ rep(sk(Γ))`, the inequality of (6.7) that the proof of (6.2) uses. -/
theorem rep_le_sk : Painting.rep rad ≤ D.rep := by
  refine le_sInf ?_
  rintro _ ⟨F, hF, hN, hnn, rfl⟩
  obtain ⟨C, hC, hCn, hle⟩ := exists_circuit_of_curve rad hS hD h3 hγ hval hF hN hnn
  have h₁ : Painting.rep rad ≤ ((C.E.ncard / 2 : ℕ) : ℕ∞) := sInf_le ⟨C, hC, hCn, rfl⟩
  refine h₁.trans ?_
  exact_mod_cast Nat.div_le_of_le_mul hle

end Walks

end GraphMinor.GM19
