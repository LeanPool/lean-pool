/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section9c
public import LeanPool.GraphMinor.GM19.Section8d

/-!
# Graph Minors XIX, (9.2)

The new edge of an arm of a heart carries a patch on its march. There are finitely many patches on
a march of bounded length up to the names of the vertices, so these can be put into the
well-quasi-order that a well-behaved set of places lets us choose.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface
open GraphMinor.GM04 (Patchwork freePatch IsGrouping IsComponent)

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

/-- The adjacency of a grouping `δ`, read off by positions in the march `π`. -/
def marchAdj (π : List S) (δ : (⊤ : SimpleGraph S).Subgraph) : Set (ℕ × ℕ) :=
  {p | ∃ (h₁ : p.1 < π.length) (h₂ : p.2 < π.length), δ.Adj π[p.1] π[p.2]}

/-- A patch on the terms of a march, read off by positions in the march. -/
def marchPattern (π : List S) (Δ : GM04.Patch S) : Set (Set (ℕ × ℕ)) :=
  marchAdj π '' Δ.groupings

omit [TopologicalSpace S] in
/-- Two patches with the same pattern on marches of the same length correspond. -/
theorem mapsTo_of_pattern {π π' : List S} (_hπ : π.Nodup) (_hπ' : π'.Nodup)
    (hlen : π.length = π'.length) {Δ Δ' : GM04.Patch S} (hV : Δ.verts = {v | v ∈ π})
    (hV' : Δ'.verts = {v | v ∈ π'}) (h : marchPattern π Δ = marchPattern π' Δ') :
    MapsTo (GM04.marchMapSubgraph π π') Δ.groupings Δ'.groupings := by
  intro δ hδ
  obtain ⟨δ', hδ', hEq⟩ : marchAdj π δ ∈ marchPattern π' Δ' := h ▸ ⟨δ, hδ, rfl⟩
  have hδv : δ.verts = {v | v ∈ π} := (Δ.verts_eq δ hδ).trans hV
  have hδv' : δ'.verts = {v | v ∈ π'} := (Δ'.verts_eq δ' hδ').trans hV'
  have hval : GM04.marchMapSubgraph π π' δ = δ' := by
    ext y y'
    · constructor
      · rintro ⟨x, -, i, hi, hi', -, rfl⟩
        rw [hδv']
        exact List.getElem_mem hi'
      · intro hy
        rw [hδv'] at hy
        obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.1 hy
        have hi : i < π.length := hlen ▸ hi'
        refine ⟨π[i], ?_, i, hi, hi', rfl, rfl⟩
        rw [hδv]
        exact List.getElem_mem hi
    · constructor
      · rintro ⟨-, x₁, x₂, ⟨i, hi, hi', rfl, rfl⟩, ⟨j, hj, hj', rfl, rfl⟩, hadj⟩
        have hm : (i, j) ∈ marchAdj π' δ' := by
          rw [hEq]
          exact ⟨hi, hj, hadj⟩
        obtain ⟨hh₁, hh₂, hg⟩ := hm
        exact hg
      · intro hadj
        have hy : y ∈ δ'.verts := δ'.edge_vert hadj
        have hy' : y' ∈ δ'.verts := δ'.edge_vert hadj.symm
        rw [hδv'] at hy hy'
        obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.1 hy
        obtain ⟨j, hj', rfl⟩ := List.mem_iff_getElem.1 hy'
        have hm : (i, j) ∈ marchAdj π δ := by
          rw [← hEq]
          exact ⟨hi', hj', hadj⟩
        obtain ⟨hi, hj, hg⟩ := hm
        exact ⟨hadj.ne, _, _, ⟨i, hi, hi', rfl, rfl⟩, ⟨j, hj, hj', rfl, rfl⟩, hg⟩
  rw [← hval] at hδ'
  exact hδ'

/-- The finitely many values of `marchPattern` on marches shorter than `θ`. -/
def patternBox (θ : ℕ) : Set (Set (Set (ℕ × ℕ))) :=
  {C | C ⊆ {c | c ⊆ Iio θ ×ˢ Iio θ}}

theorem finite_patternBox (θ : ℕ) : (patternBox θ).Finite :=
  (((finite_Iio θ).prod (finite_Iio θ)).finite_subsets).finite_subsets

omit [TopologicalSpace S] in
theorem marchPattern_mem {π : List S} {θ : ℕ} (hlt : π.length < θ) (Δ : GM04.Patch S) :
    marchPattern π Δ ∈ patternBox θ := by
  rintro _ ⟨δ, -, rfl⟩ p ⟨h₁, h₂, -⟩
  exact ⟨h₁.trans hlt, h₂.trans hlt⟩

/-- A well-quasi-order with a finite tag that must agree. -/
def taggedOrder (Ω' : Type*) [Preorder Ω'] (θ : ℕ) : QuasiOrder (Ω' × Set (Set (ℕ × ℕ))) where
  E := {p | p.2 ∈ patternBox θ}
  le p q := p.1 ≤ q.1 ∧ p.2 = q.2
  refl _ _ := ⟨le_rfl, rfl⟩
  trans _ _ _ _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem isWQO_taggedOrder (Ω' : Type*) [Preorder Ω'] [WellQuasiOrderedLE Ω'] (θ : ℕ) :
    (taggedOrder Ω' θ).IsWQO := by
  intro f hf
  have hfin : Finite (patternBox θ) := (finite_patternBox θ).to_subtype
  obtain ⟨C, hC⟩ := Finite.exists_infinite_fiber (fun n ↦ (⟨(f n).2, hf n⟩ : patternBox θ))
  have hI : ((fun n ↦ (⟨(f n).2, hf n⟩ : patternBox θ)) ⁻¹' {C}).Infinite :=
    infinite_coe_iff.mp hC
  have hO : (QuasiOrder.ofPreorder Ω').IsWQO :=
    (QuasiOrder.isWQO_ofPreorder_iff Ω').2 inferInstance
  obtain ⟨i, hi, j, hj, hij, hle⟩ := hO.exists_pair (f := fun n ↦ (f n).1) hI fun _ _ ↦ mem_univ _
  exact ⟨i, j, hij, hle, congrArg Subtype.val (hi.trans hj.symm)⟩

theorem Arm.order_eq {Γ : Painting S} (A : Arm Γ) : A.order = A.π.length := by
  classical
  have h : (A.minus ∩ A.compl).vertexSet = (A.π.toFinset : Set S) := by
    rw [← A.π_set]
    ext v
    simp
  rw [Arm.order, Hypergraph.separationOrder, h, ncard_coe_finset,
    List.toFinset_card_of_nodup A.π_nodup]

theorem RootedLocation.order_le {Γ : Painting S} (L : RootedLocation Γ) {A : Arm Γ}
    (hA : A ∈ L.arms) : A.order ≤ L.ord :=
  le_csSup (L.finite_arms.image _).bddAbove (mem_image_of_mem _ hA)

variable {χ : ColourScheme S α}

/-- The hearts of the places of `Pl` of order less than `θ`. -/
def heartClass (hd : χ.IsDisjoint) (Pl : Set (Place χ)) (θ : ℕ) :
    Set (GM18.PartialPatchwork (ColourScheme.Colour hd) S (Set S)) :=
  {H | ∃ X ∈ Pl, X.L.ord < θ ∧
    GM18.HasPlaceHeart (GM18.toPartialPatchwork (X.P.toPatchwork hd)) X.L.rooted H}

theorem wellBehaved_heartClass (hd : χ.IsDisjoint) {Pl : Set (Place χ)} (θ : ℕ)
    (hPl : IsWellBehavedPlaces Pl) (hinc : ∀ X ∈ Pl, ∀ v ∈ X.P.Γ.V, ∃ c ∈ X.P.Γ.E, v ∈ tilde c) :
    GM18.WellBehaved (heartClass hd Pl θ) := by
  intro Ω' _ ι hwqo Q hQ
  choose H hH hcomp using hQ
  choose X hX hord hheart using hH
  choose new hnew using hheart
  have hcq : ∀ i, IsCompletedHeart hd (X i) ι (new i) (Q i) := fun i ↦
    isCompletedHeart_of hd (hnew i) (hcomp i)
  have hlt : ∀ i, ∀ A ∈ (X i).L.arms, A.π.length < θ := fun i A hA ↦ by
    rw [← A.order_eq]
    exact ((X i).L.order_le hA).trans_lt (hord i)
  let ξ : ∀ i, Arm (X i).P.Γ → Ω' × Set (Set (ℕ × ℕ)) := fun i A ↦
    (((Q i).φ (new i A.toRootedHypergraph)),
      marchPattern A.π ((Q i).Δ (new i A.toRootedHypergraph)))
  obtain ⟨i, j, hij, τ, hτ, hle⟩ := hPl (taggedOrder Ω' θ) (isWQO_taggedOrder Ω' θ) X hX ξ
    fun i A hA ↦ marchPattern_mem (hlt i A hA) _
  refine ⟨i, j, hij, simulated_of_outline hd hτ (hcq i) (hcq j) (hinc _ (hX i))
    (fun A hA ↦ (hle A hA).1) fun A hA ↦ ?_⟩
  obtain ⟨hmem, -, σv, σe, -, -, hπ, -⟩ := hτ
  have hV : ∀ k, ∀ B ∈ (X k).L.arms, ((Q k).Δ (new k B.toRootedHypergraph)).verts = {v | v ∈ B.π} :=
    fun k B hB ↦ by
      rw [(hcq k).Δ_new _ ⟨B, hB, rfl⟩]
      rfl
  exact mapsTo_of_pattern A.π_nodup (τ A).π_nodup (hπ A hA).1.symm (hV i A hA)
    (hV j _ (hmem A hA)) (hle A hA).2

/-- A set of places inside a well-behaved set is well-behaved. -/
theorem IsWellBehavedPlaces.mono {Pl Pl' : Set (Place χ)} (h : IsWellBehavedPlaces Pl)
    (hsub : Pl' ⊆ Pl) : IsWellBehavedPlaces Pl' :=
  fun Ω hΩ seq hseq ξ hξ ↦ h Ω hΩ seq (fun i ↦ hsub (hseq i)) ξ hξ

theorem RootedLocation.Isolates.toGM18 {S : Type} [TopologicalSpace S] {Γ : Painting S}
    {Shat : Type} [TopologicalSpace Shat] {cap : IsCappedSurface S Shat}
    {rad : RadialDrawing cap Γ} {tb : TieBreaker rad} {L : RootedLocation Γ} {θ ord : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h : L.Isolates tb θ ord 𝒯) :
    GM18.Isolates Γ.toHypergraph tb.lambdaOrder θ 𝒯
      (GM18.rootedLocationToLocation Γ.toHypergraph.toRooted L.rooted) := by
  rw [L.location_eq]
  refine ⟨L.isLocation, h.seps_subset, ?_, ?_, ?_⟩
  · have : GM18.locationOrder L.seps = L.ord := by
      unfold GM18.locationOrder RootedLocation.ord RootedLocation.seps
      rw [image_image]
      rfl
    rw [this]
    exact h.ord_lt
  · rintro C D ⟨A, hA, hEq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    exact (L.order_le hA).trans_lt h.ord_lt
  · rintro C D ⟨A, hA, hEq⟩ θ' 𝒯' h𝒯' hθ' hswap A' B' hdist
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    exact h.distinction_le A hA θ' 𝒯' h𝒯' hθ' hswap A' B' hdist

/-- A connected surface carrying two points has infinitely many points. -/
theorem infinite_of_edge {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {x y : S} (hne : x ≠ y) : Infinite S := by
  by_contra h
  have hfin : Finite S := not_infinite_iff_finite.mp h
  have hdis : DiscreteTopology S := Finite.instDiscreteTopology
  exact hne (isPreconnected_univ.subsingleton (mem_univ x) (mem_univ y))

/-- **Graph Minors XIX, (9.2).** "Let $\chi$ be a disjoint colour scheme, let $(\Gamma_i, \phi_i)$
($i = 1, 2, \ldots$) be a
countable sequence of $\chi$-coloured paintings and for each $i \ge 1$ let $\lambda_i$ be a
tie-breaker in $\Gamma_i$. Let $\theta \ge 1$, and for each $i \ge 1$ and every tangle
$\mathscr{T}$ in $\Gamma_i$ of order $\ge \theta$, let $\mathscr{L}(\mathscr{T})$ be a
rooted location in $\Gamma_i$ which $\theta$-isolates $\mathscr{T}$. Let the set of all
these $(\Gamma_i, \phi_i, \mathscr{L}(\mathscr{T}))$ (over all $i$ and $\mathscr{T}$) be
well-behaved. Then there exist $j > i \ge 1$ such that there is an inflation of $(\Gamma_i,
\phi_i)$ in $(\Gamma_j, \phi_j)$." -/
theorem theorem_9_2_proof {S Shat : Type} {α : Type w} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace Shat] {χ : ColourScheme S α}
    {cap : IsCappedSurface S Shat} (hd : χ.IsDisjoint) (seq : ℕ → ColouredPainting χ)
    (rad : ∀ i, RadialDrawing cap (seq i).Γ) (tb : ∀ i, TieBreaker (rad i)) {θ : ℕ} (hθ : 1 ≤ θ)
    {Pl : Set (Place χ)} (hPl : IsWellBehavedPlaces Pl)
    (hloc : ∀ i ord (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
      GM10.IsTangle (seq i).Γ.toHypergraph ord 𝒯 → θ ≤ ord →
      ∃ L : RootedLocation (seq i).Γ, (⟨hd, seq i, L⟩ : Place χ) ∈ Pl ∧
        L.Isolates (tb i) θ ord 𝒯) :
    ∃ i j, i < j ∧ ∃ σv σe, IsColouredInflation χ (seq i) (seq j) σv σe := by
  classical
  have hS := χ.isSurface
  have h3 : ∀ i, (seq i).Γ.IsInternallyThreeConnected := fun i ↦
    (seq i).fits.internally_three_connected
  have hincseq : ∀ i, ∀ v ∈ (seq i).Γ.V, ∃ c ∈ (seq i).Γ.E, v ∈ tilde c := by
    intro i v hv
    obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS (h3 i) (rad i) hv
    exact ⟨c, hc, hvc, fun hvc' ↦ (hc.2.1 hvc').2 hv⟩
  let Pl' : Set (Place χ) := Pl ∩ {X | ∃ i, X.P = seq i}
  have hPl' : IsWellBehavedPlaces Pl' := hPl.mono inter_subset_left
  have hinc : ∀ X ∈ Pl', ∀ v ∈ X.P.Γ.V, ∃ c ∈ X.P.Γ.E, v ∈ tilde c := by
    rintro X ⟨-, i, hi⟩
    rw [hi]
    exact hincseq i
  have hS2 : Infinite (Set S) := by
    have : ConnectedSpace S := χ.connected
    obtain ⟨e, he⟩ := (h3 0).1
    have htw : 1 < (tilde e).ncard := by
      rcases (seq 0).Γ.edge_shape e he with h | h <;> rw [h.1] <;> norm_num
    have hfin : (tilde e).Finite := ((seq 0).Γ.edge_shape e he).elim (·.2.1) (·.2.1)
    obtain ⟨x, y, -, -, hne⟩ := (one_lt_ncard_iff hfin).1 htw
    have := infinite_of_edge hne
    exact Infinite.of_injective (fun x : S ↦ ({x} : Set S)) singleton_injective
  have hmain := GM18.theorem_6_7_proof (Ω := ColourScheme.Colour hd) (α := S) (β := Set S)
    inferInstance (wellBehaved_heartClass hd θ hPl' hinc) hθ
    (𝒟 := range fun i ↦ (seq i).toPatchwork hd) ?_ (fun i ↦ (seq i).toPatchwork hd)
    (fun i ↦ ⟨i, rfl⟩)
  · obtain ⟨i, j, hij, h⟩ := hmain
    exact ⟨i, j, hij, inflation_of_simulated hd h⟩
  · rintro _ ⟨i, rfl⟩
    refine ⟨?_, (seq i).toPatchwork_isRobust hd, _, inferInstance, (tb i).lambdaOrder,
      (tb i).isTieBreaker hS (h3 i), ?_⟩
    · ext v
      simp [RootedHypergraph.rootSet, ColouredPainting.toPatchwork,
        Hypergraph.toRooted]
    · intro θ' 𝒯 hle h𝒯
      obtain ⟨L, hL, hiso⟩ := hloc i θ' 𝒯 h𝒯 hle
      obtain ⟨new, Q, hheart, -⟩ := GM18.exists_fresh_isPlaceHeart
        (GM18.toPartialPatchwork ((seq i).toPatchwork hd)) L.isRootedLocation
      exact ⟨L.rooted, Q, ⟨fun e _ ↦ WithBot.coe_ne_bot, L.isRootedLocation⟩, ⟨new, hheart⟩,
        ⟨⟨hd, seq i, L⟩, ⟨hL, i, rfl⟩, hiso.ord_lt, ⟨new, hheart⟩⟩, hiso.toGM18⟩

end GraphMinor.GM19
