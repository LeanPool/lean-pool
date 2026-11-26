/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1b
public import LeanPool.GraphMinor.GM12.Induced
public import LeanPool.GraphMinor.GM12.Section2CirclePeriod
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM12.Section2Theorem
import LeanPool.GraphMinor.GM12.Section2TangleTraceExistence
import LeanPool.GraphMinor.GM12.Section2
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.Surface.ArcTools
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Graph Minors XII, (7.7): comparing tangle metrics in a subdrawing

This file formalizes **(7.7)** of Graph Minors XII (page 268) and its cited form
`GM15.GM12Theorem77Statement` using the proved `(2.1)`.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology unitInterval GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

/-- **(2.1)** of Graph Minors XII (page 243), together with the existence of a trace of a normal
closed curve of finite length defined immediately before (2.1) on page 243:
"Let $\Gamma$ be a 2-cell drawing in a connected surface $\Sigma$, with a radial drawing $K$.
Let $\mathscr{T}$ be a respectful tangle in $\Gamma$ of order $\theta \ge 1$, let $\phi
\colon S^1 \to \Sigma$ be continuous, of length $<\theta$, such that $|\phi|$ is
$\Gamma$-normal, and let $W$ be a trace of $\phi$. Then $ins(W)$ is defined. Moreover, for
any atom $c$ of $\Gamma$, if there is an $O$-arc $F \subseteq |\phi|$ with $c \cap ins(F)
\ne \emptyset$, then $c \cap ins(W) \ne \emptyset$." -/
def Theorem21Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S] [ConnectedSpace S],
    IsClosedSurface S →
    ∀ (Γ K : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Drawing S → Set S),
      (PaintingOrDrawing.drawing Γ).IsRadialDrawing K →
      1 ≤ θ →
      IsTangle Γ.toHypergraph θ T →
      (PaintingOrDrawing.drawing Γ).IsRespectful θ T →
      IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins →
      ∀ φ : C(Circle, S),
        IsNormalCurve Γ φ →
        curveLength Γ φ < θ →
        (∃ (u : S) (W : GraphWalk K.toGraph u u), IsTrace Γ K φ W) ∧
        ∀ (u : S) (W : GraphWalk K.toGraph u u),
          IsTrace Γ K φ W →
          W.length < 2 * θ ∧
          ∀ c ∈ Γ.A, ∀ F Δ : Set S,
            IsOArc F → F ⊆ range φ →
            IsClosedDisc Δ → subBd Δ = F →
            ((PaintingOrDrawing.drawing Γ).inter Δ,
              (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T →
            (c ∩ Δ).Nonempty →
            (c ∩ insWalk ins K W).Nonempty

/-- XII (2.1), page 243, in the combined form used in Section 7.
The trace exists even at length zero. The atom assertion is the proved
trace theorem, applied to the disc selected by the tangle. -/
theorem theorem_2_1_statement : Theorem21Statement.{u} := by
  intro S _ _ _ hS Γ K θ T ins hK _ hT hrespect hd φ hn hlen
  refine ⟨exists_trace_of_curveLength_lt_tangle_order hS hT hK hn hlen, ?_⟩
  intro v W hW
  refine ⟨theorem_2_1_length hW hlen, ?_⟩
  intro c hc F Δ hF hFφ hΔ hbd hm hcΔ
  exact (theorem_2_1_proof hS hT hrespect hK hd W hW hlen hF hFφ hΔ hbd hm hc hcΔ).2

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Helper lemmas on atoms, subdrawings, tangles, and metrics -/

omit [T2Space S] in
/-- Every atom of `Γ` is non-empty. -/
theorem atom_nonempty' {Γ : Drawing S} {x : Set S} (hx : x ∈ Γ.A) : x.Nonempty := by
  rcases hx with (⟨v, -, rfl⟩ | hx) | hx
  · exact singleton_nonempty v
  · exact hx.1
  · exact region_nonempty hx

omit [T2Space S] in
/-- Distinct atoms of `Γ` are disjoint. -/
theorem atom_eq_of_inter_nonempty {Γ : Drawing S} {a b : Set S}
    (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) (hne : (a ∩ b).Nonempty) : a = b := by
  have hatom : ∀ c ∈ Γ.A, IsGammaNice Γ c := fun c hc => ⟨{c}, by simpa using hc, by simp⟩
  exact Subset.antisymm (nice_atom (hatom b hb) ha hne)
    (nice_atom (hatom a ha) hb (inter_comm a b ▸ hne))

omit [T2Space S] in
/-- In a radial drawing `K` of `H`, every atom of `H` has a unique corresponding atom in `K`. -/
theorem existsUnique_correspondingAtom' {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {x : Set S} (hx : x ∈ H.A) :
    ∃! x' : Set S, IsCorrespondingAtom H K x x' := by
  exact GM12.existsUnique_correspondingAtom hK hx

/-- Any hypergraph admitting a tangle of order `θ ≥ 2` has at least one edge. -/
theorem edgeSet_nonempty_of_isTangle_of_two_le {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) (hθ : 2 ≤ θ) :
    G.edgeSet.Nonempty := by
  have hsep : G.IsSeparation ⊥ G := by
    rw [isSeparation_iff_of_le bot_le le_rfl]
    simp
  have hord : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have : ((⊥ : Hypergraph α β) ∩ G).vertexSet = ∅ := by simp
    rw [separationOrder, this, ncard_empty]
    omega
  have hbot : (⊥, G) ∈ T :=
    (hT.axiom1 hsep hord).resolve_right fun hG => hT.axiom3 hG rfl
  have hne := GM10.theorem_2_3_proof hT hθ hbot hbot hbot
  rw [GM10.union_self, GM10.union_self, bot_edgeSet] at hne
  exact nonempty_iff_ne_empty.mpr hne.symm

/-- Unconditional version of `exists_edge_dist_eq_theta`, using the proved theorems
`GM11.gm14_theorem_8_12` and `GM11.gm12_theorem_8_5`. -/
theorem exists_edge_dist_eq_theta_uncond (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {z : Set S} (hz : z ∈ H.A) (hzE : 2 ≤ H.E.ncard ∨ z ∉ H.E) :
    ∃ e ∈ H.E, d z e = θ := by
  exact exists_edge_dist_eq_theta_of_metric hS inferInstance hMetric hE hz hzE

/-- A walk of length `0` has `insWalk ins K W = {u}`. -/
theorem insWalk_eq_singleton_of_length_zero {K : Drawing S}
    {ins : Drawing S → Set S} {u : S} (W : GraphWalk K.toGraph u u) (hW0 : W.length = 0) :
    insWalk ins K W = {u} := by
  have hEdges : W.edges = [] := List.length_eq_zero_iff.mp hW0
  have hSupp : W.support = [u] := by
    cases W with
    | nil _ => rfl
    | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hW0
  have hV : (walkDrawing K W).V = {u} := by
    rw [walkDrawing_V, hSupp]
    ext x
    simp
  have hE : (walkDrawing K W).E = ∅ := by
    rw [walkDrawing_E, hEdges]
    ext e
    simp
  have hU : (walkDrawing K W).U = {u} := by
    rw [Drawing.U_eq, hV, hE]
    simp
  unfold insWalk insOf
  rw [hU]
  refine Subset.antisymm ?_ subset_union_left
  rintro x (hx | hx)
  · exact hx
  · obtain ⟨C, ⟨hC, hCs⟩, -⟩ := mem_iUnion₂.mp hx
    exfalso
    have hCU : C.U ⊆ {u} := hU ▸ hCs.U_subset
    exact (infinite_of_isOArc (IsCircuit.isOArc_U hC)) ((finite_singleton u).subset hCU)

/-- For a respectful tangle metric `d` of order `θ`, `d a b = 0` if and only if `a = b`. -/
theorem tangleMetric_eq_zero_iff (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hd : HasTangleMetric Γ θ T d)
    {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) :
    d a b = 0 ↔ a = b := by
  refine ⟨fun h0 => ?_, fun h => h ▸ metric_self hd ha⟩
  by_contra hab
  obtain ⟨hResp, K, ins, hK, hSlope, hd_eq⟩ := hd
  have hθ1 : 1 ≤ θ := hResp.2.1.one_le
  rw [hd_eq a ha b hb] at h0
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hab with hθ | ⟨-, hwit⟩
  · omega
  · rw [h0] at hwit
    obtain ⟨u, W, x', y', hx', hy', hW, hW0, hxW, hyW⟩ := hwit
    have haW : (a ∩ insWalk ins K W).Nonempty :=
      (corresponding_atom_subset_iff hS hK hSlope hx' W hW).mp hxW
    have hbW : (b ∩ insWalk ins K W).Nonempty :=
      (corresponding_atom_subset_iff hS hK hSlope hy' W hW).mp hyW
    rw [insWalk_eq_singleton_of_length_zero W (by omega)] at haW hbW
    obtain ⟨y₁, hxa, hy₁⟩ := haW
    obtain ⟨y₂, hxb, hy₂⟩ := hbW
    rw [mem_singleton_iff.mp hy₁] at hxa
    rw [mem_singleton_iff.mp hy₂] at hxb
    exact hab (atom_eq_of_inter_nonempty ha hb ⟨u, hxa, hxb⟩)

omit [T2Space S] in
/-- Every atom of a drawing `Γ` is contained in some atom of any subdrawing `Γ'`. -/
theorem exists_atom_superset_of_isSubdrawing {Γ Γ' : Drawing S}
    (hsub : Γ'.IsSubdrawing Γ) {a : Set S} (ha : a ∈ Γ.A) :
    ∃ a' ∈ Γ'.A, a ⊆ a' := by
  obtain ⟨x, hxa⟩ := atom_nonempty' ha
  obtain ⟨a', ha', hxa'⟩ := GM11.exists_atom Γ' x
  refine ⟨a', ha', ?_⟩
  rcases ha with (⟨v, hv, rfl⟩ | haE) | haR
  · rw [mem_singleton_iff.mp hxa] at hxa'
    exact singleton_subset_iff.mpr hxa'
  · by_cases haE' : a ∈ Γ'.E
    · have heq := atom_eq_of_inter_nonempty (Or.inl (Or.inr haE')) ha' ⟨x, hxa, hxa'⟩
      exact heq ▸ Subset.rfl
    · have hoff : a ⊆ univ \ Γ'.U := by
        intro y hya
        refine ⟨mem_univ y, fun hyU' => ?_⟩
        by_cases hyV' : y ∈ Γ'.V
        · exact (haE.2.1 hya).2 (hsub.1 hyV')
        · obtain ⟨e', he', hye'⟩ := Γ'.exists_edge_of_mem hyU' hyV'
          have he'Γ : e' ∈ Γ.E := hsub.2 he'
          have heq := atom_eq_of_inter_nonempty (Or.inl (Or.inr haE))
            (Or.inl (Or.inr he'Γ)) ⟨y, hya, hye'⟩
          exact haE' (heq ▸ he')
      have hr' : connectedComponentIn (univ \ Γ'.U) x ∈ Γ'.R :=
        (mem_R_iff Γ').mpr ⟨x, (hoff hxa).2, rfl⟩
      have heq := atom_eq_of_inter_nonempty (Or.inr hr') ha'
        ⟨x, mem_connectedComponentIn (hoff hxa), hxa'⟩
      rw [← heq]
      exact haE.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hxa hoff
  · have hoff : a ⊆ univ \ Γ'.U :=
      fun y hya => ⟨mem_univ y, fun hyU' => region_subset haR hya (hsub.U_subset hyU')⟩
    have hr' : connectedComponentIn (univ \ Γ'.U) x ∈ Γ'.R :=
      (mem_R_iff Γ').mpr ⟨x, (hoff hxa).2, rfl⟩
    have heq := atom_eq_of_inter_nonempty (Or.inr hr') ha'
      ⟨x, mem_connectedComponentIn (hoff hxa), hxa'⟩
    rw [← heq]
    exact (region_isPreconnected haR).subset_connectedComponentIn hxa hoff

omit [T2Space S] in
/-- If `Γ'` is a subdrawing of `Γ`, then `Γ'.U ∩ Γ.V = Γ'.V`. -/
theorem isSubdrawing_U_inter_V {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) :
    Γ'.U ∩ Γ.V = Γ'.V := by
  refine Subset.antisymm ?_ (fun x hx => ⟨Γ'.V_subset_U hx, hsub.1 hx⟩)
  rintro x ⟨hxU', hxV⟩
  by_cases hxV' : x ∈ Γ'.V
  · exact hxV'
  · obtain ⟨e', he', hxe'⟩ := Γ'.exists_edge_of_mem hxU' hxV'
    exact absurd hxV ((hsub.2 he').2.1 hxe').2

omit [T2Space S] in
/-- A `Γ`-normal set `Z` is also `Γ'`-normal for any subdrawing `Γ'` of `Γ`. -/
theorem isNormal_of_isSubdrawing {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ)
    {Z : Set S} (hZ : Γ.IsNormal Z) : Γ'.IsNormal Z := by
  intro x ⟨hxZ, hxU'⟩
  have hxV : x ∈ Γ.V := hZ ⟨hxZ, hsub.U_subset hxU'⟩
  exact (isSubdrawing_U_inter_V hsub).subset ⟨hxU', hxV⟩

omit [T2Space S] in
/-- A `Γ`-normal curve of finite length is also a `Γ'`-normal curve of finite length for any
subdrawing `Γ'` of `Γ`, with `curveLength Γ' φ ≤ curveLength Γ φ`. -/
theorem isNormalCurve_of_isSubdrawing {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ)
    {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) :
    IsNormalCurve Γ' φ ∧ curveLength Γ' φ ≤ curveLength Γ φ := by
  have hsub_hits : {x : Circle | φ x ∈ Γ'.U} ⊆ {x : Circle | φ x ∈ Γ.U} :=
    fun x hx => hsub.U_subset hx
  exact ⟨⟨hφ.1.subset hsub_hits, isNormal_of_isSubdrawing hsub hφ.2⟩,
    ncard_le_ncard hsub_hits hφ.1⟩

omit [T2Space S] in
/-- If `Γ'` is a subdrawing of `Γ`, then `Γ'.toHypergraph ≤ Γ.toHypergraph`. -/
theorem toHypergraph_le_of_isSubdrawing {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) :
    Γ'.toHypergraph ≤ Γ.toHypergraph where
  vertexSet_subset := hsub.1
  edgeSet_subset := hsub.2
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, Drawing.toHypergraph, mem_ofPred_eq]
    have hcl : closure e ∩ Γ'.V = closure e ∩ Γ.V := hsub.closure_inter_V he
    constructor
    · rintro ⟨-, hv, hve⟩
      have hv' : v ∈ Γ'.V := by
        have : v ∈ closure e ∩ Γ.V := ⟨hve, hv⟩
        rw [← hcl] at this
        exact this.2
      exact ⟨he, hv', hve⟩
    · rintro ⟨-, hv', hve⟩
      exact ⟨hsub.2 he, hsub.1 hv', hve⟩

omit [T2Space S] in
/-- Intersecting `(PaintingOrDrawing.drawing Γ).inter Δ` with `Γ'.toHypergraph` yields
`(PaintingOrDrawing.drawing Γ').inter Δ`. -/
theorem drawing_inter_inter_subdrawing {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ)
    (Δ : Set S) :
    ((PaintingOrDrawing.drawing Γ).inter Δ) ∩ Γ'.toHypergraph =
      (PaintingOrDrawing.drawing Γ').inter Δ := by
  have hle := toHypergraph_le_of_isSubdrawing hsub
  ext x
  · simp only [inter_vertexSet, PaintingOrDrawing.inter, PaintingOrDrawing.V,
      Drawing.toHypergraph]
    exact ⟨fun ⟨⟨_, hxΔ⟩, hxV'⟩ => ⟨hxV', hxΔ⟩, fun ⟨hxV', hxΔ⟩ => ⟨⟨hsub.1 hxV', hxΔ⟩, hxV'⟩⟩
  · simp only [inter_edgeSet, PaintingOrDrawing.inter, PaintingOrDrawing.E,
      Drawing.toHypergraph, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨⟨_, hxΔ⟩, hxE'⟩ => ⟨hxE', hxΔ⟩, fun ⟨hxE', hxΔ⟩ => ⟨⟨hsub.2 hxE', hxΔ⟩, hxE'⟩⟩
  · rename_i v
    simp only [inter_inc, PaintingOrDrawing.inter, PaintingOrDrawing.toHypergraph,
      Drawing.toHypergraph]
    exact ⟨fun ⟨⟨_, hxΔ, hvΔ⟩, hinc'⟩ => ⟨hinc', hxΔ, hvΔ⟩,
      fun ⟨hinc', hxΔ, hvΔ⟩ => ⟨⟨inc_of_le hle hinc', hxΔ, hvΔ⟩, hinc'⟩⟩

omit [T2Space S] in
/-- Intersecting `(PaintingOrDrawing.drawing Γ).interOutside Δ` with `Γ'.toHypergraph` yields
`(PaintingOrDrawing.drawing Γ').interOutside Δ`. -/
theorem drawing_interOutside_inter_subdrawing {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ)
    (Δ : Set S) :
    ((PaintingOrDrawing.drawing Γ).interOutside Δ) ∩ Γ'.toHypergraph =
      (PaintingOrDrawing.drawing Γ').interOutside Δ :=
  drawing_inter_inter_subdrawing hsub (closure (univ \ Δ))

/-! ## 2. Atoms meeting the range of a curve meet the underlying set of its trace -/

/-- Along `TraceSteps Γ K f a b W`, `a ≤ b` and any atom `c ∈ Γ.A` meeting `f '' Icc a b` meets
`(walkDrawing K W).V`. -/
theorem traceSteps_le_and_meets_walkDrawing_V {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W) :
    a ≤ b ∧ ∀ s ∈ Icc a b, ∀ c ∈ Γ.A, f s ∈ c → (c ∩ (walkDrawing K W).V).Nonempty := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    obtain ⟨rfl, hfa, huΓ⟩ := hW
    refine ⟨le_rfl, fun s hs c hc hfs => ?_⟩
    have hs_eq : s = a := le_antisymm hs.2 hs.1
    rw [hs_eq, hfa] at hfs
    have hc_eq : c = {u} :=
      atom_eq_of_inter_nonempty hc (Or.inl (Or.inl ⟨u, huΓ, rfl⟩)) ⟨u, hfs, rfl⟩
    refine ⟨u, hc_eq ▸ mem_singleton u, ?_⟩
    rw [walkDrawing_V]
    simp [GraphWalk.support]
  | cons hl rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv =>
      rw [hrestcase] at hW
      exact hW.elim
    | cons hl₂ rest₂ =>
      rw [hrestcase] at hW
      obtain ⟨d, had, hfa, huΓ, hfd, hwK, r, hr, hwr, hfr, _, _, ht⟩ := hW
      obtain ⟨hdb, hmeet₂⟩ := traceSteps_le_and_meets_walkDrawing_V rest₂ ht
      refine ⟨had.le.trans hdb, fun s hs c hc hfs => ?_⟩
      rcases lt_trichotomy s d with hsd | heq | hds
      · rcases eq_or_lt_of_le hs.1 with rfl | has
        · rw [hfa] at hfs
          have hc_eq : c = {u} :=
            atom_eq_of_inter_nonempty hc (Or.inl (Or.inl ⟨u, huΓ, rfl⟩)) ⟨u, hfs, rfl⟩
          refine ⟨u, hc_eq ▸ mem_singleton u, ?_⟩
          rw [walkDrawing_V]
          simp [GraphWalk.support]
        · have hsr : f s ∈ r := hfr s ⟨has, hsd⟩
          have hc_eq : c = r := atom_eq_of_inter_nonempty hc (Or.inr hr) ⟨f s, hfs, hsr⟩
          refine ⟨_, hc_eq ▸ hwr, ?_⟩
          rw [walkDrawing_V]
          simp [GraphWalk.support]
      · subst heq
        obtain ⟨z, hzc, hzV⟩ := hmeet₂ s ⟨le_rfl, hdb⟩ c hc hfs
        refine ⟨z, hzc, ?_⟩
        rw [walkDrawing_V] at hzV ⊢
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hzV)
      · obtain ⟨z, hzc, hzV⟩ := hmeet₂ s ⟨hds.le, hs.2⟩ c hc hfs
        refine ⟨z, hzc, ?_⟩
        rw [walkDrawing_V] at hzV ⊢
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hzV)
termination_by W.length
decreasing_by
  rw [hWcase, hrestcase]
  simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- If `W` is a trace of `φ` in `K` and `c ∈ Γ.A` meets `range φ`, then `c` meets
`(walkDrawing K W).U` (and hence `insWalk ins K W`). -/
theorem meets_walkDrawing_of_isTrace {Γ K : Drawing S} {φ : C(Circle, S)}
    {u : S} {W : GraphWalk K.toGraph u u} (hW : IsTrace Γ K φ W)
    {c : Set S} (hc : c ∈ Γ.A) (hmeet : (c ∩ range φ).Nonempty) :
    (c ∩ (walkDrawing K W).U).Nonempty := by
  obtain ⟨z, hzc, x, rfl⟩ := hmeet
  rcases hW.2 with ⟨-, -, huK, r, hr, hφr, hur⟩ | ⟨-, -, a, ht⟩
  · have hxr : φ x ∈ r := hφr (mem_range_self x)
    have hc_eq : c = r := atom_eq_of_inter_nonempty hc (Or.inr hr) ⟨φ x, hzc, hxr⟩
    refine ⟨u, hc_eq ▸ hur, (walkDrawing K W).V_subset_U ?_⟩
    rw [walkDrawing_V]
    exact W.start_mem_support
  · obtain ⟨s, hs, hsx⟩ := (circle_parameter_bijOn a).surjOn (mem_univ x)
    have hps : periodicCurve φ s = φ x := congrArg φ hsx
    rw [← hps] at hzc
    obtain ⟨_, hstep⟩ := traceSteps_le_and_meets_walkDrawing_V W ht
    obtain ⟨w, hwc, hwV⟩ := hstep s (Ico_subset_Icc_self hs) c hc hzc
    exact ⟨w, hwc, (walkDrawing K W).V_subset_U hwV⟩

/-! ## 3. Constructing normal closed curves from radial walks and from `O`-arcs -/

omit [T2Space S] in
/-- Any `Γ`-normal `O`-arc `F` admits a continuous parametrization `φ : C(Circle, S)` with
`range φ = F`, `IsNormalCurve Γ φ`, and `curveLength Γ φ = (F ∩ Γ.V).ncard`. -/
theorem exists_closedCurve_of_isOArc {Γ : Drawing S} {F : Set S}
    (hF : IsOArc F) (hnorm : Γ.IsNormal F) :
    ∃ φ : C(Circle, S),
      range φ = F ∧ IsNormalCurve Γ φ ∧ curveLength Γ φ = (F ∩ Γ.V).ncard := by
  obtain ⟨e⟩ := hF
  let φ : C(Circle, S) := ⟨fun z => (e z).1, continuous_subtype_val.comp e.continuous⟩
  have hrange : range φ = F := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (e z).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [φ]⟩
  have hinj : Function.Injective φ := fun x y hxy => e.injective (Subtype.ext hxy)
  have hhit_eq : φ '' {z : Circle | φ z ∈ Γ.U} = F ∩ Γ.V := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hxF : φ z ∈ F := (e z).2
      exact ⟨hxF, hnorm ⟨hxF, hz⟩⟩
    · rintro ⟨hxF, hxV⟩
      refine ⟨e.symm ⟨x, hxF⟩, ?_, by simp [φ]⟩
      change φ (e.symm ⟨x, hxF⟩) ∈ Γ.U
      have : φ (e.symm ⟨x, hxF⟩) = x := by simp [φ]
      rw [this]
      exact Γ.V_subset_U hxV
  have hfin_FV : (F ∩ Γ.V).Finite := Γ.finite_V.subset inter_subset_right
  have hfin_hits : {z : Circle | φ z ∈ Γ.U}.Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rw [hhit_eq]
    exact hfin_FV
  have hlen : curveLength Γ φ = (F ∩ Γ.V).ncard := by
    unfold curveLength
    rw [← hhit_eq, ncard_image_of_injective _ hinj]
  exact ⟨φ, hrange, ⟨hfin_hits, hrange.symm ▸ hnorm⟩, hlen⟩

omit [T2Space S] in
/-- Given a single radial link `K.toGraph.IsLink e u w`, there is a path `p : Path u w` with
`range p = closure e` whose hits with `Γ.V` in `[0, 1)` have cardinality at most `1` if `u ∈ Γ.V`
and `0` if `u ∉ Γ.V`. -/
private theorem exists_path_of_radial_link {Γ K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {e : Set S} {u w : S} (hlink : K.toGraph.IsLink e u w) :
    (u ∈ Γ.V ↔ w ∉ Γ.V) ∧
      ∃ p : Path u w,
        range p = closure e ∧
        {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.Finite ∧
        {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.ncard ≤ (open Classical in if u ∈ Γ.V then 1 else
          0) := by
  classical
  have heK : e ∈ K.E := hlink.1
  have hcap : closure e ∩ K.V = {u, w} := hlink.2.2.2
  obtain ⟨v₀, hv₀, w₀, hw₀, hcap₀⟩ := hrad.2.2.2.2.1 e heK
  have hpair : ({u, w} : Set S) = {v₀, w₀} := hcap.symm.trans hcap₀
  have hvw_ne : v₀ ≠ w₀ := fun h => hw₀.2 (h ▸ hv₀)
  have hu_or : u = v₀ ∧ w = w₀ ∨ u = w₀ ∧ w = v₀ := by
    have hu_mem : u ∈ ({v₀, w₀} : Set S) := hpair ▸ mem_insert u {w}
    have hw_mem : w ∈ ({v₀, w₀} : Set S) := hpair ▸ mem_insert_of_mem u (mem_singleton w)
    rcases hu_mem with hu_eq | hu_eq <;> rcases hw_mem with hw_eq | hw_eq
    · exfalso
      have hsing : ({v₀, w₀} : Set S) = {v₀} := by
        rw [← hpair, hu_eq, hw_eq, pair_eq_singleton]
      have hw₀_mem : w₀ ∈ ({v₀} : Set S) := hsing ▸ mem_insert_of_mem v₀ (mem_singleton w₀)
      exact hvw_ne (mem_singleton_iff.mp hw₀_mem).symm
    · exact Or.inl ⟨hu_eq, hw_eq⟩
    · exact Or.inr ⟨hu_eq, hw_eq⟩
    · exfalso
      have hsing : ({v₀, w₀} : Set S) = {w₀} := by
        rw [← hpair, hu_eq, hw_eq, pair_eq_singleton]
      have hv₀_mem : v₀ ∈ ({w₀} : Set S) := hsing ▸ mem_insert v₀ {w₀}
      exact hvw_ne (mem_singleton_iff.mp hv₀_mem)
  have huw_ne : u ≠ w := by
    rcases hu_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hvw_ne
    · exact hvw_ne.symm
  have hbipart : u ∈ Γ.V ↔ w ∉ Γ.V := by
    rcases hu_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun _ => hw₀.2, fun _ => hv₀⟩
    · exact ⟨fun h => absurd h hw₀.2, fun h => (h hv₀).elim⟩
  have hline : IsLineWithEnds (closure e) u w := by
    rcases K.edge_cond e heK with ⟨u₁, w₁, _, hcap₁, hl₁⟩ | ⟨u₁, hcap₁, _⟩
    · have hp₁ : ({u, w} : Set S) = {u₁, w₁} := hcap.symm.trans hcap₁
      have hu₁ : u ∈ ({u₁, w₁} : Set S) := hp₁ ▸ mem_insert u {w}
      have hw₁ : w ∈ ({u₁, w₁} : Set S) := hp₁ ▸ mem_insert_of_mem u (mem_singleton w)
      rcases hu₁ with rfl | rfl <;> rcases hw₁ with rfl | rfl
      · exact (huw_ne rfl).elim
      · exact hl₁
      · exact hl₁.symm
      · exact (huw_ne rfl).elim
    · exfalso
      have hp₁ : ({u, w} : Set S) = {u₁} := hcap.symm.trans hcap₁
      have hu₁ : u = u₁ := mem_singleton_iff.mp (hp₁ ▸ mem_insert u {w})
      have hw₁ : w = u₁ := mem_singleton_iff.mp (hp₁ ▸ mem_insert_of_mem u (mem_singleton w))
      exact huw_ne (hu₁.trans hw₁.symm)
  obtain ⟨a, ha, hran, ha0, ha1⟩ := hline.exists_arc
  let p : Path u w := ⟨⟨a, ha.1⟩, ha0, ha1⟩
  have hsub : {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V} ⊆ if u ∈ Γ.V then {0} else ∅ := by
    intro t ⟨ht1, htV⟩
    have htKV : a t ∈ closure e ∩ K.V := ⟨hran ▸ mem_range_self t, hrad.2.1 htV⟩
    rw [hcap] at htKV
    rcases htKV with htu | htw
    · have ht0 : t = 0 := ha.2 (htu.trans ha0.symm)
      subst ht0
      change a 0 ∈ Γ.V at htV
      rw [ha0] at htV
      simp [htV]
    · have ht_one : t = 1 := ha.2 (htw.trans ha1.symm)
      subst ht_one
      exact (lt_irrefl (1 : ℝ) ht1).elim
  have hfin : (if u ∈ Γ.V then ({0} : Set unitInterval) else ∅).Finite := by
    split_ifs
    · exact finite_singleton 0
    · exact finite_empty
  refine ⟨hbipart, p, hran, hfin.subset hsub, (ncard_le_ncard hsub hfin).trans ?_⟩
  split_ifs <;> simp

/-- Every walk `W` of positive length in a radial drawing `K` is traced by a continuous path
`p : Path u v` with `range p = (walkDrawing K W).U` whose hits with `Γ.V` in `[0, 1)` have
cardinality at most `(W.length + 1) / 2` if `u ∈ Γ.V` and `W.length / 2` if `u ∉ Γ.V`. -/
theorem exists_path_of_radial_walk {Γ K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {u v : S} (W : GraphWalk K.toGraph u v) (hpos : 0 < W.length) :
    ∃ p : Path u v,
      range p = (walkDrawing K W).U ∧
      {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.Finite ∧
      {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.ncard ≤
        (open Classical in if u ∈ Γ.V then (W.length + 1) / 2 else W.length / 2) := by
  classical
  induction W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
  | @cons u w v e hlink rest ih =>
    obtain ⟨hbip, p₁, hran₁, hfin₁, hcard₁⟩ := exists_path_of_radial_link hrad hlink
    cases hrest : rest with
    | nil hw =>
      subst hrest
      have hU : (walkDrawing K (.cons hlink (.nil hw))).U = closure e := by
        have hV : (walkDrawing K (.cons hlink (.nil hw))).V = {u, w} := by
          rw [walkDrawing_V]
          ext x
          simp [GraphWalk.support]
        have hE : (walkDrawing K (.cons hlink (.nil hw))).E = {e} := by
          rw [walkDrawing_E]
          ext f
          simp [GraphWalk.edges]
        rw [Drawing.U_eq, hV, hE, biUnion_singleton]
        refine Subset.antisymm (union_subset ?_ subset_rfl) subset_union_right
        rw [← hlink.2.2.2]
        exact inter_subset_left
      refine ⟨p₁, hran₁.trans hU.symm, hfin₁, hcard₁.trans ?_⟩
      simp [GraphWalk.length, GraphWalk.edges]
    | cons hl₂ rest₂ =>
      subst hrest
      have hpos₂ : 0 < (GraphWalk.cons hl₂ rest₂).length := by
        simp [GraphWalk.length, GraphWalk.edges]
      obtain ⟨p₂, hran₂, hfin₂, hcard₂⟩ := ih hpos₂
      let p := p₁.trans p₂
      have hran : range p = (walkDrawing K (.cons hlink (.cons hl₂ rest₂))).U := by
        rw [Path.trans_range, hran₁, hran₂]
        have hV : (walkDrawing K (.cons hlink (.cons hl₂ rest₂))).V =
            insert u (walkDrawing K (.cons hl₂ rest₂)).V := by
          rw [walkDrawing_V, walkDrawing_V]
          ext x
          simp [GraphWalk.support]
        have hE : (walkDrawing K (.cons hlink (.cons hl₂ rest₂))).E =
            insert e (walkDrawing K (.cons hl₂ rest₂)).E := by
          rw [walkDrawing_E, walkDrawing_E]
          ext f
          simp [GraphWalk.edges]
        have hu_cl : u ∈ closure e := by
          have : u ∈ closure e ∩ K.V := hlink.2.2.2 ▸ mem_insert u {w}
          exact this.1
        rw [Drawing.U_eq, Drawing.U_eq, hV, hE]
        ext x
        simp only [mem_union, mem_insert_iff, mem_iUnion, exists_prop]
        constructor
        · rintro (hx | hx | ⟨f, hf, hxf⟩)
          · exact Or.inr ⟨e, Or.inl rfl, hx⟩
          · exact Or.inl (Or.inr hx)
          · exact Or.inr ⟨f, Or.inr hf, hxf⟩
        · rintro ((rfl | hx) | ⟨f, rfl | hf, hxf⟩)
          · exact Or.inl hu_cl
          · exact Or.inr (Or.inl hx)
          · exact Or.inl hxf
          · exact Or.inr (Or.inr ⟨f, hf, hxf⟩)
      let halfLeft : unitInterval → unitInterval :=
        fun s => ⟨s.1 / 2, by have := s.2.1; linarith, by have := s.2.2; linarith⟩
      let halfRight : unitInterval → unitInterval :=
        fun s => ⟨(s.1 + 1) / 2, by have := s.2.1; linarith, by have := s.2.2; linarith⟩
      let S₁ : Set unitInterval := {t : unitInterval | t.1 < 1 ∧ p₁ t ∈ Γ.V}
      let S₂ : Set unitInterval := {t : unitInterval | t.1 < 1 ∧ p₂ t ∈ Γ.V}
      have hhit_sub : {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V} ⊆
          halfLeft '' S₁ ∪ halfRight '' S₂ := by
        intro t ⟨ht1, hpt⟩
        rcases le_or_gt t.1 (1 / 2 : ℝ) with hle | hgt
        · rcases eq_or_lt_of_le hle with heq | hlt
          · have ht_half : t = ⟨1 / 2, by norm_num, by norm_num⟩ := Subtype.ext heq
            rw [ht_half] at hpt ⊢
            have hp_half : p ⟨1 / 2, by norm_num, by norm_num⟩ = p₂ 0 := by
              change Path.trans p₁ p₂ ⟨1 / 2, by norm_num, by norm_num⟩ = p₂ 0
              rw [Path.trans_apply]
              split_ifs
              · simp [p₁.target, p₂.source]
              · exfalso; norm_num at *
            rw [hp_half] at hpt
            refine Or.inr ⟨0, ⟨by norm_num, hpt⟩, ?_⟩
            ext
            simp [halfRight]
          · let s : unitInterval := ⟨2 * t.1, by have := t.2.1; linarith, by linarith⟩
            have hpt_eq : p t = p₁ s := by
              change Path.trans p₁ p₂ t = p₁ s
              rw [Path.trans_apply]
              split_ifs with h
              · rfl
              · exact (h hle).elim
            rw [hpt_eq] at hpt
            refine Or.inl ⟨s, ⟨by change 2 * t.1 < 1; linarith, hpt⟩, ?_⟩
            ext
            simp [halfLeft, s]
        · let s : unitInterval := ⟨2 * t.1 - 1, by linarith, by linarith [t.2.2]⟩
          have hpt_eq : p t = p₂ s := by
            change Path.trans p₁ p₂ t = p₂ s
            rw [Path.trans_apply]
            split_ifs with h
            · exact (not_le_of_gt hgt h).elim
            · rfl
          rw [hpt_eq] at hpt
          refine Or.inr ⟨s, ⟨by change 2 * t.1 - 1 < 1; linarith, hpt⟩, ?_⟩
          ext
          simp [halfRight, s]
      have hfin_union : (halfLeft '' S₁ ∪ halfRight '' S₂).Finite :=
        (hfin₁.image halfLeft).union (hfin₂.image halfRight)
      have hfin : {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.Finite :=
        hfin_union.subset hhit_sub
      have hcard : {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.ncard ≤ S₁.ncard + S₂.ncard := by
        calc {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}.ncard
          _ ≤ (halfLeft '' S₁ ∪ halfRight '' S₂).ncard := ncard_le_ncard hhit_sub hfin_union
          _ ≤ (halfLeft '' S₁).ncard + (halfRight '' S₂).ncard :=
            ncard_union_le (halfLeft '' S₁) (halfRight '' S₂)
          _ ≤ S₁.ncard + S₂.ncard :=
            add_le_add (ncard_image_le hfin₁) (ncard_image_le hfin₂)
      refine ⟨p, hran, hfin, hcard.trans ?_⟩
      have hlen : (GraphWalk.cons hlink (.cons hl₂ rest₂)).length =
          (GraphWalk.cons hl₂ rest₂).length + 1 := by
        simp [GraphWalk.length, GraphWalk.edges]
      rw [hlen]
      refine (add_le_add hcard₁ hcard₂).trans ?_
      by_cases hu : u ∈ Γ.V
      · have hw : w ∉ Γ.V := hbip.mp hu
        simp only [hu, hw, ↓reduceIte]
        omega
      · have hw : w ∈ Γ.V := hbip.not_left.mp hu
        simp only [hu, hw, ↓reduceIte]
        omega

omit [T2Space S] in
/-- A closed path descends to a continuous curve on the circle. The half-open parameter
interval gives the original path values, and both maps have the same range. -/
theorem exists_closedCurve_of_loop_with_parameter {u : S} (p : Path u u) :
    ∃ φ : C(Circle, S), range φ = range p ∧
      ∀ t : unitInterval, t.1 < 1 → φ (Circle.exp (2 * Real.pi * t.1)) = p t := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  let f : ℝ → S := extI p
  have hf_per : f 0 = f 1 := by
    change extI p (0 : unitInterval).1 = extI p (1 : unitInterval).1
    rw [extI_coe, extI_coe, p.source, p.target]
  have hf_cont : Continuous f := continuous_extI p.continuous
  let g : AddCircle (1 : ℝ) → S := AddCircle.liftIco (1 : ℝ) 0 f
  have hg_cont : Continuous g :=
    AddCircle.liftIco_zero_continuous hf_per hf_cont.continuousOn
  let e : Circle ≃ₜ AddCircle (1 : ℝ) := (AddCircle.homeomorphCircle one_ne_zero).symm
  let φ : C(Circle, S) := ⟨g ∘ e, hg_cont.comp e.continuous⟩
  let q : unitInterval → Circle := fun t => Circle.exp (2 * Real.pi * t.1)
  have hφ_q : ∀ t : unitInterval, t.1 < 1 → φ (q t) = p t := by
    intro t ht1
    have ht_Ico : t.1 ∈ Ico (0 : ℝ) 1 := ⟨t.2.1, ht1⟩
    have he_qt : e (q t) = (t.1 : AddCircle (1 : ℝ)) := by
      refine (Homeomorph.symm_apply_eq (AddCircle.homeomorphCircle one_ne_zero)).mpr ?_
      symm
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
      change Circle.exp (2 * Real.pi / 1 * t.1) = Circle.exp (2 * Real.pi * t.1)
      congr 1
      ring
    change g (e (q t)) = p t
    rw [he_qt]
    change AddCircle.liftIco (1 : ℝ) 0 f (t.1 : AddCircle (1 : ℝ)) = p t
    rw [AddCircle.liftIco_zero_coe_apply ht_Ico]
    exact extI_coe p t
  have hrange : range φ = range p := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ z)
      rw [zero_add] at hs
      let t : unitInterval := ⟨s, hs.1, hs.2.le⟩
      have hqt : q t = z := hsz
      rw [← hqt, hφ_q t hs.2]
      exact mem_range_self t
    · rintro ⟨t, rfl⟩
      rcases eq_or_lt_of_le t.2.2 with ht1 | ht1
      · have ht_eq : t = 1 := Subtype.ext ht1
        rw [ht_eq, p.target, ← p.source, ← hφ_q 0 zero_lt_one]
        exact mem_range_self (q 0)
      · rw [← hφ_q t ht1]
        exact mem_range_self (q t)
  exact ⟨φ, hrange, hφ_q⟩

/-- Every closed walk `W` of positive length `2 * m` in a radial drawing `K` is traced by a
`Γ`-normal closed curve `φ : C(Circle, S)` with `range φ = (walkDrawing K W).U` and
`curveLength Γ φ ≤ m`. -/
private theorem exists_closedCurve_of_radial_walk {Γ K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {u : S} (W : GraphWalk K.toGraph u u) (hpos : 0 < W.length)
    {m : ℕ} (hlen : W.length ≤ 2 * m) :
    ∃ φ : C(Circle, S),
      range φ = (walkDrawing K W).U ∧
      IsNormalCurve Γ φ ∧
      curveLength Γ φ ≤ m := by
  classical
  obtain ⟨p, hran, hfin_p, hcard_p⟩ := exists_path_of_radial_walk hrad W hpos
  obtain ⟨φ, hrange, hφ_q⟩ := exists_closedCurve_of_loop_with_parameter p
  let q : unitInterval → Circle := fun t => Circle.exp (2 * Real.pi * t.1)
  have hrange_W : range φ = (walkDrawing K W).U := hrange.trans hran
  have hnorm_W : Γ.IsNormal (range φ) := by
    unfold Drawing.IsNormal
    rw [hrange_W, Set.inter_comm]
    exact subset_trans (inter_subset_inter_right _ (walkDrawing_isSubdrawing K W).U_subset)
      (subset_of_eq hrad.1)
  let Sp : Set unitInterval := {t : unitInterval | t.1 < 1 ∧ p t ∈ Γ.V}
  have hhit_sub : {z : Circle | φ z ∈ Γ.U} ⊆ q '' Sp := by
    intro z hz
    obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ z)
    rw [zero_add] at hs
    let t : unitInterval := ⟨s, hs.1, hs.2.le⟩
    have hqt : q t = z := hsz
    have hq : φ (q t) = p t := hφ_q t hs.2
    have hpt_U : p t ∈ Γ.U := by
      rw [← hq, hqt]
      exact hz
    have hpt_V : p t ∈ Γ.V := hnorm_W ⟨hrange ▸ mem_range_self t, hpt_U⟩
    exact ⟨t, ⟨hs.2, hpt_V⟩, hqt⟩
  have hfin_hits : {z : Circle | φ z ∈ Γ.U}.Finite := (hfin_p.image q).subset hhit_sub
  have hlen_φ : curveLength Γ φ ≤ m := by
    unfold curveLength
    calc {z : Circle | φ z ∈ Γ.U}.ncard
      _ ≤ (q '' Sp).ncard := ncard_le_ncard hhit_sub (hfin_p.image q)
      _ ≤ Sp.ncard := ncard_image_le hfin_p
      _ ≤ if u ∈ Γ.V then (W.length + 1) / 2 else W.length / 2 := hcard_p
      _ ≤ m := by split_ifs <;> omega
  exact ⟨φ, hrange_W, ⟨hfin_hits, hnorm_W⟩, hlen_φ⟩

/-! ## 4. Proof of (7.7) -/

/-- Core lemma for **(7.7)**: if `d a b < d' a' b'` for `a, b ∈ Γ.A` and `a', b' ∈ Γ'.A` with
`a ⊆ a'`, `b ⊆ b'`, and `d a b < θ`, then there is an `O`-arc `F` in `S` and a closed disc `Δ`
bounded by `F` such that:
- `((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T`,
- `((PaintingOrDrawing.drawing Γ').inter Δ, (PaintingOrDrawing.drawing Γ').interOutside Δ) ∉ T'`,
- and there exist `c ∈ Γ.A`, `f ∈ Γ.E`, and `c', f' ∈ Γ'.A` with `c ⊆ c'`, `f ⊆ f'`,
  `d c f = θ`, and `d' c' f' ≤ d a b`. -/
private theorem exists_disc_and_atoms_of_lt
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ θ' : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d)
    (hsub : Γ'.IsSubdrawing Γ)
    (hθ : θ' ≤ θ) (hd' : HasTangleMetric Γ' θ' T' d')
    {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A)
    {a' b' : Set S} (ha' : a' ∈ Γ'.A) (hb' : b' ∈ Γ'.A)
    (haa' : a ⊆ a') (hbb' : b ⊆ b')
    (hd_lt_d' : d a b < d' a' b') :
    ∃ Δ : Set S,
      ((PaintingOrDrawing.drawing Γ).inter Δ,
        (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T ∧
      ((PaintingOrDrawing.drawing Γ').inter Δ,
        (PaintingOrDrawing.drawing Γ').interOutside Δ) ∉ T' ∧
      ∃ c ∈ Γ.A, ∃ f ∈ Γ.E, ∃ c' ∈ Γ'.A, ∃ f' ∈ Γ'.A,
        c ⊆ c' ∧ f ⊆ f' ∧ d c f = θ ∧ d' c' f' ≤ d a b := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp, K, ins, hrad, hslope, hd_eq⟩ := id hd
  obtain ⟨hResp', K', ins', hrad', hslope', hd'_eq⟩ := id hd'
  have hd'_le_θ' : d' a' b' ≤ θ' := by
    rw [hd'_eq a' ha' b' hb']
    exact GM11.tangleMetric_le_order hrad'.2.1 a' b'
  have hd_lt_θ' : d a b < θ' := lt_of_lt_of_le hd_lt_d' hd'_le_θ'
  have hd_lt_θ : d a b < θ := lt_of_lt_of_le hd_lt_θ' hθ
  have hab_ne : a ≠ b := by
    rintro rfl
    obtain ⟨x, hxa⟩ := atom_nonempty' ha
    have ha'b' : a' = b' := atom_eq_of_inter_nonempty ha' hb' ⟨x, haa' hxa, hbb' hxa⟩
    subst ha'b'
    have hd'0 : d' a' a' = 0 := metric_self hd' ha'
    omega
  have hd_pos : 0 < d a b :=
    Nat.pos_of_ne_zero fun h0 => hab_ne ((tangleMetric_eq_zero_iff hS hd ha hb).mp h0)
  have hθ2 : 2 ≤ θ := by omega
  have hEΓ : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hResp.2.1 hθ2
  have hd_ab : d a b = tangleMetric Γ K ins θ a b := hd_eq a ha b hb
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hrad.2.1 hab_ne with h_eq_θ | ⟨_, hwit⟩
  · omega
  rw [← hd_ab] at hwit
  obtain ⟨u, W, a_K, b_K, ha_K, hb_K, hW_lt, hW_len, ha_sub_W, hb_sub_W⟩ := hwit
  have hposW : 0 < W.length := by omega
  have haW : (a ∩ insWalk ins K W).Nonempty :=
    (corresponding_atom_subset_iff hS hrad hslope ha_K W hW_lt).mp ha_sub_W
  have hbW : (b ∩ insWalk ins K W).Nonempty :=
    (corresponding_atom_subset_iff hS hrad hslope hb_K W hW_lt).mp hb_sub_W
  obtain ⟨φ, hranφ, hnormφ, hlenφ⟩ :=
    exists_closedCurve_of_radial_walk hrad.2.1 W hposW hW_len.le
  obtain ⟨hnormφ', hlenφ'_le⟩ := isNormalCurve_of_isSubdrawing hsub hnormφ
  have hlenφ' : curveLength Γ' φ ≤ d a b := hlenφ'_le.trans hlenφ
  have hlenφ'_lt : curveLength Γ' φ < θ' := lt_of_le_of_lt hlenφ' hd_lt_θ'
  have h21_app := theorem_2_1_statement S hS Γ' K' θ' T' ins' hrad' hResp'.2.1.one_le hResp'.2.1
    hResp'.2.2
    hslope' φ hnormφ' hlenφ'_lt
  obtain ⟨⟨v, W', htr'⟩, h21_prop⟩ := h21_app
  obtain ⟨hW'_lt, h21_disc⟩ := h21_prop v W' htr'
  have hW'_len : W'.length = 2 * curveLength Γ' φ := by
    rcases htr'.2 with ⟨h0, hW0, -⟩ | ⟨-, hW2, -⟩
    · rw [h0, hW0]
    · exact hW2
  -- Any two atoms of `Γ'` meeting `insWalk ins' K' W'` have `d'`-distance at most `d a b`.
  have hd'_le_of_meet : ∀ x' ∈ Γ'.A, ∀ y' ∈ Γ'.A,
      (x' ∩ insWalk ins' K' W').Nonempty → (y' ∩ insWalk ins' K' W').Nonempty →
      d' x' y' ≤ d a b := by
    intro x' hx' y' hy' hx'W hy'W
    by_cases hxy' : x' = y'
    · subst hxy'
      rw [metric_self hd' hx']
      exact Nat.zero_le _
    · obtain ⟨x'_K, hx'_K, -⟩ := existsUnique_correspondingAtom' hrad' hx'
      obtain ⟨y'_K, hy'_K, -⟩ := existsUnique_correspondingAtom' hrad' hy'
      have hx'_sub : x'_K ⊆ insWalk ins' K' W' :=
        (corresponding_atom_subset_iff hS hrad' hslope' hx'_K W' hW'_lt).mpr hx'W
      have hy'_sub : y'_K ⊆ insWalk ins' K' W' :=
        (corresponding_atom_subset_iff hS hrad' hslope' hy'_K W' hW'_lt).mpr hy'W
      have hwit' : GM11.MetricWitness Γ' K' ins' θ' x' y' (curveLength Γ' φ) :=
        ⟨v, W', x'_K, y'_K, hx'_K, hy'_K, hW'_lt, hW'_len, hx'_sub, hy'_sub⟩
      rw [hd'_eq x' hx' y' hy']
      exact (GM11.tangleMetric_le hwit').trans hlenφ'
  -- Hence `a'` and `b'` cannot both meet `insWalk ins' K' W'`.
  have hnot_both : ¬ ((a' ∩ insWalk ins' K' W').Nonempty ∧ (b' ∩ insWalk ins' K' W').Nonempty) :=
    fun ⟨ha'W, hb'W⟩ => not_le_of_gt hd_lt_d' (hd'_le_of_meet a' ha' b' hb' ha'W hb'W)
  have hex_z₀ : ∃ z₀ ∈ Γ.A, ∃ z₀' ∈ Γ'.A, z₀ ⊆ z₀' ∧
      (z₀ ∩ insWalk ins K W).Nonempty ∧ ¬ (z₀' ∩ insWalk ins' K' W').Nonempty := by
    by_cases ha'W : (a' ∩ insWalk ins' K' W').Nonempty
    · have hb'W : ¬ (b' ∩ insWalk ins' K' W').Nonempty := fun h => hnot_both ⟨ha'W, h⟩
      exact ⟨b, hb, b', hb', hbb', hbW, hb'W⟩
    · exact ⟨a, ha, a', ha', haa', haW, ha'W⟩
  obtain ⟨z₀, hz₀, z₀', hz₀', hzz', hz₀W, hz₀'W⟩ := hex_z₀
  -- `z₀` cannot meet `(walkDrawing K W).U = range φ`, else `z₀'` meets `insWalk ins' K' W'`.
  have hz₀_not_U : ¬ (z₀ ∩ (walkDrawing K W).U).Nonempty := by
    intro hmeet
    rw [← hranφ] at hmeet
    have hmeet' : (z₀' ∩ range φ).Nonempty := hmeet.mono (inter_subset_inter_left _ hzz')
    have hmeet_W' := meets_walkDrawing_of_isTrace htr' hz₀' hmeet'
    exact hz₀'W (hmeet_W'.mono (inter_subset_inter_right _ subset_union_left))
  -- Therefore `z₀` meets `ins C` for some circuit `C` of `walkDrawing K W`.
  obtain ⟨p₀, hp₀z, hp₀W⟩ := hz₀W
  rcases hp₀W with hp₀U | hp₀C
  · exact (hz₀_not_U ⟨p₀, hp₀z, hp₀U⟩).elim
  obtain ⟨C, ⟨hC, hCs⟩, hp₀C⟩ := mem_iUnion₂.mp hp₀C
  let F : Set S := C.U
  let Δ : Set S := ins C
  have hFO : IsOArc F := IsCircuit.isOArc_U hC
  have hF_sub_φ : F ⊆ range φ := by
    rw [hranφ]
    exact hCs.U_subset
  have hCK : C.IsSubdrawing K := hCs.trans (walkDrawing_isSubdrawing K W)
  have hC_len_le : C.length ≤ W.length := by
    have hsubE : C.E ⊆ {e | e ∈ W.edges} := by
      have := hCs.2
      rwa [walkDrawing_E] at this
    calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
          Set.ncard_le_ncard hsubE (List.finite_toSet _)
      _ ≤ W.edges.length := by
          rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
            Set.ncard_coe_finset]
          exact List.toFinset_card_le _
      _ = W.length := rfl
  have hC_len_lt : C.length < 2 * θ := lt_of_le_of_lt hC_len_le hW_lt
  obtain ⟨hΔ_disc, hΔ_bd, hΔ_memT⟩ := hslope C hC hCK hC_len_lt
  have hΔ_notMemT' :
      ((PaintingOrDrawing.drawing Γ').inter Δ,
        (PaintingOrDrawing.drawing Γ').interOutside Δ) ∉ T' := by
    intro hmemT'
    have hz₀'_Δ : (z₀' ∩ Δ).Nonempty := ⟨p₀, hzz' hp₀z, hp₀C⟩
    exact hz₀'W (h21_disc z₀' hz₀' F Δ hFO hF_sub_φ hΔ_disc hΔ_bd hmemT' hz₀'_Δ)
  -- Now find `Δ'` from `IsRespectful` of `T'` in `Γ'`.
  have hnormF' : (PaintingOrDrawing.drawing Γ').IsNormal F :=
    fun x ⟨hxF, hxU'⟩ => hnormφ'.2 ⟨hF_sub_φ hxF, hxU'⟩
  have hF_sub_img : F ∩ Γ'.V ⊆ φ '' {x : Circle | φ x ∈ Γ'.U} := by
    rintro y ⟨hyF, hyV'⟩
    obtain ⟨z, rfl⟩ := hF_sub_φ hyF
    exact ⟨z, Γ'.V_subset_U hyV', rfl⟩
  have hcardF' : (F ∩ (PaintingOrDrawing.drawing Γ').V).ncard < θ' := by
    change (F ∩ Γ'.V).ncard < θ'
    calc (F ∩ Γ'.V).ncard
      _ ≤ (φ '' {x : Circle | φ x ∈ Γ'.U}).ncard :=
        ncard_le_ncard hF_sub_img (hnormφ'.1.image φ)
      _ ≤ {x : Circle | φ x ∈ Γ'.U}.ncard := ncard_image_le hnormφ'.1
      _ = curveLength Γ' φ := rfl
      _ < θ' := hlenφ'_lt
  obtain ⟨Δ', hΔ'_disc, hΔ'_bd, hΔ'_memT'⟩ := hResp'.2.2.2 F hFO hnormF' hcardF'
  have hΔ_ne_Δ' : Δ ≠ Δ' := fun h => hΔ_notMemT' (h ▸ hΔ'_memT')
  have hdiscBd_eq : discBd Δ = discBd Δ' := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hΔ_disc,
      ← GM11.IsClosedDisc.frontier_eq_discBd hS hΔ'_disc,
      ← subBd_eq_frontier, ← subBd_eq_frontier, hΔ_bd, hΔ'_bd]
  have hcov : Δ ∪ Δ' = univ := GM11.cover_of_discBd_eq hS hΔ_disc hΔ'_disc hdiscBd_eq hΔ_ne_Δ'
  -- Choose `x₀ ∈ F` and let `c ∈ Γ.A` be the atom containing `x₀`.
  obtain ⟨x₀, hx₀F⟩ := (infinite_of_isOArc hFO).nonempty
  obtain ⟨c, hc, hx₀c⟩ := GM11.exists_atom Γ x₀
  have hc_not_E : c ∉ Γ.E := by
    intro hcE
    have hx₀K : x₀ ∈ K.U := hCK.U_subset hx₀F
    have hx₀Γ : x₀ ∈ Γ.U := (hcE.2.1 hx₀c).1
    have hx₀V : x₀ ∈ Γ.V := by
      have h1 : x₀ ∈ (PaintingOrDrawing.drawing Γ).U ∩ K.U := ⟨hx₀Γ, hx₀K⟩
      rwa [hrad.2.1.1] at h1
    exact (hcE.2.1 hx₀c).2 hx₀V
  obtain ⟨f, hfE, hd_cf⟩ :=
    exists_edge_dist_eq_theta_uncond hS hd hEΓ hc (Or.inr hc_not_E)
  have hfA : f ∈ Γ.A := Or.inl (Or.inr hfE)
  obtain ⟨c', hc', hcc'⟩ := exists_atom_superset_of_isSubdrawing hsub hc
  obtain ⟨f', hf', hff'⟩ := exists_atom_superset_of_isSubdrawing hsub hfA
  have hF_sub_Δ : F ⊆ Δ := by
    change C.U ⊆ ins C
    rw [← hΔ_bd, subBd_eq_frontier]
    exact (IsClosedDisc.isCompact hΔ_disc).isClosed.frontier_subset
  have hF_sub_Δ' : F ⊆ Δ' := by
    rw [← hΔ'_bd, subBd_eq_frontier]
    exact (IsClosedDisc.isCompact hΔ'_disc).isClosed.frontier_subset
  have hΔ_sub_W : Δ ⊆ insWalk ins K W :=
    fun x hx => Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hx⟩)
  -- `f` cannot meet `Δ`, otherwise `W` witnesses `d c f ≤ d a b < θ`.
  have hf_not_Δ : ¬ (f ∩ Δ).Nonempty := by
    intro hfΔ
    have hcW : (c ∩ insWalk ins K W).Nonempty := ⟨x₀, hx₀c, hΔ_sub_W (hF_sub_Δ hx₀F)⟩
    have hfW : (f ∩ insWalk ins K W).Nonempty := hfΔ.mono (inter_subset_inter_right _ hΔ_sub_W)
    by_cases hcf : c = f
    · subst hcf
      exact hc_not_E hfE
    · obtain ⟨c_K, hc_K, -⟩ := existsUnique_correspondingAtom' hrad hc
      obtain ⟨f_K, hf_K, -⟩ := existsUnique_correspondingAtom' hrad hfA
      have hc_sub : c_K ⊆ insWalk ins K W :=
        (corresponding_atom_subset_iff hS hrad hslope hc_K W hW_lt).mpr hcW
      have hf_sub : f_K ⊆ insWalk ins K W :=
        (corresponding_atom_subset_iff hS hrad hslope hf_K W hW_lt).mpr hfW
      have hwit_cf : GM11.MetricWitness Γ K ins θ c f (d a b) :=
        ⟨u, W, c_K, f_K, hc_K, hf_K, hW_lt, hW_len, hc_sub, hf_sub⟩
      have hd_le : d c f ≤ d a b := by
        rw [hd_eq c hc f hfA]
        exact GM11.tangleMetric_le hwit_cf
      omega
  -- Since `f.Nonempty` and `Δ ∪ Δ' = univ`, `f` meets `Δ'`.
  obtain ⟨y₀, hy₀f⟩ := hfE.1
  have hy₀Δ' : y₀ ∈ Δ' := by
    have hy₀_univ : y₀ ∈ Δ ∪ Δ' := hcov.symm ▸ mem_univ y₀
    exact hy₀_univ.resolve_left fun hy₀Δ => hf_not_Δ ⟨y₀, hy₀f, hy₀Δ⟩
  have hc'Δ' : (c' ∩ Δ').Nonempty := ⟨x₀, hcc' hx₀c, hF_sub_Δ' hx₀F⟩
  have hf'Δ' : (f' ∩ Δ').Nonempty := ⟨y₀, hff' hy₀f, hy₀Δ'⟩
  have hc'W' : (c' ∩ insWalk ins' K' W').Nonempty :=
    h21_disc c' hc' F Δ' hFO hF_sub_φ hΔ'_disc hΔ'_bd hΔ'_memT' hc'Δ'
  have hf'W' : (f' ∩ insWalk ins' K' W').Nonempty :=
    h21_disc f' hf' F Δ' hFO hF_sub_φ hΔ'_disc hΔ'_bd hΔ'_memT' hf'Δ'
  refine ⟨Δ, hΔ_memT, hΔ_notMemT', c, hc, f, hfE, c', hc', f', hf',
    hcc', hff', hd_cf, hd'_le_of_meet c' hc' f' hf' hc'W' hf'W'⟩

/-- **(7.7)** of Graph Minors XII (page 268):
"(7.7) *Let $\mathscr{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $\Gamma$ in a
connected surface $\Sigma$; let its metric be $d$. Let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$,
and let $\mathscr{T}'$ be a respectful tangle of order $\theta' \le \theta$ in $\Gamma'$, with
metric $d'$. Then*
(i) *for $k \ge 0$, if $d'(a', b') \ge d(a, b) - k$ for all $a, b \in A(\Gamma)$ and
$a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b \subseteq b'$, then
$d(a, b) \ge \min(d'(a', b'), \theta - k)$ for all such $a, b, a', b'$*
(ii) *if $\theta = \theta'$ and $\mathscr{T}$ is the tangle in $\Gamma$ induced by $\mathscr{T}'$,
then $d(a, b) \ge d'(a', b')$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with
$a \subseteq a'$ and $b \subseteq b'$.*" -/
theorem theorem_7_7_proof
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ θ' : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d)
    (hsub : Γ'.IsSubdrawing Γ) (htc' : (PaintingOrDrawing.drawing Γ').IsTwoCell)
    (hθ : θ' ≤ θ) (hd' : HasTangleMetric Γ' θ' T' d') :
    (∀ k : ℕ,
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - k ≤ d' a' b') →
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → min (d' a' b') (θ - k) ≤ d a b) ∧
    (θ = θ' → T = inducedBySubgraph Γ.toHypergraph Γ'.toHypergraph θ' T' →
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d' a' b' ≤ d a b) := by
  let _ := htc'
  refine ⟨fun k hhyp a ha b hb a' ha' b' hb' haa' hbb' => ?_,
    fun hθ_eq hT_ind a ha b hb a' ha' b' hb' haa' hbb' => ?_⟩
  · by_contra hlt
    push Not at hlt
    have hd_lt_d' : d a b < d' a' b' := lt_of_lt_of_le hlt (min_le_left _ _)
    have hd_lt_θk : d a b < θ - k := lt_of_lt_of_le hlt (min_le_right _ _)
    obtain ⟨_, _, _, c, hc, f, hfE, c', hc', f', hf', hcc', hff', hd_cf, hd'_cf⟩ :=
      exists_disc_and_atoms_of_lt hS hd hsub hθ hd' ha hb ha' hb' haa' hbb' hd_lt_d'
    have hge := hhyp c hc f (Or.inl (Or.inr hfE)) c' hc' f' hf' hcc' hff'
    omega
  · by_contra hlt
    push Not at hlt
    obtain ⟨Δ, hΔ_memT, hΔ_notMemT', -⟩ :=
      exists_disc_and_atoms_of_lt hS hd hsub hθ hd' ha hb ha' hb' haa' hbb' hlt
    rw [hT_ind] at hΔ_memT
    have hmem : (((PaintingOrDrawing.drawing Γ).inter Δ) ∩ Γ'.toHypergraph,
        ((PaintingOrDrawing.drawing Γ).interOutside Δ) ∩ Γ'.toHypergraph) ∈ T' := hΔ_memT.2.2
    rw [drawing_inter_inter_subdrawing hsub Δ,
      drawing_interOutside_inter_subdrawing hsub Δ] at hmem
    exact hΔ_notMemT' hmem

/-- Bridge theorem proving `GM15.GM12Theorem77Statement` using the proved `(2.1)`. -/
theorem gm15_theorem_7_7 :
    GM15.GM12Theorem77Statement.{u} := by
  intro S _ _ Γ Γ' θ θ' T T' d d' hS hconn hd hsub htc' hθ hd'
  exact theorem_7_7_proof hS hd hsub htc' hθ hd'

end GraphMinor.GM12
