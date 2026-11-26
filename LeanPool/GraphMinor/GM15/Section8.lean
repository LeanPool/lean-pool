/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.GraphSubhypergraph
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.Section5b

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Bridge

import LeanPool.GraphMinor.GM12.Section5Final

import LeanPool.GraphMinor.GM12.Section6

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Bridge

import LeanPool.GraphMinor.GM15.Section5

/-!
# Graph Minors XV, Section 8: Some Mild Improvements and Main Theorem (1.1)

This file formalizes the deduction of **Graph Minors XV, (1.1)** from **(1.2)** (Section 1,
pages 115–116) and Section 8 ("Some mild improvements", pages 145–148) of N. Robertson and P. D.
Seymour, *Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148:
- **Monotonicity of segregations of type `(p, κ)` and controlled clique minors**
  (`IsSegregationOfType.mono`, `ControlsCliqueMinor.mono`, `controlsCliqueMinor_of_gm12`).
- **Graph Minors XV, (1.1)** (`GM15Theorem11Statement`, `theorem_1_1`, pages 115–116): main theorem
  of Graph Minors XV, proved by induction on `k` from `(1.2)` (`theorem_1_2`) and `(5.1)`
  (`GM15Theorem51Statement`).
- **Graph Minors XV, (8.1)** (`GM15Theorem81Statement`, `theorem_8_1`, page 145): a `Σ`-span of
  order `≥ φ` with `≥ κ` independent eyes implies `T*` controls a `K_p` minor of `G`, proved from
  Graph Minors XII, `(4.5)` (`GM12Theorem45Statement`).
- **Graph Minors XV, (8.2)** (`GM15Theorem82Statement`, `theorem_8_2`, pages 145–146): clique-minor
  form of `(1.1)`, proved from `(1.1)` (`theorem_1_1`) and `(8.1)` (`theorem_8_1`).
- **Graph Minors XV, (8.3)** (`GM15Theorem83Statement`, page 146) and Claim (1) of its proof
  (`theorem_8_3_claim_1`, page 147): every `(λ + μ + 2, μ)`-level `Σ`-span is `(λ, μ)`-flat.
- **Graph Minors XV, (8.4)** (`GM15Theorem84Statement`, `theorem_8_4`, page 148): level-span form of
  `(8.2)`, proved from `(8.2)` (`theorem_8_2`) and `(8.3)` (`GM15Theorem83Statement`).
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Helper Lemmas on Truncation, Segregations, and Controlled Clique Minors -/

/-- Truncating a tangle `T` of order `θ` to order `θ` leaves `T` unchanged. -/
theorem truncation_self_of_isTangle {G_H : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : GM10.IsTangle G_H θ T) :
    GM10.truncation T θ = T := by
  ext ⟨A, B⟩
  exact ⟨fun h => h.1, fun h => ⟨h, hT.order_lt h⟩⟩

/-- By `(5.1)` (`GM15Theorem51Statement`), if `H, η, T` is `(λ₁, μ₁)`-flat of order `θ`,
`λ₂ ≤ λ₁`, `μ₁ ≤ μ₂`, and `4λ₂ + μ₂ + 2 ≤ θ`, then `H, η, T` is `(λ₂, μ₂)`-flat of order `θ`. -/
theorem IsFlatSpan.mono_lam_mu
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam₁ lam₂ μ₁ μ₂ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hFlat : IsFlatSpan G H η θ_star θ lam₁ μ₁ T_star T)
    (hlam : lam₂ ≤ lam₁) (hμ : μ₁ ≤ μ₂) (hord : 4 * lam₂ + μ₂ + 2 ≤ θ)
    (hθ_gt : lam₂ < lam₁ → 4 * lam₁ + 2 < θ) :
    IsFlatSpan G H η θ_star θ lam₂ μ₂ T_star T := by
  have h1 : 1 ≤ θ := by omega
  have htr := GraphMinor.GM15.theorem_5_1_proof.{u, v, w} G H η θ_star θ θ lam₁ lam₂ μ₁ μ₂ T_star T
    hFlat hlam hμ h1 le_rfl hord
    hθ_gt (by omega)
  rwa [truncation_self_of_isTangle hFlat.isSpan.isControlling.isTangle_H] at htr

/-- Monotonicity of `IsSegregationOfType`: if `S_seg` is of type `(p₁, κ₁)` and `p₁ ≤ p₂`,
`κ₁ ≤ κ₂`, then `S_seg` is of type `(p₂, κ₂)` (Graph Minors XV, Section 1, page 116). -/
theorem IsSegregationOfType.mono {G : Graph α β} {p₁ p₂ κ₁ κ₂ : ℕ}
    {S_seg : Set (Society α β)}
    (h : IsSegregationOfType G p₁ κ₁ S_seg) (hp : p₁ ≤ p₂) (hκ : κ₁ ≤ κ₂) :
    IsSegregationOfType G p₂ κ₂ S_seg where
  isSegregation := h.isSegregation
  vortex_count_le := h.vortex_count_le.trans hκ
  is_p_vortex _ hS₀ hgt _ hP := (h.is_p_vortex hS₀ hgt hP).trans hp

/-- Monotonicity of `ControlsCliqueMinor`: if `T*` controls a `K_{p₂}` minor of `G` and `p₁ ≤ p₂`,
then `T*` controls a `K_{p₁}` minor of `G` (Graph Minors XV, Section 8, page 146). -/
theorem ControlsCliqueMinor.mono {G : Graph α β} {p₁ p₂ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (h : ControlsCliqueMinor G p₂ T_star) (hp : p₁ ≤ p₂) :
    ControlsCliqueMinor G p₁ T_star := by
  rcases h with ⟨X_sub, hconn, hdisj, hlink, hno_small⟩
  refine ⟨fun i => X_sub (Fin.castLE hp i),
    fun i => hconn (Fin.castLE hp i),
    fun i j hij => hdisj (Fin.castLE hp i) (Fin.castLE hp j)
      (fun heq => hij ((Fin.castLE_injective hp) heq)),
    fun i j hij => hlink (Fin.castLE hp i) (Fin.castLE hp j) hij,
    fun A B hAB hord i => hno_small hAB (lt_of_lt_of_le hord hp) (Fin.castLE hp i)⟩

/-- `GM12.ControlsMinor` for `completeGraph p` implies `GM15.ControlsCliqueMinor`. -/
theorem controlsCliqueMinor_of_gm12 {G : Graph α β}
    {hV : V(G).Finite} {hE : E(G).Finite} {θ_star p : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (h : GM12.ControlsMinor (Hypergraph.ofGraph G hV hE) θ_star T_star (completeGraph p)) :
    ControlsCliqueMinor G p T_star := by
  rcases h with ⟨a, b, ha_conn, ha_disj, hb_link, _, _, _, hno_small⟩
  let X_sub : Fin p → Graph α β := fun i => subgraphOfSubhypergraph G (a i)
  have hcard : V(completeGraph p).ncard = p := by
    change (Set.univ : Set (Fin p)).ncard = p
    simp
  refine ⟨X_sub, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hle, hne, hconn⟩ := ha_conn i (mem_univ i)
    refine ⟨subgraphOfSubhypergraph_le hle, hne, ⟨hne, fun u hu v hv => ?_⟩⟩
    have hVH : V(X_sub i).Finite := (a i).vertexSet_finite
    have hEH : E(X_sub i).Finite :=
      (a i).edgeSet_finite.subset (by rw [edgeSet_subgraphOfSubhypergraph hle])
    have hof : Hypergraph.ofGraph (X_sub i) hVH hEH = a i := ofGraph_subgraphOfSubhypergraph hle
    rw [← hof] at hconn
    obtain ⟨w⟩ := hconn u hu v hv
    exact reflTransGen_adj_of_skeleton_walk w
  · intro i j hij
    exact ha_disj i (mem_univ i) j (mem_univ j) hij
  · intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    obtain ⟨hbe, ⟨x, hx, hinc_x⟩, ⟨y, hy, hinc_y⟩⟩ :=
      hb_link s(i, j) i j ⟨hne, rfl⟩ hne
    have hxy : x ≠ y := (ha_disj i (mem_univ i) j (mem_univ j) hne).ne_of_mem hx hy
    exact ⟨b s(i, j), hbe, x, hx, y, hy, isLink_of_inc_of_inc_of_ne hinc_x hinc_y hxy⟩
  · intro A B hAB hord i
    rw [← hcard] at hord
    exact hno_small A B hAB hord i (mem_univ i)

/-! ## Proof of Graph Minors XV, (1.1) from (1.2) -/

/-- If `u ∈ V(H) ∩ closure(r_i)` and `v ∈ V(H) ∩ closure(r_j)` for regions `r_i, r_j ∈ H.R` with
`d(r_i, r_j) = θ` and `μ + 2 ≤ θ`, then `μ ≤ d({u}, {v})`
(Graph Minors XV, Section 1, proof of (1.1), page 116:
"$$\mu+2 \le \theta_{\kappa+1} = d(r_i, r_j) \le d(u, r_i) + d(u, v) + d(v, r_j) \le d(u, v) + 2").
-/
theorem dist_ge_of_eye_bd_vertices
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ μ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r_i r_j : Set S} {u v : S}
    (hClosed : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    (hri : r_i ∈ H.R) (hrj : r_j ∈ H.R)
    (hu : u ∈ H.V ∧ u ∈ closure r_i) (hv : v ∈ H.V ∧ v ∈ closure r_j)
    (hd : d r_i r_j = θ) (hθ : μ + 2 ≤ θ) :
    μ ≤ d {u} {v} := by
  obtain ⟨_, _, _, hsymm, htri, hadj, -⟩ := gm11_theorem_9_1 H θ T d hClosed hConn hMetric
  have huA : {u} ∈ H.A := Or.inl (Or.inl ⟨u, hu.1, rfl⟩)
  have hvA : {v} ∈ H.A := Or.inl (Or.inl ⟨v, hv.1, rfl⟩)
  have hriA : r_i ∈ H.A := Or.inr hri
  have hrjA : r_j ∈ H.A := Or.inr hrj
  have h1 : d r_i {u} ≤ 1 := by
    rw [hsymm r_i hriA {u} huA]
    exact hadj hE u hu.1 r_i hri hu.2
  have h2 : d {v} r_j ≤ 1 := hadj hE v hv.1 r_j hrj hv.2
  have h3 : d r_i r_j ≤ d r_i {u} + d {u} r_j := htri r_i hriA {u} huA r_j hrjA
  have h4 : d {u} r_j ≤ d {u} {v} + d {v} r_j := htri {u} huA {v} hvA r_j hrjA
  omega

/-- `IsHPathWithEnds` is symmetric in the two ends `a` and `b`. -/
theorem _root_.GraphMinor.GM14.IsHPathWithEnds.symm {G H P : Graph α β} {a b : α}
    (h : IsHPathWithEnds G H P a b) : IsHPathWithEnds G H P b a :=
  ⟨h.1, h.2.1.symm, h.2.2.1.symm, h.2.2.2.2.1, h.2.2.2.1,
    by rw [h.2.2.2.2.2.1, Set.pair_comm], h.2.2.2.2.2.2⟩

/-- In a path `P` from `a` to `b` with `a ≠ b`, `a` is incident with some edge of `P`. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.exists_inc_left {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ e ∈ E(P), P.Inc e a := by
  obtain ⟨_, W, _, _, _⟩ := hP
  cases W with
  | nil _ => exact False.elim (hab rfl)
  | cons h _ => exact ⟨_, h.edge_mem, h.inc_left⟩

/-- In a path `P` from `a` to `b` with `a ≠ b`, `b` is incident with some edge of `P`. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.exists_inc_right {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ e ∈ E(P), P.Inc e b :=
  hP.symm.exists_inc_left hab.symm

/-- In a `(4, μ)`-flat `Σ`-span `H, η, T` of order `θ ≥ μ + 18` with `μ ≥ 12`, any two `η(H)`-paths
`R₁` (with ends in `V(H) ∩ closure r₁`) and `R₂` (with ends in `V(H) ∩ closure r₂`) for regions
`r₁, r₂ ∈ H.R` with `d r₁ r₂ = θ` are vertex-disjoint
(Graph Minors XV, Section 1, proof of (1.1), page 116). -/
private theorem disjoint_eye_paths_of_flatSpan
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ μ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r₁ r₂ : Set S} {u₁ v₁ u₂ v₂ : S} {R₁ R₂ : Graph α β}
    (hFlat : IsFlatSpan G H η θ_star θ 4 μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hμ : 12 ≤ μ) (hθ : μ + 18 ≤ θ)
    (hr₁ : r₁ ∈ H.R) (hr₂ : r₂ ∈ H.R) (hd : d r₁ r₂ = θ)
    (hu₁ : u₁ ∈ H.V ∧ u₁ ∈ closure r₁) (hv₁ : v₁ ∈ H.V ∧ v₁ ∈ closure r₁)
    (hu₂ : u₂ ∈ H.V ∧ u₂ ∈ closure r₂) (hv₂ : v₂ ∈ H.V ∧ v₂ ∈ closure r₂)
    (hR₁ : IsHPathWithEnds G η.imageGraph R₁ (η.vMap u₁) (η.vMap v₁))
    (hR₂ : IsHPathWithEnds G η.imageGraph R₂ (η.vMap u₂) (η.vMap v₂)) :
    Disjoint V(R₁) V(R₂) := by
  by_contra hnot
  have hne : (V(R₁) ∩ V(R₂)).Nonempty := Set.not_disjoint_iff_nonempty_inter.mp hnot
  have hClosed : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hE : H.E.Nonempty := edges_nonempty_of_tangle hClosed hMetric.1 (by omega)
  obtain ⟨_, hd_refl, _, _, _, _⟩ := gm11_theorem_9_1 H θ T d hClosed hConn hMetric
  have hdist_ge : ∀ x ∈ ({u₁, v₁} : Set S), ∀ y ∈ ({u₂, v₂} : Set S), μ ≤ d {x} {y} := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · exact dist_ge_of_eye_bd_vertices hClosed hConn hMetric hE hr₁ hr₂ hu₁ hu₂ hd (by omega)
    · exact dist_ge_of_eye_bd_vertices hClosed hConn hMetric hE hr₁ hr₂ hu₁ hv₂ hd (by omega)
    · exact dist_ge_of_eye_bd_vertices hClosed hConn hMetric hE hr₁ hr₂ hv₁ hu₂ hd (by omega)
    · exact dist_ge_of_eye_bd_vertices hClosed hConn hMetric hE hr₁ hr₂ hv₁ hv₂ hd (by omega)
  have hdisj_ends : Disjoint ({η.vMap u₁, η.vMap v₁} : Set α) {η.vMap u₂, η.vMap v₂} := by
    refine Set.disjoint_left.mpr ?_
    rintro _ (rfl | rfl) (hEq | hEq)
    · have hEq' : u₁ = u₂ := η.bijOn_v.injOn hu₁.1 hu₂.1 hEq
      have hge := hdist_ge u₁ (Or.inl rfl) u₂ (Or.inl rfl)
      rw [← hEq', hd_refl {u₁} (Or.inl (Or.inl ⟨u₁, hu₁.1, rfl⟩))] at hge
      omega
    · have hEq' : u₁ = v₂ := η.bijOn_v.injOn hu₁.1 hv₂.1 hEq
      have hge := hdist_ge u₁ (Or.inl rfl) v₂ (Or.inr rfl)
      rw [← hEq', hd_refl {u₁} (Or.inl (Or.inl ⟨u₁, hu₁.1, rfl⟩))] at hge
      omega
    · have hEq' : v₁ = u₂ := η.bijOn_v.injOn hv₁.1 hu₂.1 hEq
      have hge := hdist_ge v₁ (Or.inr rfl) u₂ (Or.inl rfl)
      rw [← hEq', hd_refl {v₁} (Or.inl (Or.inl ⟨v₁, hv₁.1, rfl⟩))] at hge
      omega
    · have hEq' : v₁ = v₂ := η.bijOn_v.injOn hv₁.1 hv₂.1 hEq
      have hge := hdist_ge v₁ (Or.inr rfl) v₂ (Or.inr rfl)
      rw [← hEq', hd_refl {v₁} (Or.inl (Or.inl ⟨v₁, hv₁.1, rfl⟩))] at hge
      omega
  obtain ⟨P, hP, _, _⟩ := exists_isHPathWithEnds_of_inter_nonempty hR₁ hR₂ hdisj_ends hne
  exact not_isMuSteppedSpan_of_isFlatSpan hFlat hMetric (by omega)
    ⟨P, u₁, v₂, hu₁.1, hv₂.1, hP, hdist_ge u₁ (Or.inl rfl) v₂ (Or.inr rfl)⟩

/-- Last step in the proof of (1.1) (Graph Minors XV, Section 1, page 116):
in a `(4, μ)`-flat `Σ`-span `H, η, T` of order `θ ≥ μ + 18` with `κ + 1` eyes `r_1, ..., r_{κ+1}`
mutually at distance `θ`, the eyes `r_1, ..., r_{κ+1}` are independent eyes. -/
theorem independentEyes_of_flatSpan
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ μ κ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin (κ + 1) → Set S)
    (hFlat : IsFlatSpan G H η θ_star θ 4 μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hμ : 12 ≤ μ) (hθ : μ + 18 ≤ θ)
    (hr_inj : Injective r)
    (hr_eye : ∀ i : Fin (κ + 1), IsDrawingEye G H η θ T (r i))
    (hr_dist : ∀ i j : Fin (κ + 1), i ≠ j → d (r i) (r j) = θ) :
    HasIndependentEyes G H η θ T d (κ + 1) := by
  classical
  have hex : ∀ i : Fin (κ + 1), ∃ P₁ P₂ : Graph α β,
      IsEyeWithPaths G H η θ T (r i) P₁ P₂ ∧
      ∃ a b c d_v : S,
        a ∈ H.V ∧ a ∈ closure (r i) ∧
        b ∈ H.V ∧ b ∈ closure (r i) ∧
        c ∈ H.V ∧ c ∈ closure (r i) ∧
        d_v ∈ H.V ∧ d_v ∈ closure (r i) ∧
        IsHPathWithEnds G η.imageGraph P₁ (η.vMap a) (η.vMap c) ∧
        IsHPathWithEnds G η.imageGraph P₂ (η.vMap b) (η.vMap d_v) := by
    intro i
    obtain ⟨hri, C, a, b, c, d_v, P₁, P₂, hC, hCH, hCU, haC, hbC, hcC, hdC,
      hnd, hord, hfree, hdisj, hP₁, hP₂⟩ := hr_eye i
    have hsub_cl : C.V ⊆ closure (r i) := by
      intro x hx
      have hxU : x ∈ C.U := C.V_subset_U hx
      rw [hCU] at hxU
      exact hxU.1
    refine ⟨P₁, P₂,
      ⟨hri, C, a, b, c, d_v, hC, hCH, hCU, haC, hbC, hcC, hdC, hnd, hord, hfree, hdisj, hP₁, hP₂⟩,
      a, b, c, d_v,
      hCH.1 haC, hsub_cl haC, hCH.1 hbC, hsub_cl hbC,
      hCH.1 hcC, hsub_cl hcC, hCH.1 hdC, hsub_cl hdC, hP₁, hP₂⟩
  choose P Q hEye hEnds using hex
  refine ⟨r, P, Q, hr_inj, hEye, hr_dist, fun i j hij => ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁_v, ha₁V, ha₁cl, hb₁V, hb₁cl, hc₁V, hc₁cl, hd₁V, hd₁cl, hP₁, hQ₁⟩ := hEnds i
  obtain ⟨a₂, b₂, c₂, d₂_v, ha₂V, ha₂cl, hb₂V, hb₂cl, hc₂V, hc₂cl, hd₂V, hd₂cl, hP₂, hQ₂⟩ := hEnds j
  have hri : r i ∈ H.R := (hEye i).1
  have hrj : r j ∈ H.R := (hEye j).1
  have hd_ij : d (r i) (r j) = θ := hr_dist i j hij
  rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact disjoint_eye_paths_of_flatSpan hFlat hMetric hμ hθ hri hrj hd_ij
      ⟨ha₁V, ha₁cl⟩ ⟨hc₁V, hc₁cl⟩ ⟨ha₂V, ha₂cl⟩ ⟨hc₂V, hc₂cl⟩ hP₁ hP₂
  · exact disjoint_eye_paths_of_flatSpan hFlat hMetric hμ hθ hri hrj hd_ij
      ⟨ha₁V, ha₁cl⟩ ⟨hc₁V, hc₁cl⟩ ⟨hb₂V, hb₂cl⟩ ⟨hd₂V, hd₂cl⟩ hP₁ hQ₂
  · exact disjoint_eye_paths_of_flatSpan hFlat hMetric hμ hθ hri hrj hd_ij
      ⟨hb₁V, hb₁cl⟩ ⟨hd₁V, hd₁cl⟩ ⟨ha₂V, ha₂cl⟩ ⟨hc₂V, hc₂cl⟩ hQ₁ hP₂
  · exact disjoint_eye_paths_of_flatSpan hFlat hMetric hμ hθ hri hrj hd_ij
      ⟨hb₁V, hb₁cl⟩ ⟨hd₁V, hd₁cl⟩ ⟨hb₂V, hb₂cl⟩ ⟨hd₂V, hd₂cl⟩ hQ₁ hQ₂

/-- Downward induction on `k = κ + 1 - n` using (1.2) (`GM15Theorem12Statement`) and (5.1)
(`GM15Theorem51Statement`) in the proof of (1.1) (Graph Minors XV, Section 1, page 116). -/
private theorem inductive_step_1_1
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hSurf : IsSurface S) (hConn : ConnectedSpace S) (hBd : bd S = ∅)
    {κ φ' μ' lam_target θ_target : ℕ}
    (hφ'8 : 8 ≤ φ') (hμ'12 : 12 ≤ μ') (hμ'_even : Even μ')
    (hlam_t : 4 ≤ lam_target) (hθ_t : 4 * lam_target + μ' + 2 ≤ θ_target) :
    ∀ n ≤ κ + 1,
      ∃ (p_n lam_n θ_n : ℕ),
        4 ≤ lam_n ∧ 4 * lam_n + μ' + 2 ≤ θ_n ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam_n μ' T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ_n ≤ θ₀ →
          HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ (κ + 1 - n) θ_n →
          Section7S1 S G θ_star T_star κ μ' lam_target θ_target ∨
          Section7S2 S G θ_star T_star φ' ∨
          Section7ProperS3 S G T_star p_n κ := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, lam_target, θ_target, hlam_t, hθ_t, ?_⟩
    intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
    left
    have h4 : 4 ≤ θ_target := by omega
    exact GraphMinor.GM15.theorem_7_1_proof.{u, v, w} G H₀ η₀ θ_star θ₀ θ_target lam_target μ'
      (κ + 1) T_star T₀ d₀
      hFlat₀ hMetric₀ (by omega) hθ_t h4 hθ₀_ge hEyes₀
  | succ n ih =>
    intro hn1
    have hn : n ≤ κ + 1 := Nat.le_of_succ_le hn1
    obtain ⟨p_n, lam_n, θ_n, hlam_n4, hθ_n_ge, hIH⟩ := ih hn
    let k := κ + 1 - (n + 1)
    have hk_le : k ≤ κ := by omega
    have hk_succ : k + 1 = κ + 1 - n := by omega
    obtain ⟨p_k, lam_k, θ_k, hθ_k_ge, hStep⟩ :=
      GraphMinor.GM15.theorem_1_2_proper.{u, v, w} S hSurf hConn hBd k φ' μ' lam_n θ_n hφ'8 hμ'12
        hμ'_even hlam_n4 hθ_n_ge
    let p_next := max p_k p_n
    let lam_next := max lam_k 4
    let θ_next := max θ_k (4 * lam_next + μ' + 2)
    have hlam_next4 : 4 ≤ lam_next := le_max_right _ _
    have hθ_next_ge : 4 * lam_next + μ' + 2 ≤ θ_next := le_max_right _ _
    refine ⟨p_next, lam_next, θ_next, hlam_next4, hθ_next_ge, ?_⟩
    intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
    have hθ_k_le_θ_next : θ_k ≤ θ_next := le_max_left _ _
    have hθ_k_le_θ₀ : θ_k ≤ θ₀ := hθ_k_le_θ_next.trans hθ₀_ge
    have hFlat_k : IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ' T_star T₀ :=
      hFlat₀.mono_lam_mu (le_max_left _ _) le_rfl (hθ_k_ge.trans hθ_k_le_θ₀)
        (fun _ => by have := hFlat₀.order_ge; omega)
    have hEyes_k : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k := by
      rcases hEyes₀ with ⟨r, hr_inj, hr_eye, hr_dist⟩
      exact ⟨r, hr_inj, hr_eye, fun i j hij => hθ_k_le_θ_next.trans (hr_dist i j hij)⟩
    rcases hStep G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat_k hMetric₀ hθ_k_le_θ₀ hEyes_k with
      hS1 | hS2 | hS3
    · rcases hS1 with ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩
      have hEyes₁ : HasEyesAtDistance G H₁ η₁ θ_n T₁ d₁ (k + 1) θ_n :=
        ⟨r₁, hr₁_inj, hr₁_eye, fun i j hij => le_of_eq (hr₁_dist i j hij).symm⟩
      rw [hk_succ] at hEyes₁
      rcases hIH G θ_star T_star H₁ η₁ θ_n T₁ d₁ hFlat₁ hMetric₁ le_rfl hEyes₁ with
        hOut1 | hOut2 | ⟨S_seg, α_disc, α_pt, hCent, hType, hArr⟩
      · exact Or.inl hOut1
      · exact Or.inr (Or.inl hOut2)
      · exact Or.inr (Or.inr ⟨S_seg, α_disc, α_pt, hCent,
          hType.mono (le_max_right _ _) le_rfl, hArr⟩)
    · exact Or.inr (Or.inl hS2)
    · rcases hS3 with ⟨S_seg, α_disc, α_pt, hCent, hType, hArr⟩
      exact Or.inr (Or.inr ⟨S_seg, α_disc, α_pt, hCent,
        hType.mono (le_max_left _ _) hk_le, hArr⟩)

/-- Statement of Graph Minors XV, (1.1) (page 115):
"For any surface $\Sigma$ with $bd(\Sigma) = \emptyset$, and any integers $\kappa, \phi, \mu
\ge 0$, there are integers $\theta, \lambda, \rho \ge 0$ such that the following holds. Let
$\mathscr{T}^*$ be a tangle in a graph $G$, such that some $\Sigma$-span of order $\ge
\theta$ is $(\lambda, \mu)$-flat. Then either* (i) *there is a $\Sigma$-span of order $\ge
\phi$ with $> \kappa$ independent eyes, or* (ii) *there is a $\Sigma'$-span of order $\ge
\phi$, where $\Sigma'$ is a surface obtained by adding a crosscap to $\Sigma$, or* (iii)
*there is a $\mathscr{T}^*$-central segregation of $G$ of type $(\rho, \kappa)$ with an
arrangement in $\Sigma$." -/
def GM15Theorem11Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (κ φ μ : ℕ),
      ∃ (θ lam p : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ ≤ θ₀ →
          (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsSigmaSpan G H' η' θ_star θ' T_star T' ∧
            HasTangleMetric H' θ' T' d' ∧
            φ ≤ θ' ∧
            HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
               φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          Section7S3 S G T_star p κ

/-- Downward eye induction for XV (1.1) retaining the proper arrangement used in XVI (7.2). -/
theorem theorem_1_1_proper :
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (κ φ μ : ℕ),
      ∃ (θ lam p : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ ≤ θ₀ →
          (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsSigmaSpan G H' η' θ_star θ' T_star T' ∧
            HasTangleMetric H' θ' T' d' ∧
            φ ≤ θ' ∧
            HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
               φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          Section7ProperS3 S G T_star p κ := by
  intro S _ _ hSurf hConn hBd κ φ μ
  let μ' : ℕ := 2 * (μ + 6)
  let φ' : ℕ := max φ 8
  let lam_top : ℕ := 4
  let θ_top : ℕ := max φ' (4 * lam_top + μ' + 2)
  have hφ'8 : 8 ≤ φ' := le_max_right _ _
  have hφ_le_φ' : φ ≤ φ' := le_max_left _ _
  have hμ'12 : 12 ≤ μ' := by omega
  have hμ_le_μ' : μ ≤ μ' := by omega
  have hμ'_even : Even μ' := ⟨μ + 6, by ring⟩
  have hθ_top_ge : 4 * lam_top + μ' + 2 ≤ θ_top := le_max_right _ _
  have hφ_le_θ_top : φ ≤ θ_top := hφ_le_φ'.trans (le_max_left _ _)
  obtain ⟨p, lam₀, θ₀_base, hlam₀4, hθ₀_base_ge, hInd⟩ :=
    inductive_step_1_1 hSurf hConn hBd hφ'8 hμ'12 hμ'_even
      (le_refl 4) hθ_top_ge (κ + 1) le_rfl
  let θ : ℕ := max θ₀_base (4 * lam₀ + μ' + 2)
  refine ⟨θ, lam₀, p, ?_⟩
  intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ_le
  have hθ₀_base_le : θ₀_base ≤ θ₀ := (le_max_left _ _).trans hθ_le
  have hord_μ' : 4 * lam₀ + μ' + 2 ≤ θ₀ := (le_max_right _ _).trans hθ_le
  have hFlat_μ' : IsFlatSpan G H₀ η₀ θ_star θ₀ lam₀ μ' T_star T₀ :=
    hFlat₀.mono_mu hμ_le_μ' hord_μ'
  have hEyes0 : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ (κ + 1 - (κ + 1)) θ₀_base := by
    rw [Nat.sub_self]
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  rcases hInd G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat_μ' hMetric₀ hθ₀_base_le hEyes0 with
    ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩ |
    ⟨S', hTS', hT2S', hCross, H', η', T', hSpan'⟩ | hS3
  · left
    have hθ_top_18 : μ' + 18 ≤ θ_top := by omega
    have hIndEyes : HasIndependentEyes G H₁ η₁ θ_top T₁ d₁ (κ + 1) :=
      independentEyes_of_flatSpan G H₁ η₁ θ_star θ_top μ' κ T_star T₁ d₁ r₁ hFlat₁ hMetric₁
        hμ'12 hθ_top_18 hr₁_inj hr₁_eye hr₁_dist
    exact ⟨H₁, η₁, θ_top, T₁, d₁, hFlat₁.isSpan, hMetric₁, hφ_le_θ_top, hIndEyes⟩
  · right; left
    exact ⟨S', hTS', hT2S', hCross, H', η', φ', T', hφ_le_φ', hSpan'⟩
  · right; right
    exact hS3

/-- **Graph Minors XV, (1.1)** (pages 115–116):
Main theorem of Graph Minors XV, proved from `(1.2)` (`GM15Theorem12Statement`), `(5.1)`
(`theorem_5_1_proof`), and `(7.1)` (`theorem_7_1_proof`). -/
theorem theorem_1_1_proof
     :
    GM15Theorem11Statement.{u, v, w} := by
  intro S _ _ hSurface hConnected hBoundary κ φ μ
  obtain ⟨order, flatness, width, hresult⟩ :=
    theorem_1_1_proper.{u,v,w} S hSurface hConnected hBoundary κ φ μ
  refine ⟨order, flatness, width, ?_⟩
  intro α β G θ_star T_star H η θ₀ T d hFlat hMetric hle
  exact (hresult G θ_star T_star H η θ₀ T d hFlat hMetric hle).imp id
    (Or.imp id Section7ProperS3.toSection7S3)

/-! ## Section 8: Statements and Proofs of `(8.1)`, `(8.2)`, `(8.3)`, and `(8.4)` -/

/-- Statement of Graph Minors XV, (8.1) (page 145):
"For any surface $\Sigma$ with $\text{bd}(\Sigma) = \emptyset$, and any integer $p \ge 0$
there exists $\kappa, \phi \ge 0$ such that the following is true. Let $\mathcal{T}^*$ be a
tangle in a graph $G$ of order $\ge p$, and let $H, \eta, \mathcal{T}$ be a $\Sigma$-span of
order $\ge \phi$, with $\ge \kappa$ independent eyes. Then $\mathcal{T}^*$ controls a $K_p$
minor of $G$." -/
def GM15Theorem81Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ p : ℕ, ∃ κ φ : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ),
        IsSigmaSpan G H η θ_star θ T_star T →
        HasTangleMetric H θ T d →
        p ≤ θ_star → φ ≤ θ →
        HasIndependentEyes G H η θ T d κ →
        ControlsCliqueMinor G p T_star

/-- **Graph Minors XV, (8.1)** (page 145):
For any connected surface `Σ` with `bd(Σ) = ∅` and any `p ≥ 0`, there exist `κ, φ ≥ 0` such that if
`T*` is a tangle in `G` of order `≥ p` and `H, η, T` is a `Σ`-span of order `≥ φ` with `≥ κ`
independent eyes, then `T*` controls a `K_p` minor of `G`.
Proved from Graph Minors XII, `(4.5)` (`GM12Theorem45Statement`). -/
theorem theorem_8_1_proof :
    GM15Theorem81Statement.{u, v, w} := by
  intro S _ _ hSurf hConn hBd p
  have hClosed : IsClosedSurface S :=
    ⟨hSurf.1, hSurf.2.1, fun x => by
      by_contra hx
      exact Set.eq_empty_iff_forall_notMem.mp hBd x hx⟩
  obtain ⟨κ, φ, h⟩ := GraphMinor.GM12.gm15_theorem45.{u, v, w} S hClosed hConn p
  refine ⟨κ, φ, ?_⟩
  intro α β G θ_star T_star H η θ T d hSpan hMetric hp hφ hEyes
  exact controlsCliqueMinor_of_gm12 (h G θ_star T_star H η θ T d hSpan hMetric hp hφ hEyes)

/-- If a `Σ`-span has `κ₂` independent eyes and `κ₁ ≤ κ₂`, then it has `κ₁` independent eyes. -/
theorem HasIndependentEyes.mono {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {κ₁ κ₂ : ℕ}
    (h : HasIndependentEyes G H η θ T d κ₂) (hκ : κ₁ ≤ κ₂) :
    HasIndependentEyes G H η θ T d κ₁ := by
  rcases h with ⟨r, P, Q, hr_inj, hEye, hDist, hDisj⟩
  refine ⟨fun i => r (Fin.castLE hκ i), fun i => P (Fin.castLE hκ i),
    fun i => Q (Fin.castLE hκ i),
    hr_inj.comp (Fin.castLE_injective hκ),
    fun i => hEye (Fin.castLE hκ i),
    fun i j hij => hDist (Fin.castLE hκ i) (Fin.castLE hκ j)
      (fun heq => hij ((Fin.castLE_injective hκ) heq)),
    fun i j hij => hDisj (Fin.castLE hκ i) (Fin.castLE hκ j)
      (fun heq => hij ((Fin.castLE_injective hκ) heq))⟩

/-- Statement of Graph Minors XV, (8.2) (pages 145–146):
"For any surface $\Sigma$ with $\text{bd}(\Sigma) = \emptyset$, and any integers $p, \phi,
\mu \ge 0$, there are integers $\kappa, \theta, \lambda, \rho \ge 0$ such that the following
holds. Let $\mathcal{T}^*$ be a tangle in a graph $G$ such that there is no
$\mathcal{T}^*$-central segregation of $G$ of type $(\rho, \kappa)$ with an arrangement in
$\Sigma$. Then either* ... (i) *$\mathcal{T}^*$ controls a $K_p$ minor of $G$, or* (ii) *there
is a $\Sigma'$-span of order $\ge \phi$, where $\Sigma'$ is a surface obtained by adding a
crosscap to $\Sigma$, or* (iii) *no $\Sigma$-span of order $\ge \theta$ is $(\lambda,
\mu)$-flat." -/
def GM15Theorem82Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (p φ μ : ℕ),
      ∃ (κ θ lam ρ : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β)),
          ¬ Section7S3 S G T_star ρ κ →
          ControlsCliqueMinor G p T_star ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
              φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          (∀ (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
            (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d₀ : Set S → Set S → ℕ),
            θ ≤ θ₀ → HasTangleMetric H₀ θ₀ T₀ d₀ →
            ¬ IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀)

/-- **Graph Minors XV, (8.2)** (pages 145–146):
Proved from `(1.1)` (`theorem_1_1_proof`) and `(8.1)` (`theorem_8_1_proof`). -/
theorem theorem_8_2_proof
     :
    GM15Theorem82Statement.{u, v, w} := by
  have h11 : GM15Theorem11Statement.{u, v, w} :=
    theorem_1_1_proof
  have h81 : GM15Theorem81Statement.{u, v, w} := theorem_8_1_proof
  intro S _ _ hSurf hConn hBd p φ μ
  let p4 := max p 4
  obtain ⟨κ, φ₁, hClique⟩ := h81 S hSurf hConn hBd p4
  let φ₂ := max φ φ₁
  obtain ⟨θ₁, lam, ρ, hMain⟩ := h11 S hSurf hConn hBd κ φ₂ μ
  let θ := max θ₁ p4
  refine ⟨κ, θ, lam, ρ, ?_⟩
  intro α β G θ_star T_star hNoS3
  by_cases hAllNotFlat :
      ∀ (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
        (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d₀ : Set S → Set S → ℕ),
        θ ≤ θ₀ → HasTangleMetric H₀ θ₀ T₀ d₀ →
        ¬ IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀
  · exact Or.inr (Or.inr hAllNotFlat)
  · push Not at hAllNotFlat
    rcases hAllNotFlat with ⟨H₀, η₀, θ₀, T₀, d₀, hθ_le, hMetric₀, hFlat₀⟩
    have hp4_le_θ_star : p4 ≤ θ_star :=
      (le_max_right θ₁ p4).trans (hθ_le.trans hFlat₀.isSpan.isControlling.theta_le)
    have hθ₁_le_θ₀ : θ₁ ≤ θ₀ := (le_max_left θ₁ p4).trans hθ_le
    rcases hMain G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₁_le_θ₀ with
      ⟨H', η', θ', T', d', hSpan', hMetric', hφ₂_le, hIndEyes⟩ |
      ⟨S', hTS', hT2S', hCross, H', η', θ', T', hφ₂_le, hSpan'⟩ | hS3
    · left
      have hφ₁_le : φ₁ ≤ θ' := (le_max_right φ φ₁).trans hφ₂_le
      have hEyes_κ : HasIndependentEyes G H' η' θ' T' d' κ :=
        hIndEyes.mono (Nat.le_succ κ)
      have hMinor_p4 : ControlsCliqueMinor G p4 T_star :=
        hClique G θ_star T_star H' η' θ' T' d' hSpan' hMetric' hp4_le_θ_star hφ₁_le hEyes_κ
      exact hMinor_p4.mono (le_max_left p 4)
    · right; left
      exact ⟨S', hTS', hT2S', hCross, H', η', θ', T',
        (le_max_left φ φ₁).trans hφ₂_le, hSpan'⟩
    · exact (hNoS3 hS3).elim

/-- Statement of Graph Minors XV, (8.3) (page 146):
"Let $\lambda, \mu \ge 0$ be integers, let $\mathcal{T}^*$ be a tangle in a graph $G$, and
let $\Sigma$ be a surface with $\text{bd}(\Sigma) = \emptyset$. Then every $\Sigma$-span
which is $(\lambda + \mu + 2, \mu)$-level is $(\lambda, \mu)$-flat." -/
def GM15Theorem83Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ lam μ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ),
    4 * (lam + μ + 2) + 2 < θ →
    IsLevelSpan G H η θ_star θ (lam + μ + 2) μ T_star T d →
    IsFlatSpan G H η θ_star θ lam μ T_star T

/-- **Graph Minors XV, (8.3), Claim (1)** (page 147):
"If $d(z, a), d(z, b) \le \lambda + \mu + 2$, then $H, \eta, \mathcal{T}$ is not $(\lambda + \mu +
2)$-level." (The paper omits `, μ` in `(λ + μ + 2, μ)-level`.) -/
theorem theorem_8_3_claim_1 {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam μ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d'' : Set S → Set S → ℕ} {z : Set S} {P : Graph α β} {a b : S}
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ (lam + μ + 2) T_star T T'' d d'' z)
    (hStep : IsMuStepped G H' η' d'' μ P a b)
    (ha : pointAtomDist H d a z ≤ lam + μ + 2)
    (hb : pointAtomDist H d b z ≤ lam + μ + 2) :
    ¬ IsLevelSpan G H η θ_star θ (lam + μ + 2) μ T_star T d :=
  fun hLevel => hLevel.no_local_stepped_rearrangement hRearr hStep ⟨ha, hb⟩

private theorem path_meets_original_vertices_only_at_start
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (lam : ℕ)
    (μ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (hLevel : IsLevelSpan G H η θ_star θ (lam + μ + 2) μ T_star T d)
    (hord_level : 4 * (lam + μ + 2) + μ + 2 ≤ θ)
    (H' : Drawing S)
    (η' : SpanEmbedding H' G)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ)
    (z : Set S)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hd_symm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (P : Graph α β)
    (a : S)
    (b : S)
    (haH' : a ∈ H'.V)
    (hbH' : b ∈ H'.V)
    (hP : IsHPathWithEnds G η'.imageGraph P (η'.vMap a) (η'.vMap b))
    (hdist' : μ ≤ d' {a} {b})
    (ha_far : lam + μ + 3 ≤ d z {a})
    (hx_a : {a} ∈ H.A)
    (haH : a ∈ H.V)
    (hva_eq : η'.vMap a = η.vMap a)
    (hClaim3 : ∀ e ∈ E(P), P.Inc e (η.vMap a) → e ∉ E(η.imageGraph)) :
    ∀ v ∈ H.V, η.vMap v ∈ V(P) → v = a := by
  intro v₀ hv₀H hv₀P
  by_contra hv₀_ne
  let X : Set α := V(η.imageGraph) \ {η.vMap a}
  have hv₀X : η.vMap v₀ ∈ V(P) ∩ X :=
    ⟨hv₀P, η.bijOn_v.mapsTo hv₀H, fun hEq => hv₀_ne (η.bijOn_v.injOn hv₀H haH hEq)⟩
  have hP_path_a : IsGraphPathWithEnds G P (η.vMap a) (η'.vMap b) := hva_eq ▸ hP.2.1
  obtain ⟨x, Q, _, hxP, hxX, hQP, _, hQ_P, _, _, _, _, hQX⟩ :=
    hP_path_a.exists_first_split_of_nonempty ⟨η.vMap v₀, hv₀X⟩
  obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxX.1
  have hva_ne : η.vMap a ≠ η.vMap v := Ne.symm hxX.2
  have hv_ne_a : v ≠ a := fun hEq => hva_ne (hEq ▸ rfl)
  have hQ_path : IsGraphPathWithEnds G Q (η.vMap a) (η.vMap v) := hQ_P.mono hP.2.1.le
  have hVQ_H : V(Q) ∩ V(η.imageGraph) = {η.vMap a, η.vMap v} := by
    ext y
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hyQ, hyH⟩
      by_cases hya : y = η.vMap a
      · exact Or.inl hya
      · have hyX : y ∈ V(Q) ∩ X := ⟨hyQ, hyH, hya⟩
        rw [hQX, mem_singleton_iff] at hyX
        exact Or.inr hyX
    · rintro (rfl | rfl)
      · exact ⟨hQ_P.left_mem, η.bijOn_v.mapsTo haH⟩
      · exact ⟨hQ_P.right_mem, hxX.1⟩
  have hEQ_H : Disjoint E(Q) E(η.imageGraph) := by
    refine Set.disjoint_left.mpr fun e heQ heH => ?_
    have heG : e ∈ E(G) := hQ_path.le.edgeSet_mono heQ
    obtain ⟨u₁, u₂, hlinkQ⟩ := exists_isLink_of_mem_edgeSet heQ
    have hlinkG : G.IsLink e u₁ u₂ := hlinkQ.mono hQ_path.le
    have hlinkH : η.imageGraph.IsLink e u₁ u₂ := (η.imageGraph_le.isLink_iff heH).mpr hlinkG
    have hu₁ : u₁ ∈ ({η.vMap a, η.vMap v} : Set α) :=
      hVQ_H ▸ ⟨hlinkQ.left_mem, hlinkH.left_mem⟩
    have hu₂ : u₂ ∈ ({η.vMap a, η.vMap v} : Set α) :=
      hVQ_H ▸ ⟨hlinkQ.right_mem, hlinkH.right_mem⟩
    have hu_ne : u₁ ≠ u₂ := fun hEq => hQ_path.not_isLink_self (hEq ▸ hlinkQ)
    have hinc_a : Q.Inc e (η.vMap a) := by
      rcases hu₁ with rfl | rfl <;> rcases hu₂ with rfl | rfl
      · exact False.elim (hu_ne rfl)
      · exact ⟨_, hlinkQ⟩
      · exact ⟨_, hlinkQ.symm⟩
      · exact False.elim (hu_ne rfl)
    obtain ⟨w, hlink_a⟩ := hinc_a
    exact hClaim3 e (hQP.edgeSet_mono heQ) ⟨w, hlink_a.mono hQP⟩ heH
  have hQ_HPath : IsHPathWithEnds G η.imageGraph Q (η.vMap a) (η.vMap v) :=
    ⟨η.imageGraph_le, hQ_path, hva_ne, η.bijOn_v.mapsTo haH, η.bijOn_v.mapsTo hvH,
      hVQ_H, hEQ_H⟩
  have hd_av_lt : d {a} {v} < μ := by
    by_contra hge
    exact hLevel.not_stepped ⟨Q, a, v, haH, hvH, hQ_HPath, Nat.not_lt.mp hge⟩
  have hv_A : {v} ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
  have htri_zv := hd_tri z hRearr.z_mem {v} hv_A {a} hx_a
  have hsym_av := hd_symm {a} hx_a {v} hv_A
  obtain ⟨hvH', hvv_eq⟩ := hRearr.vMap_eq v hvH (by omega)
  have hv_in_P' : η'.vMap v ∈ V(P) ∩ V(η'.imageGraph) :=
    ⟨hQP.vertexSet_mono (hvv_eq ▸ hQ_P.right_mem), η'.bijOn_v.mapsTo hvH'⟩
  rw [hP.2.2.2.2.2.1] at hv_in_P'
  rcases hv_in_P' with hv_eq_a | hv_eq_b
  · exact hv_ne_a (η'.bijOn_v.injOn hvH' haH' hv_eq_a)
  · have hvb : v = b := η'.bijOn_v.injOn hvH' hbH' hv_eq_b
    subst hvb
    let Λ : Set S := ⋃ z' ∈ {z' ∈ H.A | d z z' ≤ lam}, z'
    have hZ_sub : ∀ z' ∈ H.A, z' ∉ H'.A → z' ⊆ Λ := by
      intro z' hz' hnot
      have hle : d z z' ≤ lam := by
        by_contra hgt
        exact hnot (hRearr.atom_mem z' hz' (Nat.not_le.mp hgt))
      exact subset_biUnion_of_mem (u := id) ⟨hz', hle⟩
    have hpt_ab : pointDist H d a v = d {a} {v} :=
      pointDist_eq_of_mem_atom hx_a hv_A (mem_singleton a) (mem_singleton v)
    have hpt'_ab : pointDist H' d' a v = d' {a} {v} :=
      pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨a, haH', rfl⟩))
        (Or.inl (Or.inl ⟨v, hvH', rfl⟩)) (mem_singleton a) (mem_singleton v)
    have hltZ : ∀ σ ∈ Λ, pointDist H d a v < pointDist H d a σ := by
      intro σ hσ
      obtain ⟨z', ⟨hz'A, hz'_le⟩, hσz'⟩ := mem_iUnion₂.mp hσ
      rw [hpt_ab, pointDist_eq_of_mem_atom hx_a hz'A (mem_singleton a) hσz']
      have htri := hd_tri z hRearr.z_mem z' hz'A {a} hx_a
      have hsym := hd_symm {a} hx_a z' hz'A
      omega
    have hle_42 :=
      theorem_4_2_proof H H' Λ θ (θ - (4 * lam + 2)) (4 * lam + 2)
        T T' d d' a v hS hConn hLevel.hasMetric hRearr.isCompression.hasMetric'
        hZ_sub (Or.inl hRearr.isCompression) hltZ (by rw [hpt_ab]; omega)
    rw [hpt_ab, hpt'_ab] at hle_42
    omega

private theorem return_vertex_has_small_atom_distance
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (lam : ℕ)
    (μ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (hLevel : IsLevelSpan G H η θ_star θ (lam + μ + 2) μ T_star T d)
    (H' : Drawing S)
    (η' : SpanEmbedding H' G)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ)
    (z : Set S)
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hd_symm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (b : S)
    (Q : Graph α β)
    (c : S)
    (hcH : c ∈ H.V)
    (hQ_H' : IsGraphPathWithEnds η'.imageGraph Q (η'.vMap b) (η.vMap c))
    (hbc_ne : η'.vMap b ≠ η.vMap c)
    (hEQ_H : Disjoint E(Q) E(η.imageGraph))
    (hc_A : {c} ∈ H.A) :
    d z {c} ≤ lam + 2 := by
  by_contra hgt
  obtain ⟨hcH', hvc_eq⟩ := hRearr.vMap_eq c hcH (by omega)
  obtain ⟨e', he'Q, hinc_c⟩ := hQ_H'.exists_inc_right hbc_ne
  have he'H' : e' ∈ E(η'.imageGraph) := hQ_H'.le.edgeSet_mono he'Q
  obtain ⟨f, hf, hfe'⟩ := η'.bijOn_e.surjOn he'H'
  obtain ⟨w, hlinkQ⟩ := hinc_c
  have hlinkH' : η'.imageGraph.IsLink (η'.eMap f) (η'.vMap c) w := by
    rw [hfe', hvc_eq]
    exact hlinkQ.mono hQ_H'.le
  have hcf : c ∈ closure f := (η'.inc_iff f hf c hcH').mp ⟨w, hlinkH'⟩
  let S_A : Set (Set S) := {z' ∈ H.A | d z z' ≤ lam}
  have hHA_fin : H.A.Finite :=
    ((H.finite_V.image fun v => ({v} : Set S)).union H.finite_edges).union
      (GM11.finite_R hS H)
  have hS_A_fin : S_A.Finite := hHA_fin.subset fun _ h => h.1
  have hf_sub : f ⊆ ⋃ z' ∈ S_A, z' := by
    intro σ hσf
    obtain ⟨aσ, haσ, hσ_aσ⟩ := exists_atom_of_point H σ
    have haσ_le : d z aσ ≤ lam := by
      by_contra hgt_σ
      have haσ_H' : aσ ∈ H'.A := hRearr.atom_mem aσ haσ (Nat.not_le.mp hgt_σ)
      have haσ_eq : aσ = f :=
        atom_eq_of_mem haσ_H' (Or.inl (Or.inr hf)) hσ_aσ hσf
      rw [haσ_eq] at haσ hgt_σ
      have hfH : f ∈ H.E := edge_mem_E_of_mem_A hS hf haσ
      obtain ⟨_, hf_eq⟩ := hRearr.eMap_eq f hfH (Nat.not_le.mp hgt_σ)
      have he'H : e' ∈ E(η.imageGraph) := by
        rw [← hfe', hf_eq]
        exact η.bijOn_e.mapsTo hfH
      exact Set.disjoint_left.mp hEQ_H he'Q he'H
    exact mem_iUnion₂.mpr ⟨aσ, ⟨haσ, haσ_le⟩, hσ_aσ⟩
  have hc_cl : c ∈ closure (⋃ z' ∈ S_A, z') := closure_mono hf_sub hcf
  rw [hS_A_fin.closure_biUnion] at hc_cl
  obtain ⟨z', ⟨hz'A, hz'_le⟩, hcz'⟩ := mem_iUnion₂.mp hc_cl
  have hdc_z' : d {c} z' ≤ 2 :=
    vertex_atom_dist_le_two hS hLevel.hasMetric c hcH z' hz'A hcz'
  have htri := hd_tri z hRearr.z_mem z' hz'A {c} hc_A
  have hsym := hd_symm {c} hc_A z' hz'A
  omega

/-- **Graph Minors XV, (8.3)** (pages 146–148):
Every `(λ + μ + 2, μ)`-level `Σ`-span is `(λ, μ)`-flat. -/
theorem theorem_8_3_proof
     :
    GM15Theorem83Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ lam μ T_star T d hθ_lt hLevel
  have hord_level : 4 * (lam + μ + 2) + μ + 2 ≤ θ := hLevel.order_ge
  have hord_lam : 4 * lam + μ + 2 ≤ θ := by omega
  refine ⟨hLevel.isSpan, hord_lam, fun H' η' T' d₁ d' z hRearr₀ hStep₀ => ?_⟩
  have hS : IsClosedSurface S :=
    ⟨hLevel.isSpan.isSurface.1, hLevel.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hLevel.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hLevel.isSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hd₁_A, hd₁_pt, _⟩ :=
    tangleMetric_eq_of_hasTangleMetric hS hConn hRearr₀.isCompression.hasMetric
      hLevel.hasMetric
  have hRearr : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z := by
    refine ⟨hRearr₀.z_mem, hRearr₀.isSpan, hRearr₀.isSpan',
      fun a ha hlt => hRearr₀.atom_mem a ha ?_,
      fun v hv hlt => hRearr₀.vMap_eq v hv ?_,
      fun e he hlt => hRearr₀.eMap_eq e he ?_,
      ⟨hRearr₀.isCompression.lam_lt, hLevel.hasMetric, hRearr₀.isCompression.hasMetric',
        fun σ₁ σ₂ => ?_⟩⟩
    · rwa [hd₁_A z hRearr₀.z_mem a ha]
    · rwa [hd₁_A z hRearr₀.z_mem {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
    · rwa [hd₁_A z hRearr₀.z_mem e (Or.inl (Or.inr he))]
    · rw [← hd₁_pt σ₁ σ₂]
      exact hRearr₀.isCompression.dist_le σ₁ σ₂
  obtain ⟨_, hd_refl, _, hd_symm, hd_tri, hd_inc⟩ := gm11_theorem_9_1 H θ T d hS hConn
    hLevel.hasMetric
  obtain ⟨_, hd'_refl, _, hd'_symm, hd'_tri, hd'_inc⟩ :=
    gm11_theorem_9_1 H' (θ - (4 * lam + 2)) T' d' hS hConn hRearr.isCompression.hasMetric'
  obtain ⟨P, a₀, b₀, ha₀H', hb₀H', hP₀, hdist₀⟩ := hStep₀
  -- Step 1: By Claim (1), we cannot have both `d(z, a₀), d(z, b₀) ≤ lam + μ + 2`.
  have hNotBoth : ¬ (pointAtomDist H d a₀ z ≤ lam + μ + 2 ∧
      pointAtomDist H d b₀ z ≤ lam + μ + 2) := by
    rintro ⟨ha₀, hb₀⟩
    obtain ⟨d'', hRearr'', hd''_eq, _⟩ :=
      hRearr.truncation_of_dist_le hRearr.z_mem (lam₂ := lam + μ + 2) (by omega)
        (by rw [hd_refl z hRearr.z_mem]; omega) hθ_lt
    have hStep'' : IsMuStepped G H' η' d'' μ P a₀ b₀ := by
      refine ⟨ha₀H', hb₀H', hP₀, ?_⟩
      rw [hd''_eq {a₀} (Or.inl (Or.inl ⟨a₀, ha₀H', rfl⟩))
        {b₀} (Or.inl (Or.inl ⟨b₀, hb₀H', rfl⟩))]
      omega
    exact theorem_8_3_claim_1 hRearr'' hStep'' ha₀ hb₀ hLevel
  -- We may assume `lam + μ + 3 ≤ pointAtomDist H d a z`.
  have hex_ab : ∃ a b : S,
      a ∈ H'.V ∧ b ∈ H'.V ∧
      IsHPathWithEnds G η'.imageGraph P (η'.vMap a) (η'.vMap b) ∧
      μ ≤ d' {a} {b} ∧
      lam + μ + 3 ≤ pointAtomDist H d a z := by
    by_cases ha₀_le : pointAtomDist H d a₀ z ≤ lam + μ + 2
    · have hb₀_gt : ¬ pointAtomDist H d b₀ z ≤ lam + μ + 2 :=
        fun hb₀_le => hNotBoth ⟨ha₀_le, hb₀_le⟩
      refine ⟨b₀, a₀, hb₀H', ha₀H', hP₀.symm, ?_, by omega⟩
      rwa [hd'_symm {b₀} (Or.inl (Or.inl ⟨b₀, hb₀H', rfl⟩))
        {a₀} (Or.inl (Or.inl ⟨a₀, ha₀H', rfl⟩))]
    · exact ⟨a₀, b₀, ha₀H', hb₀H', hP₀, hdist₀, by omega⟩
  obtain ⟨a, b, haH', hbH', hP, hdist', ha_far⟩ := hex_ab
  -- Claim (2): `lam + μ + 3 ≤ d z {a}`, `a ∈ H.V`, and `η'.vMap a = η.vMap a`.
  obtain ⟨x_a, hx_a, ha_xa⟩ := exists_atom_of_point H a
  have hpt_a : pointAtomDist H d a z = d z x_a := by
    rw [pointAtomDist_eq_of_mem_atom hx_a ha_xa, hd_symm x_a hx_a z hRearr.z_mem]
  rw [hpt_a] at ha_far
  have hx_a_H' : x_a ∈ H'.A := hRearr.atom_mem x_a hx_a (by omega)
  have hx_a_eq : x_a = {a} :=
    atom_eq_of_mem hx_a_H' (Or.inl (Or.inl ⟨a, haH', rfl⟩)) ha_xa (mem_singleton a)
  rw [hx_a_eq] at hx_a ha_far
  have haH : a ∈ H.V := vertex_mem_V_of_mem_A hS haH' hx_a
  have hva_eq : η'.vMap a = η.vMap a := (hRearr.vMap_eq a haH (by omega)).2
  -- Claim (3): No edge of `P` incident with `η.vMap a` is in `E(η.imageGraph)`.
  have hClaim3 : ∀ e ∈ E(P), P.Inc e (η.vMap a) → e ∉ E(η.imageGraph) := by
    intro e heP hinc_a heH
    obtain ⟨f, hf, hfe⟩ := η.bijOn_e.surjOn heH
    obtain ⟨w, hlinkP⟩ := hinc_a
    have hlinkG : G.IsLink e (η.vMap a) w := hlinkP.mono hP.2.1.le
    have hlinkH : η.imageGraph.IsLink (η.eMap f) (η.vMap a) w :=
      hfe ▸ (η.imageGraph_le.isLink_iff heH).mpr hlinkG
    have haf : a ∈ closure f := (η.inc_iff f hf a haH).mp ⟨w, hlinkH⟩
    have hdf : d {a} f ≤ 2 := hd_inc.2 a haH f hf haf
    have htri := hd_tri z hRearr.z_mem f (Or.inl (Or.inr hf)) {a} hx_a
    have hsym := hd_symm {a} hx_a f (Or.inl (Or.inr hf))
    obtain ⟨hf', hf_eq⟩ := hRearr.eMap_eq f hf (by omega)
    have heH' : e ∈ E(η'.imageGraph) := by
      rw [← hfe, ← hf_eq]
      exact η'.bijOn_e.mapsTo hf'
    exact Set.disjoint_left.mp hP.2.2.2.2.2.2 heP heH'
  -- Claim (4): There is no `v ∈ H.V` with `v ≠ a` and `η.vMap v ∈ V(P)`.
  have hClaim4 : ∀ v ∈ H.V, η.vMap v ∈ V(P) → v = a := by
    exact path_meets_original_vertices_only_at_start (S := S) (α := α) (β := β) G H η θ_star θ lam
      μ T_star T d hLevel hord_level H' η' T' d' z hS hRearr hd_symm hd_tri P a b haH' hbH'
      hP hdist' ha_far hx_a haH hva_eq hClaim3
  have hVP_H : V(P) ∩ V(η.imageGraph) = {η.vMap a} := by
    ext y
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hyP, hyH⟩ => ?_, ?_⟩
    · obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hyH
      rw [hClaim4 v hvH hyP]
    · rintro rfl
      exact ⟨hva_eq ▸ hP.2.1.left_mem, η.bijOn_v.mapsTo haH⟩
  -- Claim (5) & (6): Choose a minimal path `Q` of `η'(H')` from `η'(b)` to `V(η(H))`.
  have hH'E : H'.E.Nonempty :=
    edges_nonempty_of_tangle hS hRearr.isCompression.hasMetric'.1 (by omega)
  obtain ⟨R₀, hR₀⟩ :=
    η'.exists_path_imageGraph hS hRearr.isSpan'.isRespectful.1 hH'E hbH' haH'
  have hR₀_inter : (V(R₀) ∩ V(η.imageGraph)).Nonempty :=
    ⟨η.vMap a, hva_eq ▸ hR₀.right_mem, η.bijOn_v.mapsTo haH⟩
  obtain ⟨x_c, Q, _, hxR₀, hxH, hQR₀, _, hQ_R₀, _, _, _, _, hQV_H⟩ :=
    hR₀.exists_first_split_of_nonempty hR₀_inter
  obtain ⟨c, hcH, rfl⟩ := η.bijOn_v.surjOn hxH
  have hQ_H' : IsGraphPathWithEnds η'.imageGraph Q (η'.vMap b) (η.vMap c) :=
    hQ_R₀.mono hR₀.le
  have hQ_G : IsGraphPathWithEnds G Q (η'.vMap b) (η.vMap c) :=
    hQ_H'.mono η'.imageGraph_le
  -- Claim (5): `η'.vMap b ≠ η.vMap c`.
  have hbc_ne : η'.vMap b ≠ η.vMap c := by
    intro hEq
    have hb_in : η'.vMap b ∈ V(P) ∩ V(η.imageGraph) :=
      ⟨hP.2.1.right_mem, hEq ▸ hxH⟩
    rw [hVP_H, mem_singleton_iff, ← hva_eq] at hb_in
    exact hP.2.2.1 hb_in.symm
  have hEQ_H : Disjoint E(Q) E(η.imageGraph) := by
    refine Set.disjoint_left.mpr fun e heQ heH => ?_
    obtain ⟨u₁, u₂, hlinkQ⟩ := exists_isLink_of_mem_edgeSet heQ
    have hlinkG : G.IsLink e u₁ u₂ := hlinkQ.mono hQ_G.le
    have hlinkH : η.imageGraph.IsLink e u₁ u₂ := (η.imageGraph_le.isLink_iff heH).mpr hlinkG
    have hu₁ : u₁ = η.vMap c := by
      have : u₁ ∈ V(Q) ∩ V(η.imageGraph) := ⟨hlinkQ.left_mem, hlinkH.left_mem⟩
      rwa [hQV_H, mem_singleton_iff] at this
    have hu₂ : u₂ = η.vMap c := by
      have : u₂ ∈ V(Q) ∩ V(η.imageGraph) := ⟨hlinkQ.right_mem, hlinkH.right_mem⟩
      rwa [hQV_H, mem_singleton_iff] at this
    exact hQ_G.not_isLink_self (hu₁ ▸ hu₂ ▸ hlinkQ)
  -- Claim (6): `d z {c} ≤ lam + 2`.
  have hc_A : {c} ∈ H.A := Or.inl (Or.inl ⟨c, hcH, rfl⟩)
  have hClaim6 : d z {c} ≤ lam + 2 := by
    exact return_vertex_has_small_atom_distance (S := S) (α := α) (β := β) G H η θ_star θ lam μ
      T_star T d hLevel H' η' T' d' z hS hRearr hd_symm hd_tri b Q c hcH hQ_H' hbc_ne
      hEQ_H hc_A
  -- Combine `P` and `Q` into an `η(H)`-path from `η(a)` to `η(c)` with `d({a}, {c}) ≥ μ`.
  have hac_ne : a ≠ c := fun hEq => by
    rw [hEq] at ha_far
    omega
  have hvac_ne : η.vMap a ≠ η.vMap c :=
    fun hEq => hac_ne (η.bijOn_v.injOn haH hcH hEq)
  have hVP_Q : V(P) ∩ V(Q) = {η'.vMap b} := by
    ext y
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hyP, hyQ⟩
      have hy_ab : y ∈ ({η'.vMap a, η'.vMap b} : Set α) :=
        hP.2.2.2.2.2.1 ▸ ⟨hyP, hQ_H'.le.vertexSet_mono hyQ⟩
      rcases hy_ab with rfl | rfl
      · exfalso
        have ha_in_Q : η.vMap a ∈ V(Q) ∩ V(η.imageGraph) :=
          ⟨hva_eq ▸ hyQ, η.bijOn_v.mapsTo haH⟩
        rw [hQV_H, mem_singleton_iff] at ha_in_Q
        exact hvac_ne ha_in_Q
      · rfl
    · rintro rfl
      exact ⟨hP.2.1.right_mem, hQ_H'.left_mem⟩
  let P_union := subgraphUnion G P Q
  have hPu_path : IsGraphPathWithEnds G P_union (η.vMap a) (η.vMap c) :=
    (hva_eq ▸ hP.2.1).subgraphUnion hQ_G hVP_Q
  have hVPu_H : V(P_union) ∩ V(η.imageGraph) = {η.vMap a, η.vMap c} := by
    rw [vertexSet_subgraphUnion, union_inter_distrib_right, hVP_H, hQV_H]
    rfl
  have hEPu_H : Disjoint E(P_union) E(η.imageGraph) := by
    rw [edgeSet_subgraphUnion hP.2.1.le hQ_G.le, disjoint_union_left]
    refine ⟨?_, hEQ_H⟩
    refine Set.disjoint_left.mpr fun e heP heH => ?_
    obtain ⟨u₁, u₂, hlinkP⟩ := exists_isLink_of_mem_edgeSet heP
    have hlinkG : G.IsLink e u₁ u₂ := hlinkP.mono hP.2.1.le
    have hlinkH : η.imageGraph.IsLink e u₁ u₂ := (η.imageGraph_le.isLink_iff heH).mpr hlinkG
    have hu₁ : u₁ = η.vMap a := by
      have : u₁ ∈ V(P) ∩ V(η.imageGraph) := ⟨hlinkP.left_mem, hlinkH.left_mem⟩
      rwa [hVP_H, mem_singleton_iff] at this
    have hu₂ : u₂ = η.vMap a := by
      have : u₂ ∈ V(P) ∩ V(η.imageGraph) := ⟨hlinkP.right_mem, hlinkH.right_mem⟩
      rwa [hVP_H, mem_singleton_iff] at this
    exact hP.2.1.not_isLink_self (hu₁ ▸ hu₂ ▸ hlinkP)
  have hPu_HPath : IsHPathWithEnds G η.imageGraph P_union (η.vMap a) (η.vMap c) :=
    ⟨η.imageGraph_le, hPu_path, hvac_ne, η.bijOn_v.mapsTo haH, η.bijOn_v.mapsTo hcH,
      hVPu_H, hEPu_H⟩
  have htri_ac := hd_tri z hRearr.z_mem {c} hc_A {a} hx_a
  have hsym_ac := hd_symm {a} hx_a {c} hc_A
  exact hLevel.not_stepped ⟨P_union, a, c, haH, hcH, hPu_HPath, by omega⟩

/-- Statement of Graph Minors XV, (8.4) (page 148):
"For any surface $\Sigma$ with $bd(\Sigma) = \emptyset$, and any integers $p, \phi, \mu \ge 0$,
there are integers $\kappa, \theta, \lambda, \rho \ge 0$ such that the following holds. Let
$\mathscr{T}^*$ be a tangle in a graph $G$ such that there is no $\mathscr{T}^*$-central
segregation of $G$ of type $(\rho, \kappa)$ with an arrangement in $\Sigma$. Then either
(i) $\mathscr{T}^*$ controls a $K_p$ minor of $G$, or
(ii) there is a $\Sigma'$-span of order $\ge \phi$, where $\Sigma'$ is a surface obtained by adding
a crosscap to $\Sigma$, or
(iii) no $\Sigma$-span of order $\ge \theta$ is $(\lambda, \mu)$-level." -/
def GM15Theorem84Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (p φ μ : ℕ),
      ∃ (κ θ lam ρ : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β)),
          ¬ Section7S3 S G T_star ρ κ →
          ControlsCliqueMinor G p T_star ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
              φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          (∀ (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
            (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d₀ : Set S → Set S → ℕ),
            θ ≤ θ₀ → ¬ IsLevelSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ d₀)

/-- **Graph Minors XV, (8.4)** (page 148):
"Choose $\kappa, \theta, \lambda', \rho$ to satisfy (8.2). Let $\lambda = \lambda' + \mu +
2$; and we claim that (8.4) holds. For let $\mathscr{T}^*, G$ be as (8.4). By (8.2), we may
assume that no $\Sigma$-span of order $\ge \theta$ is $(\lambda', \mu)$-flat. By (8.3), no
$\Sigma$-span of order $\ge \theta$ is $(\lambda, \mu)$-level, as required." -/
theorem theorem_8_4_proof
     :
    GM15Theorem84Statement.{u, v, w} := by
  have h82 : GM15Theorem82Statement.{u, v, w} :=
    theorem_8_2_proof
  have h83 : GM15Theorem83Statement.{u, v, w} := theorem_8_3_proof
  intro S _ _ hSurf hConn hBd p φ μ
  obtain ⟨κ, θ₁, lam', ρ, h⟩ := h82 S hSurf hConn hBd p φ μ
  refine ⟨κ, max θ₁ (4 * (lam' + μ + 2) + 3), lam' + μ + 2, ρ, ?_⟩
  intro α β G θ_star T_star hNoS3
  rcases h G θ_star T_star hNoS3 with hClique | hCross | hNotFlat
  · exact Or.inl hClique
  · exact Or.inr (Or.inl hCross)
  · right; right
    intro H₀ η₀ θ₀ T₀ d₀ hθ_le hLevel
    exact hNotFlat H₀ η₀ θ₀ T₀ d₀ ((le_max_left _ _).trans hθ_le) hLevel.hasMetric
      (h83 G H₀ η₀ θ_star θ₀ lam' μ T_star T₀ d₀
        (by have := (le_max_right θ₁ (4 * (lam' + μ + 2) + 3)).trans hθ_le; omega) hLevel)

end GraphMinor.GM15
