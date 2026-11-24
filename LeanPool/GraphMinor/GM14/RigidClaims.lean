/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidThread
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM14.WhitneyFaces
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Claims (1) and (2) of Graph Minors XIV, (6.5)

Claim (1) (`claim_1_three_paths`): for a circuit `C` of a drawing `H` that is rigid in `Δ`, there
are three
disjoint paths of `H` from `V(C)` to `V(H) ∩ bd(Δ)`. If not, Menger's theorem gives a separation of
order
at most two. The form of Menger's theorem for planar graphs that the paper cites is
`exists_thread_disc`: it
turns the separation into an `O`-arc that bounds a closed disc in `Δ`. This disc holds `U(C)`, which
contradicts rigidity by `claim_1_dial_contradiction_6_5`.

For Claim (2), let `Γ` be the part of `H` in a society, and let `X` be `V(H) ∩ ΩBar`. Each of the
three paths of
Claim (1) from a circuit of `Γ` must pass through `X`, since a vertex of `Γ` off `X` has all its
edges
in `Γ` and is off `bd(Δ)` (`walk_hits`). As `|X| ≤ 3`, each path holds exactly one vertex of `X`,
and
what follows that vertex on the path is off `Γ` (`tail_off`).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11

universe u v

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- **Graph Minors XIV, (6.5), Claim (1), dial contradiction step** (pages 34–35):
In a drawing `H` that is rigid in a closed disc `Δ`, no `O`-arc `F ⊆ Δ` with `F ∩ U(H) ⊆ V(H)` and
`|F ∩ V(H)| ≤ 2` can bound a closed disc `Δ₀ ⊆ Δ` with `U(C) ⊆ Δ₀` for a circuit `C` of `H` ("But
$H$ is rigid, and $F$ only bounds one closed disc in $\Delta$, a contradiction"). -/
theorem claim_1_dial_contradiction_6_5
    {H C : Drawing S} {Δ F Δ₀ : Set S} (hΔ : IsClosedDisc Δ)
    (hrigid : ∀ F' : Set S, F' ⊆ Δ → IsOArc F' → F' ∩ H.U ⊆ H.V →
      (F' ∩ H.V).ncard ≤ 2 →
      ∃ Δ' : Set S, Δ' ⊆ Δ ∧ IsDial H F' Δ' ∧ discBd Δ' = F')
    (hC : C.IsCircuit) (hCH : C.IsSubdrawing H)
    (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFnorm : F ∩ H.U ⊆ H.V) (hFcard : (F ∩ H.V).ncard ≤ 2)
    (hΔ₀ : IsClosedDisc Δ₀) (hΔ₀Δ : Δ₀ ⊆ Δ) (hΔ₀discBd : discBd Δ₀ = F) (hCU₀ : C.U ⊆ Δ₀) :
    False := by
  obtain ⟨Δ₁, hΔ₁Δ, hdial₁, hΔ₁discBd⟩ := hrigid F hFΔ hFo hFnorm hFcard
  obtain ⟨Δ_uniq, -, h_uniq⟩ := disc_oArc Δ F hΔ hFΔ hFo
  have hΔ₀_eq : Δ₀ = Δ_uniq := h_uniq Δ₀ hΔ₀Δ hΔ₀ hΔ₀discBd
  have hΔ₁_eq : Δ₁ = Δ_uniq := h_uniq Δ₁ hΔ₁Δ hdial₁.1 hΔ₁discBd
  have hCU₁ : C.U ⊆ Δ₁ := (hΔ₀_eq.trans hΔ₁_eq.symm) ▸ hCU₀
  exact no_circuit_in_dial hdial₁ hFnorm hC hCH hCU₁

namespace Whitney

variable {H J Γ Γ' : Drawing S} {Δ B X : Set S} {a : S}

/-- **Graph Minors XIV, (6.5), Claim (1)** (pages 34 and 35). Vertices of `H` on an edge of `J` off
`H` lie on
`bd(Δ)`. -/
theorem claim_1_three_paths [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ')
    (hS : IsClosedSurface S) (hsph : IsSphere S) {G₀ : Graph S (Set S)} {Q₀ : Set S → Graph S
      (Set S)}
    (hsd : SubData J.toGraph G₀ Q₀)
    (hB : ∀ v ∈ H.V, ∀ g ∈ J.E, g ∉ H.E → v ∈ closure g → v ∈ subBd Δ) {R : Drawing S}
    (hR : R.IsCircuit) (hRH : R.IsSubdrawing H) :
    ∃ Q : Fin 3 → Graph S (Set S), Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i, IsFromToPath H.toGraph (Q i) R.V (H.V ∩ subBd Δ) := by
  classical
  have : Finite V(H.toGraph) := H.finite_V.to_subtype
  rcases exists_fromToPaths_or_graphSeparation (G := H.toGraph) (X := R.V) (Y
    := H.V ∩ subBd Δ) hRH.1
      inter_subset_left 3 with ⟨Q, h₁, h₂⟩ | ⟨G₁, G₂, hsep, -, hX, hY, hc⟩
  · exact ⟨Q, h₁, h₂⟩
  exfalso
  obtain ⟨hle₁, hle₂, hV, hE, -⟩ := hsep
  have hHJ : H.IsSubdrawing J := ⟨f.Vsub, f.Esub⟩
  have hRJ : R.IsSubdrawing J := hRH.trans hHJ
  let A : Set (Set S) := E(G₁) ∪ R.E
  have hA : A ⊆ H.E := union_subset hle₁.edgeSet_mono hRH.2
  have hbd : Whitney.bdry J.toGraph A ⊆ V(G₁) ∩ V(G₂) := by
    rintro v ⟨⟨e, he, ⟨y, hl⟩⟩, ⟨e', he', hie'⟩⟩
    have hl' := (hHJ.isLink_iff (hA he)).mpr hl
    have hvH : v ∈ H.V := hl'.2.1
    have hv₁ : v ∈ V(G₁) := by
      rcases he with h | h
      · exact ((hle₁.isLink_iff h).mpr hl').left_mem
      · exact hX ((hRH.isLink_iff h).mpr hl').2.1
    refine ⟨hv₁, ?_⟩
    by_contra hv₂
    have hvb : v ∉ subBd Δ := fun h => hv₂ (hY ⟨hvH, h⟩)
    obtain ⟨y', hl₂⟩ := hie'
    have hclo : v ∈ closure e' := by
      have h₁ : v ∈ closure e' ∩ J.V := hl₂.2.2.2 ▸ mem_insert _ _
      exact h₁.1
    have heH : e' ∈ H.E := by
      by_contra hn
      exact hvb (hB v hvH e' he'.1 hn hclo)
    have heG : e' ∈ E(G₂) := by
      have h₁ : e' ∈ E(G₁) ∪ E(G₂) := hE ▸ heH
      exact h₁.resolve_left fun h => he'.2 (Or.inl h)
    exact hv₂ ((hle₂.isLink_iff heG).mpr ((hHJ.isLink_iff heH).mpr hl₂)).left_mem
  have hfinS : (V(G₁) ∩ V(G₂)).Finite := H.finite_V.subset (inter_subset_left.trans
    hle₁.vertexSet_mono)
  have hRE : R.E.Nonempty := by
    obtain ⟨u, W₂, -, hpos, -, hE₂⟩ := id hR
    cases W₂ with
    | nil _ => simp [GraphWalk.length] at hpos
    | @cons _ m _ g hl rest => exact ⟨g, by rw [hE₂]; simp [GraphWalk.edges]⟩
  obtain ⟨g, hg⟩ := hRE
  obtain ⟨x, y, P, D, -, -, -, -, hPE, -, hh, rfl⟩ := exists_thread_disc f r hS hsph hA
    (by have := ncard_le_ncard hbd hfinS; omega) (hfinS.subset hbd) ⟨g, Or.inr hg⟩
  have hEsub : ∀ e ∈ R.E, closure e ⊆ D := fun e he => by
    have h₁ : e ∈ (H.interSet D).E := hPE ▸ Or.inr he
    exact closure_minimal (mem_interSet_E.mp h₁).2 hh.disc.isClosed
  refine claim_1_dial_contradiction_6_5 (F := discBd D) f.disc (fun F' h₁ h₂ h₃ h₄ => ?_) hR hRH
    ((Surface.discBd_subset D).trans hh.sub) hh.disc.isOArc_discBd hh.norm
    (by rw [hh.cap, ncard_pair hh.ne]) hh.disc hh.sub rfl ?_
  · obtain ⟨Δ', h₅, h₆⟩ := f.rigid F' h₁ h₂ h₃ h₄
    exact ⟨Δ', h₅, h₆, (IsClosedDisc.subBd_eq_discBd hS h₆.1).symm.trans h₆.2.1⟩
  · intro z hz
    rw [R.U_eq] at hz
    rcases hz with hz | hz
    · obtain ⟨e, he, -, -, -, ⟨y', hl⟩, -⟩ := circuit_two_edges hsd hR hRJ hz
      have h₁ : z ∈ closure e ∩ J.V := hl.2.2.2 ▸ mem_insert _ _
      exact hEsub e he h₁.1
    · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
      exact hEsub e he hze

omit [T2Space S] in
/-- A walk from `Γ` to `B` meets `X`, if each vertex of `Γ` off `X` is off `B` and has all its edges
in `Γ`. -/
theorem walk_hits (hΓ : Γ.IsSubdrawing H)
    (hout : ∀ v ∈ Γ.V, v ∉ X → v ∉ B ∧ ∀ e ∈ H.E, v ∈ closure e → e ∈ Γ.E) {P : Graph S (Set S)}
    (hP : P ≤ H.toGraph) {u b : S} (W : GraphWalk P u b) (hu : u ∈ Γ.V) (hb : b ∈ B) :
    ∃ x ∈ W.support, x ∈ X := by
  induction W with
  | nil _ =>
    by_contra hn
    refine (hout _ hu fun h => hn ⟨_, ?_, h⟩).1 hb
    simp [GraphWalk.support]
  | @cons u t b g hl rest ih =>
    by_cases huX : u ∈ X
    · exact ⟨u, by simp [GraphWalk.support], huX⟩
    obtain ⟨-, hall⟩ := hout u hu huX
    have hl' := hl.mono hP
    have hcap : closure g ∩ H.V = {u, t} := hl'.2.2.2
    have hu₁ : u ∈ closure g ∩ H.V := hcap ▸ mem_insert _ _
    have ht₁ : t ∈ closure g ∩ H.V := hcap ▸ mem_insert_of_mem _ rfl
    have hgΓ := hall g hl'.1 hu₁.1
    rw [← hΓ.closure_inter_V hgΓ] at ht₁
    obtain ⟨x, hx, hxX⟩ := ih ht₁.2 hb
    exact ⟨x, by simp [GraphWalk.support, hx], hxX⟩

omit [TopologicalSpace S] [T2Space S] in
/-- The part of a walk after one of its vertices. -/
theorem walk_tail {α β : Type*} {P : Graph α β} {u b : α} (W : GraphWalk P u b) {x : α}
  (hx : x ∈ W.support)
    (hs : W.IsSimple) :
    ∃ T : GraphWalk P x b, T.IsSimple ∧ (∀ z ∈ T.support, z ∈ W.support)
      ∧ ∀ e ∈ T.edges, e ∈ W.edges := by
  induction W with
  | @nil v hv =>
    have h₁ : x = v := by simpa [GraphWalk.support] using hx
    subst h₁
    exact ⟨.nil hv, hs, fun z hz => hz, fun e he => he⟩
  | @cons u t b g hl rest ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨.cons hl rest, hs, fun z hz => hz, fun e he => he⟩
    · have hx' : x ∈ rest.support := by
        simp only [GraphWalk.support, List.mem_cons] at hx
        exact hx.resolve_left hxu
      obtain ⟨T, h₁, h₂, h₃⟩ := ih hx' (List.nodup_cons.mp hs).2
      refine ⟨T, h₁, fun z hz => ?_, fun e he => ?_⟩
      · simp [GraphWalk.support, h₂ z hz]
      · simp [GraphWalk.edges, h₃ e he]

omit [T2Space S] in
/-- **What follows the only vertex of `X` on a simple walk to `B` is off `Γ`.** -/
theorem tail_off (hΓ : Γ.IsSubdrawing H)
    (hout : ∀ v ∈ Γ.V, v ∉ X → v ∉ B ∧ ∀ e ∈ H.E, v ∈ closure e → e ∈ Γ.E) {P : Graph S (Set S)}
    (hP : P ≤ H.toGraph) {x b : S} (T : GraphWalk P x b) (hs : T.IsSimple) (hb : b ∈ B)
    (huniq : ∀ z ∈ T.support, z ∈ X → z = x) {z : S} (hz : z ∈ T.support) (hzx : z ≠ x) : z ∉ Γ.V
      := by
  intro hzΓ
  cases T with
  | nil _ => exact hzx (by simpa [GraphWalk.support] using hz)
  | @cons _ t _ g hl rest =>
    have hnd := List.nodup_cons.mp hs
    have hz' : z ∈ rest.support := by
      simp only [GraphWalk.support, List.mem_cons] at hz
      exact hz.resolve_left hzx
    obtain ⟨T₂, -, h₂, -⟩ := walk_tail rest hz' hnd.2
    obtain ⟨w, hw, hwX⟩ := walk_hits hΓ hout hP T₂ hzΓ hb
    have hw' := h₂ w hw
    have hwx : w = x := huniq w (by simp [GraphWalk.support, hw']) hwX
    exact hnd.1 (hwx ▸ hw')

omit [T2Space S] in
/-- The ends of an edge of a walk lie on the walk. -/
theorem walk_edge_ends {u b : S} (W : GraphWalk J.toGraph u b) {g : Set S} (hg : g ∈ W.edges) :
    ∃ p q, J.toGraph.IsLink g p q ∧ p ∈ W.support ∧ q ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at hg
  | @cons u t b c hl rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at hg
    rcases hg with rfl | hg
    · refine ⟨u, t, hl, by simp [GraphWalk.support], ?_⟩
      cases rest <;> simp [GraphWalk.support]
    · obtain ⟨p, q, h₁, h₂, h₃⟩ := ih hg
      exact ⟨p, q, h₁, by simp [GraphWalk.support, h₂], by simp [GraphWalk.support, h₃]⟩

end Whitney

end GraphMinor.GM14
