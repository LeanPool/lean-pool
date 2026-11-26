/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffNest
import LeanPool.GraphMinor.Surface.Circle

/-!
# Parallel copies of the circuits, and the grid of page 234

Graph Minors VII, (5.9), page 234. A circuit of `G` that bounds a disc has a parallel copy `H(C)`,
just outside it, which is a `G`-normal `O`-arc with the same vertices.
We apply the grid theorem (5.8) to the part of the surface between the parallel copies of two
circuits of the nest.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- An `O`-arc is infinite. -/
theorem isOArc_infinite_any {Y : Type*} [TopologicalSpace Y] {F : Set Y}
    (hF : IsOArc F) : F.Infinite :=
  hF.infinite

/-- The closure of an edge adds only vertices. -/
theorem closure_edge_subset_union [T2Space S] (H : Drawing S) {e : Set S}
  (he : e ∈ H.E) : closure e ⊆ e ∪ H.V := fun x hx => by
  obtain ⟨γ, hγc, h0, h1, -, himg⟩ := exists_edge_param H he
  have hc : closure e ⊆ range γ := by
    refine closure_minimal (fun y hy => ?_) (isCompact_range hγc).isClosed
    rw [← himg] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact ⟨t, rfl⟩
  obtain ⟨t, rfl⟩ := hc hx
  by_cases h3 : t ∈ Ioo (0 : unitInterval) 1
  · exact .inl (himg ▸ mem_image_of_mem _ h3)
  · have : t = 0 ∨ t = 1 := by
      by_contra hn
      push Not at hn
      exact h3 ⟨unitInterval.pos_iff_ne_zero.mpr hn.1, unitInterval.lt_one_iff_ne_one.mpr hn.2⟩
    rcases this with rfl | rfl
    · exact .inr h0
    · exact .inr h1

/-- **The parallel copy of a circuit.** "Let $H(C)$ be a $G$-normal $O$-arc surrounding $C$, with
$V(G) \cap H(C) = V(N(C))$, such
that the points of $U(G)$ inside $H(C)$ are the points of $U(G)$ inside $U(N(C))$ together
with the points in the edges of $N(C)$" (page 235). -/
theorem exists_parallel_disc [T2Space S] [T2Space T] {G c : Drawing S}
  (hcG : c.IsSubdrawing G) {j : S → T} (hj : IsClosedEmbedding j) {B F : Set T}
    (hB : IsClosedDisc B) (hF : IsClosedDisc F) (hBF : B ⊆ F \ discBd F) (hbd : discBd B
      = j '' c.U) :
    ∃ B', IsClosedDisc B' ∧ B ⊆ B' ∧ B' ⊆ F \ discBd F ∧ G.IsNormal (j ⁻¹' discBd B')
      ∧ G.V ∩ j ⁻¹' discBd B' = c.V ∧ ∀ x ∈ G.U, j x ∈ B' → j x ∈ B := by
  classical
  let Z₀ : Set S := G.V ∪ ⋃ e ∈ {e ∈ G.E | e ∉ c.E}, closure e
  have hZ₀ : IsClosed Z₀ := by
    refine G.finite_V.isClosed.union ?_
    exact (G.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
  have hZ : IsClosed (j '' Z₀) := hj.isClosedMap _ hZ₀
  obtain ⟨B', h1, h2, h3, h4, h5, h6, h7⟩ := exists_disc_push_off hB hF hBF hZ
  have hin : ∀ {x}, x ∈ G.V → j x ∈ j '' Z₀ := fun hx => mem_image_of_mem j (.inl hx)
  have hedge : ∀ {x e}, x ∈ e → e ∈ G.E → e ∉ c.E → j x ∈ j '' Z₀ := fun {x e} hx he hc
    => mem_image_of_mem j (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hc⟩, subset_closure hx⟩))
  have hoff : ∀ {x e}, j x ∈ j '' Z₀ → x ∉ G.V → e ∈ c.E → x ∈ e → False := fun {x e} hx hV he hxe
    => by
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' := hj.injective hyx
    subst hyx'
    rcases hy with hy | hy
    · exact hV hy
    · obtain ⟨e', ⟨he', hc⟩, hy⟩ := mem_iUnion₂.mp hy
      by_cases hy' : y ∈ e'
      · exact hc (arcComponent_eq (hcG.2 he) he' hxe hy' ▸ he)
      · exact hV ((closure_edge_subset_union G he' hy).resolve_left hy')
  have hbU : ∀ {x}, j x ∈ discBd B → x ∈ c.U := fun {x} hx => by
    rw [hbd] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact hj.injective he ▸ hy
  refine ⟨B', h1, h2, h3, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hU⟩
    by_contra hV
    obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hU hV
    by_cases hc : e ∈ c.E
    · have hxc : x ∈ c.U := hc.2.1 hxe |>.1
      exact hoff (h5 ⟨hx, Surface.discBd_subset _ (hbd ▸ mem_image_of_mem j hxc)⟩) hV hc hxe
    · have h8 := h7 ⟨hx, hedge hxe he hc⟩
      have hxc := hbU h8
      have hxV : x ∉ c.V := fun h => hV (hcG.1 h)
      obtain ⟨e', he', hxe'⟩ := c.exists_edge_of_mem hxc hxV
      exact hc (arcComponent_eq (hcG.2 he') he hxe' hxe ▸ he')
  · refine subset_antisymm (fun x hx => ?_) fun x hx => ?_
    · exact mem_V_of_subdrawing hcG (hbU (h7 ⟨hx.2, hin hx.1⟩)) hx.1
    · have hxc := c.V_subset_U hx
      exact ⟨hcG.1 hx, h6 ⟨hbd ▸ mem_image_of_mem j hxc, hin (hcG.1 hx)⟩⟩
  · intro x hU hx
    by_contra hxB
    by_cases hV : x ∈ G.V
    · exact disjoint_left.mp h4 ⟨hx, hxB⟩ (hin hV)
    · obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hU hV
      by_cases hc : e ∈ c.E
      · exact hxB (Surface.discBd_subset _ (hbd ▸ mem_image_of_mem j (hc.2.1 hxe |>.1)))
      · exact disjoint_left.mp h4 ⟨hx, hxB⟩ (hedge hxe he hc)

/-- The nest of circuits `C_j` of page 234, for a cuff disc `E`, in a disc `Δ`. -/
structure IsCuffNest (G : Drawing S) (j : S → T) (C : Set S) (E : Set T) (r : ℕ) (s : ℕ) (B : ℕ
  → Drawing S) (Ds : ℕ → Set T) (Δ : Set T) : Prop where
  circuit : ∀ t < s, (B t).IsCircuit
  sub : ∀ t < s, (B t).IsSubdrawing G
  offE : ∀ t < s, Disjoint (j ⁻¹' discInt E) (B t).U
  disc : ∀ t < s, IsClosedDisc (Ds t)
  bd_eq : ∀ t < s, discBd (Ds t) = j '' (B t).U
  mem : ∀ t < s, E ⊆ Ds t
  inΔ : ∀ t < s, Ds t ⊆ Δ
  off : ∀ t < s, Disjoint (Ds t) (bd T)
  reach : ∀ t < s, ∀ y ∈ (B t).V, ∃ X, IsScriptASet G r C X ∧ y ∈ X ∧ j ⁻¹' discBd E ⊆ X
  disj : ∀ t t', t < t' → t' < s → Disjoint (B t).U (B t').U
  nest : ∀ t t', t < t' → t' < s → Ds t ⊆ Ds t'

/-- **The nest exists.** -/
theorem exists_cuff_nest (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) (habc : 3 ≤ 3 * a + 3 * b + c) (hcyl : ¬ Nonempty
    (S ≃ₜ SurfaceModel 0 0 2)) {C : Set S} (hC : C ∈ cuffs S) {j : S → T} {D : Set T}
      (hc : IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C)) {G : Drawing S}
        (hG : G.IsProper) {ra n : ℕ} {E : Set T}
    (hd : IsCuffDisc G j D ra E) (h₁ : ra + n < alpha G) (h₂ : ra + (ra + n) < alpha G)
      (h₃ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → ra + n + (G.V ∩ C₁).ncard < alpha G) {Δ : Set T}
        (hΔ : IsClosedDisc Δ) (hEΔ : E ⊆ Δ) (hA : ∀ z ∈ scriptA G (ra + n) C, j z ∈ Δ) {s : ℕ}
          (hs : s ≤ n) (hs0 : 0 < s) :
    ∃ B Ds, IsCuffNest G j C E (ra + n) s B Ds Δ := by
  classical
  obtain ⟨W, tW, hWc, i, K, G₁, Γ, r₀, p, h⟩ := exists_layer_setup hS hm hC hc hbT hG hd h₁ h₂ h₃
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space T := hc.isSurface.2.1
  have : T2Space W := h.closedW.2.1
  obtain ⟨B, Ds, h1, h2⟩ := h.exists_nest hS habc hm hcyl hC hΔ hEΔ hA hs
  let f : ℕ → Fin s := fun t => if ht : t < s then ⟨t, ht⟩ else ⟨0, hs0⟩
  have hf : ∀ t (ht : t < s), f t = ⟨t, ht⟩ := fun t ht => dite_eq_left ht
  refine ⟨B ∘ f, Ds ∘ f, ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht
    => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t t' htt ht
      => ?_, fun t t' htt ht => ?_⟩⟩
  · exact (h1 (f t)).1
  · have h3 := (h1 (f t)).2.1
    exact ⟨h3.1.trans h.sub.1, h3.2.trans h.sub.2⟩
  · rw [disjoint_left]
    intro x hx hU
    have h3 := (h1 (f t)).2.1.U_subset hU
    rw [h.U] at h3
    exact h3.2 hx
  · exact (h1 (f t)).2.2.1
  · exact (h1 (f t)).2.2.2.1
  · exact (h1 (f t)).2.2.2.2.1
  · exact (h1 (f t)).2.2.2.2.2.1
  · exact (h1 (f t)).2.2.2.2.2.2.1
  · exact (h1 (f t)).2.2.2.2.2.2.2
  · have hlt : f t < f t' := by
      rw [hf t (htt.trans ht), hf t' ht]
      exact htt
    exact (h2 _ _ hlt).1
  · have hlt : f t < f t' := by
      rw [hf t (htt.trans ht), hf t' ht]
      exact htt
    exact (h2 _ _ hlt).2

/-- The discs of the nest are strictly nested. -/
theorem IsCuffNest.subset_diff {G : Drawing S} {j : S → T} {C : Set S} {E : Set T} {r s
  : ℕ} {B : ℕ → Drawing S} {Ds : ℕ → Set T} {Δ : Set T} (h : IsCuffNest G j C E r s B Ds Δ)
    (hman : ∀ x : T, IsManifoldPoint x) (hj : Injective j) {t t' : ℕ} (htt : t < t') (ht : t' < s) :
    Ds t ⊆ Ds t' \ discBd (Ds t') := fun x hx => by
  refine ⟨h.nest t t' htt ht hx, fun hb => ?_⟩
  by_cases h3 : x ∈ discBd (Ds t)
  · rw [h.bd_eq t (htt.trans ht)] at h3
    rw [h.bd_eq t' ht] at hb
    obtain ⟨y, hy, rfl⟩ := h3
    obtain ⟨y', hy', he⟩ := hb
    exact disjoint_left.mp (h.disj t t' htt ht) hy (hj he ▸ hy')
  · exact (discInt_mono hman (h.disc t (htt.trans ht)) (h.nest t t' htt ht) ⟨hx, h3⟩).2 hb

/-- The discs of the nest are nested. -/
theorem IsCuffNest.mono {G : Drawing S} {j : S → T} {C : Set S} {E : Set T} {r s : ℕ} {B : ℕ
  → Drawing S} {Ds : ℕ → Set T} {Δ : Set T} (h : IsCuffNest G j C E r s B Ds Δ) {t t' : ℕ} (htt : t
    ≤ t') (ht : t' < s) : Ds t ⊆ Ds t' := by
  rcases htt.lt_or_eq with h1 | rfl
  · exact h.nest t t' h1 ht
  · exact Subset.refl _

/-- The grid of page 234: the paths `P_i` and the circuits `B_j(C)` between two discs. -/
structure IsCuffGrid (G : Drawing S) (j : S → T) (D₁ Δ₂ : Set T) {r s : ℕ} (P : Fin r → Drawing S)
  (u v : Fin r → S) (B : Fin s → Drawing S) (E : Fin s → Set T) : Prop where
  path : ∀ i, (P i).IsSubdrawing G ∧ j (u i) ∈ discBd D₁ ∧ j (v i) ∈ discBd Δ₂ ∧
    (P i).IsPathBetween (u i) (v i) ∧ j '' (P i).U ⊆ Δ₂ \ discInt D₁
  path_disj : ∀ i i', i ≠ i' → Disjoint (P i).V (P i').V
  circuit : ∀ l, (B l).IsSubdrawing G ∧ (B l).IsCircuit ∧ IsClosedDisc (E l) ∧ discBd (E l) = j ''
    (B l).U ∧ D₁ ⊆ E l ∧ E l ⊆ Δ₂
  mono : ∀ l l', l ≤ l' → E l ⊆ E l'
  circuit_disj : ∀ l l', l ≠ l' → Disjoint (B l).V (B l').V
  inter : ∀ i l, ∃ (Q : Drawing S) (x y : S), Q.IsSubdrawing G ∧ Q.U = (P i).U ∩ (B l).U ∧ Q.V =
    (P i).V ∩ (B l).V ∧ Q.IsPathBetween x y

/-- **The application of (5.8) on page 234.** Take the parallel copies `D₁` of the circuit `C_1` and
`Δ₂` of the circuit `C_{β+1}`. A disc between them with fewer than `r` vertices on its boundary
would contradict the choice of `E`, and a line across them meets `β` disjoint circuits. So (5.8)
gives `r` paths and `β` circuits. -/
theorem IsCuffNest.exists_grid {G : Drawing S} {j : S → T} {C : Set S} {D E : Set T} {r : ℕ} {B :
  ℕ → Drawing S} {Ds : ℕ → Set T} {Δ : Set T} {ra β : ℕ} (h : IsCuffNest G j C E r (β + 3) B Ds Δ)
    (hS : IsSurface S) [ConnectedSpace S] (hc : IsCappedCuff C T j D) (hd : IsCuffDisc G j D ra E)
      (hmax : ∀ Δ', IsCuffDisc G j D ra Δ' → cuffCount G j Δ' ≤ cuffCount G j E) (hβ : 1 ≤ β) :
    ∃ (D₁ Δ₂ : Set T) (P : Fin ra → Drawing S) (u v : Fin ra → S) (N : Fin β → Drawing S)
      (En : Fin β → Set T), IsClosedDisc D₁ ∧ IsClosedDisc Δ₂ ∧ Ds 1 ⊆ D₁ ∧ D₁ ⊆ Ds 2 \ discBd
        (Ds 2) ∧ Ds (β + 1) ⊆ Δ₂ ∧ Δ₂ ⊆ Ds (β + 2) \ discBd (Ds (β + 2))
          ∧ IsCuffGrid G j D₁ Δ₂ P u v N En := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  have hcj : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  have hji := hc.isEmbedding.injective
  have hsd : ∀ {t t'}, t < t' → t' < β + 3 → Ds t ⊆ Ds t' \ discBd (Ds t') := fun htt ht
    => h.subset_diff hman hji htt ht
  obtain ⟨D₁, p1, p2, p3, p4, -, -⟩ := exists_parallel_disc (h.sub 1 (by omega)) hcj (h.disc 1
    (by omega)) (h.disc 2 (by omega)) (hsd (by omega) (by omega)) (h.bd_eq 1 (by omega))
  obtain ⟨Δ₂, q1, q2, q3, q4, -, -⟩ := exists_parallel_disc (h.sub (β + 1) (by omega)) hcj (h.disc
    (β + 1) (by omega)) (h.disc (β + 2) (by omega)) (hsd (by omega) (by omega)) (h.bd_eq (β + 1)
      (by omega))
  have hsub2 : ∀ t, t ≤ β + 1 → Ds t ⊆ Δ₂ := fun t ht => (h.mono ht (by omega)).trans q2
  have hin : D₁ ⊆ Δ₂ \ discBd Δ₂ := fun x hx => by
    have h1 := p3 hx
    refine ⟨hsub2 2 (by omega) h1.1, fun h2 => ?_⟩
    exact (discInt_mono hman (h.disc 2 (by omega)) (hsub2 2 (by omega)) h1).2 h2
  have hDE := hd.2.1
  have hE₁ : E ⊆ D₁ := (h.mem 1 (by omega)).trans p2
  have hr : Δ₂ \ discInt D₁ ⊆ range j := fun x hx => by
    by_contra hxr
    rcases hc.union_eq.ge (mem_univ x) with h1 | h1
    · exact hxr h1
    · refine hx.2 (discInt_mono hman hc.isClosedDisc (hDE.trans hE₁) ⟨h1, fun hb => hxr ?_⟩)
      rw [hc.discBd_eq] at hb
      exact image_subset_range _ _ hb
  have hint : ∀ x ∈ discBd Δ₂, IsInteriorPoint x := fun x hx => by
    by_contra hb
    exact disjoint_left.mp (h.off (β + 2) (by omega)) (q3 (Surface.discBd_subset _ hx)).1 hb
  -- discs between
  have hi : ∀ B', IsClosedDisc B' → D₁ ⊆ B' → B' ⊆ Δ₂ → G.IsNormal (j ⁻¹' discBd B') → ra ≤
    (G.V ∩ j ⁻¹' discBd B').ncard := fun B' h1 h2 _ h4 => by
    by_contra hlt
    have hB' : IsCuffDisc G j D ra B' := ⟨h1, hDE.trans (hE₁.trans h2), h4, by omega⟩
    have h5 := hmax B' hB'
    have hinf : (B 0).U.Infinite := by
      have h6 := isOArc_infinite_any (h.disc 0 (by omega)).isOArc_discBd
      rw [h.bd_eq 0 (by omega)] at h6
      exact fun hf => h6 (hf.image j)
    obtain ⟨x, hx, hxV⟩ := (hinf.sdiff (B 0).finite_V).nonempty
    obtain ⟨e, he, hxe⟩ := (B 0).exists_edge_of_mem hx hxV
    have heG : e ∈ G.E := (h.sub 0 (by omega)).2 he
    have hE₂ : E ⊆ B' := hE₁.trans h2
    have hnew : ∃ e ∈ G.E, j '' e ⊆ B' ∧ ¬ j '' e ⊆ E := by
      refine ⟨e, heG, ?_, fun h6 => ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        have h7 : j y ∈ discBd (Ds 0) := by
          rw [h.bd_eq 0 (by omega)]
          exact mem_image_of_mem j (he.2.1 hy).1
        exact h2 (p2 (h.mono (Nat.zero_le 1) (by omega) (Surface.discBd_subset _ h7)))
      · have h7 := h6 (mem_image_of_mem j hxe)
        have h8 : j x ∉ discInt E := fun h9 => disjoint_left.mp (h.offE 0 (by omega)) h9 hx
        have h9 : j x ∈ discBd E := by
          by_contra h10
          exact h8 ⟨h7, h10⟩
        exact (heG.2.1 hxe).2 (hd.2.2.1 ⟨h9, (heG.2.1 hxe).1⟩)
    have h6 := cuffCount_lt G j hE₂ (.inr hnew)
    omega
  -- lines across
  have hii : ∀ L u v, IsLineWithEnds L u v → u ∈ discBd D₁ → v ∈ discBd Δ₂ → L ⊆ Δ₂ → Disjoint L
    (discInt D₁) → G.IsNormal (j ⁻¹' L) → β ≤ (G.V ∩ j ⁻¹' L).ncard := fun L u v h1 h2 h3 h4 _ h6
      => by
    have hex : ∀ t : Fin β, ∃ y, y ∈ G.V ∩ j ⁻¹' L ∧ y ∈ (B (t.1 + 2)).U := fun t => by
      have ht1 : t.1 + 2 ≤ β + 1 := by omega
      have ht2 : t.1 + 2 < β + 3 := by omega
      have hne : ¬ Disjoint L (discBd (Ds (t.1 + 2))) := fun hdis => by
        rcases inside_or_off (isPreconnected_of_isLine h1) (h.disc _ ht2).isClosed (hdis.mono_right
          (frontier_disc_subset hman (h.disc _ ht2))) with h7 | h7
        · have h8 : v ∈ discInt (Ds (t.1 + 2)) := ⟨interior_subset (h7 h1.right_mem),
            disjoint_left.mp hdis h1.right_mem⟩
          exact (discInt_mono hman (h.disc _ ht2) (hsub2 _ ht1) h8).2 h3
        · exact h7 h1.left_mem (h.mono (by omega) ht2 (p3 (Surface.discBd_subset _ h2)).1)
      obtain ⟨z, hzL, hzb⟩ := not_disjoint_iff.mp hne
      rw [h.bd_eq _ ht2] at hzb
      obtain ⟨y, hy, rfl⟩ := hzb
      exact ⟨y, ⟨h6 ⟨hzL, (h.sub _ ht2).U_subset hy⟩, hzL⟩, hy⟩
    choose f hf1 hf2 using hex
    have hinj : Injective f := fun t t' he => by
      by_contra hne
      have hne' : t.1 ≠ t'.1 := fun h7 => hne (Fin.ext h7)
      rcases lt_or_gt_of_ne hne' with h7 | h7
      · exact disjoint_left.mp (h.disj (t.1 + 2) (t'.1 + 2) (by omega) (by omega)) (hf2 t)
          (he ▸ hf2 t')
      · exact disjoint_left.mp (h.disj (t'.1 + 2) (t.1 + 2) (by omega) (by omega)) (hf2 t')
          (he ▸ hf2 t)
    have h8 := ncard_image_of_injective (univ : Set (Fin β)) hinj
    rw [ncard_univ, Nat.card_fin] at h8
    rw [← h8]
    refine ncard_le_ncard ?_ (G.finite_V.subset inter_subset_left)
    rintro _ ⟨t, -, rfl⟩
    exact hf1 t
  obtain ⟨P, u, v, N, En, g1, g2, g3, g4, g5, g6⟩ := exists_disc_grid hman hcj p1 q1 hin hr p4 q4
    hint hi hii
  exact ⟨D₁, Δ₂, P, u, v, N, En, p1, q1, p2, p3, q2, q3, g1, g2, g3, g4, g5, g6⟩

end GraphMinor.GM07
