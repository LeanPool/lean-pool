/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Special
public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM11.Theorem61
public import LeanPool.GraphMinor.GM15.Section3
public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.GM10.Section6

/-!
# Graph Minors XII, Section 6: the claims in the proof of (6.1)

* `ins_eq_of_disc` is claim (1) of the proof of (6.1) (page 258). Let `D ⊆ Δ` be a closed disc, and
  let `I` be a closed disc with the same boundary whose separation is in the tangle. Then `I = D`.
  As in
  the paper, `Γ ∩ D` has no circuit, since `Γ ∩ Δ` is a union of disjoint paths
  (`not_hasCircuit_inter`), and so [4, Theorem (2.10)] gives `I = D`.
* `lev61` is a level on `Δ`: a point on `P_j` has level `2j + 1`, and a point off the paths has
  level
  twice the number of chords before it. An edge of `K` in `Δ` changes the level by one (`lev_step`).
  The paper says without proof that a closed walk `W*` of `K` in `Δ` with `e_1, e_{θ/2}` in
  `ins(W*)`
  has length at least `2θ`. We prove it with this level (`exists_low`, `exists_high`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

/-! ### Claim (1) -/

/-- **A union of disjoint forests has no circuit.** Let the vertex sets of the hypergraphs `H i` be
disjoint, and let none of them have a circuit. If each edge of `G` is an edge of some `H i` with the
same
ends, then `G` has no circuit. -/
theorem not_hasCircuit_of_parts {α β ι : Type*} {G : Hypergraph α β} (H : ι → Hypergraph α β)
    (hdisj : ∀ i j, i ≠ j → Disjoint (H i).vertexSet (H j).vertexSet)
    (hH : ∀ i, ¬ HasCircuit (H i))
    (hE : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (H i).edgeSet ∧ G.ends e = (H i).ends e) :
    ¬ HasCircuit G := by
  have hidx : ∀ {i j : ι} {x : α}, x ∈ (H i).vertexSet → x ∈ (H j).vertexSet → i = j :=
    fun hi hj => by
      by_contra hne
      exact disjoint_left.mp (hdisj _ _ hne) hi hj
  have hadj : ∀ {x y : α}, G.skeleton.Adj x y →
      ∃ i, x ∈ (H i).vertexSet ∧ y ∈ (H i).vertexSet ∧ (H i).skeleton.Adj x y := by
    rintro x y ⟨hxy, e, hx, hy⟩
    obtain ⟨i, -, hends⟩ := hE e (G.edge_mem_of_inc hx)
    have hx' : x ∈ (H i).ends e := hends ▸ hx
    have hy' : y ∈ (H i).ends e := hends ▸ hy
    exact ⟨i, (H i).vertex_mem_of_inc hx', (H i).vertex_mem_of_inc hy', hxy, e, hx', hy'⟩
  have hwalk : ∀ {u v : α} (p : G.skeleton.Walk u v) (i : ι), u ∈ (H i).vertexSet →
      ∀ e ∈ p.edges, e ∈ (H i).skeleton.edgeSet := by
    intro u v p
    induction p with
    | nil => simp
    | cons hstep q ih =>
      intro i hu e he
      obtain ⟨j, hj, hj', hadj'⟩ := hadj hstep
      have hij := hidx hu hj
      subst hij
      rcases List.mem_cons.mp he with rfl | he
      · exact hadj'
      · exact ih _ hj' e he
  rintro (⟨e, he, hc⟩ | ⟨e₁, he₁, e₂, he₂, hne, hc⟩ | hcyc)
  · obtain ⟨i, hei, hends⟩ := hE e he
    exact hH i (.inl ⟨e, hei, hends ▸ hc⟩)
  · obtain ⟨i, hi1, h1⟩ := hE e₁ he₁
    obtain ⟨j, hj2, h2⟩ := hE e₂ he₂
    obtain ⟨x, hx1, hx2⟩ : (G.ends e₁ ∩ G.ends e₂).Nonempty :=
      nonempty_of_ncard_ne_zero (by omega)
    have hx1' : x ∈ (H i).ends e₁ := h1 ▸ hx1
    have hx2' : x ∈ (H j).ends e₂ := h2 ▸ hx2
    obtain rfl := hidx ((H i).vertex_mem_of_inc hx1') ((H j).vertex_mem_of_inc hx2')
    exact hH i (.inr (.inl ⟨e₁, hi1, e₂, hj2, hne, by rwa [h1, h2] at hc⟩))
  · apply hcyc
    intro u c hc
    obtain ⟨i, hu, -, -⟩ := hadj (c.adj_snd hc.not_nil)
    have hp := hwalk c i hu
    exact hH i (.inr (.inr fun hac => hac (c.transfer _ hp) (hc.transfer hp)))

variable {S : Type u} [TopologicalSpace S] [T2Space S]
  {Γ : Drawing S} {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {P : Fin k → Drawing S}

/-- **`Γ ∩ Δ` has no circuit.** It is the union of the disjoint paths `P i`. So for a closed set
`Z ⊆ Δ`, `Γ ∩ Z` has no circuit. -/
theorem Setup61.not_hasCircuit_inter (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S)
    {Z : Set S} (hZ : IsClosed Z) (hZΔ : Z ⊆ Δ) :
    ¬ HasCircuit ((PaintingOrDrawing.drawing Γ).inter Z) := by
  refine not_hasCircuit_of_parts (fun i => (P i).toHypergraph)
    (fun i j hij => (h.disj hij).mono (P i).V_subset_U (P j).V_subset_U)
    (fun i => GM15.not_hasCircuit_of_isPathBetween (h.path i).1) ?_
  rintro e ⟨heΓ, heZ⟩
  obtain ⟨y, hy⟩ := heΓ.1
  obtain ⟨-, i, hi⟩ := h.edge_mem hS heΓ ⟨y, hy, hZΔ (heZ hy)⟩
  refine ⟨i, hi, ?_⟩
  rw [← (inter_le hZ).ends_eq e ⟨heΓ, heZ⟩]
  exact (GM15.toHypergraph_le_of_isSubdrawing (h.isSub i)).ends_eq e hi

/-- **Claim (1) of (6.1).** Let `I` be a closed disc whose separation is in the tangle, and let
`D ⊆ Δ` be a closed disc with the same boundary. Then `I = D`. Otherwise `I ∪ D` is the whole
surface
(`cover_of_discBd_eq`), so the part of `Γ` outside `I` lies in `Γ ∩ D`. It has no circuit by
`not_hasCircuit_inter`, against [4, Theorem (2.10)]. -/
theorem Setup61.ins_eq_of_disc (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S)
    [ConnectedSpace S] {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle (PaintingOrDrawing.drawing Γ).toHypergraph θ T) (hθ : 3 ≤ θ) {I D : Set S}
    (hI : IsClosedDisc I)
    (hIT : ((PaintingOrDrawing.drawing Γ).inter I, (PaintingOrDrawing.drawing Γ).interOutside I) ∈
      T)
    (hD : IsClosedDisc D) (hDΔ : D ⊆ Δ) (hb : discBd I = discBd D) : I = D := by
  by_contra hne
  have hcov := cover_of_discBd_eq hS hI hD hb hne
  have hsub : closure (univ \ I) ⊆ D := by
    refine closure_minimal (fun x hx => ?_) hD.isClosed
    have : x ∈ I ∪ D := hcov.symm ▸ mem_univ x
    exact this.resolve_left hx.2
  exact h.not_hasCircuit_inter hS isClosed_closure (hsub.trans hDΔ) (theorem_2_10_proof hT hθ hIT)

/-- A form of claim (1): a closed disc `I` of the tangle whose boundary lies in a closed disc
`Z ⊆ Δ` lies in `Z`. -/
theorem Setup61.sub_of_bd_sub (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S)
    [ConnectedSpace S] {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle (PaintingOrDrawing.drawing Γ).toHypergraph θ T) (hθ : 3 ≤ θ) {I Z : Set S}
    (hI : IsClosedDisc I)
    (hIT : ((PaintingOrDrawing.drawing Γ).inter I, (PaintingOrDrawing.drawing Γ).interOutside I) ∈
      T)
    (hZ : IsClosedDisc Z) (hZΔ : Z ⊆ Δ) (hIZ : discBd I ⊆ Z) : I ⊆ Z := by
  obtain ⟨D, ⟨hDZ, hD, hDb, -⟩, -⟩ := disc_oArc Z (discBd I) hZ hIZ hI.isOArc_discBd
  rw [h.ins_eq_of_disc hS hT hθ hI hIT hD (hDZ.trans hZΔ) hDb.symm]
  exact hDZ

/-! ### Levels -/

omit [T2Space S] in
/-- A vertex of a circuit lies on an edge of the circuit. -/
theorem IsCircuit.exists_edge_of_mem_V {C : Drawing S} (hC : C.IsCircuit) {x : S} (hx : x ∈ C.V) :
    ∃ t ∈ C.E, x ∈ closure t := by
  obtain ⟨u, W, -, hlen, hV, hE⟩ := hC
  have key : ∀ {u v : S} (W : GraphWalk C.toGraph u v), 0 < W.length → x ∈ W.support →
      ∃ t ∈ W.edges, x ∈ closure t := by
    intro u v W
    induction W with
    | nil _ => intro h0; simp [GraphWalk.length, GraphWalk.edges] at h0
    | @cons u' v' w' e hl rest ih =>
      intro _ hx
      have hcap : closure e ∩ C.V = {u', v'} := hl.2.2.2
      have hu : u' ∈ closure e := (show u' ∈ closure e ∩ C.V by rw [hcap]; exact .inl rfl).1
      have hv : v' ∈ closure e := (show v' ∈ closure e ∩ C.V by rw [hcap]; exact .inr rfl).1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨e, List.mem_cons_self, hu⟩
      · cases rest with
        | nil _ =>
          have : x = v' := by simpa [GraphWalk.support] using hx
          exact ⟨e, List.mem_cons_self, this ▸ hv⟩
        | cons hl' r' =>
          obtain ⟨t, ht, hxt⟩ := ih (by simp [GraphWalk.length, GraphWalk.edges]) hx
          exact ⟨t, List.mem_cons_of_mem _ ht, hxt⟩
  rw [hV] at hx
  obtain ⟨t, ht, hxt⟩ := key W hlen hx
  exact ⟨t, hE ▸ ht, hxt⟩

variable {X Y A B : Fin k → Set S} {E r : Fin (k + 1) → Set S}

open Classical in
/-- The level of a point of `Δ`: one for each chord with the point on its second side, and one for
each chord with the point off its first side. A point of `P j` has level `2j + 1`. A point off the
paths has level twice the number of chords with the point on their second side. -/
noncomputable def lev61 (X Y : Fin k → Set S) (y : S) : ℕ :=
  ∑ i, ((if y ∈ Y i then 1 else 0) + (if y ∈ X i then 0 else 1))

omit [T2Space S] in
theorem term_off {i : Fin k} {Xi Yi Ai Bi : Set S}
    (hs : IsSide F Δ (P i).U a b i Xi Yi Ai Bi) {y : S} (hyΔ : y ∈ Δ) (hyR : y ∉ (P i).U)
    [Decidable (y ∈ Xi)] [Decidable (y ∈ Yi)] :
    ((if y ∈ Yi then 1 else 0) + (if y ∈ Xi then 0 else 1) : ℕ) = if y ∈ Xi then 0 else 2 := by
  have h1 : y ∈ Xi ∪ Yi := hs.union ▸ hyΔ
  have h2 : ¬ (y ∈ Xi ∧ y ∈ Yi) := fun h => hyR (hs.inter ▸ h)
  rcases h1 with h1 | h1 <;> split_ifs <;> first | rfl | (exfalso; tauto)

/-- **The sides of an edge of `K` in `Δ`.** Let `t` be an edge of `K` with closure in `Δ`, from a
vertex `v` of `Γ` to a vertex `w` of `K` off `Γ`. Then `w` is off `U(Γ)`, `v` lies on a path `P j`,
and
`t` lies on one side of each chord: on the second side of the chords before `P j`, and on the first
side
of the chords after it. -/
theorem Pieces61.edge_sides (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    (hS : IsClosedSurface S) {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {t : Set S} (ht : t ∈ K.E)
    (htΔ : closure t ⊆ Δ) {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ K.V \ Γ.V)
    (hc : closure t ∩ K.V = {v, w}) :
    w ∉ Γ.U ∧ ∃ j, v ∈ (P j).U ∧ (∀ i, i < j → closure t ⊆ Y i) ∧
      (∀ i, j < i → closure t ⊆ X i) ∧ ∀ i, closure t ⊆ X i ∨ closure t ⊆ Y i := by
  have hwU : w ∉ Γ.U := by
    obtain ⟨r', hr', hwr⟩ := hK.2.2.2.1 w hw
    exact not_mem_U_of_region hr' hwr
  have htU : Disjoint t Γ.U := by
    refine disjoint_left.mpr fun x hx hxU => edge_notMem_V ht hx ?_
    have : x ∈ (PaintingOrDrawing.drawing Γ).U ∩ K.U := ⟨hxU, K.closure_subset_U ht
      (subset_closure hx)⟩
    rw [hK.1] at this
    exact hK.2.1 this
  have hvt : v ∈ closure t := (show v ∈ closure t ∩ K.V by rw [hc]; exact .inl rfl).1
  obtain ⟨j, hvj⟩ := h.U_inter hS (Γ.V_subset_U hv) (htΔ hvt)
  have hside : ∀ i, closure t ⊆ X i ∨ closure t ⊆ Y i := by
    intro i
    have hcon : IsPreconnected t := ht.2.2.1.isConnected.isPreconnected
    rcases subset_side (hp.side i).discX.isClosed (hp.side i).discY.isClosed hcon
      (by rw [(hp.side i).union]; exact subset_closure.trans htΔ)
      (by rw [(hp.side i).inter]; exact htU.mono_right (h.isSub i).U_subset) with h1 | h1
    · exact .inl (closure_minimal h1 (hp.side i).discX.isClosed)
    · exact .inr (closure_minimal h1 (hp.side i).discY.isClosed)
  have hoff : ∀ i, i ≠ j → v ∉ X i ∩ Y i := fun i hij hx => by
    rw [(hp.side i).inter] at hx
    exact disjoint_left.mp (h.disj hij.symm) hvj hx
  refine ⟨hwU, j, hvj, fun i hij => ?_, fun i hij => ?_, hside⟩
  · refine (hside i).resolve_left fun hX => hoff i hij.ne ⟨hX hvt, ?_⟩
    exact R_after (h.chords hS) hp.side hij hvj
  · refine (hside i).resolve_right fun hY => hoff i hij.ne' ⟨?_, hY hvt⟩
    exact R_before (h.chords hS) hp.side hij hvj

/-- **An edge of `K` in `Δ` changes the level by one.** -/
theorem Pieces61.lev_step (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    (hS : IsClosedSurface S) {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {t : Set S} (ht : t ∈ K.E)
    (htΔ : closure t ⊆ Δ) {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ K.V \ Γ.V)
    (hc : closure t ∩ K.V = {v, w}) :
    lev61 X Y v ≤ lev61 X Y w + 1 ∧ lev61 X Y w ≤ lev61 X Y v + 1 := by
  classical
  obtain ⟨hwU, j, hvj, -, -, hside⟩ := hp.edge_sides h hS hK ht htΔ hv hw hc
  have hvt : v ∈ closure t := (show v ∈ closure t ∩ K.V by rw [hc]; exact .inl rfl).1
  have hwt : w ∈ closure t := (show w ∈ closure t ∩ K.V by rw [hc]; exact .inr rfl).1
  let f : S → Fin k → ℕ := fun y i => (if y ∈ Y i then 1 else 0) + (if y ∈ X i then 0 else 1)
  have hlev : ∀ y, lev61 X Y y = f y j + ∑ i ∈ Finset.univ.erase j, f y i := fun y =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hwR : ∀ i, w ∉ (P i).U := fun i hx => hwU ((h.isSub i).U_subset hx)
  have hrest : ∑ i ∈ Finset.univ.erase j, f v i = ∑ i ∈ Finset.univ.erase j, f w i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hvR : v ∉ (P i).U := fun hx => disjoint_left.mp (h.disj hij.symm) hvj hx
    simp only [f]
    rw [term_off (hp.side i) (htΔ hvt) hvR, term_off (hp.side i) (htΔ hwt) (hwR i)]
    rcases hside i with hX | hY
    · simp [hX hvt, hX hwt]
    · have h1 : v ∉ X i := fun hx => hvR ((hp.side i).inter ▸ ⟨hx, hY hvt⟩)
      have h2 : w ∉ X i := fun hx => hwR i ((hp.side i).inter ▸ ⟨hx, hY hwt⟩)
      simp [h1, h2]
  have hfv : f v j = 1 := by
    have hXY : v ∈ X j ∩ Y j := by rw [(hp.side j).inter]; exact hvj
    simp [f, hXY.1, hXY.2]
  have hfw : f w j = 0 ∨ f w j = 2 := by
    simp only [f]
    rw [term_off (hp.side j) (htΔ hwt) (hwR j)]
    split_ifs <;> simp
  rw [hlev v, hlev w, hrest, hfv]
  omega

omit [TopologicalSpace S] [T2Space S] in
open Classical in
theorem lev_eq_zero {y : S} (hy : ∀ i, y ∈ X i ∧ y ∉ Y i) : lev61 X Y y = 0 := by
  unfold lev61
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [(hy i).1, (hy i).2]

omit [TopologicalSpace S] [T2Space S] in
open Classical in
theorem lev_eq_top {y : S} (hy : ∀ i, y ∉ X i ∧ y ∈ Y i) : lev61 X Y y = 2 * k := by
  unfold lev61
  have : ∀ i : Fin k, ((if y ∈ Y i then 1 else 0) + (if y ∈ X i then 0 else 1) : ℕ) = 2 :=
    fun i => by simp [(hy i).1, (hy i).2]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- If no vertex of a circuit `C` of `K` in `Δ` has level `0`, then `U(C)` lies on the second side
of
the first chord. -/
theorem Pieces61.U_sub_first (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    (hS : IsClosedSurface S) {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {C : Drawing S} (hC : C.IsCircuit)
    (hCK : C.IsSubdrawing K) (hCΔ : C.U ⊆ Δ) {i₀ : Fin k} (hi₀ : i₀.1 = 0)
    (hno : ∀ x ∈ C.V, lev61 X Y x ≠ 0) : C.U ⊆ Y i₀ := by
  have hedge : ∀ t ∈ C.E, closure t ⊆ Y i₀ := by
    intro t htC
    have htK := hCK.2 htC
    obtain ⟨v, hv, w, hw, hc⟩ := hK.2.2.2.2.1 t htK
    have htΔ : closure t ⊆ Δ := (C.closure_subset_U htC).trans hCΔ
    obtain ⟨hwU, j, -, hlt, hgt, hside⟩ := hp.edge_sides h hS hK htK htΔ hv hw hc
    have hwt : w ∈ closure t ∩ K.V := by rw [hc]; exact .inr rfl
    have hwC : w ∈ C.V := by
      have : w ∈ closure t ∩ C.V := by rw [hCK.closure_inter_V htC]; exact hwt
      exact this.2
    by_contra hnot
    have hj : j = i₀ := by
      by_contra hne
      exact hnot (hlt i₀ (Fin.lt_def.mpr (by have := Fin.val_ne_of_ne hne; omega)))
    subst hj
    have hX : closure t ⊆ X j := (hside j).resolve_right hnot
    refine hno w hwC (lev_eq_zero fun i => ?_)
    have hXi : w ∈ X i := by
      by_cases hij : i = j
      · exact hij ▸ hX hwt.1
      · exact hgt i (Fin.lt_def.mpr (by have := Fin.val_ne_of_ne hij; omega)) hwt.1
    exact ⟨hXi, fun hYi => hwU ((h.isSub i).U_subset ((hp.side i).inter ▸ ⟨hXi, hYi⟩))⟩
  intro x hx
  rw [C.U_eq] at hx
  rcases hx with hx | hx
  · obtain ⟨t, ht, hxt⟩ := IsCircuit.exists_edge_of_mem_V hC hx
    exact hedge t ht hxt
  · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact hedge t ht hxt

/-- If no vertex of a circuit `C` of `K` in `Δ` has level `2k`, then `U(C)` lies on the first side
of
the last chord. -/
theorem Pieces61.U_sub_last (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    (hS : IsClosedSurface S) {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {C : Drawing S} (hC : C.IsCircuit)
    (hCK : C.IsSubdrawing K) (hCΔ : C.U ⊆ Δ) {i₁ : Fin k} (hi₁ : i₁.1 + 1 = k)
    (hno : ∀ x ∈ C.V, lev61 X Y x ≠ 2 * k) : C.U ⊆ X i₁ := by
  have hedge : ∀ t ∈ C.E, closure t ⊆ X i₁ := by
    intro t htC
    have htK := hCK.2 htC
    obtain ⟨v, hv, w, hw, hc⟩ := hK.2.2.2.2.1 t htK
    have htΔ : closure t ⊆ Δ := (C.closure_subset_U htC).trans hCΔ
    obtain ⟨hwU, j, -, hlt, hgt, hside⟩ := hp.edge_sides h hS hK htK htΔ hv hw hc
    have hwt : w ∈ closure t ∩ K.V := by rw [hc]; exact .inr rfl
    have hwC : w ∈ C.V := by
      have : w ∈ closure t ∩ C.V := by rw [hCK.closure_inter_V htC]; exact hwt
      exact this.2
    by_contra hnot
    have hj : j = i₁ := by
      by_contra hne
      exact hnot (hgt i₁ (Fin.lt_def.mpr (by have := Fin.val_ne_of_ne hne; have := j.2; omega)))
    subst hj
    have hY : closure t ⊆ Y j := (hside j).resolve_left hnot
    refine hno w hwC (lev_eq_top fun i => ?_)
    have hYi : w ∈ Y i := by
      by_cases hij : i = j
      · exact hij ▸ hY hwt.1
      · exact hlt i (Fin.lt_def.mpr (by have := Fin.val_ne_of_ne hij; have := i.2; omega)) hwt.1
    exact ⟨fun hXi => hwU ((h.isSub i).U_subset ((hp.side i).inter ▸ ⟨hXi, hYi⟩)), hYi⟩
  intro x hx
  rw [C.U_eq] at hx
  rcases hx with hx | hx
  · obtain ⟨t, ht, hxt⟩ := IsCircuit.exists_edge_of_mem_V hC hx
    exact hedge t ht hxt
  · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact hedge t ht hxt

/-- **A circuit around a point of the first path has a vertex of level `0`.** Let `C` be a circuit
of
`K` in `Δ` whose disc `I` contains a point `p` of `P_1` off `U(C)`. If no vertex of `C` had level
`0`,
then `U(C)` and so `I` would lie on the second side of the first chord (claim (1)). But `p` is in
the
closure of `D_0`, which is on the first side. -/
theorem Pieces61.exists_low (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    (hS : IsClosedSurface S) [ConnectedSpace S] {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle (PaintingOrDrawing.drawing Γ).toHypergraph θ T) (hθ : 3 ≤ θ) {C : Drawing S}
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K) (hCΔ : C.U ⊆ Δ) {I : Set S} (hI : IsClosedDisc I)
    (hIb : discBd I = C.U)
    (hIT : ((PaintingOrDrawing.drawing Γ).inter I, (PaintingOrDrawing.drawing Γ).interOutside I) ∈
      T)
    {i₀ : Fin k} (hi₀ : i₀.1 = 0) {p : S} (hpI : p ∈ I) (hpC : p ∉ C.U) (hpR : p ∈ (P i₀).U) :
    ∃ x ∈ C.V, lev61 X Y x = 0 := by
  by_contra hno
  push Not at hno
  have hU := hp.U_sub_first h hS hK hC hCK hCΔ hi₀ hno
  have hIY := h.sub_of_bd_sub hS hT hθ hI hIT (hp.side i₀).discY
    ((hp.side i₀).union ▸ subset_union_right) (hIb ▸ hU)
  have hpint : p ∈ interior I := by
    rw [interior_eq_sdiff_discBd hS hI, hIb]
    exact ⟨hpI, hpC⟩
  have hpE : p ∈ closure (discInt (E i₀.castSucc)) :=
    (hp.disc _).subset_closure_discInt (Surface.discBd_subset _ ((hp.bd i₀).1 hpR))
  obtain ⟨z, hzY, hzD⟩ := mem_closure_iff.mp hpE _ isOpen_interior (interior_mono hIY hpint)
  have hzX := hp.int_X i₀.castSucc i₀ (by simp) hzD
  exact disjoint_left.mp (hp.int_P _ i₀) hzD ((hp.side i₀).inter ▸ ⟨hzX, interior_subset hzY⟩)

/-- **A circuit around a point of the last path has a vertex of level `2k`.** This is
`exists_low` from the other end. -/
theorem Pieces61.exists_high (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    (hS : IsClosedSurface S) [ConnectedSpace S] {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle (PaintingOrDrawing.drawing Γ).toHypergraph θ T) (hθ : 3 ≤ θ) {C : Drawing S}
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K) (hCΔ : C.U ⊆ Δ) {I : Set S} (hI : IsClosedDisc I)
    (hIb : discBd I = C.U)
    (hIT : ((PaintingOrDrawing.drawing Γ).inter I, (PaintingOrDrawing.drawing Γ).interOutside I) ∈
      T)
    {i₁ : Fin k} (hi₁ : i₁.1 + 1 = k) {p : S} (hpI : p ∈ I) (hpC : p ∉ C.U) (hpR : p ∈ (P i₁).U) :
    ∃ x ∈ C.V, lev61 X Y x = 2 * k := by
  by_contra hno
  push Not at hno
  have hU := hp.U_sub_last h hS hK hC hCK hCΔ hi₁ hno
  have hIX := h.sub_of_bd_sub hS hT hθ hI hIT (hp.side i₁).discX
    ((hp.side i₁).union ▸ subset_union_left) (hIb ▸ hU)
  have hpint : p ∈ interior I := by
    rw [interior_eq_sdiff_discBd hS hI, hIb]
    exact ⟨hpI, hpC⟩
  have hpE : p ∈ closure (discInt (E i₁.succ)) :=
    (hp.disc _).subset_closure_discInt (Surface.discBd_subset _ ((hp.bd i₁).2 hpR))
  obtain ⟨z, hzX, hzD⟩ := mem_closure_iff.mp hpE _ isOpen_interior (interior_mono hIX hpint)
  have hzY := hp.int_Y i₁.succ i₁ (by simp) hzD
  exact disjoint_left.mp (hp.int_P _ i₁) hzD ((hp.side i₁).inter ▸ ⟨interior_subset hzX, hzY⟩)

/-! ### The disc of the circuit `Q_i` -/

theorem Setup61.a_V (h : Setup61 Γ F Δ k a b P) (i : Fin k) : a i ∈ (P i).V := by
  obtain ⟨W, -, hV, -⟩ := (h.path i).1
  rw [hV]
  exact W.start_mem_support

theorem Setup61.b_V (h : Setup61 Γ F Δ k a b P) (i : Fin k) : b i ∈ (P i).V := by
  obtain ⟨W, -, hV, -⟩ := (h.path i).1
  rw [hV]
  exact W.end_mem_support

/-- The lines of a star in a closed disc `D` from `c` to two points `x ≠ y` of the boundary make a
line
from `x` to `y` in `D` that meets the boundary only at `x` and `y`. With a line `R` from `x` to `y`
in
the boundary, it bounds a closed disc in `D`. -/
theorem disc_of_star {D R Lx Ly : Set S} {c x y : S} (hD : IsClosedDisc D)
    (hR : IsLineWithEnds R x y) (hRD : R ⊆ discBd D)
    (hx : IsLineWithEnds Lx c x ∧ Lx ⊆ D ∧ Lx ∩ discBd D = {x})
    (hy : IsLineWithEnds Ly c y ∧ Ly ⊆ D ∧ Ly ∩ discBd D = {y}) (hxy : Lx ∩ Ly = {c}) :
    ∃ G, IsClosedDisc G ∧ G ⊆ D ∧ discBd G = (Lx ∪ Ly) ∪ R ∧ (Lx ∪ Ly) ∩ R ⊆ {x, y} := by
  have hJ : IsLineWithEnds (Lx ∪ Ly) x y := GM11.IsLineWithEnds.union hx.1 hy.1 hxy
  have hcap : (Lx ∪ Ly) ∩ R ⊆ {x, y} := by
    rintro z ⟨hz | hz, hzR⟩
    · have : z ∈ Lx ∩ discBd D := ⟨hz, hRD hzR⟩
      rw [hx.2.2] at this
      exact .inl this
    · have : z ∈ Ly ∩ discBd D := ⟨hz, hRD hzR⟩
      rw [hy.2.2] at this
      exact .inr this
  have hO : IsOArc ((Lx ∪ Ly) ∪ R) := isOArc_union hJ hR hcap
  have hOD : (Lx ∪ Ly) ∪ R ⊆ D :=
    union_subset (union_subset hx.2.1 hy.2.1) (hRD.trans (Surface.discBd_subset _))
  obtain ⟨G, ⟨hGD, hG, hGb, -⟩, -⟩ := disc_oArc D _ hD hOD hO
  exact ⟨G, hG, hGD, hGb, hcap⟩

/-- **The disc of `Q_i`.** The lines from the hubs `c_{i-1}` and `c_i` to the ends of `P_i` bound a
closed disc in `Δ` that includes `U(P_i)`. It is the union of the two discs that these lines cut off
from `DBar_{i-1}` and `DBar_i`, glued along `U(P_i)` (`disc_union`). -/
theorem Pieces61.exists_Q_disc (hp : Pieces61 Γ F Δ a b P X Y A B E r) (h : Setup61 Γ F Δ k a b P)
    {c : Fin (k + 1) → S} {L : Fin (k + 1) → S → Set S}
    (hL : ∀ m, ∀ x ∈ sideVerts P m, IsLineWithEnds (L m x) (c m) x ∧ L m x ⊆ E m ∧
      L m x ∩ discBd (E m) = {x} ∧ ∀ y ∈ sideVerts P m, x ≠ y → L m x ∩ L m y = {c m})
    (i : Fin k) :
    ∃ G, IsClosedDisc G ∧ G ⊆ Δ ∧ (P i).U ⊆ G ∧
      discBd G = (L i.castSucc (a i) ∪ L i.castSucc (b i)) ∪ (L i.succ (a i) ∪ L i.succ (b i)) := by
  have ha₀ : a i ∈ sideVerts P i.castSucc := ⟨i, .inl rfl, h.a_V i⟩
  have hb₀ : b i ∈ sideVerts P i.castSucc := ⟨i, .inl rfl, h.b_V i⟩
  have ha₁ : a i ∈ sideVerts P i.succ := ⟨i, .inr rfl, h.a_V i⟩
  have hb₁ : b i ∈ sideVerts P i.succ := ⟨i, .inr rfl, h.b_V i⟩
  have hab := h.ne i
  have hline := h.line i
  obtain ⟨G₀, hG₀, hG₀E, hG₀b, hcap₀⟩ := disc_of_star (hp.disc i.castSucc) hline (hp.bd i).1
    ⟨(hL _ _ ha₀).1, (hL _ _ ha₀).2.1, (hL _ _ ha₀).2.2.1⟩
    ⟨(hL _ _ hb₀).1, (hL _ _ hb₀).2.1, (hL _ _ hb₀).2.2.1⟩ ((hL _ _ ha₀).2.2.2 _ hb₀ hab)
  obtain ⟨G₁, hG₁, hG₁E, hG₁b, hcap₁⟩ := disc_of_star (hp.disc i.succ) hline (hp.bd i).2
    ⟨(hL _ _ ha₁).1, (hL _ _ ha₁).2.1, (hL _ _ ha₁).2.2.1⟩
    ⟨(hL _ _ hb₁).1, (hL _ _ hb₁).2.1, (hL _ _ hb₁).2.2.1⟩ ((hL _ _ ha₁).2.2.2 _ hb₁ hab)
  have hR₀ : (P i).U ⊆ discBd G₀ := hG₀b ▸ subset_union_right
  have hR₁ : (P i).U ⊆ discBd G₁ := hG₁b ▸ subset_union_right
  have hinter : G₀ ∩ G₁ = (P i).U := by
    refine subset_antisymm ?_ (subset_inter (hR₀.trans (Surface.discBd_subset _))
      (hR₁.trans (Surface.discBd_subset _)))
    rintro z ⟨hz₀, hz₁⟩
    rw [← (hp.side i).inter]
    exact ⟨hp.sub_X (i := i) (by simp) (hG₀E hz₀), hp.sub_Y (i := i) (by simp) (hG₁E hz₁)⟩
  obtain ⟨hG, hGb⟩ := disc_union G₀ G₁ (P i).U (a i) (b i) hG₀ hG₁ hline hinter hR₀ hR₁
  refine ⟨G₀ ∪ G₁, hG, union_subset (hG₀E.trans (hp.sub _)) (hG₁E.trans (hp.sub _)),
    hR₀.trans ((Surface.discBd_subset _).trans subset_union_left), ?_⟩
  rw [hGb, hG₀b, hG₁b]
  have ha : a i ∈ L i.castSucc (a i) ∪ L i.castSucc (b i) := .inl (hL _ _ ha₀).1.right_mem
  have hb : b i ∈ L i.castSucc (a i) ∪ L i.castSucc (b i) := .inr (hL _ _ hb₀).1.right_mem
  ext z
  simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨(h1 | h1) | (h1 | h1), h2⟩
    · exact .inl h1
    · rcases not_and_or.mp h2 with h3 | h3
      · exact (h3 h1).elim
      · push Not at h3
        rcases h3 with rfl | rfl
        · exact .inl ha
        · exact .inl hb
    · exact .inr h1
    · rcases not_and_or.mp h2 with h3 | h3
      · exact (h3 h1).elim
      · push Not at h3
        rcases h3 with rfl | rfl
        · exact .inl ha
        · exact .inl hb
  · rintro (h1 | h1)
    · refine ⟨.inl (.inl h1), fun ⟨hzR, hzab⟩ => hzab ?_⟩
      exact hcap₀ ⟨h1, hzR⟩
    · refine ⟨.inr (.inl h1), fun ⟨hzR, hzab⟩ => hzab ?_⟩
      exact hcap₁ ⟨h1, hzR⟩

end GraphMinor.GM12
