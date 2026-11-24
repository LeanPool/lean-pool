/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section810Connected

/-!
# Graph Minors XI, (8.10), (8.11) and (8.12)

`theorem_8_10` is (8.10) of the paper, for a union that is not empty. An empty union is not arc-wise
connected
in our definition, since Mathlib's path-connected sets are not empty. The proof is the paper's. The
connected case is `theorem_8_10_connected`; here the general case is reduced to it. `compPts Γ w` is
the point set of the component of `Γ` at the vertex `w`, and `Γ ∩ compPts Γ w` is connected. As the
paper says, the union `Z` is the union of the sets `Z_w` of restraints with boundary in one
component, any two of these are nested by (7.7) and (8.4), so `Z` is one of them, and
`restraint_down`, `restraint_up` turn it into the union for that component.

`theorem_8_11` and `theorem_8_12` follow the paper. The paper applies (8.10) to `Γ ∩ X` in the proof
of (8.11).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}

variable {k K : ℕ} {ins : Drawing S → Set S}

/-! ## The components of `Γ`, for the general case of (8.10) -/

omit [T2Space S] [ConnectedSpace S] in
/-- Two vertices in the closure of one edge are joined by a walk. -/
theorem nonempty_walk_of_edge {e : Set S} (he : e ∈ Γ.E) {p q : S} (hp : p ∈ closure e ∩ Γ.V)
    (hq : q ∈ closure e ∩ Γ.V) : Nonempty (GraphWalk Γ.toGraph p q) := by
  have hlink : ∀ {x y : S}, closure e ∩ Γ.V = {x, y} → ∀ {p q : S}, p ∈ closure e ∩ Γ.V →
      q ∈ closure e ∩ Γ.V → Nonempty (GraphWalk Γ.toGraph p q) := by
    intro x y hxy p q hp hq
    have hx : x ∈ closure e ∩ Γ.V := by rw [hxy]; exact Or.inl rfl
    have hy : y ∈ closure e ∩ Γ.V := by rw [hxy]; exact Or.inr rfl
    have hl : Γ.toGraph.IsLink e x y := ⟨he, hx.2, hy.2, hxy⟩
    have hl' : Γ.toGraph.IsLink e y x := ⟨he, hy.2, hx.2, by rw [hxy, pair_comm]⟩
    rw [hxy] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact ⟨.nil hx.2⟩
    · exact ⟨.cons hl (.nil hy.2)⟩
    · exact ⟨.cons hl' (.nil hx.2)⟩
    · exact ⟨.nil hy.2⟩
  rcases Γ.edge_cond e he with ⟨x, y, -, hcap, -⟩ | ⟨x, hcap, -⟩
  · exact hlink hcap hp hq
  · exact hlink (x := x) (y := x) (by rw [hcap, pair_eq_singleton]) hp hq

/-- The vertices joined to `w` by a walk. -/
def reachV (Γ : Drawing S) (w : S) : Set S := {x | x ∈ Γ.V ∧ Nonempty (GraphWalk Γ.toGraph w x)}

/-- The point set of the component of `Γ` that contains the vertex `w`: the vertices joined to `w`
by a walk,
and the closures of the edges at them. -/
def compPts (Γ : Drawing S) (w : S) : Set S :=
  reachV Γ w ∪ ⋃ e ∈ {e | e ∈ Γ.E ∧ ∃ y ∈ reachV Γ w, y ∈ closure e}, closure e

omit [T2Space S] [ConnectedSpace S] in
theorem reachV_trans {w x y : S} (hx : x ∈ reachV Γ w) (hy : y ∈ reachV Γ x) : y ∈ reachV Γ w := by
  obtain ⟨-, ⟨W₁⟩⟩ := hx
  obtain ⟨hyV, ⟨W₂⟩⟩ := hy
  exact ⟨hyV, ⟨W₁.append W₂⟩⟩

omit [T2Space S] [ConnectedSpace S] in
theorem reachV_symm {w x : S} (hw : w ∈ Γ.V) (hx : x ∈ reachV Γ w) : w ∈ reachV Γ x := by
  obtain ⟨-, ⟨W⟩⟩ := hx
  exact ⟨hw, ⟨W.reverse⟩⟩

omit [T2Space S] [ConnectedSpace S] in
theorem self_mem_reachV {w : S} (hw : w ∈ Γ.V) : w ∈ reachV Γ w := ⟨hw, ⟨.nil hw⟩⟩

omit [T2Space S] [ConnectedSpace S] in
/-- A vertex of `Γ` in `compPts Γ w` is joined to `w`. -/
theorem mem_reachV_of_mem_compPts {w x : S} (hx : x ∈ compPts Γ w) (hxV : x ∈ Γ.V) : x ∈ reachV Γ w
  := by
  rcases hx with hx | hx
  · exact hx
  obtain ⟨e, ⟨he, y, hy, hye⟩, hxe⟩ := mem_iUnion₂.mp hx
  obtain ⟨W⟩ := nonempty_walk_of_edge he ⟨hye, hy.1⟩ ⟨hxe, hxV⟩
  exact reachV_trans hy ⟨hxV, ⟨W⟩⟩

omit [T2Space S] [ConnectedSpace S] in
/-- The points of a walk from `w` lie in `compPts Γ w`. -/
theorem walkPts_subset_compPts {w y : S} (W : GraphWalk Γ.toGraph w y) : walkPts W ⊆ compPts Γ w
  := by
  have key : ∀ {a b : S} (W : GraphWalk Γ.toGraph a b), a ∈ reachV Γ w →
      (∀ x ∈ W.support, x ∈ reachV Γ w) ∧ ∀ e ∈ W.edges, e ∈ Γ.E ∧ ∃ y ∈ reachV Γ w, y ∈ closure e
        := by
    intro a b W
    induction W with
    | nil h =>
      exact fun ha => ⟨fun x hx => (List.mem_singleton.mp hx).symm ▸ ha,
        fun e he => by simp [GraphWalk.edges] at he⟩
    | @cons a' b' c' e hl rest ih =>
      intro ha
      have hac : a' ∈ closure e := by
        have : a' ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inl rfl
        exact this.1
      have hb : b' ∈ reachV Γ w := reachV_trans ha ⟨hl.2.2.1, ⟨.cons hl (.nil hl.2.2.1)⟩⟩
      obtain ⟨h₁, h₂⟩ := ih hb
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact h₁ x hx
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨hl.1, a', ha, hac⟩
        · exact h₂ f hf
  have hw : w ∈ reachV Γ w := self_mem_reachV (W.mem_vertexSet_of_mem_support W.start_mem_support)
  obtain ⟨h₁, h₂⟩ := key W hw
  rintro x (hx | ⟨e, he, hxe⟩)
  · exact Or.inl (h₁ x hx)
  · exact Or.inr (mem_iUnion₂.mpr ⟨e, h₂ e he, hxe⟩)

omit [ConnectedSpace S] in
/-- `compPts Γ w` is closed. -/
theorem isClosed_compPts (w : S) : IsClosed (compPts Γ w) := by
  have hv : (reachV Γ w).Finite := Γ.finite_V.subset fun _ hx => hx.1
  have he : {e ∈ Γ.E | ∃ y ∈ reachV Γ w, y ∈ closure e}.Finite :=
    Γ.finite_edges.subset fun _ h => h.1
  exact hv.isClosed.union (he.isClosed_biUnion fun _ _ => isClosed_closure)

omit [T2Space S] [ConnectedSpace S] in
/-- Two components that meet are equal. -/
theorem compPts_eq_of_meet {w w' : S} (hw' : w' ∈ Γ.V)
    (h : (compPts Γ w ∩ compPts Γ w').Nonempty) : compPts Γ w = compPts Γ w' := by
  have hrw : ∀ {a b : S}, b ∈ reachV Γ a → reachV Γ a = reachV Γ b := by
    intro a b hb
    have ha : a ∈ Γ.V := by
      obtain ⟨hbV, ⟨W⟩⟩ := hb
      exact W.mem_vertexSet_of_mem_support W.start_mem_support
    ext x
    exact ⟨fun hx => reachV_trans (reachV_symm ha hb) hx, fun hx => reachV_trans hb hx⟩
  suffices hw'w : w' ∈ reachV Γ w by
    simp only [compPts, hrw hw'w]
  obtain ⟨x, hx, hx'⟩ := h
  by_cases hxV : x ∈ Γ.V
  · exact reachV_trans (mem_reachV_of_mem_compPts hx hxV)
      (reachV_symm hw' (mem_reachV_of_mem_compPts hx' hxV))
  have hedge : ∀ {a : S}, x ∈ compPts Γ a → ∃ e ∈ Γ.E, x ∈ e ∧ ∃ y ∈ reachV Γ a, y ∈ closure e := by
    intro a hxa
    rcases hxa with hxa | hxa
    · exact absurd hxa.1 hxV
    obtain ⟨e, ⟨he, y, hy, hye⟩, hxe⟩ := mem_iUnion₂.mp hxa
    refine ⟨e, he, ?_, y, hy, hye⟩
    rw [← Γ.closure_diff_V he]
    exact ⟨hxe, hxV⟩
  obtain ⟨e, he, hxe, y, hy, hye⟩ := hedge hx
  obtain ⟨e', he', hxe', y', hy', hye'⟩ := hedge hx'
  obtain rfl := Γ.edge_eq_of_mem he he' hxe hxe'
  obtain ⟨W⟩ := nonempty_walk_of_edge he ⟨hye, hy.1⟩ ⟨hye', hy'.1⟩
  exact reachV_trans (reachV_trans hy ⟨hy'.1, ⟨W⟩⟩) (reachV_symm hw' hy')

omit [ConnectedSpace S] in
/-- The component `Γ ∩ compPts Γ w` is connected. -/
theorem isConnected_interSet_compPts {w : S} (hw : w ∈ Γ.V) :
    (Γ.interSet (compPts Γ w)).IsConnected := by
  have hT := isClosed_compPts (Γ := Γ) w
  have hsub : (Γ.interSet (compPts Γ w)).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hdown : ∀ x ∈ reachV Γ w, Nonempty (GraphWalk (Γ.interSet (compPts Γ w)).toGraph w x) := by
    rintro x ⟨-, ⟨W⟩⟩
    have hpts := walkPts_subset_compPts W
    obtain ⟨W', -, -⟩ := hsub.exists_walk_down W
      (fun y hy => (mem_interSet_V_iff hT).mpr ⟨W.mem_vertexSet_of_mem_support hy, hpts
        (Or.inl hy)⟩)
      (fun e he => by
        have hE : ∀ {a b : S} (W' : GraphWalk Γ.toGraph a b), ∀ f ∈ W'.edges, f ∈ Γ.E := by
          intro a b W'
          induction W' with
          | nil => simp [GraphWalk.edges]
          | cons hl rest ih =>
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact hl.1
            · exact ih f hf
        have heE : e ∈ Γ.E := hE W e he
        exact mem_interSet_E_iff.mpr ⟨heE, fun y hy => hpts (Or.inr ⟨e, he, subset_closure hy⟩)⟩)
    exact ⟨W'⟩
  have hV : ∀ x ∈ (Γ.interSet (compPts Γ w)).V, x ∈ reachV Γ w := fun x hx => by
    obtain ⟨h₁, h₂⟩ := (mem_interSet_V_iff hT).mp hx
    exact mem_reachV_of_mem_compPts h₂ h₁
  refine ⟨⟨w, (mem_interSet_V_iff hT).mpr ⟨hw, Or.inl (self_mem_reachV hw)⟩⟩, fun x hx y hy => ?_⟩
  obtain ⟨W₁⟩ := hdown x (hV x hx)
  obtain ⟨W₂⟩ := hdown y (hV y hy)
  exact ⟨W₁.reverse.append W₂⟩

/-- **(8.10)** of Graph Minors XI (pages 100–102): "Let $c \in \Sigma$, let $0 \le k < 2\theta$, and
let $Z$
be the union of all restraints $X$ with $l(X) \le k$ and $c \in X$. Then $Z$ is simply-connected."
We ask
that the union is not empty, because the empty set is not arc-wise connected in our definition. The
proof
reduces to one component of `Γ`, as the paper does, and then applies `theorem_8_10_connected`. -/
theorem theorem_8_10_proof (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) {c : S} (hne : (restraintUnion Γ ins K c k).Nonempty) :
    IsSimplyConnectedSet (restraintUnion Γ ins K c k) := by
  classical
  set Z := restraintUnion Γ ins K c k with hZdef
  -- `Z_w` is the union of the restraints in `Z` with boundary in the component of `w`.
  let Zw : S → Set S := fun w => restraintUnion (Γ.interSet (compPts Γ w)) ins K c k
  have hmemZw : ∀ w x, x ∈ Zw w ↔ ∃ X, (IsRestraint Γ ins K X ∧ perimeterWalkLength Γ X ≤ k
    ∧ c ∈ X) ∧
      frontier X ⊆ compPts Γ w ∧ x ∈ X := by
    intro w x
    constructor
    · intro hx
      obtain ⟨X, ⟨hX, hl, hc⟩, hxX⟩ := mem_iUnion₂.mp hx
      obtain ⟨hX', hf, hl'⟩ := restraint_up hS (isClosed_compPts w) hX
      exact ⟨X, ⟨hX', hl' ▸ hl, hc⟩, hf, hxX⟩
    · rintro ⟨X, ⟨hX, hl, hc⟩, hf, hxX⟩
      obtain ⟨hX', hl'⟩ := restraint_down hS (isClosed_compPts w) hX hf
      exact mem_iUnion₂.mpr ⟨X, ⟨hX', hl'.symm ▸ hl, hc⟩, hxX⟩
  -- Every restraint has connected boundary, which lies in one component.
  have hbd : ∀ X, IsRestraint Γ ins K X → ∃ w ∈ Γ.V, frontier X ⊆ compPts Γ w ∧
      IsPreconnected (frontier X) := by
    intro X hX
    obtain ⟨u₀, W₀, -, -, -, -, hd⟩ := hX.exists_walk hS
    have hf : frontier X = walkPts W₀ := by
      rw [walkPts_eq, hd, frontier_interSet hS hX.isClosed hX.isGammaNice]
    refine ⟨u₀, W₀.mem_vertexSet_of_mem_support W₀.start_mem_support,
      hf ▸ walkPts_subset_compPts W₀, ?_⟩
    rw [hf]
    exact (isPathConnected_walk_U W₀).isConnected.isPreconnected
  -- "Then $Z = Z_1 \cup \dots \cup Z_t$, since every restraint has connected boundary."
  have hZ : Z = ⋃ w ∈ Γ.V, Zw w := by
    ext x
    constructor
    · intro hx
      obtain ⟨X, hX, hxX⟩ := mem_iUnion₂.mp hx
      obtain ⟨w, hw, hf, -⟩ := hbd X hX.1
      exact mem_iUnion₂.mpr ⟨w, hw, (hmemZw w x).mpr ⟨X, hX, hf, hxX⟩⟩
    · intro hx
      obtain ⟨w, -, hxw⟩ := mem_iUnion₂.mp hx
      obtain ⟨X, hX, -, hxX⟩ := (hmemZw w x).mp hxw
      exact mem_iUnion₂.mpr ⟨X, hX, hxX⟩
  -- "We claim that either $Z_i \subseteq Z_j$ or $Z_j \subseteq Z_i$."
  have hcmp : ∀ w ∈ Γ.V, ∀ w' ∈ Γ.V, Zw w ⊆ Zw w' ∨ Zw w' ⊆ Zw w := by
    intro w hw w' hw'
    by_cases hmeet : (compPts Γ w ∩ compPts Γ w').Nonempty
    · left
      simp only [Zw, compPts_eq_of_meet hw' hmeet, subset_rfl]
    by_contra! hno
    obtain ⟨a, haw, haw'⟩ := not_subset.mp hno.1
    obtain ⟨b, hbw', hbw⟩ := not_subset.mp hno.2
    obtain ⟨X, hX, hfX, haX⟩ := (hmemZw w a).mp haw
    obtain ⟨Y, hY, hfY, hbY⟩ := (hmemZw w' b).mp hbw'
    obtain ⟨-, -, -, hXp⟩ := hbd X hX.1
    obtain ⟨-, -, -, hYp⟩ := hbd Y hY.1
    have hXY := theorem_7_7_proof (X := X) (Y := Y)
      (by rw [subBd_eq_frontier]; exact hXp)
      (by rw [subBd_eq_frontier]; exact hYp) ⟨c, hX.2.2, hY.2.2⟩
      (fun h => theorem_8_4_proof hS hs hX.1 hY.1 hX.1 (by rw [union_right_comm, union_self, h]))
      (by
        rw [subBd_eq_frontier, subBd_eq_frontier]
        exact disjoint_iff_inter_eq_empty.mpr (subset_empty_iff.mp fun x hx =>
          hmeet ⟨x, hfX hx.1, hfY hx.2⟩))
    rcases hXY with h | h
    · exact haw' ((hmemZw w' a).mpr ⟨Y, hY, hfY, h haX⟩)
    · exact hbw ((hmemZw w b).mpr ⟨X, hX, hfX, h hbY⟩)
  -- "Hence there exists $i$ with $Z = Z_i$."
  have hVne : Γ.V.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨X, hX, -⟩ := mem_iUnion₂.mp hz
    obtain ⟨w, hw, -⟩ := hbd X hX.1
    exact ⟨w, hw⟩
  obtain ⟨w, hw, hmax⟩ := Set.Finite.exists_maximalFor Zw Γ.V Γ.finite_V hVne
  have hZw : Z = Zw w := by
    rw [hZ]
    refine subset_antisymm (iUnion₂_subset fun w' hw' => ?_) (subset_iUnion₂_of_subset w hw
      subset_rfl)
    rcases hcmp w' hw' w hw with h | h
    · exact h
    · exact hmax hw' h
  -- "by the argument above when $\Gamma$ is connected, the union of $\mathrm{ins}'$-restraints ...
  -- is
  -- simply-connected."
  rw [hZw] at hne ⊢
  exact theorem_8_10_connected hS (theorem_4_2_proof hs (Drawing.span_isSubdrawing Γ _ _))
    (isConnected_interSet_compPts hw) hne

/-- **(8.10)** of Graph Minors XI (page 100), with no hypothesis: "Then $Z$ is simply-connected."
The paper's definition (page 76) holds for the empty set. Mathlib's path-connected sets are not
empty, so the conclusion is written as "$Z$ is empty or simply-connected". -/
theorem theorem_8_10_empty_or (hS : IsClosedSurface S) (hs : IsSlope Γ K ins) (c : S) (k : ℕ) :
    restraintUnion Γ ins K c k = ∅ ∨ IsSimplyConnectedSet (restraintUnion Γ ins K c k) := by
  rcases (restraintUnion Γ ins K c k).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (theorem_8_10_proof hS hs h)


/-- **(8.11)** of Graph Minors XI (page 101): "Let $c \in \Sigma$, let $0 \le k < 2\theta$, and let
$Z$ be the union of all restraints $X$
with $l(X) \le k$ and $c \in X$. Then for any restraint $Y$ with $c \in Y$, if $bd(Y)
\subseteq Z$ then $Y \subseteq Z$." -/
theorem theorem_8_11_proof (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) {c : S} {Y : Set S} (hY : IsRestraint Γ ins K Y) (hc : c ∈ Y)
    (hbd : frontier Y ⊆ restraintUnion Γ ins K c k) : Y ⊆ restraintUnion Γ ins K c k := by
  by_contra hnot
  set Z := restraintUnion Γ ins K c k with hZdef
  have hZc : IsClosed Z := isClosed_restraintUnion hS c k
  have hZn : IsGammaNice Γ Z := isGammaNice_restraintUnion c k
  have hZne : Z.Nonempty := by
    obtain ⟨y, hy⟩ := nonempty_frontier_iff.mpr ⟨hY.nonempty, hY.ne_univ⟩
    exact ⟨y, hbd hy⟩
  obtain ⟨z₀, hz₀⟩ := hZne
  obtain ⟨X₀, hX₀, -⟩ := mem_iUnion₂.mp hz₀
  have hcZ : c ∈ Z := mem_iUnion₂.mpr ⟨X₀, hX₀, hX₀.2.2⟩
  have hZs : IsSimplyConnectedSet Z := theorem_8_10_proof hS hs ⟨c, hcZ⟩
  obtain ⟨y, hyY, hyZ⟩ := not_subset.mp hnot
  have hZu : Z ≠ univ := fun h => hyZ (h ▸ mem_univ y)
  have hZconn := isConnected_compl hS hZc hZn hZs ⟨c, hcZ⟩ hZu
  -- A connected set that meets `T` and misses `bd(T)` lies in `T`.
  have hin : ∀ {C T : Set S}, IsPreconnected C → Disjoint C (frontier T) → (C ∩ T).Nonempty → C ⊆ T
    := by
    intro C T hC hd hne x hx
    by_contra hxT
    obtain ⟨w, hw, hwf⟩ := meets_frontier hC hne hx hxT
    exact disjoint_left.mp hd hw hwf
  have hZY : Zᶜ ⊆ Y := hin hZconn.isPreconnected
    (disjoint_left.mpr fun x hx hxf => hx (hbd hxf)) ⟨y, hyZ, hyY⟩
  obtain ⟨X, hX, hYX, -⟩ := exists_extreme hS hY
  have hr := hX.1
  have hXc := hr.isClosed
  have hZX : Zᶜ ⊆ X := hZY.trans hYX
  have hXZ : Xᶜ ⊆ Z := fun x hx => by
    by_contra hxZ
    exact hx (hZX hxZ)
  have hXconn := isConnected_compl hS hXc hr.isGammaNice hr.isSimplyConnected hr.nonempty hr.ne_univ
  -- The set `Z'` of the paper, which is the set `Z` of `Γ ∩ X`.
  have hcX := hYX hc
  have hZ' : restraintUnion (Γ.interSet X) ins K c k = Z ∩ X := by
    apply subset_antisymm
    · refine iUnion₂_subset fun T hT x hx => ?_
      obtain ⟨hT', hf, hl⟩ := restraint_up hS hXc hT.1
      refine ⟨mem_iUnion₂.mpr ⟨T, ⟨hT', hl ▸ hT.2.1, hT.2.2⟩, hx⟩, ?_⟩
      by_contra hxX
      have hsub : Xᶜ ⊆ T := hin hXconn.isPreconnected
        (disjoint_left.mpr fun w hw hwf => hw (hf hwf)) ⟨x, hxX, hx⟩
      have hcov : X ∪ T ∪ T = univ := by
        refine eq_univ_of_forall fun w => ?_
        by_cases hw : w ∈ X
        · exact Or.inl (Or.inl hw)
        · exact Or.inr (hsub hw)
      exact theorem_8_4_proof hS hs hr hT' hT' hcov
    · rintro z ⟨hzZ, hzX⟩
      obtain ⟨T, hT, hzT⟩ := mem_iUnion₂.mp hzZ
      obtain ⟨X', hX', hl⟩ := exists_optimal hT.1 hT.2.2 hzT
      have hsub : X' ⊆ X := theorem_8_9_proof hS hs hX' hX hcX hzX
      obtain ⟨h₁, h₂⟩ := restraint_down hS hXc hX'.1
        (hX'.1.isClosed.frontier_subset.trans hsub)
      exact mem_iUnion₂.mpr ⟨X', ⟨h₁, by rw [h₂]; exact hl.trans hT.2.1, hX'.2.1⟩, hX'.2.2.1⟩
  have hs' : IsSlope (Γ.interSet X) K ins := theorem_4_2_proof hs interSet_isSub
  have hsimp : IsSimplyConnectedSet (Z ∩ X) := by
    have := theorem_8_10_proof hS hs' (c := c) (k := k)
      (by rw [hZ']; exact ⟨c, hcZ, hcX⟩)
    rwa [hZ'] at this
  have hIne : (Z ∩ X).Nonempty := ⟨c, hcZ, hcX⟩
  have hIu : Z ∩ X ≠ univ := fun h => hZu (eq_univ_of_univ_subset (h ▸ inter_subset_left))
  have hIconn := isConnected_compl hS (hZc.inter hXc) (hZn.inter hr.isGammaNice) hsimp hIne hIu
  obtain ⟨x, hxX⟩ := (ne_univ_iff_exists_notMem _).mp hr.ne_univ
  have hne' : (Z ∩ X)ᶜ ∩ Zᶜ ∈ {A : Set S | A.Nonempty} := ⟨y, fun h => hyZ h.1, hyZ⟩
  have hsub := hIconn.isPreconnected.subset_left_of_subset_union hZc.isOpen_compl hXc.isOpen_compl
    (disjoint_left.mpr fun w h₁ h₂ => h₂ (hZX h₁))
    (fun w hw => by
      by_cases hwZ : w ∈ Z
      · exact Or.inr fun hwX => hw ⟨hwZ, hwX⟩
      · exact Or.inl hwZ) hne'
  exact hsub (fun h => hxX h.2 : x ∈ (Z ∩ X)ᶜ) (hXZ hxX)

omit [ConnectedSpace S] in
/-- Each non-empty open set has a point off `U(Γ)`. -/
theorem exists_off_U (hS : IsClosedSurface S) (Γ : Drawing S) {O : Set S} (hO : IsOpen O)
  (hne : O.Nonempty) :
    (O \ Γ.U).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨D, -, hD, -, -, -, hDO, -⟩ := exists_closedDisc_nbhd hS hO hx
  have hinf : (D \ Γ.V).Infinite :=
    ((infinite_of_isOArc hD.isOArc_discBd).mono (discBd_subset D)).sdiff Γ.finite_V
  obtain ⟨p, hpD, hpV⟩ := hinf.nonempty
  have hpO := hDO hpD
  by_cases hpU : p ∈ Γ.U
  · obtain ⟨e, he, hpe⟩ := Γ.exists_edge_of_mem hpU hpV
    obtain ⟨W, A₁, -, -, hpW, -, -, -, -, hd₁, -, hc₁, -⟩ :=
      exists_edge_sides hS Γ he hpe
    obtain ⟨q, hqO, hqA⟩ := mem_closure_iff.mp (hc₁ ⟨hpe, hpW⟩) O hO hpO
    exact ⟨q, hqO, disjoint_left.mp hd₁ hqA⟩
  · exact ⟨p, hpO, hpU⟩

/-- Each point of the frontier of a closed nice set `T` is in the closure of a region outside `T`.
-/
theorem exists_region_outside (hS : IsClosedSurface S) {T : Set S} (hTc : IsClosed T)
  (hTn : IsGammaNice Γ T)
    {b : S} (hb : b ∈ closure Tᶜ) : ∃ r ∈ Γ.R, r ⊆ Tᶜ ∧ b ∈ closure r := by
  classical
  have hfin : {r | r ∈ Γ.R ∧ r ⊆ Tᶜ}.Finite := (finite_R hS Γ).subset fun r hr => hr.1
  have hsub : Tᶜ ⊆ closure (⋃ r ∈ {r | r ∈ Γ.R ∧ r ⊆ Tᶜ}, r) := by
    intro x hx
    refine mem_closure_iff.mpr fun O hO hxO => ?_
    obtain ⟨y, ⟨hyO, hyT⟩, hyU⟩ := exists_off_U hS Γ (hO.inter hTc.isOpen_compl) ⟨x, hxO, hx⟩
    obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
    have hrT : r ⊆ Tᶜ := fun w hw hwT => hyT (nice_region hTn hr ⟨w, hw, hwT⟩ hyr)
    exact ⟨y, hyO, mem_iUnion₂.mpr ⟨r, ⟨hr, hrT⟩, hyr⟩⟩
  have hb' := closure_minimal hsub isClosed_closure hb
  rw [hfin.closure_biUnion] at hb'
  obtain ⟨r, hr, hbr⟩ := mem_iUnion₂.mp hb'
  exact ⟨r, hr.1, hr.2, hbr⟩

/-- The restraints through `c` with `l(X) = 0` are `{c}`, so that `Z₀ ≠ Σ`, as in the proof of
(8.12). -/
theorem restraintUnion_zero_ne_univ (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) (c : S) :
    restraintUnion Γ ins K c 0 ≠ univ := by
  classical
  intro hall
  obtain ⟨X, hX, -⟩ := mem_iUnion₂.mp (hall ▸ mem_univ c : c ∈ restraintUnion Γ ins K c 0)
  have hone : ∀ T, IsRestraint Γ ins K T → perimeterWalkLength Γ T ≤ 0 → c ∈ T → T ⊆ {c} := by
    intro T hT hl hc x hx
    obtain ⟨u, W, -, hlen, -, -, hd⟩ := hT.exists_walk hS
    have hl0 : W.length = 0 := by omega
    have hins := theorem_8_3_proof hS hs hT
    rw [subBd_eq_frontier, ← hd] at hins
    have hsup : ∀ y ∈ T, y = u := by
      intro y hy
      rw [← hins] at hy
      have hed : W.edges = [] := List.length_eq_zero_iff.mp hl0
      have hE : ∀ e, e ∉ (walkDrawing Γ W).E := fun e => by
        rw [walkDrawing_E]
        simp [hed]
      rcases hy with hy | hy
      · rcases (mem_walkDrawing_U Γ W).mp hy with h | ⟨e, he, -⟩
        · cases W with
          | nil _ => simpa [GraphWalk.support] using h
          | cons _ _ => simp [GraphWalk.edges] at hed
        · simp [hed] at he
      · obtain ⟨C, ⟨hC, hCs⟩, -⟩ := mem_iUnion₂.mp hy
        obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
        exact (hE e (hCs.2 he)).elim
    rw [mem_singleton_iff, hsup x hx, hsup c hc]
  refine hX.1.ne_univ (eq_univ_of_forall fun y => ?_)
  obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.mp (hall ▸ mem_univ y : y ∈ restraintUnion Γ ins K c 0)
  obtain rfl : y = c := hone T hT.1 hT.2.1 hT.2.2 hyT
  exact hX.2.2

/-- **(8.12)** of Graph Minors XI (page 102): "If $c \in \Sigma$, there is a region $r$ of $\Gamma$
such that there is no restraint $X$
with $c \in X$ and $r \subseteq X$." -/
theorem theorem_8_12_proof (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) (c : S) :
    ∃ r ∈ Γ.R, ∀ X : Set S, IsRestraint Γ ins K X → ¬ (c ∈ X ∧ r ⊆ X) := by
  classical
  let Z : ℕ → Set S := fun k => restraintUnion Γ ins K c k
  -- Choose `k` largest with `k < 2θ` and `Z_k ≠ Σ`.
  have hK0 : 0 < K := by
    have := hs.two_le
    omega
  have hex : ∃ k, K - 1 - k < K ∧ Z (K - 1 - k) ≠ univ := by
    refine ⟨K - 1, by omega, ?_⟩
    have h0 : K - 1 - (K - 1) = 0 := by omega
    rw [h0]
    exact restraintUnion_zero_ne_univ hS hs c
  obtain ⟨hkK, hkZ⟩ := Nat.find_spec hex
  set k := K - 1 - Nat.find hex with hk
  have hbig : ∀ m, k < m → m < K → Z m = univ := by
    intro m hm hmK
    by_contra hne
    have hle := Nat.find_min' hex (m := K - 1 - m) ⟨by omega, by
      have : K - 1 - (K - 1 - m) = m := by omega
      rw [this]
      exact hne⟩
    omega
  have hZc : ∀ m, IsClosed (Z m) := fun m => isClosed_restraintUnion hS c m
  have hZn : ∀ m, IsGammaNice Γ (Z m) := fun m => isGammaNice_restraintUnion c m
  have hmem : ∀ {m T}, IsRestraint Γ ins K T → perimeterWalkLength Γ T ≤ m → c ∈ T → T ⊆ Z m :=
    fun {m T} hT hl hc x hx => mem_iUnion₂.mpr ⟨T, ⟨hT, hl, hc⟩, hx⟩
  obtain ⟨y₀, hy₀⟩ := (ne_univ_iff_exists_notMem _).mp hkZ
  obtain ⟨y, ⟨-, hyZ⟩, hyU⟩ := exists_off_U hS Γ (isOpen_univ.inter (hZc k).isOpen_compl) ⟨y₀,
    mem_univ _, hy₀⟩
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
  have hrZ : r ⊆ (Z k)ᶜ := fun w hw hwZ => hyZ (nice_region (hZn k) hr ⟨w, hw, hwZ⟩ hyr)
  refine ⟨r, hr, fun X₀ hX₀ ⟨hcX₀, hrX₀⟩ => ?_⟩
  have hlX₀ := hX₀.length_lt
  have hk1 : k + 1 < K := by
    by_contra hge
    have hle : perimeterWalkLength Γ X₀ ≤ k := by omega
    exact hrZ hyr (hmem hX₀ hle hcX₀ (hrX₀ hyr))
  have hall := hbig (k + 1) (by omega) hk1
  -- A point off `Z_k` is in a restraint with `l ≤ k + 1`.
  have hopt : ∀ z, z ∉ Z k → ∃ X', IsOptimalRestraint Γ ins K c z X' ∧ perimeterWalkLength Γ X'
    = k + 1 := by
    intro z hz
    obtain ⟨T, hT, hzT⟩ := mem_iUnion₂.mp (hall ▸ mem_univ z : z ∈ Z (k + 1))
    obtain ⟨X', hX', hl⟩ := exists_optimal hT.1 hT.2.2 hzT
    refine ⟨X', hX', le_antisymm (hl.trans hT.2.1) ?_⟩
    by_contra hlt
    exact hz (hmem hX'.1 (by omega) hX'.2.1 hX'.2.2.1)
  obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.mp (hall ▸ mem_univ y : y ∈ Z (k + 1))
  obtain ⟨X, hX, hTX, hl⟩ := exists_extreme hS hT.1
  have hcX : c ∈ X := hTX hT.2.2
  have hyX : y ∈ X := hTX hyT
  -- `bd(X) ⊄ Z_k`, by (8.11).
  have hb : ¬ frontier X ⊆ Z k := fun hsub =>
    hyZ (theorem_8_11_proof hS hs hX.1 hcX hsub hyX)
  obtain ⟨b, hbf, hbZ⟩ := not_subset.mp hb
  have hbcl : b ∈ closure Xᶜ := by
    rw [frontier_eq_closure_inter_closure] at hbf
    exact hbf.2
  obtain ⟨r', hr', hr'X, hbr'⟩ := exists_region_outside hS hX.1.isClosed hX.1.isGammaNice hbcl
  have hr'Z : r' ⊆ (Z k)ᶜ := fun w hw hwZ =>
    hbZ (closure_minimal (nice_region (hZn k) hr' ⟨w, hw, hwZ⟩) (hZc k) hbr')
  obtain ⟨w, hw⟩ := region_nonempty hr'
  obtain ⟨X', hX', hl'⟩ := hopt w (hr'Z hw)
  have hr'X' : r' ⊆ X' := nice_region hX'.1.isGammaNice hr' ⟨w, hw, hX'.2.2.1⟩
  have hbX' : b ∈ X' := closure_minimal hr'X' hX'.1.isClosed hbr'
  -- `X'` is `c, b`-optimal.
  have hopt' : IsOptimalRestraint Γ ins K c b X' := by
    refine ⟨hX'.1, hX'.2.1, hbX', fun U hU hcU hbU => ?_⟩
    rw [hl']
    by_contra hlt
    exact hbZ (hmem hU (by omega) hcU hbU)
  have hsub := theorem_8_9_proof hS hs hopt' hX hcX
    (hX.1.isClosed.frontier_subset hbf)
  exact hr'X hw (hsub (hr'X' hw))

end GraphMinor.GM11
