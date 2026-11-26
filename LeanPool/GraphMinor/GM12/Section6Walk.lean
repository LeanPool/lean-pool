/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Claims
public import LeanPool.GraphMinor.GM11.EvenCircuit
public import LeanPool.GraphMinor.GM11.ThreeCircuits
public import LeanPool.GraphMinor.GM11.RadialFacts
public import LeanPool.GraphMinor.GM11.RadialTwoCell
public import LeanPool.GraphMinor.GM11.RadialCorners
public import LeanPool.GraphMinor.GM11.Section5b
public import LeanPool.GraphMinor.GM14.RigidThread
public import LeanPool.GraphMinor.GM11.Section85
public import LeanPool.GraphMinor.GM11.Rings
public import LeanPool.GraphMinor.GM11.CircuitRegions
public import LeanPool.GraphMinor.GM11.Restraints
public import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM10.Section6

/-!
# Graph Minors XII, Section 6: the walk `W`

The paper takes for `W` a trace of a homeomorphism of the circle onto `F`. With the radial drawing
`K`
of `exists_special_radial`, this trace is the walk `h₀, a₁, h₁, a₂, h₂, …, a_k, h_k, b_k, h_{k-1},
…,
b₁, h₀` through the hubs `h_m` of the discs `D_m` and the ends of the paths. We write it out
(`exists_W`). It has length `2θ = 4k`. For each path `P_i` it uses the four spokes from the ends of
`P_i` to the hubs on its two sides, and these spokes form a circuit `Q_i` (`exists_Q`).
-/


public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The regions `r m` of (6.1), and their hubs in `K`. -/
structure Hubs (Γ K : Drawing S) {k : ℕ} (P : Fin k → Drawing S) (r : Fin (k + 1) → Set S)
    (c : Fin (k + 1) → S) : Prop where
  /-- Each `r m` is a region of `Γ`. -/
  r_mem : ∀ m, r m ∈ Γ.R
  /-- The regions are distinct. -/
  r_inj : Function.Injective r
  /-- Each path lies on its two regions. -/
  side : ∀ i : Fin k, (P i).U ⊆ closure (r i.castSucc) ∧ (P i).U ⊆ closure (r i.succ)
  /-- The hub lies in its region. -/
  c_mem : ∀ m, c m ∈ r m
  /-- The hub is a vertex of `K`. -/
  c_V : ∀ m, c m ∈ K.V

/-- The spokes at the ends of the paths, one from each end to each of its two hubs. -/
structure Spokes (Γ K : Drawing S) {k : ℕ} (a b : Fin k → S) (P : Fin k → Drawing S)
    (c : Fin (k + 1) → S) (α₀ α₁ β₀ β₁ : Fin k → Set S) : Prop where
  mem_α₀ : ∀ i, α₀ i ∈ K.E
  mem_α₁ : ∀ i, α₁ i ∈ K.E
  mem_β₀ : ∀ i, β₀ i ∈ K.E
  mem_β₁ : ∀ i, β₁ i ∈ K.E
  cap_α₀ : ∀ i, closure (α₀ i) ∩ K.V = {a i, c i.castSucc}
  cap_α₁ : ∀ i, closure (α₁ i) ∩ K.V = {a i, c i.succ}
  cap_β₀ : ∀ i, closure (β₀ i) ∩ K.V = {b i, c i.castSucc}
  cap_β₁ : ∀ i, closure (β₁ i) ∩ K.V = {b i, c i.succ}

variable [ConnectedSpace S]

omit [T2Space S] [ConnectedSpace S] in
/-- Every edge of `Γ` lies in a region of a pre-radial drawing `K`. -/
theorem edge_region (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : PreRad (PaintingOrDrawing.drawing Γ) K) {f : Set S} (hf : f ∈ Γ.E) :
    ∃ s ∈ K.R, f ⊆ s := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨y, hy⟩ := hf.1
  have hd := edge_disjoint hrad hf
  obtain ⟨s, hs, hys⟩ := exists_region_of_notMem (Set.disjoint_left.mp hd hy)
  exact ⟨s, hs, subset_region hs hf.2.2.1.isConnected.isPreconnected hd hy hys⟩

variable {Γ K : Drawing S} {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {P : Fin k → Drawing S}
  {r : Fin (k + 1) → Set S} {c : Fin (k + 1) → S} (h : Setup61 Γ F Δ k a b P)
  (hh : Hubs Γ K P r c)

variable {α₀ α₁ β₀ β₁ : Fin k → Set S}

section Facts

omit [T2Space S] [ConnectedSpace S] in
theorem hub_notMem (hh : Hubs Γ K P r c) (m : Fin (k + 1)) : c m ∉ Γ.V :=
  notMem_V_of_mem_region (hh.r_mem m) (hh.c_mem m)

omit [T2Space S] [ConnectedSpace S] in
theorem hub_inj (hh : Hubs Γ K P r c) {m m' : Fin (k + 1)} (he : c m = c m') : m = m' := by
  have : r m = r m' := region_eq_of_mem (hh.r_mem m) (hh.r_mem m') (hh.c_mem m) (he ▸ hh.c_mem m')
  exact hh.r_inj this

include h

omit [ConnectedSpace S] in
theorem same_path {i j : Fin k} {x : S} (hi : x ∈ (P i).U) (hj : x ∈ (P j).U) : i = j := by
  by_contra hne
  exact Set.disjoint_left.mp (h.disj hne) hi hj

omit [ConnectedSpace S] in
theorem a_inj {i j : Fin k} (he : a i = a j) : i = j :=
  same_path h (h.line i).left_mem (he ▸ (h.line j).left_mem)

omit [ConnectedSpace S] in
theorem b_inj {i j : Fin k} (he : b i = b j) : i = j :=
  same_path h (h.line i).right_mem (he ▸ (h.line j).right_mem)

omit [ConnectedSpace S] in
theorem a_ne_b (i j : Fin k) : a i ≠ b j := fun he => by
  have hij : i = j := same_path h (h.line i).left_mem (he ▸ (h.line j).right_mem)
  subst hij
  exact h.ne i he

omit [ConnectedSpace S] in
theorem a_ne_hub (hh : Hubs Γ K P r c) (i : Fin k) (m : Fin (k + 1)) : a i ≠ c m := fun he =>
  hub_notMem hh m (he ▸ (h.a_mem i).2)

omit [ConnectedSpace S] in
theorem b_ne_hub (hh : Hubs Γ K P r c) (i : Fin k) (m : Fin (k + 1)) : b i ≠ c m := fun he =>
  hub_notMem hh m (he ▸ (h.b_mem i).2)

end Facts

omit [T2Space S] [ConnectedSpace S] in
theorem cap_ne {t t' : Set S} {u d u' d' : S} (hc : closure t ∩ K.V = {u, d})
    (hc' : closure t' ∩ K.V = {u', d'}) (hu : u ∈ Γ.V) (hd' : d' ∉ Γ.V) (hne : u ≠ u' ∨ d ≠ d') :
    t ≠ t' := by
  rintro rfl
  rw [hc] at hc'
  rcases Set.pair_eq_pair_iff.mp hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne.elim (· h1) (· h2)
  · exact hd' (h1 ▸ hu)

omit [T2Space S] [ConnectedSpace S] in
/-- A link from a spoke. -/
theorem spoke_link {e : Set S} {x y : S} (he : e ∈ K.E) (hc : closure e ∩ K.V = {x, y}) :
    K.toGraph.IsLink e x y := by
  have hx : x ∈ closure e ∩ K.V := by rw [hc]; exact .inl rfl
  have hy : y ∈ closure e ∩ K.V := by rw [hc]; exact .inr rfl
  exact ⟨he, hx.2, hy.2, hc⟩

omit [T2Space S] [ConnectedSpace S] in
omit [TopologicalSpace S] in
theorem pair_swap {x y : S} {A : Set S} (h : A = {x, y}) : A = {y, x} := h.trans (pair_comm x y)

omit [T2Space S] [TopologicalSpace S] [ConnectedSpace S] in
theorem eq_of_pair_eq_singleton {x y z : S} (h : ({x, y} : Set S) = {z}) : x = y := by
  have h1 : x ∈ ({z} : Set S) := h ▸ .inl rfl
  have h2 : y ∈ ({z} : Set S) := h ▸ .inr rfl
  exact h1.trans h2.symm

omit [T2Space S] [ConnectedSpace S] in
/-- A walk up the chain of hubs, through the points `p i`. -/
theorem exists_spine {K : Drawing S} {k : ℕ} {c : Fin (k + 1) → S} {p : Fin k → S}
    {t₀ t₁ : Fin k → Set S} (h₀ : ∀ i, t₀ i ∈ K.E) (h₁ : ∀ i, t₁ i ∈ K.E)
    (c₀ : ∀ i, closure (t₀ i) ∩ K.V = {p i, c i.castSucc})
    (c₁ : ∀ i, closure (t₁ i) ∩ K.V = {p i, c i.succ}) (h0V : c 0 ∈ K.V) :
    ∀ (m : ℕ) (hm : m < k + 1), ∃ w : GraphWalk K.toGraph (c 0) (c ⟨m, hm⟩), w.length = 2 * m ∧
      (∀ e, e ∈ w.edges ↔ ∃ i : Fin k, i.1 < m ∧ (e = t₀ i ∨ e = t₁ i)) ∧
      (∀ x ∈ w.support, (∃ j, x = c j) ∨ ∃ i, x = p i) := by
  intro m
  induction m with
  | zero =>
    intro hm
    refine ⟨.nil h0V, rfl, fun e => ?_, ?_⟩
    · simp [GraphWalk.edges]
    · intro x hx
      exact .inl ⟨0, by simpa [GraphWalk.support] using hx⟩
  | succ m ih =>
    intro hm
    obtain ⟨w, hl, he, hs⟩ := ih (by omega)
    let i : Fin k := ⟨m, by omega⟩
    have l₀ : K.toGraph.IsLink (t₀ i) (c ⟨m, by omega⟩) (p i) := spoke_link (h₀ i) (pair_swap
      (c₀ i))
    have l₁ : K.toGraph.IsLink (t₁ i) (p i) (c ⟨m + 1, hm⟩) := spoke_link (h₁ i) (c₁ i)
    refine ⟨w.append (.cons l₀ (.cons l₁ (.nil l₁.2.2.1))), ?_, fun e => ?_, fun x hx => ?_⟩
    · rw [GraphWalk.length_append, hl]
      simp only [GraphWalk.length, GraphWalk.edges, List.length_cons, List.length_nil]
      omega
    · rw [GraphWalk.edges_append, List.mem_append, he]
      simp only [GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (⟨j, hj, hh⟩ | hh)
        · exact ⟨j, by omega, hh⟩
        · exact ⟨i, by simp [i], hh⟩
      · rintro ⟨j, hj, hh⟩
        by_cases hjm : j.1 < m
        · exact .inl ⟨j, hjm, hh⟩
        · have : j = i := Fin.ext (by simp [i]; omega)
          exact .inr (this ▸ hh)
    · rcases (GraphWalk.mem_support_append _ _).mp hx with hx | hx
      · exact hs x hx
      · simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact .inl ⟨_, rfl⟩
        · exact .inr ⟨_, rfl⟩
        · exact .inl ⟨_, rfl⟩

omit [T2Space S] [ConnectedSpace S] in
/-- **The walk `W`.** It goes up the hubs through the points `a i`, and back through the points
`b i`. -/
theorem exists_W (sp : Spokes Γ K a b P c α₀ α₁ β₀ β₁) (h0V : c 0 ∈ K.V) :
    ∃ W : GraphWalk K.toGraph (c 0) (c 0), W.length = 4 * k ∧
      (∀ e, e ∈ W.edges ↔ ∃ i, e = α₀ i ∨ e = α₁ i ∨ e = β₀ i ∨ e = β₁ i) ∧
      (∀ x ∈ W.support, (∃ j, x = c j) ∨ ∃ i, x = a i ∨ x = b i) := by
  obtain ⟨u, hul, hue, hus⟩ := exists_spine sp.mem_α₀ sp.mem_α₁ sp.cap_α₀ sp.cap_α₁ h0V k (by omega)
  obtain ⟨d, hdl, hde, hds⟩ := exists_spine sp.mem_β₀ sp.mem_β₁ sp.cap_β₀ sp.cap_β₁ h0V k (by omega)
  refine ⟨u.append d.reverse, ?_, fun e => ?_, fun x hx => ?_⟩
  · rw [GraphWalk.length_append, GraphWalk.length_reverse, hul, hdl]
    omega
  · rw [GraphWalk.edges_append, GraphWalk.edges_reverse, List.mem_append, List.mem_reverse, hue,
      hde]
    constructor
    · rintro (⟨i, -, h1 | h1⟩ | ⟨i, -, h1 | h1⟩)
      · exact ⟨i, .inl h1⟩
      · exact ⟨i, .inr (.inl h1)⟩
      · exact ⟨i, .inr (.inr (.inl h1))⟩
      · exact ⟨i, .inr (.inr (.inr h1))⟩
    · rintro ⟨i, h1 | h1 | h1 | h1⟩
      · exact .inl ⟨i, i.2, .inl h1⟩
      · exact .inl ⟨i, i.2, .inr h1⟩
      · exact .inr ⟨i, i.2, .inl h1⟩
      · exact .inr ⟨i, i.2, .inr h1⟩
  · rcases (GraphWalk.mem_support_append _ _).mp hx with hx | hx
    · rcases hus x hx with h1 | ⟨i, h1⟩
      · exact .inl h1
      · exact .inr ⟨i, .inl h1⟩
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hx
      rcases hds x hx with h1 | ⟨i, h1⟩
      · exact .inl h1
      · exact .inr ⟨i, .inr h1⟩

include h hh in
omit [ConnectedSpace S] in
/-- **The circuit `Q i`** of the four spokes at the ends of `P i`. -/
theorem exists_Q (sp : Spokes Γ K a b P c α₀ α₁ β₀ β₁) (i : Fin k) :
    ∃ Q : Drawing S, Q.IsCircuit ∧ Q.IsSubdrawing K ∧ Q.length ≤ 4 ∧
      Q.V = {c i.castSucc, a i, c i.succ, b i} ∧ Q.E = {α₀ i, α₁ i, β₁ i, β₀ i} := by
  have l₀ := spoke_link (sp.mem_α₀ i) (pair_swap (sp.cap_α₀ i))
  have l₁ := spoke_link (sp.mem_α₁ i) (sp.cap_α₁ i)
  have l₂ := spoke_link (sp.mem_β₁ i) (pair_swap (sp.cap_β₁ i))
  have l₃ := spoke_link (sp.mem_β₀ i) (sp.cap_β₀ i)
  have hc : c i.castSucc ≠ c i.succ := fun he =>
    (Fin.castSucc_lt_succ (i := i)).ne (hub_inj hh he)
  have hab := a_ne_b h i i
  have hac := a_ne_hub h hh i
  have hbc := b_ne_hub h hh i
  have ha := (h.a_mem i).2
  have hb := (h.b_mem i).2
  have hn := hub_notMem hh
  let W : GraphWalk K.toGraph (c i.castSucc) (c i.castSucc) :=
    .cons l₀ (.cons l₁ (.cons l₂ (.cons l₃ (.nil l₀.2.1))))
  have hW : W.IsSimpleClosed := by
    constructor
    · simp only [W, GraphWalk.support, List.tail_cons, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨hac _, hab, hac _⟩, ⟨(hbc i.succ).symm, hc.symm⟩, hbc _⟩
    · simp only [W, GraphWalk.edges, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true, not_false_eq_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · exact cap_ne (sp.cap_α₀ i) (sp.cap_α₁ i) ha (hn _) (.inr hc)
      · exact cap_ne (sp.cap_α₀ i) (sp.cap_β₁ i) ha (hn _) (.inl hab)
      · exact cap_ne (sp.cap_α₀ i) (sp.cap_β₀ i) ha (hn _) (.inl hab)
      · exact cap_ne (sp.cap_α₁ i) (sp.cap_β₁ i) ha (hn _) (.inl hab)
      · exact cap_ne (sp.cap_α₁ i) (sp.cap_β₀ i) ha (hn _) (.inl hab)
      · exact cap_ne (sp.cap_β₁ i) (sp.cap_β₀ i) hb (hn _) (.inr hc.symm)
  have hE : (walkDrawing K W).E = {α₀ i, α₁ i, β₁ i, β₀ i} := by
    rw [walkDrawing_E]
    ext e
    simp [W, GraphWalk.edges]
  refine ⟨walkDrawing K W, isCircuit_walkDrawing K hW (by simp [W, GraphWalk.length,
    GraphWalk.edges]),
    walkDrawing_isSubdrawing K W, ?_, ?_, hE⟩
  · rw [Drawing.length, hE]
    refine (ncard_insert_le _ _).trans ?_
    have h3 := ncard_insert_le (α₁ i) {β₁ i, β₀ i}
    have h2 := ncard_insert_le (β₁ i) {β₀ i}
    rw [ncard_singleton] at h2
    omega
  · rw [walkDrawing_V]
    ext x
    simp [W, GraphWalk.support]
    tauto


omit [ConnectedSpace S] in
/-- The ends of an edge `L \ {c, x}` of a drawing, whose closure is the line `L` from `c` to `x`. -/
theorem cap_of_line {K : Drawing S} {L : Set S} {c x : S} (hL : IsLineWithEnds L c x)
    (he : L \ {c, x} ∈ K.E) : closure (L \ {c, x}) ∩ K.V = {x, c} := by
  have hcl := closure_sdiff_pair hL
  have hdiff := K.closure_diff_V he
  have hend : ∀ z ∈ ({c, x} : Set S), z ∈ K.V := by
    intro z hz
    by_contra hzV
    have hzL : z ∈ closure (L \ {c, x}) := by
      rw [hcl]
      rcases hz with rfl | rfl
      · exact hL.left_mem
      · exact hL.right_mem
    have : z ∈ closure (L \ {c, x}) \ K.V := ⟨hzL, hzV⟩
    rw [hdiff] at this
    exact this.2 hz
  ext z
  constructor
  · rintro ⟨hzL, hzV⟩
    by_contra hz
    have hz' : z ∉ ({c, x} : Set S) := by
      rintro (rfl | rfl)
      · exact hz (.inr rfl)
      · exact hz (.inl rfl)
    rw [hcl] at hzL
    exact edge_notMem_V he ⟨hzL, hz'⟩ hzV
  · rintro (rfl | rfl)
    · refine ⟨?_, hend _ (.inr rfl)⟩
      rw [hcl]
      exact hL.right_mem
    · refine ⟨?_, hend _ (.inl rfl)⟩
      rw [hcl]
      exact hL.left_mem

omit [ConnectedSpace S] in
/-- **The special radial drawing of (6.1), with its hubs and spokes.** -/
theorem exists_hubs_spokes (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S)
    (hT : (PaintingOrDrawing.drawing Γ).IsTwoCell) {X Y A B : Fin k → Set S}
    {E : Fin (k + 1) → Set S} (hp : Pieces61 Γ F Δ a b P X Y A B E r)
    (hside : ∀ i : Fin k, (P i).U ⊆ closure (r i.castSucc) ∧ (P i).U ⊆ closure (r i.succ)) :
    ∃ (K : Drawing S) (c : Fin (k + 1) → S) (L : Fin (k + 1) → S → Set S),
      (PaintingOrDrawing.drawing Γ).IsRadialDrawing K ∧ Hubs Γ K P r c ∧
      (∀ m, c m ∈ discInt (E m)) ∧
      (∀ m, ∀ x ∈ sideVerts P m, IsLineWithEnds (L m x) (c m) x ∧ L m x ⊆ E m ∧
        L m x ∩ discBd (E m) = {x} ∧ ∀ y ∈ sideVerts P m, x ≠ y → L m x ∩ L m y = {c m}) ∧
      Spokes Γ K a b P c (fun i => L i.castSucc (a i) \ {c i.castSucc, a i})
        (fun i => L i.succ (a i) \ {c i.succ, a i}) (fun i => L i.castSucc
          (b i) \ {c i.castSucc, b i})
        (fun i => L i.succ (b i) \ {c i.succ, b i}) := by
  obtain ⟨K, c, L, hK, hc, hL⟩ := exists_special_radial h hS hT hp
  have ha₀ : ∀ i : Fin k, a i ∈ sideVerts P i.castSucc := fun i => ⟨i, .inl rfl, h.a_V i⟩
  have hb₀ : ∀ i : Fin k, b i ∈ sideVerts P i.castSucc := fun i => ⟨i, .inl rfl, h.b_V i⟩
  have ha₁ : ∀ i : Fin k, a i ∈ sideVerts P i.succ := fun i => ⟨i, .inr rfl, h.a_V i⟩
  have hb₁ : ∀ i : Fin k, b i ∈ sideVerts P i.succ := fun i => ⟨i, .inr rfl, h.b_V i⟩
  refine ⟨K, c, L, hK, ⟨hp.reg, hp.inj, hside, fun m => hp.int_r m (hc m).1, fun m => (hc m).2⟩,
    fun m => (hc m).1, fun m x hx => ⟨(hL m x hx).1, (hL m x hx).2.1, (hL m x hx).2.2.1,
      (hL m x hx).2.2.2.1⟩, ⟨fun i => (hL _ _ (ha₀ i)).2.2.2.2, fun i => (hL _ _ (ha₁ i)).2.2.2.2,
      fun i => (hL _ _ (hb₀ i)).2.2.2.2, fun i => (hL _ _ (hb₁ i)).2.2.2.2, fun i => ?_, fun i
        => ?_,
      fun i => ?_, fun i => ?_⟩⟩
  · exact cap_of_line (hL _ _ (ha₀ i)).1 (hL _ _ (ha₀ i)).2.2.2.2
  · exact cap_of_line (hL _ _ (ha₁ i)).1 (hL _ _ (ha₁ i)).2.2.2.2
  · exact cap_of_line (hL _ _ (hb₀ i)).1 (hL _ _ (hb₀ i)).2.2.2.2
  · exact cap_of_line (hL _ _ (hb₁ i)).1 (hL _ _ (hb₁ i)).2.2.2.2

end GraphMinor.GM12
