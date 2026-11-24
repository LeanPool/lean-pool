/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section89

/-!
# Paths along a drawing, for the proof of (8.10)

The proof of (8.10) in Graph Minors XI (pages 101–102) joins each vertex `v` of `Γ ∩ Z` to a fixed
vertex `u`
by a walk `P_v`, and shows that a closed walk of `Γ ∩ Z` is null-homotopic in `Z` because each of
its edges
`e` with ends `v₁, v₂` is homotopic to `P_{v₁} + P_{v₂}⁻¹` (claim (1)), so that the sum telescopes
(claim (2)). This file has the tools.

* `cl_path_eq` is the telescoping sum, for a path cut at finitely many points. We work with homotopy
  classes of paths (`Cl`), in which the sum is associative.
* `cl_path_of_edges` is claim (2) for a path that runs along `Γ`: if claim (1) holds for every piece
  of
  the path that lies in the closure of one edge, then the path is homotopic to `P_a + P_b⁻¹`.
* `exists_vertex_mem_nice` gives the vertex `u` of the paper: a vertex in every closed nice set that
  contains `c`.
* `joinedIn_of_restraint` is the paper's reason for the walk `P_v`: "Since $\Gamma \cap bd(X_v)$ is
  connected and so is $\Gamma$, and $u, v \in X_v$, there is a simple walk $P_v$ of $\Gamma$ from
  $v$ to
  $u$ with $U(P_v) \subseteq X_v$." We keep only the curve of the walk, which is what the proof
  uses.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

/-! ## The telescoping sum -/

section Telescope

variable {T : Type*} [TopologicalSpace T]

/-- **The telescoping sum along a path.** The points `x` with `P x` carry classes `f x` of paths
from
`x` to a fixed point `c`. If `γ` meets such points only finitely often, and each piece of `γ`
between
two consecutive such points is homotopic to `f x + (f y)⁻¹`, then so is every piece of `γ` between
two
such points. -/
theorem cl_subpath_eq {c a b : T} (P : T → Prop) (f : ∀ x, P x → Cl x c) (γ : Path a b)
    (hfin : {t : I | P (γ t)}.Finite)
    (hstep : ∀ s t : I, s < t → ∀ (hs : P (γ s)) (ht : P (γ t)), (∀ r, s < r → r < t → ¬ P (γ r)) →
      Cl.mk (γ.subpath s t) = (f _ hs).trans (f _ ht).symm)
    {s t : I} (hst : s ≤ t) (hs : P (γ s)) (ht : P (γ t)) :
    Cl.mk (γ.subpath s t) = (f _ hs).trans (f _ ht).symm := by
  classical
  suffices key : ∀ n : ℕ, ∀ s t : I, s ≤ t → ∀ (hs : P (γ s)) (ht : P (γ t)),
      {r : I | s < r ∧ r < t ∧ P (γ r)}.ncard = n →
      Cl.mk (γ.subpath s t) = (f _ hs).trans (f _ ht).symm from key _ s t hst hs ht rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hst hs ht hn
    by_cases hex : ∃ r, s < r ∧ r < t ∧ P (γ r)
    · obtain ⟨r, hsr, hrt, hr⟩ := hex
      have hfin' : {r' : I | s < r' ∧ r' < t ∧ P (γ r')}.Finite := hfin.subset fun r' h => h.2.2
      have h₁ : {r' : I | s < r' ∧ r' < r ∧ P (γ r')}.ncard < n := by
        rw [← hn]
        refine ncard_lt_ncard ⟨fun r' h => ⟨h.1, h.2.1.trans hrt, h.2.2⟩, fun h => ?_⟩ hfin'
        exact lt_irrefl r (h ⟨hsr, hrt, hr⟩).2.1
      have h₂ : {r' : I | r < r' ∧ r' < t ∧ P (γ r')}.ncard < n := by
        rw [← hn]
        refine ncard_lt_ncard ⟨fun r' h => ⟨hsr.trans h.1, h.2.1, h.2.2⟩, fun h => ?_⟩ hfin'
        exact lt_irrefl r (h ⟨hsr, hrt, hr⟩).1
      have e := Path.Homotopic.mk_subpath_trans_mk_subpath γ s r t
      change (Cl.mk (γ.subpath s r)).trans (Cl.mk (γ.subpath r t)) = Cl.mk (γ.subpath s t) at e
      rw [← e, ih _ h₁ s r hsr.le hs hr rfl, ih _ h₂ r t hrt.le hr ht rfl, cl_assoc,
        ← cl_assoc (f _ hr).symm, cl_symm_trans, cl_refl_trans]
    · push Not at hex
      rcases hst.lt_or_eq with hlt | rfl
      · exact hstep s t hlt hs ht fun r h₁ h₂ => hex r h₁ h₂
      · rw [Path.subpath_self, cl_trans_symm]
        rfl

/-- `cl_subpath_eq` for the whole path. -/
theorem cl_path_eq {c a b : T} (P : T → Prop) (f : ∀ x, P x → Cl x c) (γ : Path a b)
    (hfin : {t : I | P (γ t)}.Finite)
    (hstep : ∀ s t : I, s < t → ∀ (hs : P (γ s)) (ht : P (γ t)), (∀ r, s < r → r < t → ¬ P (γ r)) →
      Cl.mk (γ.subpath s t) = (f _ hs).trans (f _ ht).symm)
    (ha : P a) (hb : P b) :
    Cl.mk γ = (f a ha).trans (f b hb).symm := by
  rcases γ with ⟨g, rfl, rfl⟩
  have h := cl_subpath_eq P f ⟨g, rfl, rfl⟩ hfin hstep zero_le_one ha hb
  rwa [Path.subpath_zero_one] at h

end Telescope

/-! ## Paths that run along a drawing -/

variable {S : Type u} [TopologicalSpace S]

/-- **Claim (2) of (8.10), for a path along `Γ`.** Let `Z ⊆ Σ` be a union of atoms, and let each
vertex
`x ∈ Z` carry a class `f x` of paths in `Z` from `x` to `c`. Suppose that every path in `Z` between
two
vertices that stays in the closure of an edge `e ⊆ Z` is homotopic to `f x + (f y)⁻¹` (claim (1)).
Then so is every path in `Z` between vertices that stays in `U(Γ)` and meets `V(Γ)` only finitely
often. -/
theorem cl_path_of_edges {Γ : Drawing S} {Z : Set S} {c : Z}
    (hZe : ∀ e ∈ Γ.E, (e ∩ Z).Nonempty → e ⊆ Z)
    (f : ∀ x : Z, x.1 ∈ Γ.V → Cl x c)
    (h1 : ∀ e ∈ Γ.E, e ⊆ Z → ∀ (x y : Z) (hx : x.1 ∈ Γ.V) (hy : y.1 ∈ Γ.V) (q : Path x y),
      (∀ u, (q u).1 ∈ closure e) → Cl.mk q = (f x hx).trans (f y hy).symm)
    {a b : Z} (γ : Path a b) (hU : ∀ t, (γ t).1 ∈ Γ.U) (hfin : {t : I | (γ t).1 ∈ Γ.V}.Finite)
    (ha : a.1 ∈ Γ.V) (hb : b.1 ∈ Γ.V) :
    Cl.mk γ = (f a ha).trans (f b hb).symm := by
  refine cl_path_eq (fun x : Z => x.1 ∈ Γ.V) f γ hfin (fun s t hst hs ht hno => ?_) ha hb
  let g : ℝ → S := fun x => (γ.extend x).1
  have hg : Continuous g := continuous_subtype_val.comp γ.continuous_extend
  have hgI : ∀ r : I, g r = (γ r).1 := fun r => by simp [g]
  have hst' : (s : ℝ) < t := hst
  let A := g '' Ioo (s : ℝ) t
  have hAc : IsPathConnected A :=
    ((convex_Ioo (s : ℝ) t).isPathConnected (nonempty_Ioo.mpr hst')).image hg
  have hmem : ∀ x ∈ Ioo (s : ℝ) t, ∃ r : I, s < r ∧ r < t ∧ g x = (γ r).1 := by
    intro x hx
    refine ⟨⟨x, s.2.1.trans hx.1.le, hx.2.le.trans t.2.2⟩, hx.1, hx.2, ?_⟩
    rw [← hgI]
  have hAUV : A ⊆ Γ.U \ Γ.V := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, h₁, h₂, he⟩ := hmem x hx
    rw [he]
    exact ⟨hU r, hno r h₁ h₂⟩
  obtain ⟨y, hy⟩ := hAc.nonempty
  obtain ⟨e, he, hye⟩ := Γ.exists_edge_of_mem (hAUV hy).1 (hAUV hy).2
  have hAe : A ⊆ e := by
    have hun : IsPathConnected (e ∪ A) := he.2.2.1.union hAc ⟨y, hye, hy⟩
    have := he.2.2.2 (e ∪ A) (union_subset he.2.1 hAUV) hun subset_union_left
    rw [← this]
    exact subset_union_right
  have hAZ : A ⊆ Z := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, -, -, he⟩ := hmem x hx
    rw [he]
    exact (γ r).2
  have heZ : e ⊆ Z := hZe e he ⟨y, hye, hAZ hy⟩
  refine h1 e he heZ _ _ hs ht _ fun u => ?_
  have hu : (γ.subpath s t) u ∈ γ '' Icc s t := by
    rw [← Path.range_subpath_of_le _ _ _ hst.le]
    exact mem_range_self u
  obtain ⟨r, hr, hru⟩ := hu
  rw [← hru, ← hgI]
  have hr' : (r : ℝ) ∈ closure (Ioo (s : ℝ) t) := by
    rw [closure_Ioo hst'.ne]
    exact hr
  exact closure_mono hAe (image_closure_subset_closure_image hg (mem_image_of_mem g hr'))

/-! ## The vertex `u` -/

variable [T2Space S]

omit [T2Space S] in
/-- **The vertex `u` of the proof of (8.10).** "Choose $u \in V(\Gamma)$ such that $u = c$ if
$c \in V(\Gamma)$, $u \in \bar{e}$ if $c \in e$ for some edge $e$ of $\Gamma$, $u \in \bar{r}$ if
$c \in r$ for some region $r$ of $\Gamma$." Such a `u` lies in every closed nice set that contains
`c`. -/
theorem exists_vertex_mem_nice [ConnectedSpace S] (hS : IsClosedSurface S) {Γ : Drawing S}
    (hV : Γ.V.Nonempty) (c : S) :
    ∃ u ∈ Γ.V, ∀ X : Set S, IsClosed X → IsGammaNice Γ X → c ∈ X → u ∈ X := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hedge : ∀ e ∈ Γ.E, ∃ u ∈ Γ.V, u ∈ closure e := by
    intro e he
    rcases Γ.edge_cond e he with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
    · have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact Or.inl rfl
      exact ⟨u, this.2, this.1⟩
    · have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact rfl
      exact ⟨u, this.2, this.1⟩
  by_cases hcV : c ∈ Γ.V
  · exact ⟨c, hcV, fun X _ _ hc => hc⟩
  by_cases hcU : c ∈ Γ.U
  · obtain ⟨e, he, hce⟩ := Γ.exists_edge_of_mem hcU hcV
    obtain ⟨u, hu, hue⟩ := hedge e he
    refine ⟨u, hu, fun X hXc hXn hc => ?_⟩
    exact closure_minimal (nice_edge hXn he ⟨c, hce, hc⟩) hXc hue
  obtain ⟨r, hr, hcr⟩ := exists_region_of_notMem hcU
  have hro : IsOpen r := region_isOpen hr
  have hrne : r ≠ univ := by
    obtain ⟨v, hv⟩ := hV
    intro h
    exact region_subset hr (h ▸ mem_univ v) (Γ.V_subset_U hv)
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨⟨c, hcr⟩, hrne⟩
  have hpr : p ∈ closure r := frontier_subset_closure hp
  have hpU : p ∈ Γ.U := by
    rcases closure_region_subset hr hpr with h | h
    · exact absurd h (hro.frontier_eq ▸ hp).2
    · exact h
  have key : ∃ u ∈ Γ.V, u ∈ closure r := by
    by_cases hpV : p ∈ Γ.V
    · exact ⟨p, hpV, hpr⟩
    obtain ⟨e, he, hpe⟩ := Γ.exists_edge_of_mem hpU hpV
    obtain ⟨u, hu, hue⟩ := hedge e he
    have her : e ⊆ closure r := edge_subset_closure_of_incident hS he hr ⟨p, hpe, hpr⟩
    exact ⟨u, hu, closure_minimal her isClosed_closure hue⟩
  obtain ⟨u, hu, hur⟩ := key
  refine ⟨u, hu, fun X hXc hXn hc => ?_⟩
  exact closure_minimal (nice_region hXn hr ⟨c, hcr, hc⟩) hXc hur

/-! ## The walks `P_v` -/

omit [T2Space S] in
/-- The points of a walk lie in `U(Γ)`. -/
theorem walk_pts_subset_U {Γ : Drawing S} {x y : S} (W : GraphWalk Γ.toGraph x y) :
    {z | z ∈ W.support ∨ ∃ e ∈ W.edges, z ∈ closure e} ⊆ Γ.U := by
  rintro z (hz | ⟨e, he, hz⟩)
  · exact Γ.V_subset_U (W.mem_vertexSet_of_mem_support hz)
  · have hE : ∀ {x' y' : S} (W' : GraphWalk Γ.toGraph x' y'), ∀ f ∈ W'.edges, f ∈ Γ.E := by
      intro x' y' W'
      induction W' with
      | nil => simp [GraphWalk.edges]
      | cons hl rest ih =>
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hl.1
        · exact ih f hf
    exact Γ.closure_subset_U (hE W e he) hz

/-- The curve of a walk: the ends of a walk whose points lie in `T` are joined in `T ∩ U(Γ)`. -/
theorem joinedIn_of_walk [ConnectedSpace S] {Γ : Drawing S} {T : Set S} {x y : S}
    (W : GraphWalk Γ.toGraph x y) (hT : {z | z ∈ W.support ∨ ∃ e ∈ W.edges, z ∈ closure e} ⊆ T) :
    JoinedIn (T ∩ Γ.U) x y :=
  ((isPathConnected_walk_U W).joinedIn x (Or.inl W.start_mem_support) y
    (Or.inl W.end_mem_support)).mono fun _ hz => ⟨hT hz, walk_pts_subset_U W hz⟩

omit [T2Space S] in
/-- A walk of `Γ` from a vertex of a closed nice set `X` to a vertex of `bd(X)` can be cut so that
it stays
in `X`: it can only leave `X` through `bd(X)`. -/
theorem exists_walk_to_frontier {Γ : Drawing S} {X : Set S} (hXc : IsClosed X)
  (hXn : IsGammaNice Γ X)
    {w y : S} (W : GraphWalk Γ.toGraph w y) (hw : w ∈ X) (hy : y ∈ frontier X) :
    ∃ y' ∈ frontier X, ∃ W' : GraphWalk Γ.toGraph w y',
      {z | z ∈ W'.support ∨ ∃ e ∈ W'.edges, z ∈ closure e} ⊆ X := by
  induction W with
  | @nil a ha =>
    refine ⟨a, hy, .nil ha, ?_⟩
    rintro z (hz | ⟨e, he, -⟩)
    · simp only [GraphWalk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact hw
    · simp [GraphWalk.edges] at he
  | @cons a b d e hl rest ih =>
    by_cases hwf : a ∈ frontier X
    · refine ⟨a, hwf, .nil hl.2.1, ?_⟩
      rintro z (hz | ⟨e, he, -⟩)
      · have hz' : z = a := List.mem_singleton.mp hz
        exact hz'.symm ▸ hw
      · simp [GraphWalk.edges] at he
    have hint : a ∈ interior X := by
      by_contra h
      exact hwf ⟨subset_closure hw, h⟩
    have hac : a ∈ closure e := by
      have : a ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact this.1
    have hbc : b ∈ closure e := by
      have : b ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inr rfl
      exact this.1
    obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp hac _ isOpen_interior hint
    have heX : closure e ⊆ X := closure_minimal (nice_edge hXn hl.1 ⟨z, hze, interior_subset hzi⟩)
      hXc
    obtain ⟨y', hy', W', hW'⟩ := ih (heX hbc) hy
    refine ⟨y', hy', .cons hl W', ?_⟩
    rintro x (hx | ⟨f, hf, hx⟩)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hW' (Or.inl hx)
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact heX hx
      · exact hW' (Or.inr ⟨f, hf, hx⟩)

/-- **The walks `P_v` of (8.10).** If `Γ` is connected and `X` is a restraint, then any two vertices
of
`X` are joined by a curve in `X ∩ U(Γ)`: each is joined to `Γ ∩ bd(X)` inside `X`, and `Γ ∩ bd(X)`
is
connected. -/
theorem joinedIn_of_restraint [ConnectedSpace S] (hS : IsClosedSurface S) {Γ : Drawing S}
    {ins : Drawing S → Set S} {k : ℕ} (hΓ : Γ.IsConnected) {X : Set S} (hr : IsRestraint Γ ins k X)
    {v w : S} (hv : v ∈ Γ.V) (hvX : v ∈ X) (hw : w ∈ Γ.V) (hwX : w ∈ X) :
    JoinedIn (X ∩ Γ.U) v w := by
  have hXc := hr.isClosed
  have hXn := hr.isGammaNice
  have hsub : (Γ.interSet (frontier X)).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hfU : (Γ.interSet (frontier X)).U ⊆ frontier X := interSet_U_subset isClosed_frontier
  obtain ⟨u₀, W₀, -, -, -, -, hd⟩ := hr.exists_walk hS
  have hu₀ : u₀ ∈ (Γ.interSet (frontier X)).V := by
    rw [← hd, walkDrawing_V]
    exact W₀.start_mem_support
  have hu₀f : u₀ ∈ frontier X := hfU ((Γ.interSet (frontier X)).V_subset_U hu₀)
  have hbd : ∀ y ∈ frontier X, y ∈ Γ.V → JoinedIn (X ∩ Γ.U) y u₀ := by
    intro y hy hyV
    have hy' : y ∈ (Γ.interSet (frontier X)).V := mem_interSet_V hyV hy
    obtain ⟨W⟩ := exists_walk_in_bd hS hr hy' hu₀
    refine (joinedIn_of_walk W (T := frontier X) fun z hz => hfU (walk_pts_subset_U W hz)).mono ?_
    rintro z ⟨h₁, h₂⟩
    exact ⟨hXc.frontier_subset h₁, hsub.U_subset h₂⟩
  have hto : ∀ x ∈ Γ.V, x ∈ X → JoinedIn (X ∩ Γ.U) x u₀ := by
    intro x hx hxX
    obtain ⟨W⟩ := hΓ.2 x hx u₀ (hsub.1 hu₀)
    obtain ⟨y, hy, W', hW'⟩ := exists_walk_to_frontier hXc hXn W hxX hu₀f
    exact (joinedIn_of_walk W' hW').trans (hbd y hy (W'.mem_vertexSet_of_mem_support
      W'.end_mem_support))
  exact (hto v hv hvX).trans (hto w hw hwX).symm

end GraphMinor.GM11
