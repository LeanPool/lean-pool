/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.SideDisc
public import LeanPool.GraphMinor.GM07.Section5b
public import LeanPool.GraphMinor.GM14.RigidNoose
public import LeanPool.GraphMinor.GM11.Separate
public import LeanPool.GraphMinor.GM11.OArcCircuit
public import LeanPool.GraphMinor.GM11.Section5b

/-!
# Nested circuits from layers of regions

Let `Γ` be a drawing in a sphere and `r₀` a region. Layer `t` is the set of regions that a chain of
regions from `r₀`, with `t` common vertices, reaches. If another region
`r₂` is not in layer `t`, then the boundary of the layer holds an `O`-arc that separates `r₀` from
`r₂`, and these `O`-arcs are vertex-disjoint and nested for different `t`.
This fills in how Graph Minors VII gets the nest in (5.8) from condition (ii), and it is the circuit
`C_j` of the proof of (5.9).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

local notation "I" => unitInterval

variable {T : Type} [TopologicalSpace T]

/-- Layer `t` of regions around `r₀`. -/
def regLayer (Γ : Drawing T) (r₀ : Set T) : ℕ → Set (Set T)
  | 0 => {r₀}
  | t + 1 => regLayer Γ r₀ t ∪ {r ∈ Γ.R | ∃ r' ∈ regLayer Γ r₀ t, ∃ v ∈ Γ.V, v ∈ closure r
    ∧ v ∈ closure r'}

theorem regLayer_subset {Γ : Drawing T} {r₀ : Set T} (h₀ : r₀ ∈ Γ.R) (t : ℕ) : regLayer Γ r₀ t ⊆
  Γ.R := by
  induction t with
  | zero =>
    rintro r rfl
    exact h₀
  | succ t ih =>
    rintro r (h | h)
    · exact ih h
    · exact h.1

theorem regLayer_mono {Γ : Drawing T} {r₀ : Set T} {t t' : ℕ} (h : t ≤ t') : regLayer Γ r₀ t ⊆
  regLayer Γ r₀ t' := by
  induction h with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans subset_union_left

/-- If a vertex is on a region of layer `t` and on a region outside layer `t + 1`, we have a
contradiction. -/
theorem not_incident_far {Γ : Drawing T} {r₀ r r'' : Set T} {t : ℕ} (hr : r ∈ regLayer Γ r₀ t)
  (hr'' : r'' ∈ Γ.R) (hn : r'' ∉ regLayer Γ r₀ (t + 1)) {v : T} (hv : v ∈ Γ.V)
    (h1 : v ∈ closure r) (h2 : v ∈ closure r'') : False :=
  hn (.inr ⟨hr'', r, hr, v, hv, h2, h1⟩)

variable [T2Space T]

omit [T2Space T] in
/-- A region that holds a point of an atom is that atom. -/
theorem region_eq_of_mem_atom {Γ : Drawing T} {r a : Set T} (hr : r ∈ Γ.R) (ha : a ∈ Γ.A) {y : T}
  (hy : y ∈ r) (hya : y ∈ a) : a = r := by
  have hrU : ∀ {r : Set T}, r ∈ Γ.R → ∀ {y}, y ∈ r → y ∉ Γ.U := fun {r} hr {y} hy h => by
    obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
    exact (connectedComponentIn_subset _ _ hy).2 h
  rcases ha with (⟨v, hv, rfl⟩ | he) | hr'
  · obtain rfl := hya
    exact absurd (Γ.V_subset_U hv) (hrU hr hy)
  · exact absurd (he.2.1 hya).1 (hrU hr hy)
  · obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
    obtain ⟨x', -, rfl⟩ := (mem_R_iff Γ).mp hr'
    exact (connectedComponentIn_eq hya).trans (connectedComponentIn_eq hy).symm

omit [T2Space T] in
/-- A vertex on the closure of a region can be reached from the region. -/
theorem isPathConnected_insert_region_surface (hS : IsClosedSurface T) {Γ : Drawing T} {r : Set T}
  {v : T} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V) (hvr : v ∈ closure r) : IsPathConnected (insert v r) := by
  obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_vertex hS Γ hv
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hvr _ isOpen_interior hΦ.nhd
  obtain ⟨x, rfl⟩ := interior_subset hy1
  have hx : x ≠ polarCentre := fun e => by
    obtain ⟨z, -, rfl⟩ := (mem_R_iff Γ).mp hr
    have : Φ x ∈ Γ.V := by rw [e, hΦ.centre]; exact hv
    exact (connectedComponentIn_subset _ _ hy2).2 (Γ.V_subset_U this)
  have hray : ∀ c : I, 0 < c → Φ (discScale c x) ∈ r := fun c hc => by
    obtain ⟨a, ha, h1, h2⟩ := hΦ.ray x hx c hc
    rw [region_eq_of_mem_atom hr ha hy2 h1] at h2
    exact h2
  have hp : JoinedIn (insert v r) v (Φ x) := by
    refine ⟨⟨⟨fun c : I => Φ (discScale c x), Φ.continuous.comp (continuous_discScale.comp
      (Continuous.prodMk continuous_id continuous_const))⟩, ?_, ?_⟩, fun c => ?_⟩
    · simp [discScale_zero, hΦ.centre]
    · simp [discScale_one]
    · by_cases hc : c = 0
      · subst hc
        left
        simp
      · exact .inr (hray c (unitInterval.pos_iff_ne_zero.mpr hc))
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  have hrp : IsPathConnected r := isPathConnected_of_isOpen hS (region_isOpen hr)
    (region_isPreconnected hr) ⟨_, hy2⟩
  refine ⟨v, mem_insert v r, fun z hz => ?_⟩
  rcases hz with rfl | hz
  · exact JoinedIn.refl (mem_insert _ r)
  · exact hp.trans ((hrp.joinedIn _ hy2 _ hz).mono (subset_insert v r))

omit [T2Space T] in
/-- A chain of regions gives a connected set that meets the drawing in few vertices. -/
theorem exists_chain_set (hS : IsClosedSurface T) {Γ : Drawing T} {r₀ : Set T} (h₀ : r₀ ∈ Γ.R)
  (t : ℕ) : ∀ r ∈ regLayer Γ r₀ t, ∃ A : Set T, IsPathConnected A ∧ r₀ ⊆ A ∧ r ⊆ A
    ∧ ∃ X : Finset T, X.card ≤ t ∧
    (X : Set T) ⊆ Γ.V ∧ A ⊆ (X : Set T) ∪ Γ.Uᶜ := by
  classical
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  have hoff : ∀ {r : Set T}, r ∈ Γ.R → r ⊆ Γ.Uᶜ := fun {r} hr y hy h => by
    obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
    exact (connectedComponentIn_subset _ _ hy).2 h
  induction t with
  | zero =>
    rintro r rfl
    have hrp : IsPathConnected r := isPathConnected_of_isOpen hS (region_isOpen h₀)
      (region_isPreconnected h₀) (region_nonempty h₀)
    exact ⟨r, hrp, Subset.rfl, Subset.rfl, ∅, by simp, by simp, fun x hx => .inr (hoff h₀ hx)⟩
  | succ t ih =>
    rintro r (h | ⟨hr, r', hr', v, hv, h1, h2⟩)
    · obtain ⟨A, a1, a2, a3, X, b1, b2, b3⟩ := ih r h
      exact ⟨A, a1, a2, a3, X, by omega, b2, b3⟩
    · obtain ⟨A, a1, a2, a3, X, b1, b2, b3⟩ := ih r' hr'
      have hr'R := regLayer_subset h₀ t hr'
      have c1 := isPathConnected_insert_region_surface hS hr hv h1
      have c2 := isPathConnected_insert_region_surface hS hr'R hv h2
      obtain ⟨y, hy⟩ := region_nonempty hr'R
      have c3 := a1.union c2 ⟨y, a3 hy, mem_insert_of_mem _ hy⟩
      have c4 := c3.union c1 ⟨v, .inr (mem_insert _ _), mem_insert _ _⟩
      refine ⟨_, c4, a2.trans (subset_union_left.trans subset_union_left),
        fun x hx => .inr (mem_insert_of_mem _ hx), insert v X, ?_, ?_, ?_⟩
      · exact (Finset.card_insert_le _ _).trans (by omega)
      · rw [Finset.coe_insert]
        exact insert_subset hv b2
      · rw [Finset.coe_insert]
        have hins : ∀ x, x ∈ X → x ∈ insert v X := fun x hx => Finset.mem_insert_of_mem hx
        rintro x ((h3 | h3) | h3)
        · rcases b3 h3 with h4 | h4
          · exact .inl (.inr h4)
          · exact .inr h4
        · rcases h3 with rfl | h3
          · exact .inl (.inl rfl)
          · exact .inr (hoff hr'R h3)
        · rcases h3 with rfl | h3
          · exact .inl (.inl rfl)
          · exact .inr (hoff hr h3)

variable [ConnectedSpace T]

omit [T2Space T] in
omit [ConnectedSpace T] in
/-- An edge that meets the closure of a region lies in it. -/
theorem closure_edge_subset (hS : IsClosedSurface T) {Γ : Drawing T} {e r : Set T} (he : e ∈ Γ.E)
  (hr : r ∈ Γ.R) (h : (e ∩ closure r).Nonempty) : closure e ⊆ closure r := by
  obtain ⟨y, hye, hyr⟩ := h
  obtain ⟨𝒜, h𝒜, hc⟩ := isGammaNice_closure_sUnion_regions hS Γ (ℛ := {r})
    (singleton_subset_iff.mpr hr)
  rw [sUnion_singleton] at hc
  rw [hc] at hyr
  obtain ⟨a, ha, hya⟩ := hyr
  have hyU := (he.2.1 hye)
  have hae : a = e := by
    rcases h𝒜 ha with (⟨v, hv, rfl⟩ | h1) | h1
    · obtain rfl := hya
      exact absurd hv hyU.2
    · by_contra hn
      exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ h1 he hn) hya hye
    · obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp h1
      exact absurd hyU.1 (connectedComponentIn_subset _ _ hya).2
  refine closure_minimal (fun x hx => ?_) isClosed_closure
  rw [hc]
  exact ⟨a, ha, hae ▸ hx⟩

omit [T2Space T] [ConnectedSpace T] in
theorem isPreconnected_layer {Γ : Drawing T} {r₀ : Set T} (h₀ : r₀ ∈ Γ.R)
  (t : ℕ) : IsPreconnected (⋃ r ∈ regLayer Γ r₀ t, closure r) := by
  obtain ⟨p, hp⟩ := region_nonempty h₀
  have hp0 : ∀ t, p ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r := fun t =>
    mem_iUnion₂.mpr ⟨r₀, regLayer_mono (Nat.zero_le t) rfl, subset_closure hp⟩
  have key : ∀ t, ∀ x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r, ∃ C, IsPreconnected C ∧ p ∈ C ∧ x ∈ C
    ∧ C ⊆ ⋃ r ∈ regLayer Γ r₀ t, closure r := by
    intro t
    induction t with
    | zero =>
      intro x hx
      refine ⟨closure r₀, (region_isPreconnected h₀).closure, subset_closure hp, ?_, ?_⟩
      · obtain ⟨r, rfl, h⟩ := mem_iUnion₂.mp hx
        exact h
      · exact fun y hy => mem_iUnion₂.mpr ⟨r₀, rfl, hy⟩
    | succ t ih =>
      intro x hx
      have hmono : ∀ y ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r, y ∈ ⋃ r ∈ regLayer Γ r₀
        (t + 1), closure r := fun y hy => by
        obtain ⟨r, h1, h2⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion₂.mpr ⟨r, .inl h1, h2⟩
      obtain ⟨r, h1, h2⟩ := mem_iUnion₂.mp hx
      rcases h1 with h1 | ⟨hr, r', hr', v, hvV, hv1, hv2⟩
      · obtain ⟨C, c1, c2, c3, c4⟩ := ih x (mem_iUnion₂.mpr ⟨r, h1, h2⟩)
        exact ⟨C, c1, c2, c3, c4.trans hmono⟩
      · obtain ⟨C, c1, c2, c3, c4⟩ := ih v (mem_iUnion₂.mpr ⟨r', hr', hv2⟩)
        refine ⟨C ∪ closure r, c1.union v c3 hv1 (region_isPreconnected hr).closure, .inl c2, .inr
          h2, union_subset (c4.trans hmono) fun y hy => mem_iUnion₂.mpr ⟨r, .inr ⟨hr, r', hr', v,
            hvV, hv1, hv2⟩, hy⟩⟩
  refine isPreconnected_of_forall p fun x hx => ?_
  obtain ⟨C, c1, c2, c3, c4⟩ := key t x hx
  exact ⟨C, c4, c2, c3, c1⟩

/-- The `O`-arc in the boundary of a layer. -/
theorem exists_layer_circuit (hS : IsClosedSurface T) (hsph : IsSphere T) {Γ : Drawing T} {r₀ r₂ :
  Set T} (h₀ : r₀ ∈ Γ.R) (h₂ : r₂ ∈ Γ.R) {p a : T} (hp : p ∈ r₀) (ha : a ∈ r₂) {t : ℕ}
    (hfar : r₂ ∉ regLayer Γ r₀ t) : ∃ (C : Drawing T) (D : Set T), C.IsCircuit ∧ C.IsSubdrawing
      (boundaryDrawing Γ (regLayer Γ r₀ t)) ∧ IsClosedDisc D ∧ discBd D = C.U ∧ p ∈ D ∧ a ∉ D := by
  classical
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  have hZ := regLayer_subset h₀ t
  have hr₀ : r₀ ∈ regLayer Γ r₀ t := regLayer_mono (Nat.zero_le t) rfl
  set N := boundaryDrawing Γ (regLayer Γ r₀ t) with hN
  have hNs : N.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hUoff : ∀ {r : Set T}, r ∈ Γ.R → ∀ y ∈ r, y ∉ Γ.U := fun {r} hr y hy h => by
    obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
    exact (connectedComponentIn_subset _ _ hy).2 h
  have hpU := hUoff h₀ p hp
  have haU := hUoff h₂ a ha
  have hUQ : N.U ⊆ ({p, a} : Set T)ᶜ := fun x hx h => by
    rcases h with rfl | rfl
    · exact hpU (hNs.U_subset hx)
    · exact haU (hNs.U_subset hx)
  have hdj : ∀ r ∈ regLayer Γ r₀ t, a ∉ closure r := fun r hr h => by
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp h _ (region_isOpen h₂) ha
    have hne : r = r₂ := by
      have := region_eq_of_mem_atom h₂ (.inr (hZ hr)) hy1 hy2
      exact this
    exact hfar (hne ▸ hr)
  have hnot : ¬ ∀ F, IsOArc F → F ⊆ N.U → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ ({p, a} : Set T)ᶜ ∧ discBd Δ
    = F := fun h => by
    obtain ⟨r, hr, har, hpr⟩ := same_region_of_discs (Q := ({p, a} : Set T)ᶜ) (a := a) (b
      := p) hS hsph (by simp) (by simp) _ N rfl hUQ h
    refine GM14.Whitney.not_same_side hS hZ hr₀ hp (fun hmem => ?_) ⟨r, hr, har, hpr⟩
    obtain ⟨r', h1, h2⟩ := mem_iUnion₂.mp hmem
    exact hdj r' h1 h2
  push Not at hnot
  obtain ⟨F, hF, hFU, hno⟩ := hnot
  obtain ⟨C, hC, hCs, hCU⟩ := exists_circuit_of_oArc hF hFU
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc T hsph F hF
  have hpF : p ∉ F := fun h => hUQ (hFU h) (.inl rfl)
  have haF : a ∉ F := fun h => hUQ (hFU h) (.inr rfl)
  have hhit : ∀ Δ, IsClosedDisc Δ → discBd Δ = F → p ∈ Δ ∨ a ∈ Δ := fun Δ h1 h2 => by
    by_contra hn
    push Not at hn
    refine hno Δ h1 (fun x hx h3 => ?_) h2
    rcases h3 with rfl | rfl
    · exact hn.1 hx
    · exact hn.2 hx
  have hcovp : p ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ p
  have hcova : a ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ a
  by_cases h1 : p ∈ Δ₁
  · refine ⟨C, Δ₁, hC, hCs, hΔ₁, hb₁.trans hCU.symm, h1, fun h2 => ?_⟩
    rcases hhit Δ₂ hΔ₂ hb₂ with h3 | h3
    · exact hpF (hcap ▸ ⟨h1, h3⟩)
    · exact haF (hcap ▸ ⟨h2, h3⟩)
  · have h2 : p ∈ Δ₂ := hcovp.resolve_left h1
    have h3 : a ∈ Δ₁ := (hhit Δ₁ hΔ₁ hb₁).resolve_left h1
    exact ⟨C, Δ₂, hC, hCs, hΔ₂, hb₂.trans hCU.symm, h2, fun h4 => haF (hcap ▸ ⟨h3, h4⟩)⟩

omit [ConnectedSpace T] in
/-- A point of the boundary of a far layer is off a near layer. -/
theorem boundary_off_layer (hS : IsClosedSurface T) {Γ : Drawing T} {r₀ : Set T}
  (h₀ : r₀ ∈ Γ.R) {t t' : ℕ} (htt : t < t') {x : T} (hx : x ∈ (boundaryDrawing Γ
    (regLayer Γ r₀ t')).U)
    (hxt : x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r) : False := by
  obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxt
  have hsub : regLayer Γ r₀ (t + 1) ⊆ regLayer Γ r₀ t' := regLayer_mono htt
  by_cases hv : x ∈ (boundaryDrawing Γ (regLayer Γ r₀ t')).V
  · obtain ⟨-, r'', hr'', h1⟩ := (mem_boundaryDrawing_V hS).mp hv
    exact not_incident_far hr hr''.1 (fun h => hr''.2 (hsub h)) h1.1 hxr h1.2.2
  · obtain ⟨e, he, hxe⟩ := (boundaryDrawing Γ (regLayer Γ r₀ t')).exists_edge_of_mem hx hv
    obtain ⟨-, r'', hr'', h1⟩ := mem_boundaryDrawing_E.mp he
    have hheE := h1.1
    obtain ⟨c, h2, h3, h4, h5, h6⟩ := exists_edge_param _ hheE
    have hc : EdgeParam Γ e c := ⟨h2, h3, h4, h5, h6⟩
    have hvc : c 0 ∈ closure e := by
      rw [hc.closure_eq]
      exact mem_range_self 0
    have hA := closure_edge_subset hS hheE (regLayer_subset h₀ t hr) ⟨x, hxe, hxr⟩ hvc
    have hB := closure_edge_subset hS hheE hr''.1 h1.2.2 hvc
    exact not_incident_far hr hr''.1 (fun h => hr''.2 (hsub h)) h3 hA hB

omit [ConnectedSpace T] in
theorem boundary_subset_layer (hS : IsClosedSurface T) {Γ : Drawing T} {r₀ : Set T} {t : ℕ} {x : T}
  (hx : x ∈ (boundaryDrawing Γ (regLayer Γ r₀ t)).U) :
    x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r := by
  by_cases hv : x ∈ (boundaryDrawing Γ (regLayer Γ r₀ t)).V
  · obtain ⟨⟨r, hr, h1⟩, -⟩ := (mem_boundaryDrawing_V hS).mp hv
    exact mem_iUnion₂.mpr ⟨r, hr, h1.2.2⟩
  · obtain ⟨e, he, hxe⟩ := (boundaryDrawing Γ (regLayer Γ r₀ t)).exists_edge_of_mem hx hv
    obtain ⟨⟨r, hr, h1⟩, -⟩ := mem_boundaryDrawing_E.mp he
    exact mem_iUnion₂.mpr ⟨r, hr, closure_edge_subset hS h1.1 h1.2.1 h1.2.2 (subset_closure hxe)⟩

/-- **The nest of the layers.** If `r₂` is not in the first `s` layers, they give `s` disjoint
nested circuits. -/
theorem exists_region_nest (hS : IsClosedSurface T) (hsph : IsSphere T) {Γ : Drawing T} {r₀ r₂ :
  Set T} (h₀ : r₀ ∈ Γ.R) (h₂ : r₂ ∈ Γ.R) {p a : T} (hp : p ∈ r₀) (ha : a ∈ r₂) {s : ℕ}
    (hfar : ∀ t < s, r₂ ∉ regLayer Γ r₀ t) :
    ∃ (C : Fin s → Drawing T) (D : Fin s → Set T), (∀ t, (C t).IsCircuit ∧ (C t).IsSubdrawing Γ
      ∧ IsClosedDisc (D t) ∧ discBd (D t) = (C t).U ∧ p ∈ D t ∧ a ∉ D t) ∧
      ∀ t t', t < t' → Disjoint (C t).V (C t').V ∧ D t ⊆ D t' := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hex : ∀ t : Fin s, ∃ (C : Drawing T) (D : Set T), C.IsCircuit ∧ C.IsSubdrawing
    (boundaryDrawing Γ (regLayer Γ r₀ t)) ∧ IsClosedDisc D ∧ discBd D = C.U ∧ p ∈ D ∧ a ∉ D
      := fun t =>
    exists_layer_circuit hS hsph h₀ h₂ hp ha (hfar t t.2)
  choose C D hC hCs hD hb hpD haD using hex
  refine ⟨C, D, fun t => ⟨hC t, (hCs t).trans (Drawing.span_isSubdrawing Γ _ _), hD t, hb t,
    hpD t, haD t⟩, fun t t' htt => ?_⟩
  have hin : ∀ {x}, x ∈ (C t).U → x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r := fun {x} hx
    => boundary_subset_layer hS ((hCs t).U_subset hx)
  have hfr' : frontier (D t') = (C t').U := by
    rw [IsClosedDisc.frontier_eq_discBd hS (hD t'), hb t']
  have hfr : frontier (D t) = (C t).U := by rw [IsClosedDisc.frontier_eq_discBd hS (hD t), hb t]
  have hoff : ∀ {x}, x ∈ (C t').U → x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r → False := fun {x} hx h
    => boundary_off_layer hS h₀ (Fin.lt_def.mp htt) ((hCs t').U_subset hx) h
  refine ⟨disjoint_left.mpr fun x h1 h2 => hoff ((C t').V_subset_U h2) (hin
    ((C t).V_subset_U h1)), ?_⟩
  have hL := isPreconnected_layer h₀ t
  have hpL : p ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r := mem_iUnion₂.mpr ⟨r₀, regLayer_mono
    (Nat.zero_le _) rfl, subset_closure hp⟩
  have hdis : Disjoint (⋃ r ∈ regLayer Γ r₀ t, closure r) (frontier (D t')) := by
    rw [hfr']
    exact disjoint_left.mpr fun x h1 h2 => hoff h2 h1
  have hint : (⋃ r ∈ regLayer Γ r₀ t, closure r) ⊆ interior (D t') := by
    rcases inside_or_outside hL (hD t').isClosed hdis with h | h
    · exact h
    · exact absurd (hpD t') (h hpL)
  obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph (hD t')
  have hcompl : discInt (closure (univ \ D t')) = (D t')ᶜ := by
    ext x
    have hfx : x ∈ discBd (D t') ↔ x ∈ closure (D t') ∩ closure (D t')ᶜ := by
      rw [← IsClosedDisc.frontier_eq_discBd hS (hD t'), frontier_eq_closure_inter_closure]
    rw [discInt, hbE, mem_sdiff, hfx, (hD t').isClosed.closure_eq, ← compl_eq_univ_sdiff]
    constructor
    · rintro ⟨h1, h2⟩ h3
      exact h2 ⟨h3, h1⟩
    · intro h
      exact ⟨subset_closure h, fun h3 => h h3.1⟩
  have hX : IsPreconnected (D t')ᶜ := hcompl ▸ hE.isPreconnected_discInt
  have hdis2 : Disjoint (D t')ᶜ (frontier (D t)) := by
    rw [hfr]
    exact disjoint_left.mpr fun x h1 h2 => h1 (interior_subset (hint (hin h2)))
  rcases inside_or_outside hX (hD t).isClosed hdis2 with h | h
  · exact absurd (interior_subset (h (haD t'))) (haD t)
  · exact fun x hx => by
      by_contra hn
      exact h hn hx

end GraphMinor.GM07
