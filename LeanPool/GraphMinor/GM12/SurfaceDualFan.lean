/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section4c
public import LeanPool.GraphMinor.GM12.SurfaceDualStar

/-!
# A star is an open disc

Go around `v ∈ V₀`, with the half-edges `o 0, o 1, ...` at `v` in rotation order. The regions in the
corners are all different (`IsSideSplit.corner_inj`). Start with the region in the first corner and
glue on the regions in the next corners one at a time, across the edge between them, by
`glue_open_discs`. This gives a fan, which is an open disc (`fan`).

The last step is different, since the last region touches the fan along the two edges `o 0` and the
last
half-edge, which meet at `v`. These two edges have different other ends, by `corner_alternates`. So
their union is a line through `v`, which we add to `N` as one edge, and we use `glue_open_discs` for
that
drawing. The fan and the last region are regions of this drawing since the stars are open and
disjoint.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {D K N : Drawing S}
  {V₀ : Set S}

/-- See the module docstring. -/
def fan {ι : Type*} (ρ a : ι → Set S) (o : ℕ → ι) : ℕ → Set S
  | 0 => ρ (o 0)
  | n + 1 => fan ρ a o n ∪ ρ (o (n + 1)) ∪ a (o (n + 1))

section Fan

omit [T2Space S] [ConnectedSpace S]

variable {ι : Type*} {ρ a : ι → Set S} {o : ℕ → ι}

omit [TopologicalSpace S] in
theorem face_subset_fan {i n : ℕ} (hi : i ≤ n) : ρ (o i) ⊆ fan ρ a o n := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact Subset.rfl
  | succ n ih =>
    by_cases h : i = n + 1
    · subst h
      exact fun x hx => Or.inl (Or.inr hx)
    · exact (ih (by omega)).trans fun x hx => Or.inl (Or.inl hx)

omit [TopologicalSpace S] in
theorem arm_subset_fan {i n : ℕ} (h₀ : 1 ≤ i) (hi : i ≤ n) : a (o i) ⊆ fan ρ a o n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i = n + 1
    · subst h
      exact fun x hx => Or.inr hx
    · exact (ih (by omega)).trans fun x hx => Or.inl (Or.inl hx)

omit [TopologicalSpace S] in
theorem mem_fan {n : ℕ} {x : S} (hx : x ∈ fan ρ a o n) :
    (∃ i ≤ n, x ∈ ρ (o i)) ∨ ∃ i, 1 ≤ i ∧ i ≤ n ∧ x ∈ a (o i) := by
  induction n with
  | zero => exact Or.inl ⟨0, le_rfl, hx⟩
  | succ n ih =>
    rcases hx with (hx | hx) | hx
    · rcases ih hx with ⟨i, hi, h⟩ | ⟨i, h₁, hi, h⟩
      · exact Or.inl ⟨i, by omega, h⟩
      · exact Or.inr ⟨i, h₁, by omega, h⟩
    · exact Or.inl ⟨n + 1, le_rfl, hx⟩
    · exact Or.inr ⟨n + 1, by omega, le_rfl, hx⟩

end Fan

omit [T2Space S] [ConnectedSpace S] in
/-- A connected open set that, with a disjoint open set, fills the complement of `U(H)` is a region.
-/
theorem mem_R_of_split {H : Drawing S} {C C' : Set S} (hC : IsOpen C) (hC' : IsOpen C')
    (hne : C.Nonempty) (hcon : IsPreconnected C) (hd : Disjoint C C') (hu : C ∪ C'
      = H.Uᶜ) : C ∈ H.R := by
  obtain ⟨x, hx⟩ := hne
  have hxU : x ∉ H.U := by
    have : x ∈ H.Uᶜ := hu ▸ Or.inl hx
    exact this
  rw [mem_R_iff]
  refine ⟨x, hxU, subset_antisymm ?_ ?_⟩
  · refine hcon.subset_connectedComponentIn hx fun y hy => ⟨mem_univ _, ?_⟩
    have : y ∈ H.Uᶜ := hu ▸ Or.inl hy
    exact this
  · have hc : IsPreconnected (connectedComponentIn (univ \ H.U) x) :=
      isPreconnected_connectedComponentIn
    refine hc.subset_left_of_subset_union hC hC' hd (fun y hy => ?_) ⟨x,
      mem_connectedComponentIn ⟨mem_univ _, hxU⟩, hx⟩
    rw [hu]
    exact (connectedComponentIn_subset _ _ hy).2

namespace IsSideSplit

variable (hX : IsSideSplit D K N V₀) (hrad : PreRad (PaintingOrDrawing.drawing D) K)
  (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing D) K) (hE : D.E.Nonempty)

private theorem initial_fan_is_open_disc
    {S : Type u}
    [TopologicalSpace S]
    [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {v : S}
    (H : Drawing S)
    (γ : Set S → ↑I → S)
    (next : ↑(halfEdges H γ v) → ↑(halfEdges H γ v))
    (ρ : ↑(halfEdges H γ v) → Set S)
    (d : ℕ)
    (o : ℕ → ↑(halfEdges H γ v))
    (hosucc : ∀ (i : ℕ), o (i + 1) = next (o i))
    (hoinj : ∀ {i j : ℕ}, i < d → j < d → o i = o j → i = j)
    (a : ↑(halfEdges H γ v) → Set S)
    (hEk : ∀ (k : ↑(halfEdges H γ v)), a k ∈ H.E)
    (hRk : ∀ (k : ↑(halfEdges H γ v)), ρ k ∈ H.R)
    (hOpen : ∀ k, IsOpenDisc (ρ k))
    (hleft : ∀ (k : ↑(halfEdges H γ v)), a (next k) ⊆ closure (ρ k))
    (hright : ∀ (k : ↑(halfEdges H γ v)), a (next k) ⊆ closure (ρ (next k)))
    (hρinj : ∀ {k k' : ↑(halfEdges H γ v)}, ρ k = ρ k' → k = k')
    (hd_arm : ∀ {n j : ℕ}, j < d → n < d → j = 0 ∨ n < j → Disjoint (fan ρ a o n) (closure (a (o
      j))))
    (hd_face : ∀ {n j : ℕ}, n < j → j < d → Disjoint (fan ρ a o n) (ρ (o j)))
    (hd_rc : ∀ (k k' : ↑(halfEdges H γ v)), Disjoint (ρ k) (closure (a k'))) :
    ∀ (n : ℕ), n + 2 ≤ d → IsOpenDisc (fan ρ a o n) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact hOpen _
  | succ n ih =>
    intro hn
    have hn1 : n + 1 < d := by omega
    have hne : ρ (o n) ≠ ρ (o (n + 1)) := fun h' => by
      have := hoinj (by omega) hn1 (hρinj h')
      omega
    refine glue_open_discs hS (hEk (o (n + 1))) (hRk (o n)) (hRk (o (n + 1))) hne ?_ ?_
      (face_subset_fan le_rfl) Subset.rfl (ih (by omega)) (hOpen _)
      (hd_face (by omega) hn1) (hd_arm hn1 (by omega) (Or.inr (by omega))) (hd_rc _ _)
    · rw [hosucc]
      exact hleft _
    · rw [hosucc]
      exact hright _

private theorem star_eq_completed_fan
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {v : S}
    (H : Drawing S)
    (γ : Set S → ↑I → S)
    (hγ : EdgePar H γ)
    (hvH : v ∈ H.V)
    (next : ↑(halfEdges H γ v) → ↑(halfEdges H γ v))
    (ρ : ↑(halfEdges H γ v) → Set S)
    (hcor : IsCorners H γ v next ρ)
    (d : ℕ)
    (o : ℕ → ↑(halfEdges H γ v))
    (hreach : ∀ (k : ↑(halfEdges H γ v)), ∃ i < d, o i = k)
    (a : ↑(halfEdges H γ v) → Set S)
    (ha : ∀ k, a k = k.1.1)
    (hEk : ∀ (k : ↑(halfEdges H γ v)), a k ∈ H.E)
    (hvk : ∀ (k : ↑(halfEdges H γ v)), v ∈ closure (a k))
    (e : ℕ) (hed : d = e + 2)
    (w₀ : S)
    (hw₀v : w₀ ≠ v)
    (w₁ : S)
    (hw₁v : w₁ ≠ v)
    (c : Set S) (hc : c = closure (a (o 0)) ∪ closure (a (o (e + 1))))
    (hmemc : ∀ {z : S}, z ∈ c → z = v ∨ z = w₀ ∨ z = w₁ ∨ z ∈ a (o 0) ∨ z ∈ a (o (e + 1)))
    (hw₀H : w₀ ∈ H.V)
    (hw₁H : w₁ ∈ H.V)
    (hstar : ∀ {z : S}, z ∈ fan ρ a o e → z ∈ star H v)
    (hstarF : ρ (o (e + 1)) ⊆ star H v) :
    star H v = fan ρ a o e ∪ ρ (o (e + 1)) ∪ c \ {w₀, w₁} := by
  apply subset_antisymm
  · intro x hx
    have hedge : ∀ {g}, x ∈ g → g = a (o 0) ∨ g = a (o (e + 1)) → x ∈ c \ {w₀, w₁} := by
      rintro g hxg (rfl | rfl)
      · refine ⟨hc ▸ Or.inl (subset_closure hxg), ?_⟩
        rintro (h' | h')
        · exact edge_notMem_V (hEk _) hxg (h' ▸ hw₀H)
        · exact edge_notMem_V (hEk _) hxg (h' ▸ hw₁H)
      · refine ⟨hc ▸ Or.inr (subset_closure hxg), ?_⟩
        rintro (h' | h')
        · exact edge_notMem_V (hEk _) hxg (h' ▸ hw₀H)
        · exact edge_notMem_V (hEk _) hxg (h' ▸ hw₁H)
    rcases mem_star hx with rfl | ⟨g, hg, hvg, hxg⟩ | ⟨p, hp, hvp, hxp⟩
    · refine Or.inr ⟨hc ▸ Or.inl (hvk (o 0)), ?_⟩
      rintro (h' | h')
      · exact hw₀v h'.symm
      · exact hw₁v h'.symm
    · obtain ⟨b, hb⟩ := exists_end_eq hγ hg hvH hvg
      obtain ⟨i, hi, hik⟩ := hreach ⟨(g, b), hg, hb⟩
      have hgi : a (o i) = g := by rw [hik, ha]
      by_cases h₀ : i = 0
      · subst h₀
        exact Or.inr (hedge hxg (Or.inl hgi.symm))
      by_cases h₁ : i = e + 1
      · subst h₁
        exact Or.inr (hedge hxg (Or.inr hgi.symm))
      · exact Or.inl (Or.inl (arm_subset_fan (by omega) (by omega) (hgi ▸ hxg)))
    · obtain ⟨k, rfl⟩ := IsCorners.all hcor p hp hvp
      obtain ⟨i, hi, rfl⟩ := hreach k
      by_cases h₁ : i = e + 1
      · subst h₁
        exact Or.inl (Or.inr hxp)
      · exact Or.inl (Or.inl (face_subset_fan (by omega) hxp))
  · rintro x ((hx | hx) | ⟨hx, hxw⟩)
    · exact hstar hx
    · exact hstarF hx
    · rcases hmemc hx with rfl | rfl | rfl | h' | h'
      · exact mem_star_self _ _
      · exact absurd (Or.inl rfl) hxw
      · exact absurd (Or.inr rfl) hxw
      · exact edge_subset_star (hEk _) (hvk _) h'
      · exact edge_subset_star (hEk _) (hvk _) h'

private theorem completed_fan_complements_augmented_drawing
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    [ConnectedSpace S]
    {D : Drawing S}
    {K : Drawing S}
    {N : Drawing S}
    {V₀ : Set S}
    (hX : IsSideSplit D K N V₀)
    (hrad : PreRad (PaintingOrDrawing.drawing D) K)
    (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing D) K)
    (hE : D.E.Nonempty)
    {v : S}
    (hv : v ∈ V₀)
    (H : Drawing S) (hH : H = radialUnion hrad)
    (γ : Set S → ↑I → S)
    (ρ : ↑(halfEdges H γ v) → Set S)
    (o : ℕ → ↑(halfEdges H γ v))
    (a : ↑(halfEdges H γ v) → Set S)
    (e : ℕ)
    (w₀ : S)
    (w₁ : S)
    (c : Set S)
    (H' : Drawing S)
    (hH'U : H'.U = N.U ∪ c)
    (hstar : ∀ {z : S}, z ∈ fan ρ a o e → z ∈ star H v)
    (hstarF : ρ (o (e + 1)) ⊆ star H v)
    (hdc : Disjoint (fan ρ a o e) c)
    (hdcF : Disjoint (ρ (o (e + 1))) c)
    (hstar_eq : star H v = fan ρ a o e ∪ ρ (o (e + 1)) ∪ c \ {w₀, w₁})
    (Rest : Set S) (hRest_eq : Rest = ⋃ w ∈ V₀ \ {v}, star H w)
    (hRestc : Disjoint Rest c) :
    fan ρ a o e ∪ ρ (o (e + 1)) ∪ Rest = H'.Uᶜ := by
  subst H
  rw [hH'U, hRest_eq]
  apply subset_antisymm
  · rintro x ((hx | hx) | hx) (hxU | hxU)
    · exact disjoint_left.mp (hX.star_off hrad hv) (hstar hx) hxU
    · exact disjoint_left.mp hdc hx hxU
    · exact disjoint_left.mp (hX.star_off hrad hv) (hstarF hx) hxU
    · exact disjoint_left.mp hdcF hx hxU
    · obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      exact disjoint_left.mp (hX.star_off hrad hu.1) hxu hxU
    · exact disjoint_left.mp hRestc (hRest_eq.symm ▸ hx) hxU
  · intro x hx
    have hxN : x ∉ N.U := fun h' => hx (Or.inl h')
    have hxc : x ∉ c := fun h' => hx (Or.inr h')
    obtain ⟨u, hu, hxu⟩ := hX.exists_star hrad hS hmax hE hxN
    by_cases huv : u = v
    · subst huv
      rw [hstar_eq] at hxu
      rcases hxu with (h' | h') | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')
      · exact absurd h'.1 hxc
    · exact Or.inr (mem_biUnion (show u ∈ V₀ \ {v} from ⟨hu, huv⟩) hxu)

private theorem fan_end_arms_have_single_intersection {S : Type u} [TopologicalSpace S]
    {H : Drawing S} {e₀ e₁ : Set S} {v w₀ w₁ : S} (he₀ : e₀ ∈ H.E) (he₁ : e₁ ∈ H.E)
    (hne : e₀ ≠ e₁) (hw₀₁ : w₀ ≠ w₁) (hv₀ : v ∈ closure e₀) (hv₁ : v ∈ closure e₁)
    (hcap₀ : closure e₀ ∩ H.V = {v, w₀}) (hcap₁ : closure e₁ ∩ H.V = {v, w₁}) :
    closure e₀ ∩ closure e₁ = {v} := by
  apply subset_antisymm
  · rintro z ⟨h₁, h₂⟩
    have hzV := closure_inter_subset_V he₀ he₁ hne ⟨h₁, h₂⟩
    have h₃ : z ∈ ({v, w₀} : Set S) := hcap₀ ▸ ⟨h₁, hzV⟩
    have h₄ : z ∈ ({v, w₁} : Set S) := hcap₁ ▸ ⟨h₂, hzV⟩
    rcases h₃ with h₃ | h₃
    · exact h₃
    · rcases h₄ with h₄ | h₄
      · exact h₄
      · exact absurd (h₃.symm.trans h₄) hw₀₁
  · rintro z rfl
    exact ⟨hv₀, hv₁⟩

private theorem joining_line_membership {S : Type u} [TopologicalSpace S]
    {H : Drawing S} {e₀ e₁ : Set S} {v w₀ w₁ : S} (he₀ : e₀ ∈ H.E) (he₁ : e₁ ∈ H.E)
    (hcap₀ : closure e₀ ∩ H.V = {v, w₀}) (hcap₁ : closure e₁ ∩ H.V = {v, w₁}) :
    ∀ {z : S}, z ∈ closure e₀ ∪ closure e₁ →
      z = v ∨ z = w₀ ∨ z = w₁ ∨ z ∈ e₀ ∨ z ∈ e₁ := by
  rintro z (hz | hz)
  · by_cases hzV : z ∈ H.V
    · have : z ∈ ({v, w₀} : Set S) := hcap₀ ▸ ⟨hz, hzV⟩
      rcases this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (Or.inl (H.closure_diff_V he₀ ▸ ⟨hz, hzV⟩))))
  · by_cases hzV : z ∈ H.V
    · have : z ∈ ({v, w₁} : Set S) := hcap₁ ▸ ⟨hz, hzV⟩
      rcases this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (H.closure_diff_V he₁ ▸ ⟨hz, hzV⟩))))

private theorem joining_line_meets_split_only_at_endpoints {S : Type u} [TopologicalSpace S]
    [T2Space S] {N : Drawing S} {c e₀ e₁ : Set S} {v w₀ w₁ : S}
    (hv : v ∉ N.U) (hw₀ : w₀ ∈ N.V) (hw₁ : w₁ ∈ N.V)
    (he₀ : Disjoint e₀ N.U) (he₁ : Disjoint e₁ N.U) (hne : w₀ ≠ w₁)
    (hline : IsLineWithEnds c w₀ w₁)
    (hmemc : ∀ {z}, z ∈ c → z = v ∨ z = w₀ ∨ z = w₁ ∨ z ∈ e₀ ∨ z ∈ e₁) :
    N.U ∩ (lineDrawing hline hne).U ⊆ N.V ∩ (lineDrawing hline hne).V := by
  rintro z ⟨hzN, hzc⟩
  rcases hmemc hzc with rfl | rfl | rfl | h' | h'
  · exact absurd hzN hv
  · exact ⟨hw₀, Or.inl rfl⟩
  · exact ⟨hw₁, Or.inr rfl⟩
  · exact absurd hzN (disjoint_left.mp he₀ h')
  · exact absurd hzN (disjoint_left.mp he₁ h')

include hX hS hmax hE

/-- See the module docstring. -/
theorem star_isOpenDisc {v : S} (hv : v ∈ V₀) : IsOpenDisc (star (radialUnion hrad) v) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨y₀⟩ : Nonempty S := inferInstance
  have hne' : Nonempty S := ⟨y₀⟩
  set H := radialUnion hrad with hH
  obtain ⟨γ, hγ⟩ := exists_edgePar H
  have hvH : v ∈ H.V := hX.V_sub hrad hv
  have hvD := hX.sub_V hv
  have htwo : 2 ≤ Nat.card (halfEdges H γ v) := two_half_edges hrad hS hmax hE hγ hvD
  obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS H hγ hvH htwo
  have hcor := IsSectors.corners hsec
  have : Finite (halfEdges H γ v) := (finite_halfEdges H γ v).to_subtype
  obtain ⟨k₀⟩ : Nonempty (halfEdges H γ v) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0 : Nat.card (halfEdges H γ v) = 0 := Nat.card_of_isEmpty
    omega
  have hinjn : Function.Injective next := IsCorners.inj hcor
  have hper := hinjn.mem_periodicPts k₀
  set d := Function.minimalPeriod next k₀ with hd
  have hdpos : 0 < d := Function.minimalPeriod_pos_of_mem_periodicPts hper
  let o : ℕ → halfEdges H γ v := fun i => next^[i] k₀
  have hosucc : ∀ i, o (i + 1) = next (o i) := fun i => Function.iterate_succ_apply' _ _ _
  have ho0 : o 0 = k₀ := rfl
  have hod : o d = k₀ := Function.iterate_minimalPeriod
  have hoinj : ∀ {i j}, i < d → j < d → o i = o j → i = j := fun hi hj h' =>
    Function.iterate_injOn_Iio_minimalPeriod hi hj h'
  have hreach : ∀ k, ∃ i < d, o i = k := by
    intro k
    have h₁ : ∃ n, next^[n] k₀ = k := by
      induction IsCorners.reach hcor k₀ k with
      | refl => exact ⟨0, rfl⟩
      | tail _ h' ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [Function.iterate_succ_apply', hn]
        exact h'.symm
    obtain ⟨n, hn⟩ := h₁
    exact ⟨n % d, Nat.mod_lt _ hdpos, Function.iterate_mod_minimalPeriod_eq.trans hn⟩
  have hd2 : 2 ≤ d := by
    by_contra hn
    have h1 : d = 1 := by omega
    have : o 1 = k₀ := h1 ▸ hod
    exact IsSectors.next_ne hsec k₀ ((hosucc 0).symm.trans this)
  let a : halfEdges H γ v → Set S := fun k => k.1.1
  have hEk : ∀ k, a k ∈ H.E := fun k => k.2.1
  have hvk : ∀ k, v ∈ closure (a k) := fun k => by
    have := end_mem_closure hγ k.2.1 k.1.2
    rwa [k.2.2] at this
  have hRk : ∀ k, ρ k ∈ H.R := IsCorners.region hcor
  have hleft : ∀ k, a (next k) ⊆ closure (ρ k) := IsCorners.left hcor
  have hright : ∀ k, a (next k) ⊆ closure (ρ (next k)) := IsCorners.right hcor
  have hρinj : ∀ {k k'}, ρ k = ρ k' → k = k' := fun h' =>
    hX.corner_inj hrad hS hmax hE hγ hv hsec h'
  -- Faces and fans are disjoint from later faces and from the closures of the other arms.
  have hd_arm : ∀ {n j}, j < d → n < d → (j = 0 ∨ n < j) → Disjoint (fan ρ a o n) (closure (a
    (o j))) := by
    intro n j hj hn hc
    refine disjoint_left.mpr fun x hx hxc => ?_
    rcases mem_fan hx with ⟨i, -, hi⟩ | ⟨i, h₁, hi, hxi⟩
    · exact region_subset (hRk _) hi (H.closure_subset_U (hEk _) hxc)
    · have hxV : x ∉ H.V := edge_notMem_V (hEk _) hxi
      have hxj : x ∈ a (o j) := H.closure_diff_V (hEk _) ▸ ⟨hxc, hxV⟩
      have heq : a (o i) = a (o j) := H.edge_eq_of_mem (hEk _) (hEk _) hxi hxj
      have := hoinj (by omega) hj (hX.half_inj hrad hγ hv heq)
      omega
  have hd_face : ∀ {n j}, n < j → j < d → Disjoint (fan ρ a o n) (ρ (o j)) := by
    intro n j hnj hj
    refine disjoint_left.mpr fun x hx hxρ => ?_
    rcases mem_fan hx with ⟨i, hi, hxi⟩ | ⟨i, -, -, hxi⟩
    · have := hoinj (by omega) hj (hρinj (region_eq_of_mem (hRk _) (hRk _) hxi hxρ))
      omega
    · exact region_subset (hRk _) hxρ (H.closure_subset_U (hEk _) (subset_closure hxi))
  have hd_rc : ∀ k k', Disjoint (ρ k) (closure (a k')) := fun k k' =>
    disjoint_left.mpr fun x hx hxc => region_subset (hRk _) hx (H.closure_subset_U (hEk _) hxc)
  -- The fans are open discs.
  have hfan : ∀ n, n + 2 ≤ d → IsOpenDisc (fan ρ a o n) := by
    exact initial_fan_is_open_disc hS (v := v) H γ next ρ d o hosucc hoinj a hEk hRk
      (fun k => face_isOpenDisc hrad hS hmax (hRk k)) hleft hright hρinj hd_arm hd_face hd_rc
  -- The last step.
  obtain ⟨e, hed⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hlast : next (o (e + 1)) = o 0 := by
    rw [← hosucc, ho0, ← hod, hed]
  have hfanE : IsOpenDisc (fan ρ a o e) := hfan e (by omega)
  have hF₁ : IsOpenDisc (ρ (o (e + 1))) := face_isOpenDisc hrad hS hmax (hRk _)
  obtain ⟨w₀, hw₀v, hw₀V₀, hw₀N, hcap₀, hN₀, hD₀, hK₀⟩ := hX.arm hrad (hEk (o 0)) hv (hvk _)
  obtain ⟨w₁, hw₁v, hw₁V₀, hw₁N, hcap₁, hN₁, hD₁, hK₁⟩ := hX.arm hrad (hEk (o (e + 1))) hv (hvk _)
  have hw₀₁ : w₀ ≠ w₁ := by
    have halt := corner_alternates hrad hS hmax hE hγ hvD hsec (o (e + 1))
    rw [hlast] at halt
    rcases halt with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact fun h' => hK₁ h₁ (h' ▸ hD₀ h₂)
    · exact fun h' => hK₀ h₂ (h'.symm ▸ hD₁ h₁)
  have hne0 : a (o 0) ≠ a (o (e + 1)) := fun h' => by
    have := hoinj (by omega) (by omega) (hX.half_inj hrad hγ hv h')
    omega
  have hl₀ : IsLineWithEnds (closure (a (o 0))) v w₀ := isLine_closure (hEk _) hw₀v.symm hcap₀
  have hl₁ : IsLineWithEnds (closure (a (o (e + 1)))) v w₁ := isLine_closure (hEk _) hw₁v.symm hcap₁
  have hcap : closure (a (o 0)) ∩ closure (a (o (e + 1))) = {v} := by
    exact fan_end_arms_have_single_intersection (hEk _) (hEk _) hne0 hw₀₁ (hvk _) (hvk _)
      hcap₀ hcap₁
  have hline := IsLineWithEnds.union hl₀ hl₁ hcap
  set c := closure (a (o 0)) ∪ closure (a (o (e + 1))) with hc
  -- A point of the line is `v`, one of the two other ends, or on one of the two arms.
  have hmemc : ∀ {z}, z ∈ c → z = v ∨ z = w₀ ∨ z = w₁ ∨ z ∈ a (o 0) ∨ z ∈ a (o (e + 1)) := by
    exact joining_line_membership (hEk _) (hEk _) hcap₀ hcap₁
  have hw₀H : w₀ ∈ H.V := hX.N_V_sub hrad hw₀N
  have hw₁H : w₁ ∈ H.V := hX.N_V_sub hrad hw₁N
  have hglue : N.U ∩ (lineDrawing hline hw₀₁).U ⊆ N.V ∩ (lineDrawing hline hw₀₁).V := by
    exact joining_line_meets_split_only_at_endpoints (hX.V₀_off hv) hw₀N hw₁N
      (hX.edge_off hrad (hEk _) hN₀) (hX.edge_off hrad (hEk _) hN₁) hw₀₁ hline hmemc
  let H' := N.glue (lineDrawing hline hw₀₁) hglue
  have hH'U : H'.U = N.U ∪ c := rfl
  have heH' : c \ {w₀, w₁} ∈ H'.E := by
    rw [Drawing.glue_E, lineDrawing_E]
    exact Or.inr rfl
  have hstar : ∀ {z}, z ∈ fan ρ a o e → z ∈ star H v := by
    intro z hz
    rcases mem_fan hz with ⟨i, -, h'⟩ | ⟨i, -, -, h'⟩
    · exact face_subset_star (hRk _) (IsCorners.closure_v hcor _) h'
    · exact edge_subset_star (hEk _) (hvk _) h'
  have hstarF : ρ (o (e + 1)) ⊆ star H v :=
    face_subset_star (hRk _) (IsCorners.closure_v hcor _)
  have hdc : Disjoint (fan ρ a o e) c := by
    rw [hc, disjoint_union_right]
    exact ⟨hd_arm (by omega) (by omega) (Or.inl rfl), hd_arm (by omega) (by omega) (Or.inr
      (by omega))⟩
  have hdcF : Disjoint (ρ (o (e + 1))) c := by
    rw [hc, disjoint_union_right]
    exact ⟨hd_rc _ _, hd_rc _ _⟩
  have hstar_eq : star H v = fan ρ a o e ∪ ρ (o (e + 1)) ∪ (c \ {w₀, w₁}) := by
    exact star_eq_completed_fan (S := S) (v := v) H γ hγ hvH next ρ hcor d o hreach a
      (fun _ => rfl) hEk hvk e hed w₀ hw₀v w₁ hw₁v c hc hmemc hw₀H hw₁H hstar hstarF
  let Rest : Set S := ⋃ u ∈ V₀ \ {v}, star H u
  have hRest : IsOpen Rest :=
    isOpen_biUnion fun u hu => hX.star_isOpen hrad hS hmax hE hu.1
  have hRestv : Disjoint Rest (star H v) := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    exact hu.2 (hX.star_eq hrad hS hmax hE hu.1 hv hxu hx')
  have hRestc : Disjoint Rest c := by
    refine disjoint_left.mpr fun x hx hxc => ?_
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have hnN : x ∉ N.U := disjoint_left.mp (hX.star_off hrad hu.1) hxu
    rcases hmemc hxc with rfl | rfl | rfl | h' | h'
    · exact disjoint_left.mp hRestv hx (mem_star_self _ _)
    · exact hnN (N.V_subset_U hw₀N)
    · exact hnN (N.V_subset_U hw₁N)
    · exact disjoint_left.mp hRestv hx (edge_subset_star (hEk _) (hvk _) h')
    · exact disjoint_left.mp hRestv hx (edge_subset_star (hEk _) (hvk _) h')
  -- The complement of the new drawing.
  have hcompl : fan ρ a o e ∪ ρ (o (e + 1)) ∪ Rest = H'.Uᶜ := by
    exact completed_fan_complements_augmented_drawing (S := S) (D := D) (K := K) (N := N) (V₀ :=
      V₀) hX hrad hS hmax hE (v := v) hv H hH γ ρ o a e w₀ w₁ c H' hH'U hstar hstarF hdc hdcF
      hstar_eq Rest rfl hRestc
  have hdFF : Disjoint (fan ρ a o e) (ρ (o (e + 1))) := hd_face (by omega) (by omega)
  have hdR₁ : Disjoint (fan ρ a o e) Rest := by
    refine disjoint_left.mpr fun x hx hx' => disjoint_left.mp hRestv hx' (hstar hx)
  have hdR₂ : Disjoint (ρ (o (e + 1))) Rest := by
    refine disjoint_left.mpr fun x hx hx' => disjoint_left.mp hRestv hx' (hstarF hx)
  have hneF : (fan ρ a o e).Nonempty := by
    obtain ⟨x, hx⟩ := region_nonempty (hRk (o 0))
    exact ⟨x, face_subset_fan (Nat.zero_le _) hx⟩
  have hR₁ : fan ρ a o e ∈ H'.R := by
    refine mem_R_of_split (C' := ρ (o (e + 1)) ∪ Rest) hfanE.1 (hF₁.1.union hRest) hneF
      (isPreconnected_of_isOpenDisc hfanE) (disjoint_union_right.mpr ⟨hdFF, hdR₁⟩) ?_
    rw [← hcompl, union_assoc]
  have hR₂ : ρ (o (e + 1)) ∈ H'.R := by
    refine mem_R_of_split (C' := fan ρ a o e ∪ Rest) hF₁.1 (hfanE.1.union hRest)
      (region_nonempty (hRk _)) (isPreconnected_of_isOpenDisc hF₁)
      (disjoint_union_right.mpr ⟨hdFF.symm, hdR₂⟩) ?_
    rw [← hcompl, union_right_comm, union_comm (ρ _)]
  have hclc : closure (c \ {w₀, w₁}) = c := closure_sdiff_pair hline
  have hsub_c : ∀ {T : Set S}, IsClosed T → a (o 0) ⊆ T → a (o (e + 1)) ⊆ T → v ∈ T →
      c \ {w₀, w₁} ⊆ T := by
    intro T hT h₁ h₂ hvT z hz
    rcases hmemc hz.1 with rfl | rfl | rfl | h' | h'
    · exact hvT
    · exact absurd (Or.inl rfl) hz.2
    · exact absurd (Or.inr rfl) hz.2
    · exact h₁ h'
    · exact h₂ h'
  have hh₁ : c \ {w₀, w₁} ⊆ closure (fan ρ a o e) := by
    refine hsub_c isClosed_closure ?_ ?_ ?_
    · have := hright (o (e + 1))
      rw [hlast] at this
      exact this.trans (closure_mono (face_subset_fan (Nat.zero_le _)))
    · have := hleft (o e)
      rw [← hosucc] at this
      exact this.trans (closure_mono (face_subset_fan le_rfl))
    · exact closure_mono (face_subset_fan (Nat.zero_le _)) (IsCorners.closure_v hcor _)
  have hh₂ : c \ {w₀, w₁} ⊆ closure (ρ (o (e + 1))) := by
    refine hsub_c isClosed_closure ?_ ?_ (IsCorners.closure_v hcor _)
    · have := hleft (o (e + 1))
      rwa [hlast] at this
    · have := hright (o e)
      rwa [← hosucc] at this
  rw [hstar_eq]
  refine glue_open_discs hS heH' hR₁ hR₂ (fun h' => ?_) hh₁ hh₂ Subset.rfl Subset.rfl hfanE hF₁ hdFF
    (by rw [hclc]; exact hdc) (by rw [hclc]; exact hdcF)
  obtain ⟨x, hx⟩ := hneF
  exact disjoint_left.mp hdFF hx (h' ▸ hx)

/-- The stars are the regions of `N`: they are open, connected and disjoint, and they fill the
complement of `U(N)`. -/
theorem star_mem_R {v : S} (hv : v ∈ V₀) : star (radialUnion hrad) v ∈ N.R := by
  set H := radialUnion hrad with hH
  have hd := hX.star_isOpenDisc hrad hS hmax hE hv
  refine mem_R_of_split (C' := ⋃ u ∈ V₀ \ {v}, star H u) hd.1
    (isOpen_biUnion fun u hu => hX.star_isOpen hrad hS hmax hE hu.1) ⟨v, mem_star_self _ _⟩
    (isPreconnected_of_isOpenDisc hd) ?_ ?_
  · refine disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx'
    exact hu.2 (hX.star_eq hrad hS hmax hE hu.1 hv hxu hx)
  · apply subset_antisymm
    · rintro x (hx | hx) hxU
      · exact disjoint_left.mp (hX.star_off hrad hv) hx hxU
      · obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
        exact disjoint_left.mp (hX.star_off hrad hu.1) hxu hxU
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := hX.exists_star hrad hS hmax hE hx
      by_cases huv : u = v
      · exact Or.inl (huv ▸ hxu)
      · exact Or.inr (mem_biUnion (show u ∈ V₀ \ {v} from ⟨hu, huv⟩) hxu)

theorem exists_star_eq {r : Set S} (hr : r ∈ N.R) : ∃ v ∈ V₀, r = star (radialUnion hrad) v := by
  obtain ⟨x, hx⟩ := region_nonempty hr
  obtain ⟨v, hv, hxv⟩ := hX.exists_star hrad hS hmax hE (region_subset hr hx)
  exact ⟨v, hv, region_eq_of_mem hr (hX.star_mem_R hrad hS hmax hE hv) hx hxv⟩

/-- A closed disc in a star and one more point `u` off `D`, with its boundary on `H`, does not
exist.
Its interior has a point off `H`, in a region of `H` at `v`. This region lies in the disc, since it
misses the boundary. So the disc holds the end off `V₀` of the edge of `D` beside this region. But
this
end is not in the star, since it is on `N`, and it is not `u`. -/
theorem no_disc_in_star {v u : S} (hv : v ∈ V₀) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hsub : Δ ⊆ star (radialUnion hrad) v ∪ {u}) (hu : u ∉ D.V) (huU : u ∈ (radialUnion hrad).U)
    (hb : discBd Δ ⊆ (radialUnion hrad).U) : False := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hne : (discInt Δ).Nonempty := by
    obtain ⟨h, g, c'⟩ := hΔ.exists_isChart
    rw [c'.discInt_eq]
    exact ⟨g 0, mem_image_of_mem _ (Metric.mem_ball_self one_pos)⟩
  obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := radialUnion hrad) hS (hΔ.isOpen_discInt hman) hne
  have hyΔ : y ∈ Δ := hyO.1
  have hys : y ∈ star (radialUnion hrad) v := by
    rcases hsub hyΔ with h' | h'
    · exact h'
    · exact absurd (h' ▸ huU) hyU
  obtain ⟨p, hp, hvp, hyp⟩ : ∃ p ∈ (radialUnion hrad).R, v ∈ closure p ∧ y ∈ p := by
    rcases mem_star hys with rfl | ⟨g, hg, -, hyg⟩ | h'
    · exact absurd ((radialUnion hrad).V_subset_U (hX.V_sub hrad hv)) hyU
    · exact absurd ((radialUnion hrad).closure_subset_U hg (subset_closure hyg)) hyU
    · exact h'
  have hpΔ : p ⊆ Δ := by
    intro z hz
    by_contra hzΔ
    have hdis := disjoint_disc_of_outside hman hΔ (region_isPreconnected hp)
      (disjoint_left.mpr fun w hw hw' => region_subset hp hw (hb hw')) hz hzΔ
    exact disjoint_left.mp hdis hyp hyΔ
  obtain ⟨j, hj, hjp, -, -⟩ := face_edge hrad hS hmax hE hp
  obtain ⟨u', -, w, hw, hcap⟩ := hX.D_ends j hj
  have hwj : w ∈ closure j ∩ D.V := by rw [hcap]; simp
  have hwΔ : w ∈ Δ := closure_minimal (hjp.trans (closure_minimal hpΔ hΔ.isClosed)) hΔ.isClosed
    hwj.1
  rcases hsub hwΔ with h' | h'
  · exact disjoint_left.mp (hX.star_off hrad hv) h'
      (N.V_subset_U (hX.V_eq ▸ ⟨radial_V hrad hw.1, hw.2⟩))
  · exact hu (h' ▸ hw.1)

end IsSideSplit

end GraphMinor.GM12
