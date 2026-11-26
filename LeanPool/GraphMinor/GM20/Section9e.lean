/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9d

/-!
# Graph Minors XX, Section 9: the vertices of the expansion

Let `ζ` be a linear inflation of `Γ` in `Γ'` with `ψ(c) ≤ ψ'(ζ(c))` for all `c`. This file defines
the sets
`η(v)` of the proof of (9.1), and proves its claims (2), (3), (4).

The third condition of a hull says that the nodes `n` of a cuff with `v ∈ β(n)` form an interval of
the
cuff (`Side.interval`). So a property can be carried along these nodes, from each one to the next
(`Side.walk`). This is how the paper proves (3) and (10), and we use `walk` for both.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

theorem eq_of_getElem?_eq {l : List α} (hnd : l.Nodup) {i j : ℕ} {x : α} (h₁ : l[i]? = some x)
    (h₂ : l[j]? = some x) : i = j := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h₁
  obtain ⟨hj, hy⟩ := List.getElem?_eq_some_iff.mp h₂
  exact (hnd.getElem_inj_iff (hi := hi) (hj := hj)).mp (hx.trans hy.symm)

section SideLemmas

variable {Ω : Type*} {X : GradedSurface} {F : CuffParam X.S} {Q : Patchwork Ω α β}
  (A : Side X F Q) {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S)

namespace Side

theorem isBorder_cell (m : ℕ) : Painting.IsBorder ((A.C Θ hΘ).cell m) := by
  obtain ⟨y, hy, hyΘ⟩ := (A.C Θ hΘ).meets m
  exact ⟨y, hy, cuff_subset_bd hΘ hyΘ⟩

theorem mem_of_getElem? {n : ℕ} {i : ℕ} {x : α}
    (h : (A.π ((A.C Θ hΘ).pos n))[i]? = some x) : x ∈ A.h.border ((A.C Θ hΘ).pos n) := by
  have h₁ : x ∈ A.π ((A.C Θ hΘ).pos n) := List.mem_of_getElem? h
  have h₂ := (A.labelled Θ hΘ).set_eq n
  rw [← h₂]
  exact h₁

theorem exists_getElem? {n : ℕ} {x : α} (h : x ∈ A.h.border ((A.C Θ hΘ).pos n)) :
    ∃ i : ℕ, (A.π ((A.C Θ hΘ).pos n))[i]? = some x := by
  rw [← (A.labelled Θ hΘ).set_eq n] at h
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem h
  exact ⟨i, List.getElem?_eq_some_iff.mpr ⟨hi, hx⟩⟩

theorem exists_term {m m' i : ℕ} {x : α} (h : (A.π ((A.C Θ hΘ).pos m))[i]? = some x) :
    ∃ y, (A.π ((A.C Θ hΘ).pos m'))[i]? = some y := by
  have hi := (List.getElem?_eq_some_iff.mp h).1
  rw [(A.labelled Θ hΘ).length_eq m, ← (A.labelled Θ hΘ).length_eq m'] at hi
  exact ⟨_, List.getElem?_eq_getElem hi⟩

theorem border_finite (m : ℕ) : (A.h.border ((A.C Θ hΘ).pos m)).Finite :=
  Q.G.vertexSet_finite.subset (A.h.border_subset _
    ⟨(A.C Θ hΘ).mem_N m, cuff_subset_bd hΘ ((A.C Θ hΘ).mem_cuff m)⟩)

theorem pair_finite (m : ℕ) : (A.M ((A.C Θ hΘ).cell m)).verts.Finite :=
  isPairing_verts_finite (A.border_finite hΘ m) (A.border_finite hΘ (m + 1))
    ((A.labelled Θ hΘ).pair m)

/-- If two terms of `π(pos m), π(pos (m + 1))` are linked, and `x` lies in both sets, then both
terms are
`x`. -/
theorem eq_of_linked_left {m : ℕ} {x y : α} (hl : Linked (A.M ((A.C Θ hΘ).cell m)) x y)
    (hx : x ∈ A.h.border ((A.C Θ hΘ).pos (m + 1)))
    (hy : y ∈ A.h.border ((A.C Θ hΘ).pos (m + 1))) : y = x := by
  have hp := (A.labelled Θ hΘ).pair m
  have hv : x ∈ (A.M ((A.C Θ hΘ).cell m)).verts := by
    rw [hp.verts_eq]
    exact Or.inl (Or.inr hx)
  obtain ⟨z, -, -, hu⟩ := hp.existsUnique (A.pair_finite hΘ m) hv
  rw [hu y (Or.inl hy) hl, hu x (Or.inl hx) (Or.inl rfl)]

theorem eq_of_linked_right {m : ℕ} {x y : α} (hl : Linked (A.M ((A.C Θ hΘ).cell m)) x y)
    (hx : x ∈ A.h.border ((A.C Θ hΘ).pos m)) (hy : y ∈ A.h.border ((A.C Θ hΘ).pos m)) : x = y := by
  have hp := ((A.labelled Θ hΘ).pair m).symm
  have hv : y ∈ (A.M ((A.C Θ hΘ).cell m)).verts := by
    rw [hp.verts_eq]
    exact Or.inl (Or.inr hy)
  obtain ⟨z, -, -, hu⟩ := hp.existsUnique (A.pair_finite hΘ m) hv
  rw [hu x (Or.inl hx) hl.symm, hu y (Or.inl hy) (Or.inl rfl)]

/-- The link of `IsLabelled` for every cell but `c_Θ`, with indices beyond `k`. -/
theorem link_of_ne {m : ℕ} (hm : (A.C Θ hΘ).cell m ≠ (A.C Θ hΘ).cell ((A.C Θ hΘ).k - 1)) {i : ℕ}
    {x y : α} (hx : (A.π ((A.C Θ hΘ).pos m))[i]? = some x)
    (hy : (A.π ((A.C Θ hΘ).pos (m + 1)))[i]? = some y) :
    Linked (A.M ((A.C Θ hΘ).cell m)) x y := by
  set C := A.C Θ hΘ
  have hk := C.k_pos
  have hlt : m % C.k + 1 < C.k := by
    have h₁ := Nat.mod_lt m hk
    by_contra hc
    have h₂ : m % C.k = C.k - 1 := by omega
    exact hm (by rw [← C.cell_mod m, h₂])
  have h₁ : C.pos m = C.pos (m % C.k) := (C.pos_mod m).symm
  have h₂ : C.pos (m + 1) = C.pos (m % C.k + 1) := C.pos_succ_eq_of_pos_eq h₁
  rw [h₁] at hx
  rw [h₂] at hy
  rw [← C.cell_mod m]
  exact (A.labelled Θ hΘ).link _ hlt i x y hx hy

/-- The nodes `n` on a cuff with `v ∈ β(n)` form an interval, by the third condition of a hull. -/
theorem interval {v : α} {a b : ℕ} (ha : v ∈ A.h.border ((A.C Θ hΘ).pos a))
    (hb : v ∈ A.h.border ((A.C Θ hΘ).pos b)) (_hab : a ≤ b) (_hb₂ : b ≤ a + (A.C Θ hΘ).k) :
    (∀ j, a ≤ j → j ≤ b → v ∈ A.h.border ((A.C Θ hΘ).pos j)) ∨
      ∀ j, b ≤ j → j ≤ a + (A.C Θ hΘ).k → v ∈ A.h.border ((A.C Θ hΘ).pos j) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨j₁, h₁, h₂, h₃⟩, j₂, h₄, h₅, h₆⟩ := hc
  set C := A.C Θ hΘ
  have hmem : ∀ j, C.pos j ∈ A.Γ.N ∩ Θ := fun j ↦ ⟨C.mem_N j, C.mem_cuff j⟩
  rcases A.h.border_order Θ hΘ _ (hmem a) _ (hmem j₁) _ (hmem b) _ (hmem j₂)
    (C.inOrder h₁ h₂ h₄ h₅) ⟨ha, hb⟩ with h₇ | h₇
  · exact h₃ h₇
  · exact h₆ h₇

theorem walk_fwd (R : X.S → Prop) {v : α}
    (hs : ∀ j, v ∈ A.h.border ((A.C Θ hΘ).pos j) → v ∈ A.h.border ((A.C Θ hΘ).pos (j + 1)) →
      R ((A.C Θ hΘ).pos j) → R ((A.C Θ hΘ).pos (j + 1))) {a b : ℕ} (hab : a ≤ b)
    (hv : ∀ j, a ≤ j → j ≤ b → v ∈ A.h.border ((A.C Θ hΘ).pos j)) (hR : R ((A.C Θ hΘ).pos a)) :
    R ((A.C Θ hΘ).pos b) := by
  induction b, hab using Nat.le_induction with
  | base => exact hR
  | succ b hab ih =>
    exact hs b (hv b hab (by omega)) (hv _ (by omega) le_rfl)
      (ih fun j h₁ h₂ ↦ hv j h₁ (by omega))

theorem walk_bwd (R : X.S → Prop) {v : α}
    (hs : ∀ j, v ∈ A.h.border ((A.C Θ hΘ).pos j) → v ∈ A.h.border ((A.C Θ hΘ).pos (j + 1)) →
      R ((A.C Θ hΘ).pos (j + 1)) → R ((A.C Θ hΘ).pos j)) {a b : ℕ} (hab : a ≤ b)
    (hv : ∀ j, a ≤ j → j ≤ b → v ∈ A.h.border ((A.C Θ hΘ).pos j)) (hR : R ((A.C Θ hΘ).pos b)) :
    R ((A.C Θ hΘ).pos a) := by
  induction b, hab using Nat.le_induction with
  | base => exact hR
  | succ b hab ih =>
    exact ih (fun j h₁ h₂ ↦ hv j h₁ (by omega))
      (hs b (hv b hab (by omega)) (hv _ (by omega) le_rfl) hR)

/-- A property that passes between consecutive nodes `n` of a cuff with `v ∈ β(n)` holds for all
such
nodes if it holds for one. -/
theorem walk (R : X.S → Prop) {v : α}
    (hs₁ : ∀ j, v ∈ A.h.border ((A.C Θ hΘ).pos j) → v ∈ A.h.border ((A.C Θ hΘ).pos (j + 1)) →
      R ((A.C Θ hΘ).pos j) → R ((A.C Θ hΘ).pos (j + 1)))
    (hs₂ : ∀ j, v ∈ A.h.border ((A.C Θ hΘ).pos j) → v ∈ A.h.border ((A.C Θ hΘ).pos (j + 1)) →
      R ((A.C Θ hΘ).pos (j + 1)) → R ((A.C Θ hΘ).pos j)) {a b : ℕ}
    (ha : v ∈ A.h.border ((A.C Θ hΘ).pos a)) (hb : v ∈ A.h.border ((A.C Θ hΘ).pos b))
    (hR : R ((A.C Θ hΘ).pos a)) : R ((A.C Θ hΘ).pos b) := by
  set C := A.C Θ hΘ
  have hk := C.k_pos
  have ha' := Nat.mod_lt a hk
  have hb' := Nat.mod_lt b hk
  rw [← C.pos_mod a] at ha hR
  rw [← C.pos_mod b] at hb ⊢
  generalize a % C.k = a at ha hR ha'
  generalize b % C.k = b at hb hb' ⊢
  rcases le_total a b with hab | hab
  · have hab₂ : b ≤ a + C.k := by omega
    rcases A.interval hΘ ha hb hab hab₂ with h₁ | h₁
    · exact A.walk_fwd hΘ R hs₁ hab h₁ hR
    · refine A.walk_bwd hΘ R hs₂ hab₂ h₁ ?_
      rwa [C.pos_add]
  · have hab₂ : a ≤ b + C.k := by omega
    rcases A.interval hΘ hb ha hab hab₂ with h₁ | h₁
    · exact A.walk_bwd hΘ R hs₂ hab h₁ hR
    · have := A.walk_fwd hΘ R hs₁ hab₂ h₁ hR
      rwa [C.pos_add] at this

theorem mem_μ {c : Set X.S} (hc : c ∈ A.Γ.C) (hb : Painting.IsBorder c) {n : X.S} (hn : n ∈ tilde c)
    {x : α} (hx : x ∈ A.h.border n) : x ∈ Q.μ (A.h.cell c) := by
  have hd : A.h.cell c ∈ Q.dom := by
    rw [A.dom_eq]
    exact A.h.cell_bijOn.mapsTo hc
  have h₁ : x ∈ {v | v ∈ Q.μ (A.h.cell c)} := by
    rw [Q.μ_set _ hd]
    refine (A.h.ends_border c hc hb).symm ▸ Or.inr ?_
    exact Set.mem_biUnion hn hx
  exact h₁

theorem mem_tilde_left (m : ℕ) : (A.C Θ hΘ).pos m ∈ tilde ((A.C Θ hΘ).cell m) := by
  rw [(A.C Θ hΘ).tilde_eq]
  exact Or.inl rfl

theorem mem_tilde_right (m : ℕ) : (A.C Θ hΘ).pos (m + 1) ∈ tilde ((A.C Θ hΘ).cell m) := by
  rw [(A.C Θ hΘ).tilde_eq]
  exact Or.inr rfl

theorem length_π_le {K : ℕ} (hB : A.Bounded K) (m : ℕ) : (A.π ((A.C Θ hΘ).pos m)).length ≤ K := by
  have hc := (A.C Θ hΘ).cell_mem m
  have hb := A.isBorder_cell hΘ m
  refine (length_le_of_subset ((A.labelled Θ hΘ).nodup m) fun x hx ↦ ?_).trans (hB _ hc hb)
  exact A.mem_μ hc hb (A.mem_tilde_left hΘ m) (by
    rw [← (A.labelled Θ hΘ).set_eq m]
    exact hx)

theorem length_π_le' {K : ℕ} (hB : A.Bounded K) (m : ℕ) :
    (A.π ((A.C Θ hΘ).pos (m + 1))).length ≤ K := A.length_π_le hΘ hB (m + 1)

/-- A term of the march of a node on `Θ` lies in the set `β` of this node. -/
theorem mem_border_of_term (hΘ : Θ ∈ cuffs X.S) {n : X.S} (hn : n ∈ A.Γ.N ∩ Θ) {i : ℕ} {x : α}
    (h : (A.π n)[i]? = some x) : x ∈ A.h.border n := by
  obtain ⟨m, -, rfl⟩ := (A.C Θ hΘ).exists_pos n hn
  exact A.mem_of_getElem? hΘ h

end Side

end SideLemmas

/-- The hypotheses of the main step of the proof of (9.1). -/
structure InflationHyp {Ω : Type*} [Preorder Ω] {X : GradedSurface} {F : CuffParam X.S}
    {Q Q' : Patchwork Ω α β} (A : Side X F Q) (A' : Side X F Q') (ζn : X.S → Set X.S)
    (ζc : Set X.S → Set X.S) (K : ℕ) : Prop where
  infl : IsLinearInflation A.Γ A'.Γ ζn ζc
  ψ_le : ∀ c ∈ A.Γ.C, A.ψ K c ≤ A'.ψ K (ζc c)
  two_le : 2 ≤ K
  bounded : A.Bounded K
  bounded' : A'.Bounded K

/-- The set `η(v)`. For `v = n ∈ N(Γ)` it is `ζ(n)`, and for other `v` it is the set of terms `v'`
of
`π'(n')` where `v` is the same term of `π(n)` and `n'` is in `ζ(n)`, on the same cuff as `n`. -/
def etaVert {Ω : Type*} {X : GradedSurface} {F : CuffParam X.S} {Q Q' : Patchwork Ω α β}
    (A : Side X F Q) (A' : Side X F Q') (ζn : X.S → Set X.S) (v : α) : Set α :=
  {v' | (∃ n ∈ A.Γ.N, A.h.node n = v ∧ ∃ n' ∈ ζn n, A'.h.node n' = v') ∨
    ∃ Θ ∈ cuffs X.S, ∃ n ∈ A.Γ.N ∩ Θ, ∃ n' ∈ ζn n ∩ Θ, ∃ i : ℕ,
      (A.π n)[i]? = some v ∧ (A'.π n')[i]? = some v'}

section Main

variable {Ω : Type*} [Preorder Ω] {X : GradedSurface} {F : CuffParam X.S} {Q Q' : Patchwork Ω α β}
  {A : Side X F Q} {A' : Side X F Q'} {ζn : X.S → Set X.S} {ζc : Set X.S → Set X.S} {K : ℕ}
  (H : InflationHyp A A' ζn ζc K)

namespace InflationHyp

include H

theorem exists_lift' {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) :
    ∃ L : ℕ → ℕ, L 0 = 0 ∧ Monotone L ∧
      (∀ m', (A'.C Θ hΘ).pos m' ∈ ζn ((A.C Θ hΘ).pos (L m'))) ∧
      (∀ m', (L (m' + 1) = L m' ∧ (A'.C Θ hΘ).cell m' ∉ ζc '' A.Γ.C) ∨
        (L (m' + 1) = L m' + 1 ∧ ζc ((A.C Θ hΘ).cell (L m')) = (A'.C Θ hΘ).cell m')) ∧
      (∀ m' < (A'.C Θ hΘ).k, L m' < (A.C Θ hΘ).k) ∧
      (∀ l < (A.C Θ hΘ).k, ∃ m' < (A'.C Θ hΘ).k, L m' = l) :=
  exists_lift H.infl hΘ _ _ (cut_image A A' H.infl H.ψ_le hΘ)

theorem cell_ne_cut {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {j : ℕ}
    (hj : (A'.C Θ hΘ).cell j ∉ ζc '' A.Γ.C) :
    (A'.C Θ hΘ).cell j ≠ (A'.C Θ hΘ).cell ((A'.C Θ hΘ).k - 1) := fun heq ↦
  hj ⟨_, (A.C Θ hΘ).cell_mem _, (cut_image A A' H.infl H.ψ_le hΘ).trans heq.symm⟩

/-- The terms of `π` on a cell determine the terms of `π'` on its image. -/
theorem transfer_fwd {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {m m' : ℕ}
    (h : ζc ((A.C Θ hΘ).cell m) = (A'.C Θ hΘ).cell m') {i j : ℕ} {x : α}
    (h₁ : (A.π ((A.C Θ hΘ).pos m))[i]? = some x)
    (h₂ : (A.π ((A.C Θ hΘ).pos (m + 1)))[j]? = some x) :
    ∃ x', (A'.π ((A'.C Θ hΘ).pos m'))[i]? = some x' ∧
      (A'.π ((A'.C Θ hΘ).pos (m' + 1)))[j]? = some x' := by
  have ha := aligned_cell A A' H.infl H.ψ_le H.two_le H.bounded H.bounded' hΘ h
  have hc := (A.C Θ hΘ).cell_mem m
  have hb := A.isBorder_cell hΘ m
  refine term_of_code (H.bounded _ hc hb) ha.code₁ ha.code₂ (A.length_π_le hΘ H.bounded m)
    (A.length_π_le hΘ H.bounded (m + 1)) ?_ h₁ h₂
  exact A.mem_μ hc hb (A.mem_tilde_left hΘ m) (A.mem_of_getElem? hΘ h₁)

theorem transfer_bwd {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {m m' : ℕ}
    (h : ζc ((A.C Θ hΘ).cell m) = (A'.C Θ hΘ).cell m') {i j : ℕ} {x : α}
    (h₁ : (A'.π ((A'.C Θ hΘ).pos m'))[i]? = some x)
    (h₂ : (A'.π ((A'.C Θ hΘ).pos (m' + 1)))[j]? = some x) :
    ∃ x', (A.π ((A.C Θ hΘ).pos m))[i]? = some x' ∧
      (A.π ((A.C Θ hΘ).pos (m + 1)))[j]? = some x' := by
  have ha := aligned_cell A A' H.infl H.ψ_le H.two_le H.bounded H.bounded' hΘ h
  have hc := (A'.C Θ hΘ).cell_mem m'
  have hb := A'.isBorder_cell hΘ m'
  refine term_of_code (H.bounded' _ hc hb) ha.code₁.symm ha.code₂.symm
    (A'.length_π_le hΘ H.bounded' m') (A'.length_π_le hΘ H.bounded' (m' + 1)) ?_ h₁ h₂
  exact A'.mem_μ hc hb (A'.mem_tilde_left hΘ m') (A'.mem_of_getElem? hΘ h₁)

theorem pos_eq_of_mem' {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {n : X.S} (hn : n ∈ A.Γ.N) {l : ℕ}
    {n' : X.S} (h₁ : n' ∈ ζn n) (h₂ : n' ∈ ζn ((A.C Θ hΘ).pos l)) : n = (A.C Θ hΘ).pos l := by
  by_contra hne
  exact Set.disjoint_left.mp (H.infl.node_disjoint _ hn _ ((A.C Θ hΘ).mem_N l) hne) h₁ h₂

/-- Claim (3) of the proof of (9.1). -/
theorem claim_3 {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {n₁ n₂ n₁' n₂' : X.S} (hn₁ : n₁ ∈ A.Γ.N)
    (hn₂ : n₂ ∈ A.Γ.N) (h₁ : n₁' ∈ ζn n₁ ∩ Θ) (h₂ : n₂' ∈ ζn n₂ ∩ Θ) {i j : ℕ} {v v' : α}
    (hv : (A.π n₁)[i]? = some v) (hv' : (A'.π n₁')[i]? = some v') (hj : (A'.π n₂')[j]? = some v') :
    (A.π n₂)[j]? = some v := by
  obtain ⟨L, -, -, hpos, hstep, -, -⟩ := H.exists_lift' hΘ
  set C := A.C Θ hΘ
  set C' := A'.C Θ hΘ
  let R : X.S → Prop := fun n' ↦ ∃ n ∈ A.Γ.N, n' ∈ ζn n ∧ ∃ i : ℕ, (A'.π n')[i]? = some v' ∧
    (A.π n)[i]? = some v
  obtain ⟨a, -, rfl⟩ := C'.exists_pos n₁' ⟨H.infl.node_subset _ hn₁ h₁.1, h₁.2⟩
  obtain ⟨b, -, rfl⟩ := C'.exists_pos n₂' ⟨H.infl.node_subset _ hn₂ h₂.1, h₂.2⟩
  change (A'.π (C'.pos a))[i]? = some v' at hv'
  change (A'.π (C'.pos b))[j]? = some v' at hj
  have hR : R (C'.pos b) := by
    refine A'.walk hΘ R (a := a) ?_ ?_ (A'.mem_of_getElem? hΘ hv') (A'.mem_of_getElem? hΘ hj)
      ⟨n₁, hn₁, h₁.1, i, hv', hv⟩
    · rintro k hk₁ hk₂ ⟨n, hn, hkn, i₀, hi₀, hi₀'⟩
      obtain rfl := H.pos_eq_of_mem' hΘ hn hkn (hpos k)
      rcases hstep k with ⟨hL, hni⟩ | ⟨hL, hz⟩
      · obtain ⟨y, hy⟩ := A'.exists_term hΘ (m' := k + 1) hi₀
        have hl := A'.link_of_ne hΘ (H.cell_ne_cut hΘ hni) hi₀ hy
        obtain rfl := A'.eq_of_linked_left hΘ hl hk₂ (A'.mem_of_getElem? hΘ hy)
        exact ⟨_, hn, hL ▸ hpos (k + 1), i₀, hy, hi₀'⟩
      · obtain ⟨i₂, hi₂⟩ := A'.exists_getElem? hΘ hk₂
        obtain ⟨x, hx₁, hx₂⟩ := H.transfer_bwd hΘ hz hi₀ hi₂
        obtain rfl : x = v := by
          rw [hi₀'] at hx₁
          exact (Option.some.inj hx₁).symm
        exact ⟨_, C.mem_N _, hL ▸ hpos (k + 1), i₂, hi₂, hx₂⟩
    · rintro k hk₁ hk₂ ⟨n, hn, hkn, i₀, hi₀, hi₀'⟩
      obtain rfl := H.pos_eq_of_mem' hΘ hn hkn (hpos (k + 1))
      rcases hstep k with ⟨hL, hni⟩ | ⟨hL, hz⟩
      · obtain ⟨y, hy⟩ := A'.exists_term hΘ (m' := k) hi₀
        have hl := A'.link_of_ne hΘ (H.cell_ne_cut hΘ hni) hy hi₀
        have heq := A'.eq_of_linked_right hΘ hl (A'.mem_of_getElem? hΘ hy) hk₁
        subst heq
        exact ⟨_, hn, hL.symm ▸ hpos k, i₀, hy, hi₀'⟩
      · obtain ⟨i₂, hi₂⟩ := A'.exists_getElem? hΘ hk₁
        obtain ⟨x, hx₁, hx₂⟩ := H.transfer_bwd hΘ hz hi₂ hi₀
        obtain rfl : x = v := by
          rw [hL, hx₂] at hi₀'
          exact Option.some.inj hi₀'
        exact ⟨_, C.mem_N _, hpos k, i₂, hi₂, hx₁⟩
  obtain ⟨n, hn, hkn, i₀, hi₀, hi₀'⟩ := hR
  obtain rfl := (H.pos_eq_of_mem' (Θ := Θ) hΘ hn hkn (hpos b)).trans
    (H.pos_eq_of_mem' hΘ hn₂ h₂.1 (hpos b)).symm
  obtain rfl := eq_of_getElem?_eq ((A'.labelled Θ hΘ).nodup b) hi₀ hj
  exact hi₀'

/-- Claim (2) of the proof of (9.1), and `η(v) ⊆ V(G')`. -/
theorem claim_2 {v : α} (hv : v ∈ Q.G.vertexSet) : (etaVert A A' ζn v).Nonempty := by
  have hvs := hv
  rw [show Q.G.vertexSet = _ from A.h.vertexSet_eq] at hvs
  rcases hvs with ⟨n, hn, rfl⟩ | hvs
  · obtain ⟨n', hn'⟩ := H.infl.node_nonempty n hn
    exact ⟨_, Or.inl ⟨n, hn, rfl, n', hn', rfl⟩⟩
  · simp only [mem_iUnion, exists_prop] at hvs
    obtain ⟨n, ⟨hnN, hnb⟩, hvn⟩ := hvs
    obtain ⟨Θ, hΘ, hnΘ⟩ : ∃ Θ ∈ cuffs X.S, n ∈ Θ :=
      ⟨_, ⟨n, hnb, rfl⟩, mem_connectedComponentIn hnb⟩
    obtain ⟨L, -, -, hpos, -, -, hsurj⟩ := H.exists_lift' hΘ
    obtain ⟨a, ha, rfl⟩ := (A.C Θ hΘ).exists_pos n ⟨hnN, hnΘ⟩
    obtain ⟨m', -, hm'⟩ := hsurj a ha
    obtain ⟨i, hi⟩ := A.exists_getElem? hΘ hvn
    have hlen : i < (A'.π ((A'.C Θ hΘ).pos m')).length := by
      rw [(A'.labelled Θ hΘ).length_eq, ← (A.labelled Θ hΘ).length_eq a]
      exact (List.getElem?_eq_some_iff.mp hi).1
    exact ⟨_, Or.inr ⟨Θ, hΘ, _, ⟨hnN, hnΘ⟩, (A'.C Θ hΘ).pos m', ⟨hm' ▸ hpos m',
      (A'.C Θ hΘ).mem_cuff m'⟩, i, hi, List.getElem?_eq_getElem hlen⟩⟩

theorem eta_subset (v : α) : etaVert A A' ζn v ⊆ Q'.G.vertexSet := by
  rintro v' (⟨n, hn, -, n', hn', rfl⟩ | ⟨Θ, hΘ, n, hn, n', hn', i, -, hi⟩)
  · exact A'.h.node_mem _ (H.infl.node_subset _ hn hn')
  · have hN' : n' ∈ A'.Γ.N ∩ Θ := ⟨H.infl.node_subset _ hn.1 hn'.1, hn'.2⟩
    exact A'.h.border_subset _ ⟨hN'.1, cuff_subset_bd hΘ hN'.2⟩ (A'.mem_border_of_term hΘ hN' hi)

/-- Claim (4) of the proof of (9.1). -/
theorem claim_4 {v₁ v₂ : α} (hne : v₁ ≠ v₂) :
    Disjoint (etaVert A A' ζn v₁) (etaVert A A' ζn v₂) := by
  have hnodes : ∀ {a : α} {n n' : X.S} {Θ : Set X.S}, Θ ∈ cuffs X.S → n ∈ A'.Γ.N ∩ Θ → n' ∈ A'.Γ.N →
      A'.h.node n' = a → ∀ i : ℕ, (A'.π n)[i]? = some a → False := by
    intro a n n' Θ hΘ hn hn' hna i hi
    have h₁ := A'.mem_border_of_term hΘ hn hi
    exact Set.disjoint_left.mp (A'.h.border_disjoint _ ⟨hn.1, cuff_subset_bd hΘ hn.2⟩) h₁
      ⟨n', hn', hna⟩
  rw [Set.disjoint_left]
  rintro a (⟨n₁, h₁, rfl, n₁', h₃, h₄⟩ | ⟨Θ₁, hΘ₁, n₁, h₁, n₁', h₃, i, h₅, h₆⟩)
    (⟨n₂, h₁', hv, n₂', h₃', h₄'⟩ | ⟨Θ₂, hΘ₂, n₂, h₁', n₂', h₃', j, h₅', h₆'⟩)
  · have hN₁ := H.infl.node_subset _ h₁ h₃
    have hN₂ := H.infl.node_subset _ h₁' h₃'
    have heq : n₁' = n₂' := A'.h.node_injOn hN₁ hN₂ (h₄.trans h₄'.symm)
    subst heq
    have hnn : n₁ = n₂ := by
      by_contra hc
      exact Set.disjoint_left.mp (H.infl.node_disjoint _ h₁ _ h₁' hc) h₃ h₃'
    exact hne (by rw [hnn, hv])
  · exact hnodes hΘ₂ ⟨H.infl.node_subset _ h₁'.1 h₃'.1, h₃'.2⟩ (H.infl.node_subset _ h₁ h₃) h₄ j h₆'
  · exact hnodes hΘ₁ ⟨H.infl.node_subset _ h₁.1 h₃.1, h₃.2⟩ (H.infl.node_subset _ h₁' h₃') h₄' i h₆
  · have hN₁ : n₁' ∈ A'.Γ.N ∩ Θ₁ := ⟨H.infl.node_subset _ h₁.1 h₃.1, h₃.2⟩
    have hN₂ : n₂' ∈ A'.Γ.N ∩ Θ₂ := ⟨H.infl.node_subset _ h₁'.1 h₃'.1, h₃'.2⟩
    have hm₁ := A'.mem_border_of_term hΘ₁ hN₁ h₆
    have hm₂ := A'.mem_border_of_term hΘ₂ hN₂ h₆'
    by_cases hΘ : Θ₁ = Θ₂
    · subst hΘ
      have := H.claim_3 hΘ₁ h₁.1 h₁'.1 h₃ h₃' h₅ h₆ h₆'
      rw [h₅'] at this
      exact hne (Option.some.inj this).symm
    · exact Set.disjoint_left.mp (A'.h.border_cuffs _ hΘ₁ _ hΘ₂ hΘ _ hN₁ _ hN₂) hm₁ hm₂

end InflationHyp

end Main

end GraphMinor.GM20
