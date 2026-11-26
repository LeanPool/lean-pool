/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13zc
public import LeanPool.GraphMinor.GM06.DualExists

/-!
# Graph Minors XIX, Section 13: the division is feasible

We apply VI (3.6) to the part of `sk(Γ)` in the disc bounded by a bigon.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {r u : Shat} {B : Bool → GraphWalk D.rad.G.toGraph r u} {Δ : Set
  Shat} {Sk : Drawing Shat} {G : Drawing Δ}

/-- The member of the division at position `2j + 1`. -/
noncomputable def block (B : Bool → GraphWalk D.rad.G.toGraph r u) (Δ : Set Shat) (j : ℕ) : Set Δ :=
  Subtype.val ⁻¹' (range fun i ↦ GraphWalk.vertexAt (B i) (2 * j + 1))

/-- The division of the boundary of the sector: one member for each position of `Γ` on the bigon. -/
noncomputable def blocks (B : Bool → GraphWalk D.rad.G.toGraph r u) (Δ : Set Shat) : Set (Set Δ) :=
  block B Δ '' {j | 2 * j + 1 ≤ (B false).length}

/-- The bigon and the disc it bounds. -/
structure IsBigonDisc (D : TangleDatum cap χ) (B : Bool → GraphWalk D.rad.G.toGraph r u)
  (Δ : Set Shat) (Sk : Drawing Shat) (G : Drawing Δ) : Prop where
  bigon : D.IsBigon B
  sk : D.IsSkPart Δ Sk G
  disc : IsClosedDisc Δ
  bd_eq : discBd Δ = ⋃ i, (walkDrawing D.rad.G (B i)).U

variable (h : D.IsBigonDisc B Δ Sk G)
include h

omit [T2Space S] in
theorem IsBigonDisc.vertex_mem {i : Bool} {p : ℕ} (hp : p ≤ (B false).length) : GraphWalk.vertexAt
  (B i) p ∈ discBd Δ := by
  rw [h.bd_eq]
  have hpi : p ≤ (B i).length := by rw [h.bigon.len i false]; exact hp
  exact mem_iUnion.mpr ⟨i, (mem_walkDrawing_U _ _).mpr (.inl (GraphWalk.vertexAt_mem _ hpi))⟩

theorem IsBigonDisc.exists_place {x : Δ} (hx : x ∈ bd Δ) :
    ∃ q a i, D.IsPlaced (B i) x.1 q ∧ D.IsCenteredOn x.1 (GraphWalk.vertexAt (B i) q) a ∧ (a
      = 0 ↔ Odd q) := by
  have hx' : x.1 ∈ discBd Δ := ⟨x, hx, rfl⟩
  rw [h.bd_eq] at hx'
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
  obtain ⟨q, a, h₁, h₂, h₃⟩ := h.bigon.exists_place i hi
  exact ⟨q, a, i, h₁, h₂, h₃⟩

omit [T2Space S] in
/-- Points on one side of a block are not separated by the block. -/
theorem IsBigonDisc.not_crosses {j : ℕ} (hj : 2 * j + 1 ≤ (B false).length) {s t b d : Δ}
  (hs : s ∈ block B Δ j) (ht : t ∈ block B Δ j) {i i' : Bool} {q q' : ℕ} (hb : D.IsPlaced
    (B i) b.1 q)
    (hd : D.IsPlaced (B i') d.1 q') (hside : (q < 2 * j + 1 ∧ q' < 2 * j + 1) ∨ (2 * j + 1 < q
      ∧ 2 * j + 1 < q')) : ¬ CrossesOn (bd Δ) s t b d := by
  obtain ⟨X, Y, hX, hY, hoff, hsub, hpl⟩ := h.bigon.exists_parts (p := 2 * j + 1) (by omega) hj
  have hsub' : ∀ Z : Set Shat, Z ⊆ X ∪ Y → Z ⊆ Subtype.val '' bd Δ := fun Z hZ ↦ by
    change Z ⊆ discBd Δ
    rw [h.bd_eq]
    exact hZ.trans hsub
  obtain ⟨is, hs'⟩ := hs
  obtain ⟨it, ht'⟩ := ht
  simp only at hs' ht'
  rcases hside with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact not_crossesOn_of_part hX (hsub' X subset_union_left) (hs' ▸ (hoff is).1) (ht' ▸
      (hoff it).1) ((hpl _ _ _ hb).1 h₁) ((hpl _ _ _ hd).1 h₂)
  · exact not_crossesOn_of_part hY (hsub' Y subset_union_right) (hs' ▸ (hoff is).2) (ht' ▸
      (hoff it).2) ((hpl _ _ _ hb).2 h₁) ((hpl _ _ _ hd).2 h₂)

omit [T2Space S] in
theorem IsBigonDisc.notMem_block {j : ℕ} (hj : 2 * j + 1 ≤ (B false).length) {b : Δ} {i : Bool} {q
  : ℕ} (hb : D.IsPlaced (B i) b.1 q) (hq : q ≠ 2 * j + 1) : b ∉ block B Δ j := by
  obtain ⟨X, Y, -, -, hoff, -, hpl⟩ := h.bigon.exists_parts (p := 2 * j + 1) (by omega) hj
  rintro ⟨i', hi'⟩
  simp only at hi'
  rcases lt_or_gt_of_ne hq with hlt | hlt
  · exact (hoff i').1 (hi' ▸ (hpl _ _ _ hb).1 hlt)
  · exact (hoff i').2 (hi' ▸ (hpl _ _ _ hb).2 hlt)

omit [T2Space S] in
theorem IsBigonDisc.isDivision : IsDivision (blocks B Δ) := by
  refine ⟨((Set.finite_Iio ((B false).length + 1)).subset fun j hj ↦ ?_).image _, ?_, ?_⟩
  · change 2 * j + 1 ≤ _ at hj
    change j < _
    omega
  · rintro _ ⟨j, hj, rfl⟩
    have hm := Surface.discBd_subset _ (h.vertex_mem (i := false) hj)
    exact ⟨⟨_, hm⟩, false, rfl⟩
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩ hne
    refine disjoint_left.mpr ?_
    rintro x ⟨i, hi⟩ ⟨i', hi'⟩
    simp only at hi hi'
    have hjk : 2 * j + 1 = 2 * k + 1 := h.bigon.position_unique (i := i) (i' := i')
      (by rw [h.bigon.len i false]; exact hj) (by rw [h.bigon.len i' false]; exact hk)
      (hi.trans hi'.symm)
    have : j = k := by omega
    subst this
    exact hne rfl

theorem IsBigonDisc.union_eq : divisionUnion (blocks B Δ) = G.V ∩ bd Δ := by
  ext x
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, i, hi⟩
    simp only at hi
    have hpi : 2 * j + 1 ≤ (B i).length := by rw [h.bigon.len i false]; exact hj
    refine ⟨(h.sk.mem_V x).mpr (hi ▸ (h.bigon.hatV_iff i hpi).mpr ⟨j, rfl⟩), ?_⟩
    obtain ⟨z, hz, e⟩ := h.vertex_mem (i := i) (p := 2 * j + 1) hj
    have : z = x := Subtype.ext (e.trans hi)
    exact this ▸ hz
  · rintro ⟨hxV, hxb⟩
    have hx := (h.sk.mem_V x).mp hxV
    have hx' : x.1 ∈ discBd Δ := ⟨x, hxb, rfl⟩
    rw [h.bd_eq] at hx'
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    have hG : x.1 ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hx
    obtain ⟨q, hq, e⟩ := GraphWalk.exists_vertexAt _ (support_of_mem_U _ hi hG)
    obtain ⟨j, rfl⟩ := (h.bigon.hatV_iff i hq).mp (e ▸ hx)
    refine ⟨_, ⟨j, ?_, rfl⟩, i, e.symm⟩
    change 2 * j + 1 ≤ _
    rw [← h.bigon.len i false]
    exact hq

omit [T2Space S] in
theorem IsBigonDisc.isCrossFree : IsCrossFree (bd Δ) (blocks B Δ) := by
  rintro ⟨_, ⟨j, hj, rfl⟩, _, ⟨k, hk, rfl⟩, hne, s, hs, t, ht, s', ⟨i, hi⟩, t', ⟨i', hi'⟩, hc⟩
  simp only at hi hi'
  have hk' : ∀ i, 2 * k + 1 ≤ (B i).length := fun i ↦ by rw [h.bigon.len i false]; exact hk
  have hjk : j ≠ k := fun e ↦ hne (by rw [e])
  have p₁ : D.IsPlaced (B i) s'.1 (2 * k + 1) := hi ▸ isPlaced_vertexAt D _ (hk' i)
  have p₂ : D.IsPlaced (B i') t'.1 (2 * k + 1) := hi' ▸ isPlaced_vertexAt D _ (hk' i')
  exact h.not_crosses hj hs ht p₁ p₂ (by omega) hc

omit [T2Space S] in
/-- The blocks that count for `x, y` lie between their places. -/
theorem IsBigonDisc.count_le {x y : Δ} {i i' : Bool} {q q' : ℕ} (hx : D.IsPlaced (B i) x.1 q)
  (hy : D.IsPlaced (B i') y.1 q') :
    divisionCount (bd Δ) (blocks B Δ) x y + min q q' / 2 ≤ (max q q' + 1) / 2 := by
  classical
  set m := min q q' with hm
  set M := max q q' with hM
  have hsub : {δ ∈ blocks B Δ | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn
    (bd Δ) u v x y} ⊆ block B Δ '' (↑(Finset.Ico (m / 2) ((M + 1) / 2)) : Set ℕ) := by
    rintro _ ⟨⟨j, hj, rfl⟩, hc⟩
    refine ⟨j, ?_, rfl⟩
    have hj' : 2 * j + 1 ≤ (B false).length := hj
    simp only [Finset.coe_Ico, mem_Ico]
    by_contra hn
    have hside : (q < 2 * j + 1 ∧ q' < 2 * j + 1) ∨ (2 * j + 1 < q ∧ 2 * j + 1 < q') := by omega
    rcases hc with ⟨z, hz, hz' | hz'⟩ | ⟨s, hs, t, ht, hcr⟩
    · subst hz'
      exact h.notMem_block hj' hx (by omega) hz
    · rw [mem_singleton_iff] at hz'
      subst hz'
      exact h.notMem_block hj' hy (by omega) hz
    · exact h.not_crosses hj' hs ht hx hy hside hcr
  have h₁ := Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
  have h₂ := Set.ncard_image_le (f := block B Δ) (Finset.finite_toSet (Finset.Ico (m / 2)
    ((M + 1) / 2)))
  rw [Set.ncard_coe_finset, Nat.card_Ico] at h₂
  have hle : m ≤ M := by omega
  have : divisionCount (bd Δ) (blocks B Δ) x y ≤ (M + 1) / 2 - m / 2 := h₁.trans h₂
  omega

/-- The chain condition of VI (3.6). -/
theorem IsBigonDisc.chain_bound {x y : Δ} (hx : x ∈ bd Δ) (hy : y ∈ bd Δ) {A : List (ChainTerm Δ)}
  (hA : IsXYChain G x y A) : 0 ≤ chainRedundancy G (blocks B Δ) x y A := by
  obtain ⟨q, a, i, p₁, c₁, o₁⟩ := h.exists_place hx
  obtain ⟨q', b, i', p₂, c₂, o₂⟩ := h.exists_place hy
  obtain ⟨K, hK⟩ := h.sk.chain_walk c₁ c₂ hA
  have hcount := h.count_le p₁ p₂
  have hfar : max q q' - min q q' ≤ K.length := by
    rcases le_total q q' with hle | hle
    · have := h.bigon.far i i' q q' hle p₂.1 K
      rw [max_eq_right hle, min_eq_left hle]
      exact this
    · have := h.bigon.far i' i q' q hle p₁.1 K.reverse
      rw [GraphWalk.length_reverse] at this
      rw [max_eq_left hle, min_eq_right hle]
      exact this
  have ha : a = 0 ∨ a = 1 := by rcases c₁ with h₁ | h₁; exacts [.inl h₁.1, .inr h₁.1]
  have hb : b = 0 ∨ b = 1 := by rcases c₂ with h₁ | h₁; exacts [.inl h₁.1, .inr h₁.1]
  rw [Nat.odd_iff] at o₁ o₂
  unfold chainRedundancy
  have : divisionCount (bd Δ) (blocks B Δ) x y ≤ chainLength A := by
    rcases le_total q q' with hle | hle
    · rw [max_eq_right hle, min_eq_left hle] at hcount hfar
      omega
    · rw [max_eq_left hle, min_eq_right hle] at hcount hfar
      omega
  omega

/-- The division is feasible in the part of `sk(Γ)` in the disc, by VI (3.6). -/
theorem IsBigonDisc.isFeasible : IsFeasible G.toGraph (blocks B Δ) := by
  obtain ⟨U, hU⟩ := exists_isDualPointSet (bd Δ) (divisionUnion (blocks B Δ))
  have hUb : ∀ x ∈ U ∪ divisionUnion (blocks B Δ), x ∈ bd Δ := by
    have hne : (divisionUnion (blocks B Δ)).Nonempty := by
      have h₁ : (B false).length ≠ 0 := fun e ↦ h.bigon.ne (by
        have := GraphWalk.vertexAt_length (B false) h.bigon.u_mem
        rw [e, GraphWalk.vertexAt_zero] at this
        exact this)
      have hm := Surface.discBd_subset _ (h.vertex_mem (i := false) (p := 2 * 0 + 1) (by omega))
      exact ⟨⟨_, hm⟩, _, ⟨0, by change 2 * 0 + 1 ≤ _; omega, rfl⟩, false, rfl⟩
    rintro x (hx | hx)
    · exact ((hU.2 hne).1 hx).1
    · rw [h.union_eq] at hx
      exact hx.2
  refine (GraphMinor.GM06.theorem_3_6_proof G (blocks B Δ) U h.disc h.sk.proper h.isDivision
    h.union_eq hU).mpr ⟨h.isCrossFree, fun x hx y hy A hA ↦ h.chain_bound (hUb x hx) (hUb y hy) hA⟩

end TangleDatum

end GraphMinor.GM19
