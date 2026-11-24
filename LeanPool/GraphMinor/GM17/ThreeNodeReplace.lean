/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.ReplaceDisc
public import LeanPool.GraphMinor.GM17.Section11
public import LeanPool.GraphMinor.Surface.Fan
public import LeanPool.GraphMinor.GM19.Section6Cuff
public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Replacing a disc by two cells

We prove `ThreeNodeIArcReplaceDiscPaintingStatement`, the step of the proof of (11.3) of Graph
Minors
XVII, page 193. The part of a painting inside a disc `Δ` cut off by an `I`-arc `F` with three nodes
is
replaced by an internal cell with the three nodes and a border cell. We cut `Δ` along two chords
from
`n₁` to `n₂` into three discs, and keep the outer two.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem line_inner_nonempty {P : Set S} {a b : S} (hP : IsLineWithEnds P a b) :
  (P \ {a, b}).Nonempty := by
  by_contra h
  have h3 := hP.subset_closure_diff hP.left_mem
  rw [not_nonempty_iff_eq_empty.mp h, closure_empty] at h3
  exact h3

/-- `P` without its ends is a component of the boundary without two points. -/
theorem inner_mem_comps {Y P Q : Set S} {a b : S} (hP : IsLineWithEnds P a b)
  (hQ : IsLineWithEnds Q a b)
    (hU : Y = (P ∪ Q) \ {a, b}) (hI : P ∩ Q = {a, b}) : P \ {a, b} ∈ componentsIn Y := by
  obtain ⟨x, hx⟩ := line_inner_nonempty hP
  have hsub : P \ {a, b} ⊆ Y := by
    rw [hU]
    exact fun z hz => ⟨.inl hz.1, hz.2⟩
  have hpc : IsPreconnected (P \ {a, b}) :=
    (GM11.isPathConnected_sdiff_pair hP).isConnected.isPreconnected
  refine ⟨x, hsub hx, Subset.antisymm ?_ (hpc.subset_connectedComponentIn hx hsub)⟩
  set A := connectedComponentIn Y x with hA
  have hAY : A ⊆ Y := connectedComponentIn_subset _ _
  have hxA : x ∈ A := mem_connectedComponentIn (hsub hx)
  have hcP : IsClosed P := (GM19.isClosed_of_cuffLine hP)
  have hcQ : IsClosed Q := (GM19.isClosed_of_cuffLine hQ)
  have hcov : A ⊆ P ∪ Q := fun z hz => by
    have := hAY hz
    rw [hU] at this
    exact this.1
  have hno : ¬ (A ∩ Q).Nonempty := fun hm => by
    obtain ⟨z, hzA, hz⟩ := (isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn) P Q
      hcP hcQ hcov
      ⟨x, hxA, hx.1⟩ hm
    have h3 := hAY hzA
    rw [hU] at h3
    exact h3.2 (hI ▸ hz)
  intro z hz
  have h3 := hAY hz
  rw [hU] at h3
  rcases h3.1 with h | h
  · exact ⟨h, h3.2⟩
  · exact absurd ⟨z, hz, h⟩ hno

/-- A chord cuts a disc with boundary `P ∪ Q` into a disc along `P` and a disc along `Q`. -/
theorem split_disc {D P Q : Set S} {a b : S} (hD : IsClosedDisc D) (hP : IsLineWithEnds P a b)
    (hQ : IsLineWithEnds Q a b) (hab : a ≠ b) (hU : P ∪ Q = discBd D) (hI : P ∩ Q = {a, b}) :
    ∃ L Δ₁ Δ₂, IsLineWithEnds L a b ∧ L ∩ discBd D = {a, b} ∧ L ⊆ D ∧ IsClosedDisc Δ₁
      ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ∪ Δ₂ = D ∧ Δ₁ ∩ Δ₂ = L ∧ discBd Δ₁ = P ∪ L ∧ discBd Δ₂ = Q ∪ L := by
  obtain ⟨L, hL, hLD, hLb⟩ := Surface.exists_chord hD (hU ▸ .inl hP.left_mem)
    (hU ▸ .inl hP.right_mem) hab
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hne, hc, hd₁, hd₂, hu, hi, hb₁, hb₂, -⟩ :=
    Surface.disc_iArc D L a b hD hLD hab hL hLb
  have hY : discBd D \ {a, b} = (P ∪ Q) \ {a, b} := by rw [hU]
  have hmP : P \ {a, b} ∈ componentsIn (discBd D \ {a, b}) := inner_mem_comps hP hQ hY hI
  have hmQ : Q \ {a, b} ∈ componentsIn (discBd D \ {a, b}) :=
    inner_mem_comps hQ hP (by rw [hY, union_comm]) (by rw [inter_comm, hI])
  rw [hc] at hmP hmQ
  have hdis : P \ {a, b} ≠ Q \ {a, b} := fun h => by
    obtain ⟨x, hx⟩ := line_inner_nonempty hP
    exact hx.2 (hI ▸ ⟨hx.1, (h ▸ hx : x ∈ Q \ {a, b}).1⟩)
  have hfill : ∀ {R : Set S}, IsLineWithEnds R a b → (R \ {a, b}) ∪ L = R ∪ L := fun {R} hR => by
    ext x
    constructor
    · rintro (h | h)
      · exact .inl h.1
      · exact .inr h
    · rintro (h | h)
      · by_cases hx : x ∈ ({a, b} : Set S)
        · rcases hx with rfl | rfl
          · exact .inr hL.left_mem
          · exact .inr hL.right_mem
        · exact .inl ⟨h, hx⟩
      · exact .inr h
  rcases hmP with hp | hp <;> rcases hmQ with hq | hq
  · exact absurd (hp.trans hq.symm) hdis
  · refine ⟨L, Δ₁, Δ₂, hL, hLb, hLD, hd₁, hd₂, hu, hi, ?_, ?_⟩
    · rw [hb₁, ← hp, hfill hP]
    · rw [hb₂, ← hq, hfill hQ]
  · refine ⟨L, Δ₂, Δ₁, hL, hLb, hLD, hd₂, hd₁, by rw [union_comm, hu], by rw [inter_comm, hi],
      ?_, ?_⟩
    · rw [hb₂, ← hp, hfill hP]
    · rw [hb₁, ← hq, hfill hQ]
  · exact absurd (hp.trans hq.symm) hdis

private theorem replacement_discs_intersect_at_arc_ends
    (S : Type)
    [TopologicalSpace S]
    (n₁ : S)
    (n₂ : S)
    (F : Set S)
    (I : Set S)
    (L₁ : Set S)
    (Δ₁ : Set S)
    (M : Set S)
    (hL₁ : IsLineWithEnds L₁ n₁ n₂)
    (hi₁ : Δ₁ ∩ M = L₁)
    (hb₁ : discBd Δ₁ = F ∪ L₁)
    (hbM : discBd M = I ∪ L₁)
    (L₂ : Set S)
    (Δ₂ : Set S)
    (M' : Set S)
    (hL₂ : IsLineWithEnds L₂ n₁ n₂)
    (hL₂b : L₂ ∩ discBd M = {n₁, n₂})
    (hi₂ : Δ₂ ∩ M' = L₂)
    (hb₂ : discBd Δ₂ = I ∪ L₂)
    (hsub₂ : Δ₂ ⊆ M)
    (hL₁M' : L₁ ⊆ M') :
    Δ₁ ∩ Δ₂ = {n₁, n₂} := by
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hx₁, hx₂⟩
    have hxL₁ : x ∈ L₁ := hi₁ ▸ ⟨hx₁, hsub₂ hx₂⟩
    have hxL₂ : x ∈ L₂ := hi₂ ▸ ⟨hx₂, hL₁M' hxL₁⟩
    exact hL₂b ▸ ⟨hxL₂, hbM ▸ .inr hxL₁⟩
  · rintro x (rfl | rfl)
    · exact ⟨discBd_subset _ (hb₁ ▸ .inr hL₁.left_mem), discBd_subset _ (hb₂ ▸ .inr hL₂.left_mem)⟩
    · exact ⟨discBd_subset _ (hb₁ ▸ .inr hL₁.right_mem), discBd_subset _
      (hb₂ ▸ .inr hL₂.right_mem)⟩

private theorem first_replacement_cell_closure
    (S : Type)
    [TopologicalSpace S]
    (n₁ : S)
    (n₂ : S)
    (n₃ : S)
    [T2Space S]
    (Δ₁ : Set S)
    (hd₁ : IsClosedDisc Δ₁)
    (Δ₂ : Set S)
    (hn₃Δ₁ : n₃ ∈ discBd Δ₁)
    (hn₁Δ₁ : n₁ ∈ discBd Δ₁)
    (hn₂Δ₁ : n₂ ∈ discBd Δ₁)
    (hn₃out : n₃ ∉ Δ₂) :
    closure (Δ₁ \ {n₁, n₂, n₃}) = Δ₁ := by
  let c₁ := Δ₁ \ {n₁, n₂, n₃}
  refine Subset.antisymm (closure_minimal sdiff_subset hd₁.isClosed) ?_
  refine hd₁.subset_closure_discInt.trans (closure_mono ?_)
  rintro x ⟨hx, hn⟩
  refine ⟨hx, ?_⟩
  rintro (rfl | rfl | rfl)
  · exact hn hn₁Δ₁
  · exact hn hn₂Δ₁
  · exact hn hn₃Δ₁

private theorem second_replacement_cell_closure
    (S : Type)
    [TopologicalSpace S]
    (n₁ : S)
    (n₂ : S)
    (n₃ : S)
    [T2Space S]
    (Δ₁ : Set S)
    (Δ₂ : Set S)
    (hd₂ : IsClosedDisc Δ₂)
    (hn₁Δ₂ : n₁ ∈ discBd Δ₂)
    (hn₂Δ₂ : n₂ ∈ discBd Δ₂)
    (hcl₁ : closure (Δ₁ \ {n₁, n₂, n₃}) = Δ₁) :
    closure (Δ₂ \ {n₁, n₂}) = Δ₂ := by
  let c₁ := Δ₁ \ {n₁, n₂, n₃}
  let c₂ := Δ₂ \ {n₁, n₂}
  refine Subset.antisymm (closure_minimal sdiff_subset hd₂.isClosed) ?_
  refine hd₂.subset_closure_discInt.trans (closure_mono ?_)
  rintro x ⟨hx, hn⟩
  refine ⟨hx, ?_⟩
  rintro (rfl | rfl)
  · exact hn hn₁Δ₂
  · exact hn hn₂Δ₂

private theorem first_replacement_cell_nodes
    (S : Type)
    [TopologicalSpace S]
    (n₁ : S)
    (n₂ : S)
    (n₃ : S)
    (Δ₁ : Set S)
    (Δ₂ : Set S)
    (hn₃Δ₁ : n₃ ∈ discBd Δ₁)
    (hn₁Δ₁ : n₁ ∈ discBd Δ₁)
    (hn₂Δ₁ : n₂ ∈ discBd Δ₁)
    (hcl₁ : closure (Δ₁ \ {n₁, n₂, n₃}) = Δ₁)
    (hcl₂ : closure (Δ₂ \ {n₁, n₂}) = Δ₂) :
    tilde (Δ₁ \ {n₁, n₂, n₃}) = {n₁, n₂, n₃} := by
  let c₁ := Δ₁ \ {n₁, n₂, n₃}
  let c₂ := Δ₂ \ {n₁, n₂}
  rw [tilde, hcl₁]
  ext x
  constructor
  · rintro ⟨h3, h4⟩
    exact by_contra fun h => h4 ⟨h3, h⟩
  · intro h3
    refine ⟨?_, fun h => h.2 h3⟩
    rcases h3 with rfl | rfl | rfl
    · exact discBd_subset _ hn₁Δ₁
    · exact discBd_subset _ hn₂Δ₁
    · exact discBd_subset _ hn₃Δ₁

private theorem second_replacement_cell_nodes
    (S : Type)
    [TopologicalSpace S]
    (n₁ : S)
    (n₂ : S)
    (n₃ : S)
    (Δ₁ : Set S)
    (Δ₂ : Set S)
    (hn₁Δ₂ : n₁ ∈ discBd Δ₂)
    (hn₂Δ₂ : n₂ ∈ discBd Δ₂)
    (hcl₂ : closure (Δ₂ \ {n₁, n₂}) = Δ₂)
    (ht₁ : tilde (Δ₁ \ {n₁, n₂, n₃}) = {n₁, n₂, n₃}) :
    tilde (Δ₂ \ {n₁, n₂}) = {n₁, n₂} := by
  let c₁ := Δ₁ \ {n₁, n₂, n₃}
  let c₂ := Δ₂ \ {n₁, n₂}
  rw [tilde, hcl₂]
  ext x
  constructor
  · rintro ⟨h3, h4⟩
    exact by_contra fun h => h4 ⟨h3, h⟩
  · intro h3
    refine ⟨?_, fun h => h.2 h3⟩
    rcases h3 with rfl | rfl
    · exact discBd_subset _ hn₁Δ₂
    · exact discBd_subset _ hn₂Δ₂

private theorem replacement_painting_cell_partition
    (S : Type)
    [TopologicalSpace S]
    (Γ : Painting S)
    (n₁ : S)
    (n₂ : S)
    (n₃ : S)
    (F : Set S)
    (Δ : Set S)
    (h1 : F ⊆ discBd Δ)
    (hside : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ)
    (hnF : ∀ {x : S}, x ∈ ({n₁, n₂, n₃} : Set S) → x ∈ F ∧ x ∈ Γ.N)
    (Δ₁ : Set S)
    (M : Set S)
    (hd₁ : IsClosedDisc Δ₁)
    (Δ₂ : Set S)
    (hd₂ : IsClosedDisc Δ₂)
    (hsub₁ : Δ₁ ⊆ Δ)
    (hsubM : M ⊆ Δ)
    (hsub₂ : Δ₂ ⊆ M)
    (hn₃out : n₃ ∉ Δ₂)
    (hcl₁ : closure (Δ₁ \ {n₁, n₂, n₃}) = Δ₁)
    (hcl₂ : closure (Δ₂ \ {n₁, n₂}) = Δ₂)
    (hc₁Δ : (Δ₁ \ {n₁, n₂, n₃}) ⊆ Δ)
    (hc₂Δ : (Δ₂ \ {n₁, n₂}) ⊆ Δ)
    (hne₁ : (Δ₁ \ {n₁, n₂, n₃}).Nonempty)
    (hne₂ : (Δ₂ \ {n₁, n₂}).Nonempty)
    (hdisj12 : Disjoint (Δ₁ \ {n₁, n₂, n₃}) (Δ₂ \ {n₁, n₂}))
    (hKfin : {c | c ∈ Γ.C ∧ c ⊆ Δᶜ}.Finite)
    (hN'U : ∀ x ∈ Γ.N, x ∈ closure Δᶜ → x ∈ (Γ.N \ Δ ∪ {n₁, n₂, n₃}))
    (hdisjN : ∀ x ∈ Δ, x ∈ (Γ.N \ Δ ∪ {n₁, n₂, n₃}) → x ∈ ({n₁, n₂, n₃} : Set S)) :
    arcComponentsIn ((Γ.U \ Δ ∪ Δ₁ ∪ Δ₂) \ (Γ.N \ Δ ∪ {n₁, n₂, n₃})) = (insert (Δ₁ \ {n₁, n₂, n₃})
      (insert (Δ₂ \ {n₁, n₂}) {c | c ∈ Γ.C ∧ c ⊆ Δᶜ})) := by
  let c₁ := Δ₁ \ {n₁, n₂, n₃}
  let c₂ := Δ₂ \ {n₁, n₂}
  let N' := Γ.N \ Δ ∪ {n₁, n₂, n₃}
  let J := insert c₁ (insert c₂ {c | c ∈ Γ.C ∧ c ⊆ Δᶜ})
  refine arcComponentsIn_eq_of_finite_cover ((hKfin.insert _).insert _) ?_ ?_ ?_ ?_ ?_
  · ext x
    constructor
    · rintro ⟨d, (rfl | rfl | ⟨hd, hdc⟩), hx⟩
      · exact ⟨.inl (.inr hx.1), fun h => hx.2 (hdisjN x (hc₁Δ hx) h)⟩
      · refine ⟨.inr hx.1, fun h => ?_⟩
        rcases hdisjN x (hc₂Δ hx) h with h3 | h3 | h3
        · exact hx.2 (.inl h3)
        · exact hx.2 (.inr h3)
        · exact hn₃out (h3 ▸ hx.1)
      · have hm := arcComponentsIn_subset hd hx
        refine ⟨.inl (.inl ⟨hm.1, hdc hx⟩), ?_⟩
        rintro (h | h)
        · exact hm.2 h.1
        · exact hdc hx (discBd_subset _ (h1 (hnF h).1))
    · rintro ⟨(⟨(⟨hx, hxΔ⟩ | hx)⟩ | hx), hxN⟩
      · have hxN' : x ∉ Γ.N := fun h3 => hxN (.inl ⟨h3, hxΔ⟩)
        obtain ⟨c, hc, hxc⟩ := exists_mem_arcComponentsIn (show x ∈ Γ.U \ Γ.N from ⟨hx, hxN'⟩)
        exact ⟨c, .inr (.inr ⟨hc, (hside c hc).resolve_left fun h3 => hxΔ (h3 hxc)⟩), hxc⟩
      · exact ⟨c₁, .inl rfl, hx, fun h3 => hxN (.inr h3)⟩
      · refine ⟨c₂, .inr (.inl rfl), hx, fun h3 => hxN (.inr ?_)⟩
        rcases h3 with h3 | h3
        · exact .inl h3
        · exact .inr (.inl h3)
  · rintro d (rfl | rfl | ⟨hd, -⟩)
    · exact hne₁
    · exact hne₂
    · exact arcComponentsIn_nonempty hd
  · rintro d (rfl | rfl | ⟨hd, -⟩)
    · exact isPathConnected_of_isClosedDisc_finite_diff hd₁ sdiff_subset
        (((finite_singleton _).insert _ |>.insert _).subset fun x hx => by
          by_contra h
          exact hx.2 ⟨hx.1, h⟩)
    · exact isPathConnected_of_isClosedDisc_finite_diff hd₂ sdiff_subset
        (((finite_singleton _).insert _).subset fun x hx => by
          by_contra h
          exact hx.2 ⟨hx.1, h⟩)
    · exact arcComponentsIn_isPathConnected hd
  · rintro d (rfl | rfl | ⟨hd, hdc⟩) d' (rfl | rfl | ⟨hd', hdc'⟩) hne
    · exact absurd rfl hne
    · exact hdisj12
    · exact disjoint_left.mpr fun x hx hx' => hdc' hx' (hc₁Δ hx)
    · exact hdisj12.symm
    · exact absurd rfl hne
    · exact disjoint_left.mpr fun x hx hx' => hdc' hx' (hc₂Δ hx)
    · exact disjoint_left.mpr fun x hx hx' => hdc hx (hc₁Δ hx')
    · exact disjoint_left.mpr fun x hx hx' => hdc hx (hc₂Δ hx')
    · exact arcComponentsIn_disjoint hd hd' hne
  · rintro d (rfl | rfl | ⟨hd, hdc⟩)
    · rw [hcl₁]
      ext x
      constructor
      · rintro ⟨hx, -, hxN⟩
        exact ⟨hx, fun h3 => hxN (.inr h3)⟩
      · intro hx
        exact ⟨hx.1, .inl (.inr hx.1), fun h3 => hx.2 (hdisjN x (hsub₁ hx.1) h3)⟩
    · rw [hcl₂]
      ext x
      constructor
      · rintro ⟨hx, -, hxN⟩
        refine ⟨hx, fun h3 => hxN (.inr ?_)⟩
        rcases h3 with h3 | h3
        · exact .inl h3
        · exact .inr (.inl h3)
      · intro hx
        refine ⟨hx.1, .inr hx.1, fun h3 => ?_⟩
        rcases hdisjN x (hsub₂.trans hsubM hx.1) h3 with h3 | h3 | h3
        · exact hx.2 (.inl h3)
        · exact hx.2 (.inr h3)
        · exact hn₃out (h3 ▸ hx.1)
    · ext x
      constructor
      · rintro ⟨hx, -, hxN⟩
        by_contra h
        have hxt : x ∈ tilde d := ⟨hx, h⟩
        exact hxN (hN'U x (Γ.tilde_subset_N hd hxt) (closure_mono hdc hx))
      · intro hx
        have hm := arcComponentsIn_subset hd hx
        refine ⟨subset_closure hx, .inl (.inl ⟨hm.1, hdc hx⟩), ?_⟩
        rintro (h | h)
        · exact hm.2 h.1
        · exact hdc hx (discBd_subset _ (h1 (hnF h).1))

private theorem replace_disc_in_union_eq_closed_complement
    {S : Type} [TopologicalSpace S] {U Δ A B : Set S}
    (h : ∀ x ∈ U, x ∈ closure Δᶜ → x ∈ Δ → x ∈ A) :
    (U \ Δ) ∪ A ∪ B = (U ∩ closure Δᶜ) ∪ A ∪ B := by
  apply subset_antisymm
  · exact union_subset_union_left _ (union_subset_union_left _
      (fun _ hx => ⟨hx.1, subset_closure hx.2⟩))
  · rintro x ((⟨hx, hxc⟩ | hx) | hx)
    · by_cases hΔ : x ∈ Δ
      · exact .inl (.inr (h x hx hxc hΔ))
      · exact .inl (.inl ⟨hx, hΔ⟩)
    · exact .inl (.inr hx)
    · exact .inr hx

omit [TopologicalSpace S] in
private theorem third_node_distinct_of_ncard_three {n₁ n₂ n₃ : S} (hne₁₂ : n₁ ≠ n₂)
    (hcard : ({n₁, n₂, n₃} : Set S).ncard = 3) : n₃ ≠ n₁ ∧ n₃ ≠ n₂ := by
  constructor
  · rintro rfl
    have : ({n₃, n₂, n₃} : Set S) = {n₃, n₂} := by ext; simp; tauto
    rw [this, ncard_pair hne₁₂] at hcard
    omega
  · rintro rfl
    have : ({n₁, n₃, n₃} : Set S) = {n₁, n₃} := by ext; simp
    rw [this, ncard_pair hne₁₂] at hcard
    omega

/-- **The step of the proof of (11.3) of Graph Minors XVII**, page 193. -/
theorem threeNodeIArcReplaceDisc : ThreeNodeIArcReplaceDiscPaintingStatement := by
  unfold ThreeNodeIArcReplaceDiscPaintingStatement
  intro S _ hS Γ n₁ n₂ n₃ F Δ hnorm hF hb hFN hcard hΔ h1 h2
  have ht2 : T2Space S := hS.2.1
  obtain ⟨I, I', Θ, hΘ, hI, hI', hu', hi', hu, hi, hmeet, hnb⟩ := arc_disc_data hS hF hb hΔ h1 h2
  have hne₁₂ : n₁ ≠ n₂ := hF.ne'
  have hn₃ : n₃ ≠ n₁ ∧ n₃ ≠ n₂ :=
    third_node_distinct_of_ncard_three hne₁₂ (hFN ▸ hcard)
  have hbdΔ : discBd Δ ⊆ Δ := discBd_subset Δ
  have hIΘ : I ⊆ Θ := fun z hz => hu' ▸ .inl hz
  have hΘb : Θ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hside : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ := fun c hc => cell_side hc hnorm hΔ hnb
  have hFΔ : F ⊆ closure Δᶜ := by
    have h3 : F \ {n₁, n₂} ⊆ closure Δᶜ := fun x hx => by
      refine mem_closure_compl (h1 hx.1) ?_
      by_contra hn
      exact hx.2 (hb ▸ ⟨hx.1, hn⟩)
    exact (hF.subset_closure_diff).trans (closure_minimal h3 isClosed_closure)
  have hnF : ∀ {x}, x ∈ ({n₁, n₂, n₃} : Set S) → x ∈ F ∧ x ∈ Γ.N := fun hx => hFN.symm.subset hx
  have hclosN : ∀ x ∈ Γ.U, x ∈ closure Δᶜ → x ∈ Δ → x ∈ ({n₁, n₂, n₃} : Set S) := by
    intro x hxU hxc hxΔ
    by_cases hxF : x ∈ F
    · exact hFN ▸ ⟨hxF, hnorm ⟨hxF, hxU⟩⟩
    · obtain ⟨y, hy, hy'⟩ := mem_closure_iff_nhds.mp hxc _ (hnb x ⟨hxΔ, hxF⟩)
      exact absurd hy hy'
  -- Cut `Δ` along two chords.
  obtain ⟨L₁, Δ₁, M, hL₁, hL₁b, hL₁D, hd₁, hdM, hu₁, hi₁, hb₁, hbM⟩ := split_disc hΔ hF hI hne₁₂ hu
    hi
  have hL₁I : I ∩ L₁ = {n₁, n₂} := by
    refine Subset.antisymm (fun x hx => hL₁b ▸ ⟨hx.2, hu ▸ .inr hx.1⟩) ?_
    rintro x (rfl | rfl)
    · exact ⟨hI.left_mem, hL₁.left_mem⟩
    · exact ⟨hI.right_mem, hL₁.right_mem⟩
  obtain ⟨L₂, Δ₂, M', hL₂, hL₂b, hL₂D, hd₂, hdM', hu₂, hi₂, hb₂, hbM'⟩ :=
    split_disc hdM hI hL₁ hne₁₂ hbM.symm hL₁I
  have hsub₁ : Δ₁ ⊆ Δ := hu₁ ▸ subset_union_left
  have hsubM : M ⊆ Δ := hu₁ ▸ subset_union_right
  have hsub₂ : Δ₂ ⊆ M := hu₂ ▸ subset_union_left
  have hFΔ₁ : F ⊆ discBd Δ₁ := hb₁ ▸ subset_union_left
  have hIΔ₂ : I ⊆ discBd Δ₂ := hb₂ ▸ subset_union_left
  have hL₁M' : L₁ ⊆ M' := fun x hx => discBd_subset M' (hbM' ▸ .inl hx)
  have hinter : Δ₁ ∩ Δ₂ = {n₁, n₂} := by
    exact replacement_discs_intersect_at_arc_ends S n₁ n₂ F I L₁ Δ₁ M hL₁ hi₁ hb₁ hbM L₂ Δ₂ M' hL₂
      hL₂b hi₂ hb₂ hsub₂ hL₁M'
  have hn₃Δ₁ : n₃ ∈ discBd Δ₁ := hFΔ₁ (hnF (.inr (.inr rfl))).1
  have hn₁Δ₁ : n₁ ∈ discBd Δ₁ := hFΔ₁ hF.left_mem
  have hn₂Δ₁ : n₂ ∈ discBd Δ₁ := hFΔ₁ hF.right_mem
  have hn₁Δ₂ : n₁ ∈ discBd Δ₂ := hIΔ₂ hI.left_mem
  have hn₂Δ₂ : n₂ ∈ discBd Δ₂ := hIΔ₂ hI.right_mem
  have hn₃out : n₃ ∉ Δ₂ := fun h => by
    have h3 : n₃ ∈ Δ₁ ∩ Δ₂ := ⟨discBd_subset _ hn₃Δ₁, h⟩
    rw [hinter] at h3
    rcases h3 with h3 | h3
    · exact hn₃.1 h3
    · exact hn₃.2 h3
  let c₁ : Set S := Δ₁ \ {n₁, n₂, n₃}
  let c₂ : Set S := Δ₂ \ {n₁, n₂}
  let N' : Set S := (Γ.N \ Δ) ∪ {n₁, n₂, n₃}
  have hcl₁ : closure c₁ = Δ₁ := by
    exact first_replacement_cell_closure S n₁ n₂ n₃ Δ₁ hd₁ Δ₂ hn₃Δ₁ hn₁Δ₁ hn₂Δ₁ hn₃out
  have hcl₂ : closure c₂ = Δ₂ := by
    exact second_replacement_cell_closure S n₁ n₂ n₃ Δ₁ Δ₂ hd₂ hn₁Δ₂ hn₂Δ₂ hcl₁
  have ht₁ : tilde c₁ = {n₁, n₂, n₃} := by
    exact first_replacement_cell_nodes S n₁ n₂ n₃ Δ₁ Δ₂ hn₃Δ₁ hn₁Δ₁ hn₂Δ₁ hcl₁ hcl₂
  have ht₂ : tilde c₂ = {n₁, n₂} := by
    exact second_replacement_cell_nodes S n₁ n₂ n₃ Δ₁ Δ₂ hn₁Δ₂ hn₂Δ₂ hcl₂ ht₁
  have hc₁Δ : c₁ ⊆ Δ := sdiff_subset.trans hsub₁
  have hc₂Δ : c₂ ⊆ Δ := sdiff_subset.trans (hsub₂.trans hsubM)
  have hne₁ : c₁.Nonempty := by
    obtain ⟨x, hx⟩ : (closure c₁).Nonempty := by
      rw [hcl₁]
      exact ⟨_, discBd_subset _ hn₁Δ₁⟩
    exact closure_nonempty_iff.mp ⟨x, hx⟩
  have hne₂ : c₂.Nonempty := by
    obtain ⟨x, hx⟩ : (closure c₂).Nonempty := by
      rw [hcl₂]
      exact ⟨_, discBd_subset _ hn₁Δ₂⟩
    exact closure_nonempty_iff.mp ⟨x, hx⟩
  have hdisj12 : Disjoint c₁ c₂ := disjoint_left.mpr fun x hx hx' => by
    have h3 : x ∈ Δ₁ ∩ Δ₂ := ⟨hx.1, hx'.1⟩
    rw [hinter] at h3
    exact hx'.2 h3
  have hne12 : c₁ ≠ c₂ := fun h => by
    obtain ⟨x, hx⟩ := hne₁
    exact disjoint_left.mp hdisj12 hx (h ▸ hx)
  have hKfin : {c ∈ Γ.C | c ⊆ Δᶜ}.Finite := Γ.finite_cells.subset fun c hc => hc.1
  let J : Set (Set S) := insert c₁ (insert c₂ {c ∈ Γ.C | c ⊆ Δᶜ})
  have hN'U : ∀ x ∈ Γ.N, x ∈ closure Δᶜ → x ∈ N' := fun x hx hxc => by
    by_cases h : x ∈ Δ
    · exact .inr (hclosN x (Γ.N_subset hx) hxc h)
    · exact .inl ⟨hx, h⟩
  have hdisjN : ∀ x ∈ Δ, x ∈ N' → x ∈ ({n₁, n₂, n₃} : Set S) := by
    rintro x hx (h | h)
    · exact absurd hx h.2
    · exact h
  have hJ : arcComponentsIn (((Γ.U \ Δ) ∪ Δ₁ ∪ Δ₂) \ N') = J := by
    exact replacement_painting_cell_partition S Γ n₁ n₂ n₃ F Δ h1 hside hnF Δ₁ M hd₁ Δ₂ hd₂ hsub₁
      hsubM hsub₂ hn₃out hcl₁ hcl₂ hc₁Δ hc₂Δ hne₁ hne₂ hdisj12 hKfin hN'U hdisjN
  have hIsub : Δ ∩ bd S ⊆ Δ₂ := by
    rw [hmeet]
    exact hIΔ₂.trans (discBd_subset _)
  have hU₂ : (Γ.U \ Δ) ∪ Δ₁ ∪ Δ₂ = (Γ.U ∩ closure Δᶜ) ∪ Δ₁ ∪ Δ₂ :=
    replace_disc_in_union_eq_closed_complement fun x hx hxc h => by
      apply discBd_subset Δ₁
      rcases hclosN x hx hxc h with rfl | rfl | rfl
      · exact hn₁Δ₁
      · exact hn₂Δ₁
      · exact hn₃Δ₁
  let Γ' : Painting S :=
    { U := (Γ.U \ Δ) ∪ Δ₁ ∪ Δ₂
      N := N'
      isClosed_U := by
        rw [hU₂]
        exact ((Γ.isClosed_U.inter isClosed_closure).union hd₁.isClosed).union hd₂.isClosed
      N_subset := by
        rintro x (⟨hx, h⟩ | hx)
        · exact .inl (.inl ⟨Γ.N_subset hx, h⟩)
        · refine .inl (.inr ?_)
          rcases hx with rfl | rfl | rfl
          · exact discBd_subset _ hn₁Δ₁
          · exact discBd_subset _ hn₂Δ₁
          · exact discBd_subset _ hn₃Δ₁
      finite_N := (Γ.finite_N.subset sdiff_subset).union (by simp)
      finite_cells := by
        rw [hJ]
        exact (hKfin.insert _).insert _
      cell_disc := by
        rw [hJ]
        rintro d (rfl | rfl | ⟨hd, -⟩)
        · rw [hcl₁, ht₁]
          refine ⟨hd₁, ?_, by simp, ?_⟩
          · rintro x (rfl | rfl | rfl)
            · exact hn₁Δ₁
            · exact hn₂Δ₁
            · exact hn₃Δ₁
          · have h' := ncard_pair hn₃.2.symm
            have h'' := ncard_insert_le n₁ ({n₂, n₃} : Set S)
            omega
        · rw [hcl₂, ht₂]
          refine ⟨hd₂, ?_, by simp, ?_⟩
          · rintro x (rfl | rfl)
            · exact hn₁Δ₂
            · exact hn₂Δ₂
          · rw [ncard_pair hne₁₂]
            omega
        · exact Γ.cell_disc d hd
      bd_subset := fun x hx => by
        by_cases h : x ∈ Δ
        · exact .inr (hIsub ⟨h, hx⟩)
        · exact .inl (.inl ⟨Γ.bd_subset hx, h⟩)
      border_cell := by
        rw [hJ]
        rintro d (rfl | rfl | ⟨hd, -⟩) h
        · exfalso
          obtain ⟨x, hx, hxb⟩ := h
          have h3 : x ∈ Δ₁ ∩ Δ₂ := ⟨hx.1, hIsub ⟨hc₁Δ hx, hxb⟩⟩
          rw [hinter] at h3
          rcases h3 with h3 | h3
          · exact hx.2 (.inl h3)
          · exact hx.2 (.inr (.inl h3))
        · have hcb : Δ₂ ∩ bd S = I := by
            refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
            · exact hmeet ▸ ⟨hsubM (hsub₂ hx.1), hx.2⟩
            · exact ⟨discBd_subset _ (hIΔ₂ hx), hΘb (hIΘ hx)⟩
          rw [hcl₂, ht₂, hcb, lineEnds_eq hI, ncard_pair hne₁₂]
          exact ⟨rfl, by simp, ⟨hI.choose⟩, rfl⟩
        · exact Γ.border_cell d hd h }
  have hΓC : Γ'.C = J := hJ
  have hnotK : ∀ {c : Set S}, c ⊆ Δ → c.Nonempty → c ∉ {c ∈ Γ.C | c ⊆ Δᶜ} := by
    rintro c hc ⟨x, hx⟩ ⟨-, h⟩
    exact h hx (hc hx)
  have hz₂ : (c₂ ∩ Θ).Nonempty := by
    obtain ⟨z, hz⟩ := line_inner_nonempty hI
    exact ⟨z, ⟨discBd_subset _ (hIΔ₂ hz.1), hz.2⟩, hIΘ hz.1⟩
  refine ⟨Γ', Θ, c₁, c₂, rfl, ?_, hΘ, ⟨(hnF (.inl rfl)).2, hIΘ hI.left_mem⟩,
    ⟨(hnF (.inr (.inl rfl))).2, hIΘ hI.right_mem⟩, ?_, hside, ?_, ?_, ?_, ht₁, ?_, hz₂, ht₂, hne12,
    hnotK hc₁Δ hne₁, hnotK hc₂Δ hne₂, hΓC⟩
  · rintro x (h | h)
    · exact h.1
    · exact (hnF h).2
  · rw [← hu]
    exact union_subset_union_right _ hIΘ
  · intro c hc hcΔ x hx
    exact hN'U x (Γ.tilde_subset_N hc hx) (closure_mono hcΔ hx.1)
  · rw [hΓC]
    exact .inl rfl
  · rintro ⟨x, hx, hxb⟩
    have h3 : x ∈ Δ₁ ∩ Δ₂ := ⟨hx.1, hIsub ⟨hc₁Δ hx, hxb⟩⟩
    rw [hinter] at h3
    rcases h3 with h3 | h3
    · exact hx.2 (.inl h3)
    · exact hx.2 (.inr (.inl h3))
  · rw [hΓC]
    exact .inr (.inl rfl)

end GraphMinor.GM17
