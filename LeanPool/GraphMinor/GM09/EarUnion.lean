/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.EarCompare

/-!
# The union of a closed disc with a family of ears

A finite family of ears on `Δ₀` whose discs pairwise meet only in common ends. The union of `Δ₀`
with
their discs is a closed disc. Each ear line lies in its boundary, and that boundary lies in the
boundary of `Δ₀` together with the ear lines. This is the step "It follows that the union of
$\Delta_0$
with all lawns is a closed disc" of Graph Minors IX, page 67.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

/-- A finite family of ears on `Δ₀` whose discs pairwise meet only in common ends. -/
structure EarFamily {ι : Type*} (Δ₀ : Set EuclideanPlane) (I : Set ι)
    (c L A B : ι → Set EuclideanPlane) (a b : ι → EuclideanPlane) : Prop where
  finite : I.Finite
  ear : ∀ i ∈ I, EarData Δ₀ (c i) (L i) (A i) (B i) (a i) (b i)
  inter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → L i ∩ L j ⊆ {a i, b i} ∩ {a j, b j}

namespace EarFamily

variable {ι : Type*} {Δ₀ : Set EuclideanPlane} {I : Set ι} {c L A B : ι → Set EuclideanPlane}
  {a b : ι → EuclideanPlane}

theorem mono {J : Set ι} (F : EarFamily Δ₀ I c L A B a b) (h : J ⊆ I) :
    EarFamily Δ₀ J c L A B a b :=
  ⟨F.finite.subset h, fun i hi => F.ear i (h hi), fun i hi j hj => F.inter i (h hi) j (h hj)⟩

theorem insert_step {J : Set ι} {i : ι} (F : EarFamily Δ₀ (insert i J) c L A B a b) (hi : i ∉ J)
    (hd : IsClosedDisc (Δ₀ ∪ ⋃ j ∈ J, L j)) :
    IsClosedDisc ((Δ₀ ∪ ⋃ j ∈ J, L j) ∪ L i) ∧
      discBd ((Δ₀ ∪ ⋃ j ∈ J, L j) ∪ L i) ⊆ discBd (Δ₀ ∪ ⋃ j ∈ J, L j) ∪ c i := by
  have E := F.ear i (mem_insert i J)
  have hJ : J.Finite := F.finite.subset (subset_insert i J)
  have hYc : IsClosed (⋃ j ∈ J, L j) :=
    hJ.isClosed_biUnion fun j hj => (F.ear j (mem_insert_of_mem i hj)).disc.isCompact.isClosed
  have hne : ∀ j ∈ J, i ≠ j := fun j hj h => hi (h ▸ hj)
  have hends : ∀ {x}, x ∈ L i → x ∈ ⋃ j ∈ J, L j → x ∈ ({a i, b i} : Set EuclideanPlane) := by
    intro x hx hxY
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxY
    exact (F.inter i (mem_insert i J) j (mem_insert_of_mem i hj) (hne j hj) ⟨hx, hxj⟩).1
  have hpq : ({a i, b i} : Set EuclideanPlane) ⊆ A i := by
    rintro x (rfl | rfl)
    · exact E.lineA.left_mem
    · exact E.lineA.right_mem
  have hAL : A i ⊆ L i := E.A_subset_L
  have hinter : (Δ₀ ∪ ⋃ j ∈ J, L j) ∩ L i = A i := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxL⟩
      · exact E.L_inter ▸ ⟨hxL, hx⟩
      · exact hpq (hends hxL hx)
    · intro hx
      exact ⟨Or.inl (Surface.discBd_subset _ (E.A_subset hx)), hAL hx⟩
  have hopen : A i \ {a i, b i} ⊆ discBd (Δ₀ ∪ ⋃ j ∈ J, L j) := by
    rintro x ⟨hx, hn⟩
    by_contra hb
    have hxΔ : x ∈ Δ₀ := Surface.discBd_subset _ (E.A_subset hx)
    have hxi : x ∈ interior (Δ₀ ∪ ⋃ j ∈ J, L j) := by
      rw [interior_eq_discInt_plane hd]
      exact ⟨Or.inl hxΔ, hb⟩
    have hxY : x ∉ ⋃ j ∈ J, L j := fun h => hn (hends (hAL hx) h)
    have hxi₀ : x ∈ interior Δ₀ := by
      refine mem_interior.mpr ⟨interior (Δ₀ ∪ ⋃ j ∈ J, L j) ∩ (⋃ j ∈ J, L j)ᶜ, ?_,
        isOpen_interior.inter hYc.isOpen_compl, hxi, hxY⟩
      rintro y ⟨hy, hyn⟩
      exact (interior_subset hy).resolve_right hyn
    rw [interior_eq_discInt_plane E.disc₀] at hxi₀
    exact hxi₀.2 (E.A_subset hx)
  have hsub : A i ⊆ discBd (Δ₀ ∪ ⋃ j ∈ J, L j) := by
    have hcl : IsClosed (discBd (Δ₀ ∪ ⋃ j ∈ J, L j)) := hd.isOArc_discBd.isCompact.isClosed
    exact (E.lineA.subset_closure_diff).trans (closure_minimal hopen hcl)
  obtain ⟨h₁, h₂⟩ := disc_union.{0} _ _ _ _ _ hd E.disc E.lineA hinter hsub
    (fun x hx => E.bdL ▸ Or.inl hx)
  refine ⟨h₁, ?_⟩
  rw [h₂]
  rintro x ⟨hx | hx, hn⟩
  · exact Or.inl hx
  · rw [E.bdL] at hx
    rcases hx with hx | hx
    · exact Or.inl (hsub hx)
    · exact Or.inr hx

/-- The union of `Δ₀` with the discs of a family of ears is a closed disc, and its boundary lies in
the boundary of `Δ₀` together with the ear lines. -/
theorem isClosedDisc_union (F : EarFamily Δ₀ I c L A B a b) (h₀ : IsClosedDisc Δ₀) :
    IsClosedDisc (Δ₀ ∪ ⋃ i ∈ I, L i) ∧
      discBd (Δ₀ ∪ ⋃ i ∈ I, L i) ⊆ discBd Δ₀ ∪ ⋃ i ∈ I, c i := by
  classical
  have key : ∀ J : Set ι, J.Finite → J ⊆ I → IsClosedDisc (Δ₀ ∪ ⋃ i ∈ J, L i) ∧
      discBd (Δ₀ ∪ ⋃ i ∈ J, L i) ⊆ discBd Δ₀ ∪ ⋃ i ∈ J, c i := by
    intro J hJ
    induction J, hJ using Set.Finite.induction_on with
    | empty =>
      intro _
      simp [h₀]
    | @insert i J hi _ ih =>
      intro hs
      obtain ⟨hd, hb⟩ := ih ((subset_insert i J).trans hs)
      have heq : (Δ₀ ∪ ⋃ j ∈ insert i J, L j) = (Δ₀ ∪ ⋃ j ∈ J, L j) ∪ L i := by
        rw [biUnion_insert]
        ext x
        simp only [mem_union]
        tauto
      obtain ⟨h₁, h₂⟩ := (F.mono hs).insert_step hi hd
      rw [heq]
      refine ⟨h₁, h₂.trans ?_⟩
      rw [biUnion_insert]
      rintro x (hx | hx)
      · rcases hb hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl hx)
  exact key I F.finite Subset.rfl

theorem L_subset_union {i : ι} (hi : i ∈ I) : L i ⊆ Δ₀ ∪ ⋃ j ∈ I, L j :=
  fun _ hx => Or.inr (mem_iUnion₂.mpr ⟨i, hi, hx⟩)

/-- The other discs together with `Δ₀` form a closed set. -/
theorem isClosed_others (F : EarFamily Δ₀ I c L A B a b) (h₀ : IsClosedDisc Δ₀) (i : ι) :
    IsClosed (Δ₀ ∪ ⋃ j ∈ I \ {i}, L j) :=
  h₀.isCompact.isClosed.union ((F.finite.subset sdiff_subset).isClosed_biUnion fun _ hj =>
    (F.ear _ hj.1).disc.isCompact.isClosed)

/-- A point of the open part of an ear line lies in no other disc and not in `Δ₀`. -/
theorem not_mem_others (F : EarFamily Δ₀ I c L A B a b) {i : ι} (hi : i ∈ I) {x : EuclideanPlane}
    (hx : x ∈ c i \ {a i, b i}) : x ∉ Δ₀ ∪ ⋃ j ∈ I \ {i}, L j := by
  have E := F.ear i hi
  rintro (h | h)
  · exact disjoint_left.mp E.disjoint_open hx h
  · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp h
    have hne : i ≠ j := fun h' => hj.2 h'.symm
    exact hx.2 (F.inter i hi j hj.1 hne ⟨E.c_subset_L hx.1, hxj⟩).1

/-- Near a point away from `Δ₀` and the other discs, the union of all discs is the disc `L i`. -/
theorem exists_nhds_subset (F : EarFamily Δ₀ I c L A B a b) (h₀ : IsClosedDisc Δ₀) {i : ι}
    (_hi : i ∈ I) {x : EuclideanPlane} (hx : x ∉ Δ₀ ∪ ⋃ j ∈ I \ {i}, L j) :
    ∃ N : Set EuclideanPlane, IsOpen N ∧ x ∈ N ∧ N ∩ (Δ₀ ∪ ⋃ j ∈ I, L j) ⊆ L i := by
  refine ⟨(Δ₀ ∪ ⋃ j ∈ I \ {i}, L j)ᶜ, (F.isClosed_others h₀ i).isOpen_compl, hx, ?_⟩
  rintro y ⟨hy, hy' | hy'⟩
  · exact (hy (Or.inl hy')).elim
  · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy'
    by_cases hij : j = i
    · exact hij ▸ hyj
    · exact (hy (Or.inr (mem_iUnion₂.mpr ⟨j, ⟨hj, hij⟩, hyj⟩))).elim

/-- Each ear line lies in the boundary of the union. -/
theorem c_subset_discBd (F : EarFamily Δ₀ I c L A B a b) (h₀ : IsClosedDisc Δ₀) {i : ι}
    (hi : i ∈ I) : c i ⊆ discBd (Δ₀ ∪ ⋃ j ∈ I, L j) := by
  have E := F.ear i hi
  obtain ⟨hd, -⟩ := F.isClosedDisc_union h₀
  have hopen : c i \ {a i, b i} ⊆ discBd (Δ₀ ∪ ⋃ j ∈ I, L j) := by
    intro x hx
    by_contra hb
    obtain ⟨N, hN, hxN, hs⟩ := F.exists_nhds_subset h₀ hi (F.not_mem_others hi hx)
    have hxW : x ∈ Δ₀ ∪ ⋃ j ∈ I, L j := L_subset_union hi (E.c_subset_L hx.1)
    have hxi : x ∈ interior (Δ₀ ∪ ⋃ j ∈ I, L j) := by
      rw [interior_eq_discInt_plane hd]
      exact ⟨hxW, hb⟩
    have hxL : x ∈ interior (L i) := mem_interior.mpr
      ⟨N ∩ interior (Δ₀ ∪ ⋃ j ∈ I, L j), fun y hy => hs ⟨hy.1, interior_subset hy.2⟩,
        hN.inter isOpen_interior, hxN, hxi⟩
    rw [interior_eq_discInt_plane E.disc] at hxL
    exact hxL.2 (E.bdL ▸ Or.inr hx.1)
  exact E.line.subset_closure_diff.trans
    (closure_minimal hopen hd.isOArc_discBd.isCompact.isClosed)

/-- A point of a disc on the boundary of the union lies on the ear line. -/
theorem L_inter_discBd_subset (F : EarFamily Δ₀ I c L A B a b) (h₀ : IsClosedDisc Δ₀) {i : ι}
    (hi : i ∈ I) : L i ∩ discBd (Δ₀ ∪ ⋃ j ∈ I, L j) ⊆ c i := by
  have E := F.ear i hi
  obtain ⟨hd, -⟩ := F.isClosedDisc_union h₀
  have hnoint : ∀ {x}, x ∈ discBd (Δ₀ ∪ ⋃ j ∈ I, L j) →
      x ∉ interior (Δ₀ ∪ ⋃ j ∈ I, L j) := by
    intro x hx hxi
    rw [interior_eq_discInt_plane hd] at hxi
    exact hxi.2 hx
  have hsW : Δ₀ ∪ L i ⊆ Δ₀ ∪ ⋃ j ∈ I, L j :=
    union_subset subset_union_left (L_subset_union hi)
  rintro x ⟨hxL, hxb⟩
  by_contra hxc
  have hbL : x ∈ discBd (L i) := by
    by_contra hn
    have : x ∈ interior (L i) := by
      rw [interior_eq_discInt_plane E.disc]
      exact ⟨hxL, hn⟩
    exact hnoint hxb (interior_mono (subset_union_right.trans hsW) this)
  rw [E.bdL] at hbL
  have hxA : x ∈ A i := hbL.resolve_right hxc
  have hxB : x ∉ B i := by
    intro h
    have hm : x ∈ A i ∩ B i := ⟨hxA, h⟩
    rw [E.inter] at hm
    rcases hm with rfl | rfl
    · exact hxc E.left_mem_c
    · exact hxc E.right_mem_c
  have hint : x ∈ interior (Δ₀ ∪ L i) := by
    rw [interior_eq_discInt_plane E.discW]
    refine ⟨Or.inr hxL, ?_⟩
    rw [E.bdW]
    rintro (h | h)
    · exact hxB h
    · exact hxc h
  exact hnoint hxb (interior_mono hsW hint)

end EarFamily

end GraphMinor.GM09
