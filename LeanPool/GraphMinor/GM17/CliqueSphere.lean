/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CliquePaint
import LeanPool.GraphMinor.GM07.GoodEdge
import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# Four discs around four nodes form a sphere

In the proof of (12.2) of Graph Minors XVII (page 198), four circuits of length 3 on four nodes
bound discs `Δ(C)`, `Δ(C₁)`, `Δ(C₂)`, `Δ(C₃)`, none of the last three including `Δ(C)`. The paper
says that their union "is a sphere, and hence equals `Σ`". We prove this (`four_discs_cover`).

The union is closed. We show that it is a neighbourhood of each of its points other than the four
nodes. A point inside one of the discs is inside the union. A point `x` of a chord, other than its
ends, lies on the boundaries of exactly two of the discs, and near `x` the chord has two sides.
Each of the two discs takes one side, and they take different sides, since no two of the discs
share a point inside. So near `x` the two discs cover everything. Hence the union is open in the
connected set of interior points of `Σ` other than the four nodes, so it contains that set, and
taking closures, it is all of `Σ`. Finally each cell is connected and misses the chords, so it
lies in one of the discs.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S] [T2Space S] {Γ : Painting S}

/-- Which of six chords lie on which of four circuits. With the chords `ab, bc, ca, da, db, dc`
the circuits are `abc`, `dbc`, `adc`, `abd`. -/
def circuitChords : Fin 4 → Finset (Fin 6) := ![{0, 1, 2}, {4, 1, 5}, {3, 5, 2}, {0, 4, 3}]

/-- **The four discs are all of `Σ`, so every cell lies in one of them** (Graph Minors XVII,
(12.2), claim (1), page 198). Here `e i` are the six chords, with ends `P i`, and `D k` are the
four discs, bounded by the chords `circuitChords k`. The discs `D 1, D 2, D 3` miss the inside of
`D 0`. Each chord that is not on the boundary of `D 0` or of `D k` has an end on the boundary of
`D 0` that is not on the boundary of `D k`. -/
theorem four_discs_cover [ConnectedSpace S] (hS : IsSurface S) (e P : Fin 6 → Set S)
    (hP : ∀ i, P i ⊆ Γ.N) (hPe : ∀ i, P i ⊆ e i) (hpre : ∀ i, IsPreconnected (e i \ P i))
    (hecl : ∀ i, e i ⊆ closure (e i \ P i)) (hne : ∀ i, (e i \ P i).Nonempty)
    (hreg : ∀ i, ∃ r ∈ Γ.regions, e i \ P i ⊆ r)
    (hside : ∀ i, ∀ x ∈ e i \ P i, IsChordSide (e i) (range e) x)
    (hdj : ∀ i j, i ≠ j → Disjoint (e i \ P i) (e j))
    (D : Fin 4 → Set S) (hD : ∀ k, IsClosedDisc (D k))
    (hb : ∀ k, discBd (D k) = ⋃ i ∈ circuitChords k, e i)
    (hfree : ∀ k, k ≠ 0 → Disjoint (discInt (D 0)) (D k))
    (hnode : ∀ k i, k ≠ 0 → i ∉ circuitChords 0 → i ∉ circuitChords k →
      ∃ z ∈ e i, z ∈ discBd (D 0) ∧ z ∉ discBd (D k)) :
    ∀ c ∈ Γ.C, ∃ k, c ⊆ D k := by
  have hman := hS.2.2
  let U : Set S := ⋃ k, D k
  have hUc : IsClosed U := isClosed_iUnion_of_finite fun k => (hD k).isClosed
  have hcc2 : ∀ i : Fin 6, ∃ k l, k ≠ l ∧ i ∈ circuitChords k ∧ i ∈ circuitChords l := by decide
  have hcc0 : ∀ i : Fin 6, ∃ k, k ≠ 0 ∧ i ∈ circuitChords k := by decide
  have hccD0 : ∀ k : Fin 4, k ≠ 0 → ∃ j, j ∈ circuitChords k ∧ j ∈ circuitChords 0 := by decide
  have hccD0' : ∀ (k l : Fin 4) (j : Fin 6), k ≠ 0 → l ≠ 0 → k ≠ l → j ∈ circuitChords k →
      j ∈ circuitChords 0 → j ∉ circuitChords l := by decide
  have hebd : ∀ k i, i ∈ circuitChords k → e i ⊆ discBd (D k) := fun k i hi => by
    rw [hb k]
    exact subset_biUnion_of_mem (u := e) (Finset.mem_coe.2 hi)
  have hoffbd : ∀ k i, i ∉ circuitChords k → Disjoint (e i \ P i) (discBd (D k)) := fun k i hi => by
    rw [hb k]
    refine disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx'
    exact disjoint_left.mp (hdj i j fun h => hi (h ▸ hj)) hx hxj
  have hdisjW : ∀ {A : Set S}, (∀ i, Disjoint A (e i)) → ∀ k, Disjoint A (discBd (D k)) :=
    fun {A} hA k => by
      rw [hb k]
      exact disjoint_left.mpr fun x hx hxb => by
        obtain ⟨i, -, h2⟩ := mem_iUnion₂.1 hxb
        exact disjoint_left.mp (hA i) hx h2
  have hopen : ∀ k, IsOpen (discInt (D k)) := fun k => (hD k).isOpen_discInt hman
  have hcl0 : ∀ k, k ≠ 0 → Disjoint (discInt (D k)) (D 0) := fun k hk => by
    have h1 : Disjoint (discInt (D k)) (discInt (D 0)) :=
      disjoint_left.mpr fun x hx hx0 => disjoint_left.mp (hfree k hk) hx0 hx.1
    exact (h1.closure_right (hopen k)).mono_right (hD 0).subset_closure_discInt
  -- No chord meets the inside of a disc.
  have hoff : ∀ k i, Disjoint (discInt (D k)) (e i) := by
    intro k i
    by_cases hk : k = 0
    · subst hk
      obtain ⟨l, hl, hil⟩ := hcc0 i
      exact disjoint_left.mpr fun x hx hxe =>
        disjoint_left.mp (hfree l hl) hx (discBd_subset _ (hebd l i hil hxe))
    by_cases hi0 : i ∈ circuitChords 0
    · exact (hcl0 k hk).mono_right ((hebd 0 i hi0).trans (discBd_subset _))
    by_cases hik : i ∈ circuitChords k
    · exact disjoint_left.mpr fun x hx hxe => hx.2 (hebd k i hik hxe)
    rcases disc_dichotomy hman (hD k) (hpre i) (hoffbd k i hik) with h1 | h1
    · exfalso
      obtain ⟨z, hze, hz0, hzk⟩ := hnode k i hk hi0 hik
      have hzD : z ∈ D k := closure_minimal h1 (hD k).isClosed (hecl i hze)
      exact disjoint_left.mp (hcl0 k hk) ⟨hzD, hzk⟩ (discBd_subset _ hz0)
    · have h2 : Disjoint (discInt (D k)) (e i \ P i) := h1.symm.mono_left fun x hx => hx.1
      exact (h2.closure_right (hopen k)).mono_right (hecl i)
  -- Two of the discs cannot lie on the same side of a chord.
  have hside2 : ∀ A : Set S, A.Nonempty → (∀ i, Disjoint A (e i)) → ∀ k l, k ≠ l →
      A ⊆ D k → A ⊆ D l → False := by
    intro A hA hAe k l hkl hk hl
    have hAint : ∀ m, A ⊆ D m → A ⊆ discInt (D m) := fun m hm x hx =>
      ⟨hm hx, disjoint_left.mp (hdisjW hAe m) hx⟩
    obtain ⟨x, hx⟩ := hA
    by_cases hk0 : k = 0
    · subst hk0
      exact disjoint_left.mp (hfree l (Ne.symm hkl)) (hAint 0 hk hx) (hl hx)
    by_cases hl0 : l = 0
    · subst hl0
      exact disjoint_left.mp (hfree k hkl) (hAint 0 hl hx) (hk hx)
    have hbdk : Disjoint (discInt (D k)) (discBd (D l)) :=
      (hdisjW (A := discInt (D k)) (hoff k) l)
    rcases disc_dichotomy hman (hD l) (hD k).isPreconnected_discInt hbdk with h1 | h1
    · have hkl' : D k ⊆ D l :=
        (hD k).subset_closure_discInt.trans (closure_minimal h1 (hD l).isClosed)
      obtain ⟨j, hjk, hj0⟩ := hccD0 k hk0
      obtain ⟨y, hy⟩ := hne j
      have hyl : y ∈ D l := hkl' (discBd_subset _ (hebd k j hjk hy.1))
      have hyb : y ∈ discBd (D l) := by
        by_contra hn
        exact disjoint_left.mp (hoff l j) ⟨hyl, hn⟩ hy.1
      exact disjoint_left.mp (hoffbd l j (hccD0' k l j hk0 hl0 hkl hjk hj0)) hy hyb
    · exact disjoint_left.mp h1 (hAint k hk hx) (hl hx)
  -- Near a point of a chord other than its ends, the union covers everything.
  have hchordint : ∀ i, ∀ x ∈ e i \ P i, x ∈ interior U := by
    intro i x hx
    obtain ⟨r, hr, hsub⟩ := hreg i
    have hint : IsInteriorPoint x := by
      by_contra hn
      exact (arcComponentsIn_subset hr (hsub hx)).2 (Γ.bd_subset hn)
    obtain ⟨V, A, B, hV, hxV, hVs, hA, hB, hclA, hoffAB⟩ := hside i x hx
    have hAe : ∀ j, Disjoint A (e j) := fun j => (hoffAB _ ⟨j, rfl⟩).1
    have hBe : ∀ j, Disjoint B (e j) := fun j => (hoffAB _ ⟨j, rfl⟩).2
    obtain ⟨k, l, hkl, hik, hil⟩ := hcc2 i
    have hflip : ∀ m, i ∈ circuitChords m →
        (A ⊆ D m ∧ Disjoint B (D m)) ∨ (B ⊆ D m ∧ Disjoint A (D m)) := fun m hm =>
      disc_flip hman (hD m) (hebd m i hm hx.1) hint hV hxV
        (hVs.trans (union_subset_union_right _ (hebd m i hm))) hA hB (hdisjW hAe m)
        (hdisjW hBe m)
    have hBne : ∀ m, i ∈ circuitChords m → Disjoint A (D m) → B.Nonempty := fun m hm hAm => by
      have hxD : x ∈ closure (discInt (D m)) :=
        (hD m).subset_closure_discInt (discBd_subset _ (hebd m i hm hx.1))
      obtain ⟨y, hyV, hy⟩ := mem_closure_iff.mp hxD V hV hxV
      rcases hVs hyV with (h1 | h1) | h1
      · exact absurd hy.1 (disjoint_left.mp hAm h1)
      · exact ⟨y, h1⟩
      · exact absurd h1 (disjoint_left.mp (hoff m i) hy)
    have hAne : A.Nonempty := closure_nonempty_iff.mp ⟨x, hclA⟩
    have heU : ∀ m, i ∈ circuitChords m → e i ⊆ U := fun m hm y hy =>
      mem_iUnion.2 ⟨m, discBd_subset _ (hebd m i hm hy)⟩
    have hcover : V ⊆ U := by
      rcases hflip k hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hflip l hil with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact (hside2 A hAne hAe k l hkl h1 h3).elim
      · intro y hy
        rcases hVs hy with (h5 | h5) | h5
        · exact mem_iUnion.2 ⟨k, h1 h5⟩
        · exact mem_iUnion.2 ⟨l, h3 h5⟩
        · exact heU k hik h5
      · intro y hy
        rcases hVs hy with (h5 | h5) | h5
        · exact mem_iUnion.2 ⟨l, h3 h5⟩
        · exact mem_iUnion.2 ⟨k, h1 h5⟩
        · exact heU k hik h5
      · exact (hside2 B (hBne k hik h2) hBe k l hkl h1 h3).elim
    exact interior_maximal hcover hV hxV
  -- The union is a neighbourhood of each of its points other than the ends of the chords.
  let F : Set S := ⋃ i, P i
  have hFfin : F.Finite := Γ.finite_N.subset (iUnion_subset hP)
  have hFU : F ⊆ U := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, -, hik⟩ := hcc0 i
    exact mem_iUnion.2 ⟨k, discBd_subset _ (hebd k i hik (hPe i hi))⟩
  have hUint : ∀ x ∈ U, x ∉ F → x ∈ interior U := fun x hx hxF => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    by_cases hxb : x ∈ discBd (D k)
    · rw [hb k] at hxb
      obtain ⟨i, -, hxi⟩ := mem_iUnion₂.1 hxb
      exact hchordint i x ⟨hxi, fun h => hxF (mem_iUnion.2 ⟨i, h⟩)⟩
    · have hdiscSub : discInt (D k) ⊆ U := fun _ hy => mem_iUnion.2 ⟨k, hy.1⟩
      exact interior_maximal hdiscSub (hopen k) ⟨hk, hxb⟩
  -- So the union contains every interior point other than the ends of the chords.
  have hsub : (bd S)ᶜ \ F ⊆ U := by
    have hpc := GM07.isPreconnected_interior_sdiff_finite hS hFfin
    rcases hpc.subset_or_subset isOpen_interior hUc.isOpen_compl
        (disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx))
        (fun x hx => by
          by_cases hxU : x ∈ U
          · exact .inl (hUint x hxU hx.2)
          · exact .inr hxU) with h1 | h1
    · exact h1.trans interior_subset
    · exfalso
      obtain ⟨x₀, hx₀⟩ := hne 0
      obtain ⟨r, hr, hsr⟩ := hreg 0
      have hint : IsInteriorPoint x₀ := by
        by_contra hn
        exact (arcComponentsIn_subset hr (hsr hx₀)).2 (Γ.bd_subset hn)
      have hx₀F : x₀ ∉ F := fun h => by
        obtain ⟨j, hj⟩ := mem_iUnion.1 h
        by_cases hj0 : j = 0
        · subst hj0
          exact hx₀.2 hj
        · exact disjoint_left.mp (hdj 0 j (Ne.symm hj0)) hx₀ (hPe j hj)
      exact h1 ⟨fun h => h hint, hx₀F⟩ (interior_subset (hchordint 0 x₀ hx₀))
  -- Taking closures, the union is all of `Σ`.
  have hall : ∀ x, x ∈ U := by
    intro x
    by_cases hxF : x ∈ F
    · exact hFU hxF
    by_cases hxb : x ∈ bd S
    · have hcl := mem_closure_compl_bd (hman x)
      have hx' : x ∈ closure ((bd S)ᶜ \ F) := by
        rw [mem_closure_iff] at hcl ⊢
        intro O hO hxO
        obtain ⟨y, hyO, hy⟩ := hcl (O ∩ Fᶜ) (hO.inter hFfin.isClosed.isOpen_compl) ⟨hxO, hxF⟩
        exact ⟨y, hyO.1, hy, hyO.2⟩
      exact closure_minimal hsub hUc hx'
    · exact hsub ⟨hxb, hxF⟩
  -- Each cell misses the chords, so it lies in one disc.
  have hoffU : ∀ i, e i ∩ Γ.U ⊆ Γ.N := fun i x hx => by
    by_contra hn
    obtain ⟨r, hr, hsub⟩ := hreg i
    exact (arcComponentsIn_subset hr (hsub ⟨hx.1, fun h1 => hn (hP i h1)⟩)).2 hx.2
  have hcellW : ∀ c ∈ Γ.C, ∀ i, Disjoint c (e i) := fun c hc i =>
    disjoint_left.mpr fun x hx hxi =>
      disjoint_left.mp (Γ.cell_disjoint_N hc) hx (hoffU i ⟨hxi, Γ.cell_subset_U hc hx⟩)
  intro c hc
  have hcp : IsPreconnected c := (arcComponentsIn_isPathConnected hc).isConnected.isPreconnected
  obtain ⟨z, hz⟩ := arcComponentsIn_nonempty hc
  obtain ⟨k, hk⟩ := mem_iUnion.1 (hall z)
  rcases disc_dichotomy hman (hD k) hcp (hdisjW (hcellW c hc) k) with h1 | h1
  · exact ⟨k, h1⟩
  · exact absurd hk (disjoint_left.mp h1 hz)

end GraphMinor.GM17
