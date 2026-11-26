/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10c
public import LeanPool.GraphMinor.GM09.Section4b

/-!
# Graph Minors IX, (10.2)

The paths `Q_i` of (10.2). The paper takes `Q_i` to run along `C_i`, with `C_1` the innermost
circuit of the nest. With that numbering `Q_s` runs around `C_s` and crosses the paths that lead
`Q_1` to `C_1`. So we let `Q_i` run along `C_{s+1-i}`: the path with the smallest interval runs
along the outermost circuit.

`IsGraphPath` paths may pass through `ΩBar`, so we use the sides of an arc from `ArcSides.lean`, in
place of a cross-cut. The word "clockwise" in the choice of the arc of the circuit is replaced by a
condition on sides: we take the arc for which the disc of the circuit lies on the side of `Ω(b_i,
a_i)`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

theorem CyclicPerm.getElem_ofFn_left {s : ℕ} (a b : Fin s → α) (k : Fin s)
    (hk : s - 1 - k.1 < ((List.ofFn a).reverse ++ List.ofFn b).length) :
    ((List.ofFn a).reverse ++ List.ofFn b)[s - 1 - k.1]'hk = a k := by
  have hk' := k.2
  have h₁ : s - 1 - k.1 < (List.ofFn a).reverse.length := by simp; omega
  rw [List.getElem_append_left h₁, List.getElem_reverse]
  simp only [List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp
  omega

theorem CyclicPerm.getElem_ofFn_right {s : ℕ} (a b : Fin s → α) (k : Fin s)
    (hk : s + k.1 < ((List.ofFn a).reverse ++ List.ofFn b).length) :
    ((List.ofFn a).reverse ++ List.ofFn b)[s + k.1]'hk = b k := by
  rw [List.getElem_append_right (by simp)]
  simp only [List.getElem_ofFn, List.length_reverse, List.length_ofFn]
  congr 1
  ext
  simp

/-- The facts on a clockwise list `(a_s, …, a_1, b_1, …, b_s)` that we use. -/
theorem CyclicPerm.isClockwise3_of_ofFn {Ω : CyclicPerm α} {s : ℕ} {a b : Fin s → α}
    (h : Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b)) :
    (∀ i j : Fin s, i < j → Ω.IsClockwise3 (b i) (a j) (a i) ∧ Ω.IsClockwise3 (b i) (b j) (a i)) ∧
      Injective a ∧ Injective b ∧ (∀ i j, a i ≠ b j) ∧ (∀ i, a i ∈ Ω.bar) ∧ ∀ i, b i ∈ Ω.bar := by
  set L := (List.ofFn a).reverse ++ List.ofFn b with hL
  have hlen : L.length = s + s := by simp [hL]
  have ha : ∀ (k : Fin s) (hk : s - 1 - k.1 < L.length), L[s - 1 - k.1]'hk = a k :=
    fun k hk => CyclicPerm.getElem_ofFn_left a b k hk
  have hb : ∀ (k : Fin s) (hk : s + k.1 < L.length), L[s + k.1]'hk = b k :=
    fun k hk => CyclicPerm.getElem_ofFn_right a b k hk
  have hnd := h.1
  refine ⟨fun i j hij => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hi := i.2
    have hj := j.2
    have hij' : i.1 < j.1 := hij
    have h₁ := Ω.mem_interval_of_lt h (i₁ := s - 1 - j.1) (i₂ := s - 1 - i.1) (i₃ := s + i.1)
      (by omega) (by omega) (by omega)
    have h₂ := Ω.mem_interval_of_lt h (i₁ := s - 1 - i.1) (i₂ := s + i.1) (i₃ := s + j.1)
      (by omega) (by omega) (by omega)
    rw [ha j, ha i, hb i] at h₁
    rw [ha i, hb i, hb j] at h₂
    exact ⟨Ω.isClockwise3_rotate (Ω.isClockwise3_rotate h₁.2), Ω.isClockwise3_rotate h₂.2⟩
  · intro i j e
    have hi := i.2
    have hj := j.2
    have := (List.Nodup.getElem_inj_iff hnd (i := s - 1 - i.1) (j := s - 1 - j.1)
      (hi := by omega) (hj := by omega)).mp (by rw [ha i, ha j, e])
    exact Fin.ext (by omega)
  · intro i j e
    have hi := i.2
    have hj := j.2
    have := (List.Nodup.getElem_inj_iff hnd (i := s + i.1) (j := s + j.1)
      (hi := by omega) (hj := by omega)).mp (by rw [hb i, hb j, e])
    exact Fin.ext (by omega)
  · intro i j e
    have hi := i.2
    have hj := j.2
    have := (List.Nodup.getElem_inj_iff hnd (i := s - 1 - i.1) (j := s + j.1)
      (hi := by omega) (hj := by omega)).mp (by rw [ha i, hb j, e])
    omega
  · intro i
    have hi := i.2
    exact h.2.1 _ (ha i (by omega) ▸ List.getElem_mem (by omega))
  · intro i
    have hi := i.2
    exact h.2.1 _ (hb i (by omega) ▸ List.getElem_mem (by omega))

/-- The arcs and the sides of a detour along a circuit, for (10.2). `Ra, Rb` are paths from `a, b`
to the circuit. -/
theorem exists_detour {N : Neighborhood α β} (P_pres : Presentation N) {C Ra Rb : Graph α β}
    {D I₁ I₂ : Set EuclideanPlane} {a b y y' : α} {pa pb : EuclideanPlane}
    (hC : IsGraphCircuit N.G C) (hD : IsClosedDisc D) (hDΔ : D ⊆ P_pres.Δ)
    (hbd : subBd D = graphDrawingSubgraphU P_pres.Γ C)
    (ha : a ∈ N.Ω.bar) (hb : b ∈ N.Ω.bar)
    (hRa : IsGraphPathWithEnds N.G Ra a y) (hRb : IsGraphPathWithEnds N.G Rb b y')
    (hVa : V(Ra) ∩ V(C) = {y}) (hVb : V(Rb) ∩ V(C) = {y'}) (hd : Disjoint V(Ra) V(Rb)) (hab : a ≠ b)
    (hpa : graphDrawingVertexSet P_pres.Γ a = {pa}) (hpb : graphDrawingVertexSet P_pres.Γ b = {pb})
    (hI₁ : IsPreconnected I₁) (hI₂ : IsPreconnected I₂) (hId : Disjoint I₁ I₂)
    (hIu : I₁ ∪ I₂ = discBd P_pres.Δ \ {pa, pb}) :
    ∃ (A A' Q Q' : Graph α β) (Y₁ Y₂ Y₁' Y₂' : Set EuclideanPlane),
      V(A) ⊆ V(C) ∧ V(A) ∩ V(A') = {y, y'} ∧ subgraphUnion N.G A A' = C ∧
      A ≤ C ∧ A' ≤ C ∧ IsGraphPathWithEnds N.G A y y' ∧ IsGraphPathWithEnds N.G A' y y' ∧
      graphDrawingSubgraphU P_pres.Γ A ∩ graphDrawingSubgraphU P_pres.Γ A' =
        graphDrawingVertexSet P_pres.Γ y ∪ graphDrawingVertexSet P_pres.Γ y' ∧
      IsGraphPathWithEnds N.G Q a b ∧ V(Q) = V(Ra) ∪ V(A) ∪ V(Rb) ∧
      IsGraphPathWithEnds N.G Q' a b ∧ V(Q') = V(Ra) ∪ V(A') ∪ V(Rb) ∧
      graphDrawingSubgraphU P_pres.Γ A ⊆ graphDrawingSubgraphU P_pres.Γ Q ∧
      graphDrawingSubgraphU P_pres.Γ Q' =
        graphDrawingSubgraphU P_pres.Γ Ra ∪ graphDrawingSubgraphU P_pres.Γ A' ∪
          graphDrawingSubgraphU P_pres.Γ Rb ∧
      IsArcSides P_pres.Δ (graphDrawingSubgraphU P_pres.Γ Q) I₁ I₂ Y₁ Y₂ ∧
      IsArcSides P_pres.Δ (graphDrawingSubgraphU P_pres.Γ Q') I₁ I₂ Y₁' Y₂' ∧
      D \ graphDrawingSubgraphU P_pres.Γ A ⊆ Y₂ ∧ D \ graphDrawingSubgraphU P_pres.Γ A' ⊆ Y₁' := by
  set Γ := P_pres.Γ
  have hyC : y ∈ V(C) := (hVa.symm ▸ mem_singleton y : y ∈ V(Ra) ∩ V(C)).2
  have hy'C : y' ∈ V(C) := (hVb.symm ▸ mem_singleton y' : y' ∈ V(Rb) ∩ V(C)).2
  have hyy' : y ≠ y' := fun e => Set.disjoint_left.mp hd hRa.right_mem (e ▸ hRb.right_mem)
  have hdisc : subBd D = graphDrawingSubgraphU Γ C := hbd
  obtain ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁, hQ₂, hV, hE, hunion, hl₁, hl₂, hinter, hcov⟩ :=
    circuit_two_arcs_drawing Γ hC hD hdisc hyC hy'C hyy'
  have hyG := hC.1.vertexSet_mono hyC
  have hy'G := hC.1.vertexSet_mono hy'C
  set py := (Γ.iso.vertexEquiv ⟨y, hyG⟩).1
  set py' := (Γ.iso.vertexEquiv ⟨y', hy'G⟩).1
  have hsy : graphDrawingVertexSet Γ y = {py} := graphDrawingVertexSet_eq_singleton Γ hyG
  have hsy' : graphDrawingVertexSet Γ y' = {py'} := graphDrawingVertexSet_eq_singleton Γ hy'G
  have h₁ := subgraphU_inter_disc P_pres hC.1 hD hDΔ hbd ha hRa hVa
  have h₂ := subgraphU_inter_disc P_pres hC.1 hD hDΔ hbd hb hRb hVb
  set R := graphDrawingSubgraphU Γ Ra ∪ graphDrawingSubgraphU Γ Rb with hRdef
  have hRD : R ∩ D = {py, py'} := by
    rw [hRdef, union_inter_distrib_right, h₁, h₂, hsy, hsy']
    rfl
  have hUΔ : ∀ X : Graph α β, graphDrawingSubgraphU Γ X ⊆ P_pres.Δ := fun X =>
    (graphDrawingSubgraphU_subset_U Γ X).trans (P_pres.U_subset.trans sdiff_subset)
  have hRΔ : R ⊆ P_pres.Δ := union_subset (hUΔ _) (hUΔ _)
  have hpaG : a ∈ V(N.G) := N.bar_subset ha
  have hpbG : b ∈ V(N.G) := N.bar_subset hb
  have hpa' : pa = (Γ.iso.vertexEquiv ⟨a, hpaG⟩).1 := by
    have := graphDrawingVertexSet_eq_singleton Γ hpaG
    rw [hpa] at this
    exact singleton_injective this
  have hpb' : pb = (Γ.iso.vertexEquiv ⟨b, hpbG⟩).1 := by
    have := graphDrawingVertexSet_eq_singleton Γ hpbG
    rw [hpb] at this
    exact singleton_injective this
  have hne : pa ≠ pb := by
    rw [hpa', hpb']
    exact fun e => hab (congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext e)))
  have hRb' := hRb.symm
  have mk : ∀ X : Graph α β, X ≤ C → IsGraphPathWithEnds N.G X y y' →
      ∃ Q : Graph α β, IsGraphPathWithEnds N.G Q a b ∧ V(Q) = V(Ra) ∪ V(X) ∪ V(Rb) ∧
        graphDrawingSubgraphU Γ Q = R ∪ graphDrawingSubgraphU Γ X := by
    intro X hXC hX
    have hV₁ : V(Ra) ∩ V(X) = {y} := by
      apply Subset.antisymm
      · rintro z ⟨h, h'⟩
        have : z ∈ V(Ra) ∩ V(C) := ⟨h, hXC.vertexSet_mono h'⟩
        rwa [hVa] at this
      · rintro _ rfl
        exact ⟨hRa.right_mem, hX.left_mem⟩
    have hp₁ := hRa.subgraphUnion hX hV₁
    have hV₂ : V(subgraphUnion N.G Ra X) ∩ V(Rb) = {y'} := by
      rw [vertexSet_subgraphUnion]
      apply Subset.antisymm
      · rintro z ⟨h | h, h'⟩
        · exact (Set.disjoint_left.mp hd h h').elim
        · have : z ∈ V(Rb) ∩ V(C) := ⟨h', hXC.vertexSet_mono h⟩
          rwa [hVb] at this
      · rintro _ rfl
        exact ⟨Or.inr hX.right_mem, hRb.right_mem⟩
    refine ⟨_, hp₁.subgraphUnion hRb' hV₂, ?_, ?_⟩
    · rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion]
    · rw [graphDrawingSubgraphU_subgraphUnion Γ hp₁.le hRb.le,
        graphDrawingSubgraphU_subgraphUnion Γ hRa.le hX.le, hRdef]
      ext z
      simp only [mem_union]
      tauto
  obtain ⟨Q, hQ, hVQ, hUQ⟩ := mk Q₁ hQ₁C hQ₁
  obtain ⟨Q', hQ', hVQ', hUQ'⟩ := mk Q₂ hQ₂C hQ₂
  have hline : ∀ {Z : Graph α β}, IsGraphPathWithEnds N.G Z a b →
      IsLineWithEnds (graphDrawingSubgraphU Γ Z) pa pb := by
    intro Z hZ
    have := (isLineWithEnds_graphDrawingSubgraphU Γ hZ hab).1
    rwa [← hpa', ← hpb'] at this
  have hL := hline hQ
  have hL' := hline hQ'
  rw [hUQ] at hL
  rw [hUQ'] at hL'
  have hpaU : pa ∈ graphDrawingSubgraphU Γ Ra := by
    have := graphDrawingVertexSet_subset_subgraphU_of_mem Γ hRa.left_mem
    rw [hpa] at this
    exact this rfl
  have hpbU : pb ∈ graphDrawingSubgraphU Γ Rb := by
    have := graphDrawingVertexSet_subset_subgraphU_of_mem Γ hRb.left_mem
    rw [hpb] at this
    exact this rfl
  have hbdp : ∀ {v : α}, v ∈ N.Ω.bar → ∀ {p : EuclideanPlane}, graphDrawingVertexSet Γ v = {p} →
      p ∈ discBd P_pres.Δ := by
    intro v hv p hp
    have := (P_pres.mem_bd_Δ_iff v (N.bar_subset hv)).mpr hv
    rw [hp, singleton_subset_iff, subBd_eq_discBd_plane P_pres.isClosedDisc_Δ] at this
    exact this
  obtain ⟨Y₁, Y₂, Y₁', Y₂', hs, hs', hor⟩ := exists_hole_sides (y := py) (y' := py') (R := R)
    P_pres.isClosedDisc_Δ hD hDΔ hl₁
    (by rw [hcov]) hinter hRD hRΔ hL hL' (hbdp ha hpa) (hbdp hb hpb) hne
    (Or.inl hpaU) (Or.inr hpbU) hI₁ hI₂ hId hIu
  have hle₁ : Q₁ ≤ N.G := hQ₁.le
  have hle₂ : Q₂ ≤ N.G := hQ₂.le
  have hun' : subgraphUnion N.G Q₂ Q₁ = C := by
    rw [subgraphUnion_comm hle₂ hle₁]
    exact hunion
  rw [← hUQ] at hs
  rw [← hUQ'] at hs'
  have hR1 : ∀ X, graphDrawingSubgraphU Γ X ⊆ R ∪ graphDrawingSubgraphU Γ X :=
    fun _ => subset_union_right
  have hexp : ∀ X : Graph α β, R ∪ graphDrawingSubgraphU Γ X =
      graphDrawingSubgraphU Γ Ra ∪ graphDrawingSubgraphU Γ X ∪ graphDrawingSubgraphU Γ Rb := by
    intro X
    ext z
    simp only [hRdef, mem_union]
    tauto
  rcases hor with ⟨h₂', h₁'⟩ | ⟨h₁', h₂'⟩
  · refine ⟨Q₁, Q₂, Q, Q', Y₁, Y₂, Y₁', Y₂', hQ₁C.vertexSet_mono, hV, hunion, hQ₁C, hQ₂C, hQ₁,
      hQ₂, ?_, hQ, hVQ,
      hQ', hVQ', hUQ ▸ hR1 _, hUQ'.trans (hexp _), hs, hs', h₂', h₁'⟩
    rw [hinter, hsy, hsy']
    rfl
  · refine ⟨Q₂, Q₁, Q', Q, Y₁', Y₂', Y₁, Y₂, hQ₂C.vertexSet_mono, ?_, hun', hQ₂C, hQ₁C, hQ₂, hQ₁,
      ?_, hQ', hVQ',
      hQ, hVQ, hUQ' ▸ hR1 _, hUQ.trans (hexp _), hs', hs, h₂', h₁'⟩
    · rw [Set.inter_comm]
      exact hV
    · rw [Set.inter_comm, hinter, hsy, hsy']
      rfl

private theorem pairDisjointOfNestedCircuits
    {N : Neighborhood α β} (P_pres : Presentation N) (s : ℕ) (a b : Fin s → α)
    (ha_bar : ∀ (i : Fin s), a i ∈ N.Ω.bar) (hb_bar : ∀ (i : Fin s), b i ∈ N.Ω.bar)
    (C : Fin s → Graph α β)
    (hcir : ∀ (i : Fin s), IsGraphCircuit N.G (C i))
    (hdisjC : Pairwise fun i j => Disjoint V(C i) V(C j)) (D : Fin s → Set EuclideanPlane)
    (hDs : ∀ (i : Fin s), P_pres.Δ₀ ⊆ D i ∧ D i ⊆ P_pres.Δ)
    (hDm : ∀ (i j : Fin s), i ≤ j → D i ⊆ D j)
    (hDd : ∀ (i : Fin s), IsClosedDisc (D i) ∧ subBd (D i) = graphDrawingSubgraphU (P_pres.Γ) (C
      i))
    (hpt : ∀ v ∈ V(N.G), ∃ p, graphDrawingVertexSet (P_pres.Γ) v = {p}) (i : Fin s) {y : α}
    {Ra : Graph α β} (hRa : IsGraphPathWithEnds N.G Ra (a i) y) (hVa : V(Ra) ∩ V(C (i.rev)) = {y})
    {y' : α} {Rb : Graph α β} (hRb : IsGraphPathWithEnds N.G Rb (b i) y')
    (hVb : V(Rb) ∩ V(C (i.rev)) = {y'}) (m : Fin s) (hm : m < (i.rev)) :
    Disjoint (V(Ra) ∪ V(Rb)) V(C m) := by
  classical
  let Γ := P_pres.Γ
  let k := i.rev
  have hmk : D m ⊆ D k := hDm m k hm.le
  have hne : m ≠ k := hm.ne
  have hoffC : ∀ {R : Graph α β} {u w : α}, IsGraphPathWithEnds N.G R u w → u ∈ N.Ω.bar →
      V(R) ∩ V(C k) = {w} → Disjoint V(R) V(C m) := by
    intro R u w hR hu hRV
    rw [Set.disjoint_left]
    intro v hvR hvC
    have hvG := hR.le.vertexSet_mono hvR
    have hint := subgraphU_inter_disc P_pres (hcir k).1 (hDd k).1 (hDs k).2 (hDd k).2 hu hR hRV
    obtain ⟨p, hp⟩ := hpt v hvG
    have hpm : p ∈ graphDrawingVertexSet Γ v := hp ▸ mem_singleton p
    have hpD : p ∈ D m := by
      have h₁ := graphDrawingVertexSet_subset_subgraphU_of_mem Γ hvC hpm
      rw [← (hDd m).2, subBd_eq_discBd_plane (hDd m).1] at h₁
      exact Surface.discBd_subset _ h₁
    have : p ∈ graphDrawingSubgraphU Γ R ∩ D k :=
      ⟨graphDrawingVertexSet_subset_subgraphU_of_mem Γ hvR hpm, hmk hpD⟩
    rw [hint] at this
    have hvw : v = w := graphDrawingVertexSet_inj Γ hpm this
    subst hvw
    have : v ∈ V(R) ∩ V(C k) := by rw [hRV]; rfl
    exact Set.disjoint_left.mp (hdisjC hne) hvC this.2
  rw [Set.disjoint_union_left]
  exact ⟨hoffC hRa (ha_bar i) hVa, hoffC hRb (hb_bar i) hVb⟩

private theorem pathDisjointOfDetour
    {N : Neighborhood α β} (P_pres : Presentation N) (s : ℕ) (a b : Fin s → α)
    (C : Fin s → Graph α β) (P : Fin (range a ∪ range b).ncard → Graph α β)
    (hPd : Pairwise fun i₁ i₂ => Disjoint V(P i₁) V(P i₂))
    (hPC : ∀ (i : Fin (range a ∪ range b).ncard) (j : Fin s), IsGraphPath N.G (subgraphInter N.G
      (P i) (C j)))
    (st tm : Fin (range a ∪ range b).ncard → α)
    (hst : ∀ (i : Fin (range a ∪ range b).ncard), IsFromToPathWithEnds N.G (P i) (range a ∪ range
      b) N.Ω₀.bar (st i) (tm i))
    (hst_V : ∀ (i : Fin (range a ∪ range b).ncard), st i ∈ V(P i))
    (idx : α → Fin (range a ∪ range b).ncard) (hcir : ∀ (i : Fin s), IsGraphCircuit N.G (C i))
    (D : Fin s → Set EuclideanPlane)
    (hpt : ∀ v ∈ V(N.G), ∃ p, graphDrawingVertexSet (P_pres.Γ) v = {p}) (i : Fin s) {y : α}
    {Ra : Graph α β} (hRaP : Ra ≤ P (idx (a i))) (hRa : IsGraphPathWithEnds N.G Ra (a i) y)
    {y' : α} {Rb : Graph α β} (hRbP : Rb ≤ P (idx (b i)))
    (hRb : IsGraphPathWithEnds N.G Rb (b i) y') (hd : Disjoint V(Ra) V(Rb))
    (I₁ I₂ : Set EuclideanPlane)
    (hmem₂ : ∀ c ∈ N.Ω.interval (b i) (a i), ∀ (p : EuclideanPlane), graphDrawingVertexSet
      (P_pres.Γ) c = {p} → p ∈ I₂)
    {A A' Q' : Graph α β} (Y₁' Y₂' : Set EuclideanPlane) (hAC : V(A) ⊆ V(C (i.rev)))
    (hun : subgraphUnion N.G A A' = C (i.rev)) (hAle : A ≤ C (i.rev)) (hA'le : A' ≤ C (i.rev))
    (hApath : IsGraphPathWithEnds N.G A y y') (hA'path : IsGraphPathWithEnds N.G A' y y')
    (hUAA' : graphDrawingSubgraphU P_pres.Γ A ∩ graphDrawingSubgraphU P_pres.Γ
      A' = graphDrawingVertexSet P_pres.Γ y ∪ graphDrawingVertexSet P_pres.Γ
      y')
    (hUQ' : graphDrawingSubgraphU P_pres.Γ Q' = graphDrawingSubgraphU P_pres.Γ
      Ra ∪ graphDrawingSubgraphU P_pres.Γ A' ∪ graphDrawingSubgraphU
      P_pres.Γ Rb)
    (hs' : IsArcSides P_pres.Δ (graphDrawingSubgraphU P_pres.Γ Q') I₁ I₂ Y₁' Y₂')
    (hDA' : D (i.rev) \ graphDrawingSubgraphU P_pres.Γ A' ⊆ Y₁')
    (hUU : (P_pres.Γ).drawing.U ⊆ P_pres.Δ)
    (hUD : graphDrawingSubgraphU (P_pres.Γ) (C (i.rev)) ⊆ D (i.rev))
    (t : Fin (range a ∪ range b).ncard) (ht₁ : t ≠ idx (a i)) (ht₂ : t ≠ idx (b i))
    (hstt : st t ∈ N.Ω.interval (b i) (a i)) :
    Disjoint V(P t) V(A) := by
  classical
  let Γ := P_pres.Γ
  let k := i.rev
  rw [Set.disjoint_left]
  intro v hvT hvA
  have hTle : P t ≤ N.G := (hst t).1.le
  have hAG : A ≤ N.G := hApath.le
  have hA'G : A' ≤ N.G := hA'path.le
  have hdT₁ : Disjoint V(P t) V(Ra) :=
    (hPd ht₁).mono_right hRaP.vertexSet_mono
  have hdT₂ : Disjoint V(P t) V(Rb) :=
    (hPd ht₂).mono_right hRbP.vertexSet_mono
  have hy'R : y' ∈ V(Rb) := hRb.right_mem
  have hyR : y ∈ V(Ra) := hRa.right_mem
  have hne_y : ∀ w ∈ V(P t), w ≠ y ∧ w ≠ y' := fun w hw =>
    ⟨fun e => Set.disjoint_left.mp hdT₁ hw (e ▸ hyR),
      fun e => Set.disjoint_left.mp hdT₂ hw (e ▸ hy'R)⟩
  have hyy' : y ≠ y' := fun e => Set.disjoint_left.mp hd hyR (e ▸ hy'R)
  obtain ⟨u₀, v₀, hI⟩ := hPC t k
  set I := subgraphInter N.G (P t) (C k) with hIdef
  have hIT : I ≤ P t := subgraphInter_le_left hTle (hcir k).1
  have hIC : I ≤ C k := subgraphInter_le_right hTle (hcir k).1
  have hZ := isPreconnected_graphDrawingSubgraphU Γ hI
  have hsplit : graphDrawingSubgraphU Γ I ⊆ graphDrawingSubgraphU Γ A ∪
      graphDrawingSubgraphU Γ A' := by
    rw [← graphDrawingSubgraphU_subgraphUnion Γ hAG hA'G, hun]
    exact graphDrawingSubgraphU_mono Γ hIC
  have hvI : v ∈ V(I) := by
    rw [hIdef, vertexSet_subgraphInter]
    exact ⟨hvT, hAC hvA⟩
  have hvG := hTle.vertexSet_mono hvT
  obtain ⟨pv, hpv⟩ := hpt v hvG
  have hpv' : pv ∈ graphDrawingVertexSet Γ v := hpv ▸ mem_singleton pv
  have hnot : ∀ w ∈ V(A'), w ∉ V(P t) := by
    intro w hwA' hwT
    have hwI : w ∈ V(I) := by
      rw [hIdef, vertexSet_subgraphInter]
      exact ⟨hwT, hA'le.vertexSet_mono hwA'⟩
    have hwG := hTle.vertexSet_mono hwT
    obtain ⟨pw, hpw⟩ := hpt w hwG
    have hpw' : pw ∈ graphDrawingVertexSet Γ w := hpw ▸ mem_singleton pw
    have hcl : ∀ {B : Graph α β} {c e : α}, IsGraphPathWithEnds N.G B c e → c ≠ e →
        IsClosed (graphDrawingSubgraphU Γ B) := fun hB hne =>
      (isLineWithEnds_graphDrawingSubgraphU Γ hB hne).1.isCompact.isClosed
    obtain ⟨x, hxZ, hx₁, hx₂⟩ := isPreconnected_closed_iff.mp hZ _ _ (hcl hApath hyy')
      (hcl hA'path hyy') hsplit
      ⟨pv, graphDrawingVertexSet_subset_subgraphU_of_mem Γ hvI hpv',
        graphDrawingVertexSet_subset_subgraphU_of_mem Γ hvA hpv'⟩
      ⟨pw, graphDrawingVertexSet_subset_subgraphU_of_mem Γ hwI hpw',
        graphDrawingVertexSet_subset_subgraphU_of_mem Γ hwA' hpw'⟩
    have hx : x ∈ graphDrawingSubgraphU Γ A ∩ graphDrawingSubgraphU Γ A' := ⟨hx₁, hx₂⟩
    rw [hUAA'] at hx
    have hin : ∀ q ∈ V(N.G), x ∈ graphDrawingVertexSet Γ q → q ∈ V(P t) := by
      intro q hq hxq
      refine hIT.vertexSet_mono (mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ
        (hIT.trans hTle) hq ?_)
      obtain ⟨p', hp'⟩ := hpt q hq
      rw [hp', singleton_subset_iff]
      rw [hp'] at hxq
      exact (show x = p' from hxq) ▸ hxZ
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hdT₁ (hin y (hRa.le.vertexSet_mono hyR) hx) hyR
    · exact Set.disjoint_left.mp hdT₂ (hin y' (hRb.le.vertexSet_mono hy'R) hx) hy'R
  have hdA' : Disjoint V(P t) V(A') := Set.disjoint_left.mpr fun w hw hw' => hnot w hw' hw
  have hTsub : graphDrawingSubgraphU Γ (P t) ⊆
      P_pres.Δ \ graphDrawingSubgraphU Γ Q' := by
    intro x hx
    refine ⟨hUU (graphDrawingSubgraphU_subset_U Γ _ hx), ?_⟩
    rw [hUQ']
    rintro ((h' | h') | h')
    · exact Set.disjoint_left.mp (disjoint_subgraphU_of_disjoint_vertexSet Γ hTle hRa.le hdT₁)
        hx h'
    · exact Set.disjoint_left.mp (disjoint_subgraphU_of_disjoint_vertexSet Γ hTle hA'G hdA')
        hx h'
    · exact Set.disjoint_left.mp (disjoint_subgraphU_of_disjoint_vertexSet Γ hTle hRb.le hdT₂)
        hx h'
  have hTc := isPreconnected_graphDrawingSubgraphU Γ (hst t).1
  have hstG : st t ∈ V(N.G) := hTle.vertexSet_mono (hst_V t)
  obtain ⟨ps, hps⟩ := hpt (st t) hstG
  have hps' : ps ∈ graphDrawingVertexSet Γ (st t) := hps ▸ mem_singleton ps
  have hpsU : ps ∈ graphDrawingSubgraphU Γ (P t) :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ (hst_V t) hps'
  have hpvU : pv ∈ graphDrawingSubgraphU Γ (P t) :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ hvT hpv'
  have hsY : ps ∈ Y₂' := hs'.right ⟨hmem₂ _ hstt ps hps, (hTsub hpsU).2⟩
  have hvNotA' : pv ∉ graphDrawingSubgraphU Γ A' := fun hm =>
    hnot v (mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hA'G hvG
      (by rw [hpv, singleton_subset_iff]; exact hm)) hvT
  have hvA_U : pv ∈ graphDrawingSubgraphU Γ A :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ hvA hpv'
  have hvD : pv ∈ D k := hUD (graphDrawingSubgraphU_mono Γ hAle hvA_U)
  have hvY : pv ∈ Y₁' := hDA' ⟨hvD, hvNotA'⟩
  rcases hs'.conn _ hTsub hTc with h' | h'
  · exact Set.disjoint_left.mp hs'.disj (h' hpsU) hsY
  · exact Set.disjoint_left.mp hs'.disj hvY (h' hpvU)

private theorem initialSegmentMeeting {G R Z : Graph α β} {u v z : α}
    (hR : IsGraphPathWithEnds G R u v) (hzR : z ∈ V(R)) (hzZ : z ∈ V(Z)) :
    ∃ y : α, ∃ R' : Graph α β, R' ≤ R ∧ IsGraphPathWithEnds G R' u y ∧
      V(R') ∩ V(Z) = {y} := by
  obtain ⟨T, hTR, _, hT⟩ := hR.exists_subpath hR.left_mem hzR
  obtain ⟨x, hx, y, _, R', hR'T, hR'⟩ :=
    hT.exists_isFromToPathWithEnds (X := {u}) (Y := V(Z)) (mem_singleton u) hzZ
  have hxu : x = u := hx
  subst hxu
  exact ⟨y, R', hR'T.trans hTR, hR'.1, hR'.2.2⟩

/-- **Graph Minors IX, (10.2)** (page 64), with the numbering of the circuits corrected as in the
module docstring:
"Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth $\ge s$, and let $\{a_1, a_2,
\dots, a_s, b_1, b_2, \dots, b_s\} \subseteq \bar{\Omega}$ be weakly-linked, where $(a_s,
a_{s-1}, \dots, a_1, b_1, b_2, \dots, b_s)$ is clockwise. Then there is a transaction
$\{Q_1, \dots, Q_s\}$ in $(G, \Omega)$ such that $Q_i$ has ends $a_i, b_i$ and $Q_i$ meets
every path from $\Omega(a_i, b_i)$ to $\Omega(b_i, a_i) \cup \bar{\Omega}_0$ $(1 \le i \le
s)$."
That `Q_i` meets every such path we state with a separation with `V(G₁ ∩ G₂) = V(Q_i)`. -/
theorem theorem_10_2_proof {N : Neighborhood α β} (P_pres : Presentation N) {s : ℕ}
    (h_nest : ∃ C₀ : Fin s → Graph α β, N.IsNest P_pres C₀) {a b : Fin s → α}
    (hX : N.IsWeaklyLinked (range a ∪ range b))
    (hcw : N.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b)) :
    ∃ Q : Fin s → Graph α β, (∀ i, IsGraphPathWithEnds N.G (Q i) (a i) (b i)) ∧
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i, ∃ G₁ G₂ : Graph α β, IsGraphSeparation N.G G₁ G₂ ∧ V(G₁) ∩ V(G₂) = V(Q i) ∧
        Q i ≤ G₁ ∧ N.Ω.interval (a i) (b i) ⊆ V(G₁) ∧ N.Ω.interval (b i) (a i) ⊆ V(G₂) ∧
        N.Ω₀.bar ⊆ V(G₂) := by
  classical
  by_cases hs0 : s = 0
  · subst hs0
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨hclock, hinj_a, hinj_b, hab, ha_bar, hb_bar⟩ := CyclicPerm.isClockwise3_of_ofFn hcw
  set X := range a ∪ range b with hXdef
  have hX_fin : X.Finite := (finite_range a).union (finite_range b)
  obtain ⟨C, P, hC, hP, hPd, hPC⟩ := theorem_10_1_proof P_pres h_nest hX
  choose st tm hst using hP
  have hst_X : ∀ i, st i ∈ X := fun i => (hst i).left_mem_X
  have hst_V : ∀ i, st i ∈ V(P i) := fun i => (hst i).1.left_mem
  have hsurj : ∀ x ∈ X, ∃ i, st i = x := by
    let f : Fin X.ncard → X := fun i => ⟨st i, hst_X i⟩
    have finj : Injective f := by
      intro i j e
      by_contra hne
      have e' : st i = st j := congrArg Subtype.val e
      exact Set.disjoint_left.mp (hPd hne) (hst_V i) (e' ▸ hst_V j)
    have : Finite X := hX_fin
    have hcard : Nat.card X ≤ Nat.card (Fin X.ncard) := by
      rw [Nat.card_coe_set_eq, Nat.card_fin]
    intro x hx
    obtain ⟨i, hi⟩ := (Function.Injective.bijective_of_nat_card_le finj hcard).2 ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have : Nonempty (Fin X.ncard) := by
    have hm : a ⟨0, Nat.pos_of_ne_zero hs0⟩ ∈ X := Or.inl (mem_range_self _)
    exact ⟨⟨0, (ncard_pos hX_fin).mpr ⟨_, hm⟩⟩⟩
  choose! idx hidx using hsurj
  have ha_X : ∀ i, a i ∈ X := fun i => Or.inl (mem_range_self i)
  have hb_X : ∀ i, b i ∈ X := fun i => Or.inr (mem_range_self i)
  have hidx_inj : ∀ {x y}, x ∈ X → y ∈ X → x ≠ y → idx x ≠ idx y := by
    intro x y hx hy hne e
    exact hne ((hidx x hx).symm.trans ((congrArg st e).trans (hidx y hy)))
  have hPpath : ∀ x ∈ X, IsGraphPathWithEnds N.G (P (idx x)) x (tm (idx x)) := by
    intro x hx
    have := (hst (idx x)).1
    rwa [hidx x hx] at this
  obtain ⟨hcir, hdisjC, D, hDd, hDs, hDm⟩ := hC
  obtain ⟨φ, _, hagree⟩ := P_pres.agrees_Δ
  set Γ := P_pres.Γ
  have hpt : ∀ v, v ∈ V(N.G) → ∃ p, graphDrawingVertexSet Γ v = {p} := fun v hv =>
    ⟨_, graphDrawingVertexSet_eq_singleton Γ hv⟩
  have key : ∀ i, ∃ Ra Rb A Q : Graph α β, IsGraphPathWithEnds N.G Q (a i) (b i) ∧
      V(Q) = V(Ra) ∪ V(A) ∪ V(Rb) ∧ V(Ra) ⊆ V(P (idx (a i))) ∧ V(Rb) ⊆ V(P (idx (b i))) ∧
      V(A) ⊆ V(C (Fin.rev i)) ∧
      (∀ m, m < Fin.rev i → Disjoint (V(Ra) ∪ V(Rb)) V(C m)) ∧
      (∀ t, t ≠ idx (a i) → t ≠ idx (b i) → st t ∈ N.Ω.interval (b i) (a i) →
        Disjoint V(P t) V(A)) ∧
      ∃ G₁ G₂ : Graph α β, IsGraphSeparation N.G G₁ G₂ ∧ V(G₁) ∩ V(G₂) = V(Q) ∧
        Q ≤ G₁ ∧ N.Ω.interval (a i) (b i) ⊆ V(G₁) ∧ N.Ω.interval (b i) (a i) ⊆ V(G₂) ∧
        N.Ω₀.bar ⊆ V(G₂) := by
    intro i
    set k := Fin.rev i
    have hPa := hPpath (a i) (ha_X i)
    have hPb := hPpath (b i) (hb_X i)
    have hnonempty : ∀ x, (V(P x) ∩ V(C k)).Nonempty := by
      intro x
      obtain ⟨u, v, h⟩ := hPC x k
      exact ⟨u, by simpa [vertexSet_subgraphInter] using h.left_mem⟩
    obtain ⟨z, hzP, hzC⟩ := hnonempty (idx (a i))
    obtain ⟨z', hzP', hzC'⟩ := hnonempty (idx (b i))
    obtain ⟨y, Ra, hRaP, hRa, hVa⟩ := initialSegmentMeeting (Z := C k) hPa hzP hzC
    obtain ⟨y', Rb, hRbP, hRb, hVb⟩ := initialSegmentMeeting (Z := C k) hPb hzP' hzC'
    have hne_idx : idx (a i) ≠ idx (b i) := hidx_inj (ha_X i) (hb_X i) (hab i i)
    have hd : Disjoint V(Ra) V(Rb) :=
      (hPd hne_idx).mono hRaP.vertexSet_mono hRbP.vertexSet_mono
    obtain ⟨pa, hpa⟩ := hpt (a i) (N.bar_subset (ha_bar i))
    obtain ⟨pb, hpb⟩ := hpt (b i) (N.bar_subset (hb_bar i))
    have hbdp : ∀ {v : α}, v ∈ N.Ω.bar → ∀ {p : EuclideanPlane},
        graphDrawingVertexSet Γ v = {p} → p ∈ subBd P_pres.Δ := by
      intro v hv p hp
      have := (P_pres.mem_bd_Δ_iff v (N.bar_subset hv)).mpr hv
      rwa [hp, singleton_subset_iff] at this
    have hpab : pa ≠ pb := by
      intro e
      exact hab i i (graphDrawingVertexSet_inj Γ (hpa ▸ mem_singleton pa)
        (hpb ▸ (e ▸ mem_singleton pb)))
    obtain ⟨I₁, I₂, hI₁, hI₂, hId, hIu, hfst, hsnd, -, -⟩ :=
      exists_open_arcs φ (hbdp (ha_bar i) hpa) (hbdp (hb_bar i) hpb) hpab
    have hbdeq : subBd P_pres.Δ = discBd P_pres.Δ := subBd_eq_discBd_plane P_pres.isClosedDisc_Δ
    rw [hbdeq] at hIu
    have hmem₁ : ∀ c ∈ N.Ω.interval (a i) (b i), ∀ p, graphDrawingVertexSet Γ c = {p} → p ∈ I₁ := by
      intro c hc p hp
      obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, e₁, e₂, e₃⟩ := hagree.2 _ _ _ hc.2
      rw [hpa] at e₁
      rw [hpb] at e₃
      rw [hp] at e₂
      have := hfst t₁ t₂ t₃ h₁₂ h₂₃ h₃₁ e₁ e₃
      rwa [show (φ (Circle.exp t₂)).1 = p from e₂] at this
    have hmem₂ : ∀ c ∈ N.Ω.interval (b i) (a i), ∀ p, graphDrawingVertexSet Γ c = {p} → p ∈ I₂ := by
      intro c hc p hp
      obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, e₁, e₂, e₃⟩ := hagree.2 _ _ _ hc.2
      rw [hpb] at e₁
      rw [hpa] at e₃
      rw [hp] at e₂
      have := hsnd t₁ t₂ t₃ h₁₂ h₂₃ h₃₁ e₁ e₃
      rwa [show (φ (Circle.exp t₂)).1 = p from e₂] at this
    obtain ⟨A, A', Q, Q', Y₁, Y₂, Y₁', Y₂', hAC, hVAA', hun, hAle, hA'le, hApath, hA'path, hUAA',
      hQ,
      hVQ, hQ', hVQ', hUAQ, hUQ', hs, hs', hDA, hDA'⟩ :=
      exists_detour P_pres (hcir k) (hDd k).1 (hDs k).2 (hDd k).2 (ha_bar i) (hb_bar i) hRa hRb hVa
        hVb hd (hab i i) hpa hpb hI₁ hI₂ hId hIu
    have hyA : y ∈ V(A) := hApath.left_mem
    have hUU : Γ.drawing.U ⊆ P_pres.Δ := P_pres.U_subset.trans sdiff_subset
    have hUD : graphDrawingSubgraphU Γ (C k) ⊆ (D k) := by
      rw [← (hDd k).2, subBd_eq_discBd_plane (hDd k).1]
      exact Surface.discBd_subset _
    obtain ⟨G₁, G₂, hsep, hinter, hQG₁, hY₁, hY₂, -⟩ := exists_separation_of_sides Γ hUU hQ.le hs
    have hQV₂ : V(Q) ⊆ V(G₂) := fun v hv => (hinter.symm ▸ hv : v ∈ V(G₁) ∩ V(G₂)).2
    have hQV₁ : V(Q) ⊆ V(G₁) := hQG₁.vertexSet_mono
    have hoff : ∀ v ∈ V(N.G), v ∉ V(Q) → ∀ p, graphDrawingVertexSet Γ v = {p} →
        p ∉ graphDrawingSubgraphU Γ Q := by
      intro v hv hvQ p hp hm
      exact Set.disjoint_left.mp (disjoint_graphDrawingVertexSet_subgraphU Γ hQ.le hv hvQ)
        (hp ▸ mem_singleton p) hm
    refine ⟨Ra, Rb, A, Q, hQ, hVQ, hRaP.vertexSet_mono, hRbP.vertexSet_mono, hAC, ?_, ?_, G₁, G₂,
      hsep, hinter, hQG₁, ?_, ?_, ?_⟩
    · intro m hm
      exact pairDisjointOfNestedCircuits P_pres s a b ha_bar hb_bar C hcir hdisjC D hDs hDm
        hDd hpt i hRa hVa hRb hVb m hm
    · intro t ht₁ ht₂ hstt
      exact pathDisjointOfDetour P_pres s a b C P hPd hPC st tm hst hst_V idx hcir D hpt i hRaP
        hRa hRbP hRb hd I₁ I₂ hmem₂ Y₁' Y₂' hAC hun hAle hA'le hApath hA'path hUAA' hUQ' hs' hDA'
        hUU hUD t ht₁ ht₂ hstt
    · intro c hc
      by_cases hcQ : c ∈ V(Q)
      · exact hQV₁ hcQ
      · have hcG := N.bar_subset hc.1.1
        obtain ⟨p, hp⟩ := hpt c hcG
        refine hY₁ c hcG ?_
        rw [hp, singleton_subset_iff]
        exact hs.left ⟨hmem₁ c hc p hp, hoff c hcG hcQ p hp⟩
    · intro c hc
      by_cases hcQ : c ∈ V(Q)
      · exact hQV₂ hcQ
      · have hcG := N.bar_subset hc.1.1
        obtain ⟨p, hp⟩ := hpt c hcG
        refine hY₂ c hcG ?_
        rw [hp, singleton_subset_iff]
        exact hs.right ⟨hmem₂ c hc p hp, hoff c hcG hcQ p hp⟩
    · intro c hc
      by_cases hcQ : c ∈ V(Q)
      · exact hQV₂ hcQ
      · have hcG := N.bar₀_subset hc
        obtain ⟨p, hp⟩ := hpt c hcG
        refine hY₂ c hcG ?_
        rw [hp, singleton_subset_iff]
        have hpΔ₀ : p ∈ P_pres.Δ₀ := by
          have := (isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hc).2
          have e := graphDrawingVertexSet_eq_singleton Γ hcG
          rw [hp] at e
          rwa [← singleton_injective e] at this
        exact hDA ⟨(hDs k).1 hpΔ₀, fun hm => hoff c hcG hcQ p hp (hUAQ hm)⟩
  choose Ra Rb A Q hQ hVQ hRaP hRbP hAC hout hfar hsep using key
  refine ⟨Q, hQ, ?_, hsep⟩
  have hlt : ∀ i j : Fin s, i < j → Disjoint V(Q i) V(Q j) := by
    intro i j hij
    have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
    have hrevne : Fin.rev j ≠ Fin.rev i := hrev.ne
    have hPdisj : ∀ x y, x ∈ X → y ∈ X → x ≠ y → Disjoint V(P (idx x)) V(P (idx y)) :=
      fun x y hx hy hne => hPd (hidx_inj hx hy hne)
    have haa : a i ≠ a j := fun e => hij.ne (hinj_a e)
    have hbb : b i ≠ b j := fun e => hij.ne (hinj_b e)
    obtain ⟨hc₁, hc₂⟩ := hclock i j hij
    have hfar₁ : Disjoint V(P (idx (a j))) V(A i) := by
      refine hfar i _ (hidx_inj (ha_X j) (ha_X i) haa.symm) (hidx_inj (ha_X j) (hb_X i)
        (hab j i)) ?_
      rw [hidx _ (ha_X j)]
      refine ⟨⟨ha_bar j, ?_⟩, hc₁⟩
      rintro (e | e)
      · exact hab j i e
      · exact haa (e : a j = a i).symm
    have hfar₂ : Disjoint V(P (idx (b j))) V(A i) := by
      refine hfar i _ (hidx_inj (hb_X j) (ha_X i) (hab i j).symm) (hidx_inj (hb_X j)
        (hb_X i) hbb.symm) ?_
      rw [hidx _ (hb_X j)]
      refine ⟨⟨hb_bar j, ?_⟩, hc₂⟩
      rintro (e | e)
      · exact hbb e.symm
      · exact hab i j (e : b j = a i).symm
    rw [hVQ i, hVQ j]
    have hout' := hout i _ hrev
    rw [Set.disjoint_union_left] at hout'
    rw [Set.disjoint_left]
    rintro v ((h₁ | h₁) | h₁) ((h₂ | h₂) | h₂)
    · exact Set.disjoint_left.mp (hPdisj _ _ (ha_X i) (ha_X j) haa) (hRaP i h₁) (hRaP j h₂)
    · exact Set.disjoint_left.mp hout'.1 h₁ (hAC j h₂)
    · exact Set.disjoint_left.mp (hPdisj _ _ (ha_X i) (hb_X j) (hab i j)) (hRaP i h₁) (hRbP j h₂)
    · exact Set.disjoint_left.mp hfar₁ (hRaP j h₂) h₁
    · exact Set.disjoint_left.mp (hdisjC hrevne) (hAC j h₂) (hAC i h₁)
    · exact Set.disjoint_left.mp hfar₂ (hRbP j h₂) h₁
    · exact Set.disjoint_left.mp (hPdisj _ _ (hb_X i) (ha_X j) (hab j i).symm)
        (hRbP i h₁) (hRaP j h₂)
    · exact Set.disjoint_left.mp hout'.2 h₁ (hAC j h₂)
    · exact Set.disjoint_left.mp (hPdisj _ _ (hb_X i) (hb_X j) hbb) (hRbP i h₁) (hRbP j h₂)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

end GraphMinor.GM09
