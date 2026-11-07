/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts

/-!
# Scheide Global Maximum Four Free

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideGlobalMaximumFourFree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    4 ≤ (TreeFreeColors phi T).card := by
  classical
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have htree := hglobal.2.1
  have hcounts := ScheideGlobalMaximumMissingCounts G k e0 phi T hglobal
  let X := TreeSequenceVertexSet T
  let D := (G.ends e0).toFinset
  have hDsub : D ⊆ X := by
    intro v hv
    have hv' : v ∈ G.ends e0 := Sym2.mem_toFinset.mp hv
    rw [← T.first_edge] at hv'
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    rw [hi, Sym2.mem_iff] at hv'
    rcases hv' with hv | hv <;> subst v <;>
      simp [X, TreeSequenceVertexSet]
  have hDcard : D.card = 2 := by
    have hn : ¬ (G.ends e0).IsDiag := by
      intro hd
      induction he : G.ends e0 using Sym2.inductionOn with
      | _ a b =>
        rw [he] at hd
        rw [Sym2.mk_isDiag_iff] at hd
        apply G.loopless e0 a
        rw [he, hd]
    exact Sym2.card_toFinset_of_not_isDiag _ hn
  have hDinc : ∀ v ∈ D, Incident G v e0 := by
    intro v hv
    exact Sym2.mem_toFinset.mp hv
  have hdisj : (X : Set V).PairwiseDisjoint (fun v => MissingColors G phi v) := by
    intro u hu v hv huv
    exact horder.2.2.2.1 hu hv huv
  have hnonempty : ∀ v ∈ X, (MissingColors G phi v).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    by_cases hi : Incident G v e0
    · have hh := (hcounts v hv).1 hi |>.2
      omega
    · have hh := (hcounts v hv).2 hi |>.2
      omega
  let firstColor : (v : V) → v ∈ X → Fin k := fun v hv =>
    Classical.choose (hnonempty v hv)
  have firstMem : ∀ (v : V) (hv : v ∈ X), firstColor v hv ∈ MissingColors G phi v := by
    intro v hv
    exact Classical.choose_spec (hnonempty v hv)
  have hsecond : ∀ (v : V) (hv : v ∈ D),
      ((MissingColors G phi v).erase (firstColor v (hDsub hv))).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (firstMem v (hDsub hv))]
    have hh := (hcounts v (hDsub hv)).1 (hDinc v hv) |>.2
    omega
  let extraColor : (v : V) → v ∈ D → Fin k := fun v hv =>
    Classical.choose (hsecond v hv)
  have extraMem : ∀ (v : V) (hv : v ∈ D),
      extraColor v hv ∈ (MissingColors G phi v).erase (firstColor v (hDsub hv)) := by
    intro v hv
    exact Classical.choose_spec (hsecond v hv)
  have hmissing : X.card + 2 ≤ (TreeMissingColors phi T).card := by
    let domain := Sum {v : V // v ∈ X} {v : V // v ∈ D}
    let color : domain → Fin k := fun p => match p with
      | Sum.inl v => firstColor v.1 v.2
      | Sum.inr v => extraColor v.1 v.2
    have hmap : ∀ p : domain, color p ∈ TreeMissingColors phi T := by
      intro p
      rcases p with p | p
      · apply Finset.mem_biUnion.mpr
        exact ⟨p.1, p.2, firstMem p.1 p.2⟩
      · apply Finset.mem_biUnion.mpr
        exact ⟨p.1, hDsub p.2, Finset.mem_erase.mp (extraMem p.1 p.2) |>.2⟩
    have hinj : Function.Injective color := by
      intro p q hpq
      rcases p with p | p <;> rcases q with q | q
      · have hu : p.1 = q.1 := by
          by_contra hn
          have hd := hdisj p.2 q.2 hn
          have hpq' : firstColor p.1 p.2 = firstColor q.1 q.2 := by simpa [color] using hpq
          exact (Finset.disjoint_left.mp hd) (firstMem p.1 p.2)
            (by simpa only [hpq'] using firstMem q.1 q.2)
        have heq : p = q := Subtype.ext hu
        cases heq
        rfl
      · have hu : p.1 = q.1 := by
          by_contra hn
          have hd := hdisj p.2 (hDsub q.2) hn
          have hpq' : firstColor p.1 p.2 = extraColor q.1 q.2 := by simpa [color] using hpq
          exact (Finset.disjoint_left.mp hd) (firstMem p.1 p.2)
            (by simpa only [hpq'] using Finset.mem_erase.mp (extraMem q.1 q.2) |>.2)
        have he := Finset.mem_erase.mp (extraMem q.1 q.2)
        exact False.elim (he.1 (by simpa [color, hu] using hpq.symm))
      · have hu : p.1 = q.1 := by
          by_contra hn
          have hd := hdisj (hDsub p.2) q.2 hn
          have hpq' : extraColor p.1 p.2 = firstColor q.1 q.2 := by simpa [color] using hpq
          exact (Finset.disjoint_left.mp hd) (Finset.mem_erase.mp (extraMem p.1 p.2) |>.2)
            (by simpa only [hpq'] using firstMem q.1 q.2)
        have he := Finset.mem_erase.mp (extraMem p.1 p.2)
        exact False.elim (he.1 (by simpa [color, hu] using hpq))
      · have hu : p.1 = q.1 := by
          by_contra hn
          have hd := hdisj (hDsub p.2) (hDsub q.2) hn
          have hpq' : extraColor p.1 p.2 = extraColor q.1 q.2 := by simpa [color] using hpq
          exact (Finset.disjoint_left.mp hd) (Finset.mem_erase.mp (extraMem p.1 p.2) |>.2)
            (by simpa only [hpq'] using Finset.mem_erase.mp (extraMem q.1 q.2) |>.2)
        have heq : p = q := Subtype.ext hu
        cases heq
        rfl
    let A : Finset domain :=
      X.attach.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        D.attach.map ⟨Sum.inr, Sum.inr_injective⟩
    have hAdisj : Disjoint
        (X.attach.map ⟨Sum.inl, Sum.inl_injective⟩)
        (D.attach.map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have hx := hz1
      have hy := hz2
      rw [Finset.mem_map] at hx hy
      rcases hx with ⟨u, hu, rfl⟩
      rcases hy with ⟨v, hv, h⟩
      cases h
    have hAc : A.card = X.card + 2 := by
      dsimp [A]
      rw [Finset.card_union_of_disjoint hAdisj]
      simp [hDcard]
    have hle : A.card ≤ (TreeMissingColors phi T).card := by
      apply Finset.card_le_card_of_injOn color
      · intro p hp
        exact hmap p
      · exact hinj.injOn
    omega
  have hused : (TreeUsedColors phi T).card ≤ X.card - 2 := by
    let J := (Finset.univ : Finset (Fin T.length)).filter (fun j => 1 ≤ j.val)
    let edgeColor : (j : Fin T.length) → 1 ≤ j.val → Fin k := fun j hj =>
      Classical.choose (htree j hj |>.choose_spec)
    have edgeColor_spec : ∀ (j : Fin T.length) (hj : 1 ≤ j.val),
        phi (T.edge j) = some (edgeColor j hj) := by
      intro j hj
      exact (Classical.choose_spec (htree j hj |>.choose_spec)).1
    let B := J.attach.image (fun j : {j // j ∈ J} => edgeColor j.1 (by exact
        (Finset.mem_filter.mp j.2).2))
    have husedsub : TreeUsedColors phi T ⊆ B := by
      intro c hc
      change c ∈ Finset.univ.filter (fun alpha => ∃ j, 1 ≤ j.val ∧ phi (T.edge j) = some alpha)
          at hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rcases hc with ⟨j, hj, hc⟩
      have hj' : 1 ≤ j.val := hj
      have hm := edgeColor_spec j hj'
      have he : edgeColor j hj' = c := by simpa [hc] using hm.symm
      apply Finset.mem_image.mpr
      exact ⟨⟨j, by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩⟩, by simp [he]⟩
    have hJ : J.card = T.length - 1 := by
      have hje : J = (Finset.univ : Finset (Fin T.length)).erase ⟨0, T.positive⟩ := by
        ext j
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          Finset.mem_univ, true_and, and_true]
        constructor
        · intro hj hz
          subst j
          simp at hj
        · intro hj
          by_contra hz
          apply hj
          apply Fin.ext
          have hz' : j.val = 0 := by omega
          simp [hz']
      rw [hje, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    have hX : X.card = T.length + 1 := by
      dsimp [X, TreeSequenceVertexSet]
      rw [Finset.card_image_iff.mpr (by
        intro a ha b hb hab
        exact T.vertex_injective hab)]
      simp
    have hb : B.card ≤ J.card := by simpa [B] using (Finset.card_image_le : B.card ≤ J.attach.card)
    exact (Finset.card_le_card husedsub).trans (hb.trans_eq hJ) |>.trans_eq (by omega)
  unfold TreeFreeColors
  have hsub : TreeUsedColors phi T ⊆ TreeMissingColors phi T := by
    intro c hc
    change c ∈ Finset.univ.filter (fun alpha => ∃ j, 1 ≤ j.val ∧ phi (T.edge j) = some alpha) at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨j, hj, hc⟩
    obtain ⟨i, d, hd, hdm⟩ := htree j hj
    apply Finset.mem_biUnion.mpr
    refine ⟨T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))), ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · have heq : d = c := Option.some.inj (hd.symm.trans hc)
      simpa [heq] using hdm
  rw [Finset.card_sdiff_of_subset hsub]
  have hX : X.card = T.length + 1 := by
    dsimp [X, TreeSequenceVertexSet]
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb hab
      exact T.vertex_injective hab)]
    simp
  dsimp [X] at hmissing hused ⊢
  omega

end GoldbergSeymour

end
