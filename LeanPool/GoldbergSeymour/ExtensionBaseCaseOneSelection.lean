/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseCaseOneIndices
public import LeanPool.GoldbergSeymour.ExtensionBaseClosure
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass

public import LeanPool.GoldbergSeymour.TreeSequencePrefix

public import LeanPool.GoldbergSeymour.TreeVerticesBefore

/-!
# Extension Base Case One Selection

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_261.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot _ : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (TjPrime : TreeSequence G e0) (_
        : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices :
        Fin (p + (1 : ℕ)) → Fin ett.rounds),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) ↦
        ett.series.data.stored (indices a).succ;
    let candidates : Finset (Fin (TjPrime.length + (1 : ℕ))) := ({i : Fin (TjPrime.length + (1 :
        ℕ)) | TjPrime.vertex i ≠ terminalSupport ∧ (MissingColors G rho1 (TjPrime.vertex i) ∩
        supportColors : Finset (Fin k)).Nonempty} : Finset (Fin (TjPrime.length + (1 : ℕ))));
    ∀ (candidates_nonempty : candidates.Nonempty),
    let first : Fin (TjPrime.length + (1 : ℕ)) := candidates.min' candidates_nonempty;
    let u : V := TjPrime.vertex first; (
    ∀ (i : Fin (TjPrime.length + (1 : ℕ))), (↑i : ℕ) < (↑first : ℕ) → TjPrime.vertex i ≠
        terminalSupport → (MissingColors G rho1 (TjPrime.vertex i) ∩ supportColors : Finset (Fin
        k)).Nonempty → False) →
    ∀ w ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport, (MissingColors G rho1 w ∩
        Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) ↦ ett.series.data.stored (indices a).succ
        : Finset (Fin k)).Nonempty → w = u ∨ TreeVertexOrder TjPrime u w := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q rho1
      TjPrime terminalPosition p indices supportColors candidates candidates_nonempty first u
      first_min w hw hws
  rcases hws with ⟨c, hc⟩
  rcases Finset.mem_inter.mp hc with ⟨hwm, hws⟩
  by_cases hwu : w = u
  · exact Or.inl hwu
  · right
    simp only [TreeSequenceVertexSet, Finset.mem_erase, Finset.mem_image] at hw
    rcases hw.2 with ⟨i, hi, hwi⟩
    have hineq : TjPrime.vertex i ≠ terminalSupport := by
      intro heq
      apply hw.1
      exact hwi.symm.trans heq
    have hsmall : ¬ i.val < first.val := by
      intro hlt
      apply first_min i hlt hineq
      refine ⟨c, ?_⟩
      exact Finset.mem_inter.mpr ⟨hwi.symm ▸ hwm, hws⟩
    have hle : first.val ≤ i.val := Nat.le_of_not_gt hsmall
    have hpos : ∃ j : Fin (TjPrime.length + 1),
        TjPrime.vertex j = u := by
      exact ⟨first, rfl⟩
    rcases hpos with ⟨j, hju⟩
    have hlt : first.val < i.val := by
      by_contra he
      have heq : i.val = first.val := Nat.le_antisymm
        (by omega) hle
      apply hwu
      have hv : TjPrime.vertex i = TjPrime.vertex first := by
        apply congrArg TjPrime.vertex
        apply Fin.ext
        exact heq
      exact hwi.symm.trans (hv.trans rfl)
    exact ⟨first, i, rfl, hwi, hlt⟩

private theorem helper_branch_294.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot _ : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (TjPrime : TreeSequence G e0)
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = terminalSupport →
    ∀ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma delta : Fin (p + (1 : ℕ)) →
        Fin k), (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc) → ColoredVertexSetElementary G
        (ett.series.data.coloring jSlot.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) → (
    ∀ v ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase
        terminalSupport, MissingColors G rho1 v = MissingColors G (ett.series.data.coloring
        jSlot.castSucc) v) → gamma (0 : Fin (p + (1 : ℕ))) ∈ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) terminalSupport → (
    ∀ (a : Fin (p + (1 : ℕ))), delta a ∉ TreeMissingColors (ett.series.data.coloring
        jSlot.castSucc) (ett.series.data.tree jSlot.succ.castSucc)) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) ↦
        ett.series.data.stored (indices a).succ;
    let candidates : Finset (Fin (TjPrime.length + (1 : ℕ))) := ({i : Fin (TjPrime.length + (1 :
        ℕ)) | TjPrime.vertex i ≠ terminalSupport ∧ (MissingColors G rho1 (TjPrime.vertex i) ∩
        supportColors : Finset (Fin k)).Nonempty} : Finset (Fin (TjPrime.length + (1 : ℕ))));
    ∀ (candidates_nonempty : candidates.Nonempty),
    let first : Fin (TjPrime.length + (1 : ℕ)) := candidates.min' candidates_nonempty;
    let u : V := TjPrime.vertex first; u ≠ terminalSupport →
    ∀ (gamma_exists :
    ∃ (a : Fin (p + (1 : ℕ))), gamma a ∈ MissingColors G rho1 u),
    let b : Fin (p + (1 : ℕ)) := ({a : Fin (p + (1 : ℕ)) | gamma a ∈ MissingColors G rho1 u} :
        Finset (Fin (p + (1 : ℕ)))).min' (Exists.casesOn gamma_exists fun (a : Fin (p + (1 : ℕ)))
        (ha : gamma a ∈ MissingColors G rho1 u) ↦ Exists.intro a (Finset.mem_filter.mpr
        (⟨Finset.mem_univ a, ha⟩ : a ∈ Finset.univ ∧ gamma a ∈ MissingColors G rho1 u))); gamma b
        ∈ MissingColors G rho1 u → u ∉ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q rho1
      TjPrime terminalPosition hterminalAt p indices gamma delta hchain hTjElementary
      hrhoAgreement hfirstGammaMissing hdeltaAvoidsTj supportColors candidates
      candidates_nonempty first u hu_ne gamma_exists b hbmem huTj
  have terminal_tj : terminalSupport ∈
      TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) := by
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    exact ⟨terminalPosition, Finset.mem_univ _, hterminalAt⟩
  have huErase : u ∈
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)).erase terminalSupport := by
    apply Finset.mem_erase.mpr
    exact ⟨hu_ne, huTj⟩
  have agreement := hrhoAgreement u huErase
  by_cases hbzero : b.val = 0
  · have hb : b = 0 := Fin.ext hbzero
    rw [hb] at hbmem
    have hdis := hTjElementary huTj terminal_tj hu_ne
    have hnot : gamma 0 ∉ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) u := by
      intro hm
      exact (Finset.disjoint_left.1 hdis) hm hfirstGammaMissing
    apply hnot
    rw [← agreement]
    exact hbmem
  · have hbpos : 1 ≤ b.val := Nat.one_le_iff_ne_zero.mpr hbzero
    obtain ⟨t, ht⟩ : ∃ t : Fin p, b = t.succ := by
      have hp : 0 < p := by omega
      refine ⟨⟨b.val - 1, ?_⟩, ?_⟩
      · have := b.isLt
        omega
      · apply Fin.ext
        simpa using (Nat.sub_add_cancel hbpos).symm
    have hdelta : delta t.castSucc ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
          (ett.series.data.tree jSlot.succ.castSucc) := hdeltaAvoidsTj t.castSucc
    have hnot : delta t.castSucc ∉ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) u := by
      intro hm
      apply hdelta
      rw [TreeMissingColors]
      apply Finset.mem_biUnion.mpr
      exact ⟨u, huTj, hm⟩
    have hgammaeq : gamma b = delta t.castSucc := by
      rw [ht]
      exact hchain t
    apply hnot
    rw [← hgammaeq, ← agreement]
    exact hbmem

private theorem helper_branch_370.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot _ : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (TjPrime : TreeSequence G e0) (_
        : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices :
        Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma delta : Fin (p + (1 : ℕ)) → Fin k), (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.stored (indices a).succ = (insert (gamma a)
        ({delta a} : Finset (Fin k)) : Finset (Fin k))) → (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc) → Function.Injective (Fin.cons (gamma (0 : Fin
        (p + (1 : ℕ)))) delta) → (MissingColors G rho1 terminalSupport ∩ Finset.univ.biUnion fun
        (a : Fin (p + (1 : ℕ))) ↦ ett.series.data.stored (indices a).succ : Finset (Fin k)) =
        ({delta (Fin.last p)} : Finset (Fin k)) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) ↦
        ett.series.data.stored (indices a).succ;
    let candidates : Finset (Fin (TjPrime.length + (1 : ℕ))) := ({i : Fin (TjPrime.length + (1 :
        ℕ)) | TjPrime.vertex i ≠ terminalSupport ∧ (MissingColors G rho1 (TjPrime.vertex i) ∩
        supportColors : Finset (Fin k)).Nonempty} : Finset (Fin (TjPrime.length + (1 : ℕ))));
    ∀ (candidates_nonempty : candidates.Nonempty),
    let first : Fin (TjPrime.length + (1 : ℕ)) := candidates.min' candidates_nonempty;
    let u : V := TjPrime.vertex first;
    ∀ (gamma_exists :
    ∃ (a : Fin (p + (1 : ℕ))), gamma a ∈ MissingColors G rho1 u),
    let b : Fin (p + (1 : ℕ)) := ({a : Fin (p + (1 : ℕ)) | gamma a ∈ MissingColors G rho1 u} :
        Finset (Fin (p + (1 : ℕ)))).min' (Exists.casesOn gamma_exists fun (a : Fin (p + (1 : ℕ)))
        (ha : gamma a ∈ MissingColors G rho1 u) ↦ Exists.intro a (Finset.mem_filter.mpr
        (⟨Finset.mem_univ a, ha⟩ : a ∈ Finset.univ ∧ gamma a ∈ MissingColors G rho1 u))); (delta
        (Fin.last p) ∉ (ExtensionBaseCaseOneIndices ett p indices b).biUnion fun (t : Fin
        ett.rounds) ↦ ett.series.data.stored t.succ) ∧ (MissingColors G rho1 terminalSupport ∩
        (ExtensionBaseCaseOneIndices ett p indices b).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ : Finset (Fin k)) = ∅ := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q rho1
      TjPrime terminalPosition p indices gamma delta hstored hchain hdistinct
      hterminalIntersection supportColors candidates candidates_nonempty first u gamma_exists b
  have delta_not_prefix : delta (Fin.last p) ∉
      (ExtensionBaseCaseOneIndices ett p indices b).biUnion
        (fun t => ett.series.data.stored t.succ) := by
    intro hd
    rw [ExtensionBaseCaseOneIndices] at hd
    rcases Finset.mem_biUnion.mp hd with ⟨t, ht, hdt⟩
    rcases Finset.mem_image.mp ht with ⟨a, ha, hat⟩
    have hab : a.val < b.val := (Finset.mem_filter.mp ha).2
    rw [← hat, hstored a] at hdt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdt
    rcases hdt with hdt | hdt
    · cases a using Fin.cases with
      | zero =>
        have hv : (Fin.last p).succ ≠ (0 : Fin (p + 1 + 1)) := by
          intro he
          have := congrArg Fin.val he
          simp at this
        exact hv (hdistinct (by simpa using hdt))
      | succ t =>
        have hb_le : b.val ≤ p := by omega
        have hv : (Fin.last p).succ ≠ (t.castSucc).succ := by
          intro he
          have hh := congrArg Fin.val he
          simp at hh
          have ht_lt : t.val < p := by omega
          have hab' : t.val + 1 < b.val := by simpa using hab
          omega
        exact hv (hdistinct (by
          simpa only [Fin.cons_succ] using hdt.trans (hchain t)))
    · by_cases ha0 : a.val = 0
      · have hne : (Fin.last p).succ ≠
            (0 : Fin (p + 1)).succ := by
          intro he
          have hv := congrArg Fin.val he
          simp at hv
          omega
        have ha' : a = (0 : Fin (p + 1)) := Fin.ext ha0
        exact hne (hdistinct (by simpa [ha'] using hdt))
      · obtain ⟨t, hta⟩ : ∃ t : Fin p, a = t.succ := by
          refine ⟨⟨a.val - 1, ?_⟩, ?_⟩
          · have := a.isLt
            omega
          · apply Fin.ext
            have := a.isLt
            have ha' : 1 ≤ a.val := Nat.one_le_iff_ne_zero.mpr ha0
            simpa using (Nat.sub_add_cancel ha').symm
        rw [hta] at hdt
        have hne : (Fin.last p).succ ≠
            (t.succ.succ : Fin (p + 1 + 1)) := by
          intro he
          have hv := congrArg Fin.val he
          simp at hv
          have hb_le : b.val ≤ p := by omega
          have ht_lt : t.val < p := by omega
          have hab' : t.val + 1 < b.val := by simpa [hta] using hab
          omega
        exact hne (hdistinct (by simpa [hta] using hdt))
  refine ⟨delta_not_prefix, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  rcases Finset.mem_inter.mp hd with ⟨hdm, hdp⟩
  have hds : d ∈ supportColors := by
    have : (ExtensionBaseCaseOneIndices ett p indices b).biUnion
        (fun t => ett.series.data.stored t.succ) ⊆ supportColors := by
      intro c hc
      rcases Finset.mem_biUnion.mp hc with ⟨t, ht, hct⟩
      rw [ExtensionBaseCaseOneIndices] at ht
      rcases Finset.mem_image.mp ht with ⟨a, ha, hat⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_univ _, by simpa [hat] using hct⟩
    exact this hdp
  have hi : d ∈ MissingColors G rho1 terminalSupport ∩ supportColors :=
    Finset.mem_inter.mpr ⟨hdm, hds⟩
  have hsingle := hterminalIntersection ▸ hi
  have heq : d = delta (Fin.last p) := by simpa using hsingle
  exact delta_not_prefix (heq ▸ hdp)

theorem ExtensionBaseCaseOneSelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (_ : jSlot.val ≤ q.val)
    (_ : q.val + 1 = ett.rounds)
    (_ : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (rho1 : PartialEdgeColoring E k)
    (seed TjPrime : TreeSequence G e0)
    (terminalPosition : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1))
    (hterminalAt :
      (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition =
        terminalSupport)
    (hterminalPositionPositive : 1 ≤ terminalPosition.val)
    (hseed : seed = TreeSequencePrefix
      (ett.series.data.tree jSlot.succ.castSucc) terminalPosition.val
      hterminalPositionPositive (Nat.le_of_lt_succ terminalPosition.isLt))
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (_ : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k)
    (_ : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (_ : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = r)
    (_ : indices (Fin.last p) = q)
    (_ : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (_ : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hcase :
      (((TreeSequenceVertexSet TjPrime).erase terminalSupport).biUnion
          (fun v => MissingColors G rho1 v) ∩
        (Finset.univ.biUnion fun a : Fin (p + 1) =>
          ett.series.data.stored (indices a).succ)).Nonempty)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hterminalIntersection :
      MissingColors G rho1 terminalSupport ∩
          (Finset.univ.biUnion fun a : Fin (p + 1) =>
            ett.series.data.stored (indices a).succ) =
        {delta (Fin.last p)})
    (hTjElementary : ColoredVertexSetElementary G
      (ett.series.data.coloring jSlot.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)))
    (hrhoAgreement : ∀ v : V,
      v ∈ (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)).erase
            terminalSupport →
      MissingColors G rho1 v = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v)
    (hfirstGammaMissing : gamma 0 ∈ MissingColors G
      (ett.series.data.coloring jSlot.castSucc) terminalSupport)
    (hdeltaAvoidsTj : ∀ a : Fin (p + 1),
      delta a ∉ TreeMissingColors
        (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc)) :
    ∃ (u : V) (hu : u ∈ TreeSequenceVertexSet TjPrime) (b : Fin (p + 1)),
    u ≠ terminalSupport ∧
      gamma b ∈ MissingColors G rho1 u ∧
        (∀ a : Fin (p + 1), a.val < b.val → gamma a ∉ MissingColors G rho1 u) ∧
          (∀ w : V,
              w ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
                (MissingColors G rho1 w ∩
                      (Finset.univ.biUnion fun a : Fin (p + 1) =>
                        ett.series.data.stored (indices a).succ)).Nonempty →
                  w = u ∨ TreeVertexOrder TjPrime u w) ∧
            u ∉ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧
              (let supportColors :=
                Finset.univ.biUnion fun a : Fin (p + 1) =>
                  ett.series.data.stored (indices a).succ
              let prefixColors :=
                (ExtensionBaseCaseOneIndices ett p indices b).biUnion fun t =>
                  ett.series.data.stored t.succ
              ((TreeVerticesBefore TjPrime u hu).biUnion (fun v => MissingColors G rho1 v) ∩
                    (supportColors \ {delta (Fin.last p)}) =
                  ∅) ∧
                delta (Fin.last p) ∉ prefixColors ∧
                  MissingColors G rho1 terminalSupport ∩ prefixColors = ∅) := by
  classical
  have initial_subset {A B : TreeSequence G e0}
      (h : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := h
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have reach_subset {A B : TreeSequence G e0}
      (h : TashkinovAugmentationSequence rho1 A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    unfold TashkinovAugmentationSequence at h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Finset.Subset.rfl
    | head hstep htail ih => exact (initial_subset hstep.2.1).trans ih
  have seed_prime : TreeSequenceVertexSet seed ⊆
      TreeSequenceVertexSet TjPrime := reach_subset hclosure.1
  have terminal_seed : terminalSupport ∈ TreeSequenceVertexSet seed := by
    rw [hseed]
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨Fin.last terminalPosition.val, Finset.mem_univ _, ?_⟩
    change (ett.series.data.tree jSlot.succ.castSucc).vertex
        (Fin.castLE (Nat.succ_le_succ
          (Nat.le_of_lt_succ terminalPosition.isLt))
          (Fin.last terminalPosition.val)) = terminalSupport
    have heq : Fin.castLE (Nat.succ_le_succ
        (Nat.le_of_lt_succ terminalPosition.isLt))
        (Fin.last terminalPosition.val) = terminalPosition := by
      apply Fin.ext
      simp
    rw [heq]
    exact hterminalAt
  have terminal_prime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    seed_prime terminal_seed
  let supportColors := Finset.univ.biUnion fun a : Fin (p + 1) =>
    ett.series.data.stored (indices a).succ
  let candidates := (Finset.univ : Finset (Fin (TjPrime.length + 1))).filter
    (fun i => TjPrime.vertex i ≠ terminalSupport ∧
      (MissingColors G rho1 (TjPrime.vertex i) ∩ supportColors).Nonempty)
  have candidates_nonempty : candidates.Nonempty := by
    have hcase' : (((TreeSequenceVertexSet TjPrime).erase terminalSupport).biUnion
          (fun v => MissingColors G rho1 v) ∩ supportColors).Nonempty := by
      simpa [supportColors] using hcase
    rcases hcase' with ⟨c, hc⟩
    rcases Finset.mem_inter.mp hc with ⟨hcaway, hcsupport⟩
    rcases Finset.mem_biUnion.mp hcaway with ⟨v, hv, hcv⟩
    simp only [Finset.mem_erase] at hv
    rcases hv with ⟨hvt, hvprime⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hvprime
    rcases hvprime with ⟨i, hi, hvi⟩
    have hmem : i ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro heq
        apply hvt
        rw [← hvi, heq]
      · exact ⟨c, Finset.mem_inter.mpr ⟨hvi.symm ▸ hcv, hcsupport⟩⟩
    exact ⟨i, hmem⟩
  let first := candidates.min' candidates_nonempty
  have first_mem : first ∈ candidates :=
    Finset.min'_mem candidates candidates_nonempty
  let u := TjPrime.vertex first
  have huprime : u ∈ TreeSequenceVertexSet TjPrime := by
    simp [TreeSequenceVertexSet, u]
  have hu_ne : u ≠ terminalSupport :=
    (Finset.mem_filter.mp first_mem).2.1
  have hu_support : (MissingColors G rho1 u ∩ supportColors).Nonempty := by
    simpa [u] using (Finset.mem_filter.mp first_mem).2.2
  have first_min (i : Fin (TjPrime.length + 1))
      (hi : i.val < first.val)
      (hineq : TjPrime.vertex i ≠ terminalSupport)
      (hs : (MissingColors G rho1 (TjPrime.vertex i) ∩ supportColors).Nonempty) :
      False := by
    have hm : i ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hineq, hs⟩
    exact (Nat.not_lt_of_ge (Finset.min'_le candidates i hm)) hi
  have support_mem : ∀ c ∈ supportColors,
      ∃ a : Fin (p + 1), c = gamma a ∨ c = delta a := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨a, ha, hca⟩
    rw [hstored a] at hca
    simp only [Finset.mem_insert, Finset.mem_singleton] at hca
    exact ⟨a, hca⟩
  have delta_terminal : delta (Fin.last p) ∈ MissingColors G rho1 terminalSupport := by
    have hd : delta (Fin.last p) ∈ supportColors := by
      apply Finset.mem_biUnion.mpr
      exact ⟨Fin.last p, Finset.mem_univ _, by rw [hstored]; simp⟩
    have hi : delta (Fin.last p) ∈
        MissingColors G rho1 terminalSupport ∩ supportColors := by
      rw [hterminalIntersection]
      simp
    exact (Finset.mem_inter.mp hi).1
  have delta_not_u : delta (Fin.last p) ∉ MissingColors G rho1 u := by
    intro hd
    have hd' : delta (Fin.last p) ∈ MissingColors G rho1 terminalSupport := delta_terminal
    have hdis := hprimeElementary huprime terminal_prime hu_ne
    exact (Finset.disjoint_left.1 hdis) hd hd'
  have gamma_exists : ∃ a : Fin (p + 1), gamma a ∈ MissingColors G rho1 u := by
    rcases hu_support with ⟨c, hc⟩
    rcases Finset.mem_inter.mp hc with ⟨hc, hcs⟩
    rcases support_mem c hcs with ⟨a, rfl | rfl⟩
    · exact ⟨a, hc⟩
    · by_cases ha : a = Fin.last p
      · exact (delta_not_u (ha ▸ hc)).elim
      · obtain ⟨t, ht⟩ : ∃ t : Fin p, a = t.castSucc := by
          have hav : a.val < p := by
            have := a.isLt
            have hlast : a.val ≠ p := by intro h; exact ha (Fin.ext h)
            omega
          exact ⟨⟨a.val, hav⟩, by apply Fin.ext; rfl⟩
        refine ⟨t.succ, ?_⟩
        rw [hchain t, ← ht]
        exact hc
  let b := (Finset.univ.filter fun a : Fin (p + 1) =>
    gamma a ∈ MissingColors G rho1 u).min'
      (by rcases gamma_exists with ⟨a, ha⟩; exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ha⟩⟩)
  have hbmem : gamma b ∈ MissingColors G rho1 u := by
    have := Finset.min'_mem (Finset.univ.filter fun a : Fin (p + 1) =>
      gamma a ∈ MissingColors G rho1 u) (by
        rcases gamma_exists with ⟨a, ha⟩
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩)
    exact (Finset.mem_filter.mp this).2
  refine ⟨u, huprime, b, hu_ne, hbmem, ?_, ?_, ?_, ?_⟩
  · intro a ha hga
    have hm := Finset.min'_le (Finset.univ.filter fun z : Fin (p + 1) =>
      gamma z ∈ MissingColors G rho1 u) a
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hga⟩)
    exact (Nat.not_lt_of_ge hm) ha
  · exact @helper_branch_261 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport)
      (@jSlot) (@q) (@rho1) (@TjPrime) (@terminalPosition) (@p) (@indices) (@candidates_nonempty)
      (@first_min)
  · exact @helper_branch_294 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport)
      (@jSlot) (@q) (@rho1) (@TjPrime) (@terminalPosition) (@hterminalAt) (@p) (@indices)
      (@gamma) (@delta) (@hchain) (@hTjElementary) (@hrhoAgreement) (@hfirstGammaMissing)
      (@hdeltaAvoidsTj) (@candidates_nonempty) (@hu_ne) (@gamma_exists) (@hbmem)
  · dsimp
    constructor
    · rw [Finset.eq_empty_iff_forall_notMem]
      intro d hd
      rcases Finset.mem_inter.mp hd with ⟨hbefore, hcolor⟩
      rcases Finset.mem_biUnion.mp hbefore with ⟨x, hx, hdx⟩
      simp only [TreeVerticesBefore, Finset.mem_filter] at hx
      rcases hx with ⟨hxset, hxorder⟩
      rcases hxorder with ⟨i, j, hix, hjx, hij⟩
      have hju : j = first := by
        apply TjPrime.vertex_injective
        exact hjx.trans rfl
      subst j
      have hnotterminal : x ≠ terminalSupport := by
        intro heq
        have hdt : d ∈ MissingColors G rho1 terminalSupport := by
          rw [← heq]
          exact hdx
        have hds : d ∈ supportColors :=
          (Finset.mem_sdiff.mp hcolor).1
        have hi : d ∈ MissingColors G rho1 terminalSupport ∩ supportColors :=
          Finset.mem_inter.mpr ⟨hdt, hds⟩
        have hsingle := hterminalIntersection ▸ hi
        have : d = delta (Fin.last p) := by simpa using hsingle
        exact (Finset.mem_sdiff.mp hcolor).2 (by simp [this])
      have hlt : i.val < first.val := hij
      have hcontra : False := first_min i hlt (hix.symm ▸ hnotterminal) (by
        refine ⟨d, Finset.mem_inter.mpr ⟨?_, (Finset.mem_sdiff.mp hcolor).1⟩⟩
        exact hix.symm ▸ hdx)
      exact hcontra
    · exact @helper_branch_370 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport)
        (@jSlot) (@q) (@rho1) (@TjPrime) (@terminalPosition) (@p) (@indices) (@gamma) (@delta)
        (@hstored) (@hchain) (@hdistinct) (@hterminalIntersection) (@candidates_nonempty)
        (@gamma_exists)
end GoldbergSeymour

end
