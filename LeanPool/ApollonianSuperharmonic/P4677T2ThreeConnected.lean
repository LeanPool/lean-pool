/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4677T2IncidenceLedger
public import LeanPool.ApollonianSuperharmonic.P3161T1BlockTreeReachability

-- [TABLET NODE: P4677T2ThreeConnected]

/-!
# P4677T2ThreeConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ThreeConnectivityProof

private theorem chain :
    (by
      classical
      exact
        let linkList : PeriodicSubtileIndex → List PeriodicSubtileIndex := fun z =>
        match z with
        | ⟨.A,m,n⟩ =>
        [⟨.B,m,n⟩, ⟨.D,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m+1,n+1⟩,
        ⟨.E,m,n+1⟩, ⟨.B,m,n+1⟩, ⟨.F,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.B,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.D,m-1,n-1⟩, ⟨.F,m,n-1⟩, ⟨.A,m,n-1⟩,
        ⟨.E,m,n⟩, ⟨.D,m,n⟩, ⟨.A,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.C,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.A,m,n⟩, ⟨.F,m,n⟩,
        ⟨.D,m-1,n⟩, ⟨.E,m-1,n⟩]
        | ⟨.D,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n⟩, ⟨.E,m,n⟩, ⟨.C,m+1,n⟩,
        ⟨.F,m+1,n⟩, ⟨.B,m+1,n+1⟩]
        | ⟨.E,m,n⟩ =>
        [⟨.A,m,n-1⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩, ⟨.B,m,n⟩]
        | ⟨.F,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.D,m-1,n⟩, ⟨.C,m,n⟩]
        let Chain := List.IsChain AllowedSubtileIncidence
        ∀ (z : PeriodicSubtileIndex), Chain (linkList z) ) := by
  classical
  intro linkList Chain z
  cases z with
  | mk l m n =>
    cases l
    · simp only [Chain, linkList, List.isChain_cons_cons]
      refine ⟨.BD m n, ?_⟩
      refine ⟨by simpa [sub_add_cancel, add_sub_cancel_right] using
        (AllowedSubtileIncidence.BDm1m1 (m+1) (n+1)).symm, ?_⟩
      refine ⟨.BC (m+1) (n+1), ?_⟩
      refine ⟨by simpa [sub_add_cancel] using
        (AllowedSubtileIncidence.CEm10 (m+1) (n+1)), ?_⟩
      refine ⟨(AllowedSubtileIncidence.BE m (n+1)).symm, ?_⟩
      refine ⟨by simpa [add_sub_cancel_right] using
        (AllowedSubtileIncidence.BF0m1 m (n+1)), ?_⟩
      refine ⟨(AllowedSubtileIncidence.CF m n).symm, ?_⟩
      exact .singleton _
    · simp only [Chain, linkList, List.isChain_cons_cons]
      refine ⟨.AD (m-1) (n-1), ?_⟩
      refine ⟨by simpa [add_sub_cancel_right] using
        (AllowedSubtileIncidence.DF10 (m-1) (n-1)), ?_⟩
      refine ⟨(AllowedSubtileIncidence.AF m (n-1)).symm, ?_⟩
      refine ⟨by simpa [sub_add_cancel] using
        (AllowedSubtileIncidence.AE01 m (n-1)), ?_⟩
      refine ⟨(AllowedSubtileIncidence.DE m n).symm, ?_⟩
      refine ⟨(AllowedSubtileIncidence.AD m n).symm, ?_⟩
      refine ⟨AllowedSubtileIncidence.AC m n, ?_⟩
      exact .singleton _
    · simp only [Chain, linkList, List.isChain_cons_cons]
      refine ⟨by simpa [sub_add_cancel] using
        (AllowedSubtileIncidence.AB11 (m-1) (n-1)), ?_⟩
      refine ⟨(AllowedSubtileIncidence.AB m n).symm, ?_⟩
      refine ⟨.AF m n, ?_⟩
      refine ⟨by simpa [sub_add_cancel] using
        (AllowedSubtileIncidence.DF10 (m-1) n).symm, ?_⟩
      refine ⟨.DE (m-1) n, ?_⟩
      exact .singleton _
    · simp only [Chain, linkList, List.isChain_cons_cons]
      refine ⟨.AB m n, ?_⟩
      refine ⟨AllowedSubtileIncidence.BE m n, ?_⟩
      refine ⟨by simpa [add_sub_cancel_right] using
        (AllowedSubtileIncidence.CEm10 (m+1) n).symm, ?_⟩
      refine ⟨AllowedSubtileIncidence.CF (m+1) n, ?_⟩
      refine ⟨by simpa [add_sub_cancel_right] using
        (AllowedSubtileIncidence.BF0m1 (m+1) (n+1)).symm, ?_⟩
      exact .singleton _
    · simp only [Chain, linkList, List.isChain_cons_cons]
      refine ⟨by simpa [sub_add_cancel] using
        (AllowedSubtileIncidence.AC11 m (n-1)), ?_⟩
      refine ⟨by simpa [add_sub_cancel_right] using
        (AllowedSubtileIncidence.CDm10 (m+1) n), ?_⟩
      refine ⟨(AllowedSubtileIncidence.BD m n).symm, ?_⟩
      exact .singleton _
    · simp only [Chain, linkList, List.isChain_cons_cons]
      refine ⟨.AB01 m n, ?_⟩
      refine ⟨by simpa [add_sub_cancel_right] using
        (AllowedSubtileIncidence.BDm1m1 m (n+1)), ?_⟩
      refine ⟨(AllowedSubtileIncidence.CDm10 m n).symm, ?_⟩
      exact .singleton _

private theorem adjacent :
    (by
      classical
      exact
        let linkList : PeriodicSubtileIndex → List PeriodicSubtileIndex := fun z =>
        match z with
        | ⟨.A,m,n⟩ =>
        [⟨.B,m,n⟩, ⟨.D,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m+1,n+1⟩,
        ⟨.E,m,n+1⟩, ⟨.B,m,n+1⟩, ⟨.F,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.B,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.D,m-1,n-1⟩, ⟨.F,m,n-1⟩, ⟨.A,m,n-1⟩,
        ⟨.E,m,n⟩, ⟨.D,m,n⟩, ⟨.A,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.C,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.A,m,n⟩, ⟨.F,m,n⟩,
        ⟨.D,m-1,n⟩, ⟨.E,m-1,n⟩]
        | ⟨.D,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n⟩, ⟨.E,m,n⟩, ⟨.C,m+1,n⟩,
        ⟨.F,m+1,n⟩, ⟨.B,m+1,n+1⟩]
        | ⟨.E,m,n⟩ =>
        [⟨.A,m,n-1⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩, ⟨.B,m,n⟩]
        | ⟨.F,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.D,m-1,n⟩, ⟨.C,m,n⟩]
        ∀ (z : PeriodicSubtileIndex), ∀ (u : PeriodicSubtileIndex), u ∈ linkList z →
        AllowedSubtileIncidence z u ) := by
  classical
  intro linkList z
  cases z with
  | mk l m n =>
    cases l
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, linkList] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact .AB m n
      · exact .AD m n
      · exact .AB11 m n
      · exact .AC11 m n
      · exact .AE01 m n
      · exact .AB01 m n
      · exact .AF m n
      · exact .AC m n
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, linkList] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [sub_add_cancel] using (AllowedSubtileIncidence.AB11 (m-1) (n-1)).symm
      · exact AllowedSubtileIncidence.BDm1m1 m n
      · exact .BF0m1 m n
      · simpa [sub_add_cancel] using (AllowedSubtileIncidence.AB01 m (n-1)).symm
      · exact .BE m n
      · exact .BD m n
      · exact (AllowedSubtileIncidence.AB m n).symm
      · exact .BC m n
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, linkList] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [sub_add_cancel] using (AllowedSubtileIncidence.AC11 (m-1) (n-1)).symm
      · exact (AllowedSubtileIncidence.BC m n).symm
      · exact (AllowedSubtileIncidence.AC m n).symm
      · exact AllowedSubtileIncidence.CF m n
      · exact AllowedSubtileIncidence.CDm10 m n
      · exact AllowedSubtileIncidence.CEm10 m n
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, linkList] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (AllowedSubtileIncidence.AD m n).symm
      · exact (AllowedSubtileIncidence.BD m n).symm
      · exact AllowedSubtileIncidence.DE m n
      · simpa [add_sub_cancel_right] using (AllowedSubtileIncidence.CDm10 (m+1) n).symm
      · exact AllowedSubtileIncidence.DF10 m n
      · simpa [add_sub_cancel_right] using
          (AllowedSubtileIncidence.BDm1m1 (m+1) (n+1)).symm
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, linkList] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · simpa [sub_add_cancel] using (AllowedSubtileIncidence.AE01 m (n-1)).symm
      · simpa [add_sub_cancel_right] using (AllowedSubtileIncidence.CEm10 (m+1) n).symm
      · exact (AllowedSubtileIncidence.DE m n).symm
      · exact (AllowedSubtileIncidence.BE m n).symm
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, linkList] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact (AllowedSubtileIncidence.AF m n).symm
      · simpa [add_sub_cancel_right] using (AllowedSubtileIncidence.BF0m1 m (n+1)).symm
      · simpa [sub_add_cancel] using (AllowedSubtileIncidence.DF10 (m-1) n).symm
      · exact (AllowedSubtileIncidence.CF m n).symm

private theorem edge_mem_link :
    (by
      classical
      exact
        let linkList : PeriodicSubtileIndex → List PeriodicSubtileIndex := fun z =>
        match z with
        | ⟨.A,m,n⟩ =>
        [⟨.B,m,n⟩, ⟨.D,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m+1,n+1⟩,
        ⟨.E,m,n+1⟩, ⟨.B,m,n+1⟩, ⟨.F,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.B,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.D,m-1,n-1⟩, ⟨.F,m,n-1⟩, ⟨.A,m,n-1⟩,
        ⟨.E,m,n⟩, ⟨.D,m,n⟩, ⟨.A,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.C,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.A,m,n⟩, ⟨.F,m,n⟩,
        ⟨.D,m-1,n⟩, ⟨.E,m-1,n⟩]
        | ⟨.D,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n⟩, ⟨.E,m,n⟩, ⟨.C,m+1,n⟩,
        ⟨.F,m+1,n⟩, ⟨.B,m+1,n+1⟩]
        | ⟨.E,m,n⟩ =>
        [⟨.A,m,n-1⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩, ⟨.B,m,n⟩]
        | ⟨.F,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.D,m-1,n⟩, ⟨.C,m,n⟩]
        ∀ {z : PeriodicSubtileIndex}, ∀ {u : PeriodicSubtileIndex}, AllowedSubtileIncidence z u →
            u ∈
        linkList z ∧ z ∈ linkList u ) := by
  classical
  intro linkList z u h
  induction h with
  | AB m n => simp [linkList]
  | AB01 m n => simp [linkList]
  | AB11 m n => simp [linkList]
  | AC m n => simp [linkList]
  | AC11 m n => simp [linkList]
  | AD m n => simp [linkList]
  | AE01 m n => simp [linkList]
  | AF m n => simp [linkList]
  | BC m n => simp [linkList]
  | BDm1m1 m n => simp [linkList]
  | BD m n => simp [linkList]
  | BE m n => simp [linkList]
  | BF0m1 m n => simp [linkList]
  | CDm10 m n => simp [linkList]
  | CEm10 m n => simp [linkList]
  | CF m n => simp [linkList]
  | DE m n => simp [linkList]
  | DF10 m n => simp [linkList]
  | symm _ ih => exact ⟨ih.2, ih.1⟩

private theorem wrap :
    (by
      classical
      exact
        let linkList : PeriodicSubtileIndex → List PeriodicSubtileIndex := fun z =>
        match z with
        | ⟨.A,m,n⟩ =>
        [⟨.B,m,n⟩, ⟨.D,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m+1,n+1⟩,
        ⟨.E,m,n+1⟩, ⟨.B,m,n+1⟩, ⟨.F,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.B,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.D,m-1,n-1⟩, ⟨.F,m,n-1⟩, ⟨.A,m,n-1⟩,
        ⟨.E,m,n⟩, ⟨.D,m,n⟩, ⟨.A,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.C,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.A,m,n⟩, ⟨.F,m,n⟩,
        ⟨.D,m-1,n⟩, ⟨.E,m-1,n⟩]
        | ⟨.D,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n⟩, ⟨.E,m,n⟩, ⟨.C,m+1,n⟩,
        ⟨.F,m+1,n⟩, ⟨.B,m+1,n+1⟩]
        | ⟨.E,m,n⟩ =>
        [⟨.A,m,n-1⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩, ⟨.B,m,n⟩]
        | ⟨.F,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.D,m-1,n⟩, ⟨.C,m,n⟩]
        ∀ (nonempty : ∀ (z : PeriodicSubtileIndex), linkList z ≠ []), ∀ (z :
            PeriodicSubtileIndex), AllowedSubtileIncidence ((linkList z).getLast (nonempty z))
            ((linkList z).head (nonempty
        z)) ) := by
  classical
  intro linkList nonempty z
  cases z with
  | mk l m n =>
    cases l
    · simpa [linkList] using (AllowedSubtileIncidence.BC m n).symm
    · simpa [linkList, sub_add_cancel, add_sub_cancel_right] using
        (AllowedSubtileIncidence.AC11 (m-1) (n-1)).symm
    · simpa [linkList, sub_add_cancel, add_sub_cancel_right] using
        (AllowedSubtileIncidence.AE01 (m-1) (n-1)).symm
    · simpa [linkList, sub_add_cancel, add_sub_cancel_right] using
        (AllowedSubtileIncidence.AB11 m n).symm
    · simpa [linkList, sub_add_cancel] using
        (AllowedSubtileIncidence.AB01 m (n-1)).symm
    · simpa [linkList] using (AllowedSubtileIncidence.AC m n).symm

private theorem cut_chain :
    (by
      classical
      exact
        let Chain := List.IsChain AllowedSubtileIncidence
        ∀ {p : List PeriodicSubtileIndex}, ∀ {k : PeriodicSubtileIndex}, Chain p → ∀ (hne : p ≠
            []), AllowedSubtileIncidence (p.getLast hne) (p.head hne) → k ∈ p → Chain (List.drop
        (List.idxOf k p + (1 : ℕ)) p ++ List.take (List.idxOf k p) p) ) := by
  classical
  intro Chain p k hp hne hw hk
  let i := p.idxOf k
  change Chain (p.drop (i + 1) ++ p.take i)
  have hdchain := hp.drop (i + 1)
  have htchain := hp.take i
  by_cases ht : p.take i = []
  · have hi : i = 0 := by
      have hh : i = 0 ∨ p = [] := by simpa [List.take_eq_nil_iff] using ht
      rcases hh with h | h
      · exact h
      · exact (hne h).elim
    rw [hi] at hdchain
    simpa [hi, List.drop] using hdchain
  · by_cases hd : p.drop (i + 1) = []
    · simp only [hd, List.nil_append]
      exact htchain
    · apply List.IsChain.append hdchain htchain
      intro x hx y hy
      have hxv : x = (p.drop (i+1)).getLast hd := by
        have hq := List.getLast?_eq_getLast_of_ne_nil hd
        simp only [hq, Option.mem_def] at hx
        exact Option.some.inj hx.symm
      have hyv : y = (p.take i).head ht := by
        have hq := List.head?_eq_some_head ht
        simp only [hq, Option.mem_def] at hy
        exact Option.some.inj hy.symm
      subst x
      subst y
      have hdecomp : p.take (i+1) ++ p.drop (i+1) = p := List.take_append_drop _ _
      have hlast : (p.drop (i+1)).getLast hd = p.getLast hne := by
        have hh := List.getLast_congr
          (List.append_ne_nil_of_right_ne_nil _ hd) hne hdecomp
        rw [List.getLast_append_of_right_ne_nil] at hh
        exact hh
      have hdecomp' : p.take i ++ p.drop i = p := List.take_append_drop _ _
      have hhead : (p.take i).head ht = p.head hne := by
        have hopt : (p.take i).head? = p.head? := by
          calc
            (p.take i).head? = (p.take i ++ p.drop i).head? := by
              rw [List.head?_append_of_ne_nil _ ht]
            _ = p.head? := congrArg List.head? hdecomp'
        have h₁ : (p.take i).head? = some ((p.take i).head ht) :=
          (List.head_eq_iff_head?_eq_some ht).mp rfl
        have h₂ : p.head? = some (p.head hne) :=
          (List.head_eq_iff_head?_eq_some hne).mp rfl
        rw [h₁, h₂] at hopt
        exact Option.some.inj hopt
      simpa [hlast, hhead] using hw

private theorem mem_cut :
    (by
      classical
      exact
        (Finset PeriodicSubtileIndex) → (∀ {p : List PeriodicSubtileIndex}, ∀
            {k : PeriodicSubtileIndex}, ∀ {u : PeriodicSubtileIndex}, k ∈ p → u ∈ p → u ≠ k → u ∈
        List.drop (List.idxOf k p + (1 : ℕ)) p ++ List.take (List.idxOf k p) p) ) := by
  classical
  intro D p k u hk hu huk
  let i := p.idxOf k
  have hidxne : p.idxOf u ≠ i := by
    intro he
    have he' : u = k := (List.idxOf_inj hu).mp he
    exact huk he'
  have hdecomp : p.take (i+1) ++ p.drop (i+1) = p := List.take_append_drop _ _
  have huDecomp : u ∈ p.take (i+1) ∨ u ∈ p.drop (i+1) := by
    have hm : u ∈ p.take (i+1) ++ p.drop (i+1) := by rw [hdecomp]; exact hu
    exact List.mem_append.mp hm
  rcases huDecomp with huLeft | huRight
  · have huIdx : p.idxOf u < i+1 := (List.mem_take_iff_idxOf_lt hu).mp huLeft
    have huLt : p.idxOf u < i := by omega
    exact List.mem_append.mpr (Or.inr ((List.mem_take_iff_idxOf_lt hu).2 huLt))
  · exact List.mem_append.mpr (Or.inl huRight)

private theorem k_not_mem_cut :
    (by
      classical
      exact
        (Finset PeriodicSubtileIndex) → (∀ {p : List PeriodicSubtileIndex}, ∀
            {k : PeriodicSubtileIndex}, p.Nodup → k ∈ p → k ∉ List.drop (List.idxOf k p + (1 : ℕ)) p
        ++ List.take (List.idxOf k p) p) ) := by
  classical
  intro D p k hn hk
  let i := p.idxOf k
  intro h
  rcases List.mem_append.mp h with hdrop | htake
  · have hleft : k ∈ p.take (i+1) := by
      apply (List.mem_take_iff_idxOf_lt hk).2
      omega
    have hwhole : p.take (i+1) ++ p.drop (i+1) = p := List.take_append_drop _ _
    have hnodup : (p.take (i+1) ++ p.drop (i+1)).Nodup := by rw [hwhole]; exact hn
    have hdisj := List.disjoint_of_nodup_append hnodup
    exact (List.disjoint_left.mp hdisj hleft hdrop)
  · have hidx : p.idxOf k < i := (List.mem_take_iff_idxOf_lt hk).mp htake
    omega

private theorem chain_reach :
    (by
      classical
      exact
        ∀ {R : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop}, (∀
            {x : PeriodicSubtileIndex}, ∀ {y : PeriodicSubtileIndex}, R x y → R y x) → ∀
            {p : List PeriodicSubtileIndex}, List.IsChain R p → ∀ u ∈ p, ∀ v ∈ p,
            Relation.ReflTransGen R u v ) := by
  classical
  intro R hsym p
  induction p with
  | nil => simp
  | cons x p ih =>
    cases p with
    | nil =>
      intro hc u hu v hv
      simp only [List.mem_singleton] at hu hv
      subst u
      subst v
      exact .refl
    | cons y p =>
      intro hc u hu v hv
      have htail : List.IsChain R (y :: p) := hc.tail
      have fromHead : ∀ t ∈ x :: y :: p, Relation.ReflTransGen R x t := by
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact .refl
        · exact (Relation.ReflTransGen.single hc.rel).trans
            (ih htail y (by simp) t (by simpa using ht))
      have reverse {s t} (h : Relation.ReflTransGen R s t) :
          Relation.ReflTransGen R t s := by
        induction h with
        | refl => exact .refl
        | tail _ e ih => exact ih.head (hsym e)
      exact (reverse (fromHead u hu)).trans (fromHead v hv)

private theorem safeLink :
    (by
      classical
      exact
        ∀ (D : Finset PeriodicSubtileIndex), (D.card < (3 : ℕ)) → (
        let linkList : PeriodicSubtileIndex → List PeriodicSubtileIndex := fun z =>
        match z with
        | ⟨.A,m,n⟩ =>
        [⟨.B,m,n⟩, ⟨.D,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m+1,n+1⟩,
        ⟨.E,m,n+1⟩, ⟨.B,m,n+1⟩, ⟨.F,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.B,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.D,m-1,n-1⟩, ⟨.F,m,n-1⟩, ⟨.A,m,n-1⟩,
        ⟨.E,m,n⟩, ⟨.D,m,n⟩, ⟨.A,m,n⟩, ⟨.C,m,n⟩]
        | ⟨.C,m,n⟩ =>
        [⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.A,m,n⟩, ⟨.F,m,n⟩,
        ⟨.D,m-1,n⟩, ⟨.E,m-1,n⟩]
        | ⟨.D,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n⟩, ⟨.E,m,n⟩, ⟨.C,m+1,n⟩,
        ⟨.F,m+1,n⟩, ⟨.B,m+1,n+1⟩]
        | ⟨.E,m,n⟩ =>
        [⟨.A,m,n-1⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩, ⟨.B,m,n⟩]
        | ⟨.F,m,n⟩ =>
        [⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.D,m-1,n⟩, ⟨.C,m,n⟩]
        let Chain := List.IsChain AllowedSubtileIncidence
        (∀ (z : PeriodicSubtileIndex), Chain (linkList z)) → ((∀ (z : PeriodicSubtileIndex),
            (linkList z).Nodup) → ((∀ (z : PeriodicSubtileIndex), z ∉ linkList z) → (∀ (nonempty
            : ∀ (z : PeriodicSubtileIndex), linkList z ≠ []), (∀ {z : PeriodicSubtileIndex}, ∀
            {u : PeriodicSubtileIndex}, (AllowedSubtileIncidence z u) → (u ∈ linkList z ∧ z ∈
        linkList u)) → ((∀ (z : PeriodicSubtileIndex), AllowedSubtileIncidence ((linkList
        z).getLast (nonempty z)) ((linkList z).head (nonempty z))) → ((∀
            {p : List PeriodicSubtileIndex}, ∀ {k : PeriodicSubtileIndex}, (Chain p) → (∀ (hne : p ≠
        []), (AllowedSubtileIncidence (p.getLast hne) (p.head hne)) → ((k ∈ p) → (Chain (p.drop
        (p.idxOf k + 1) ++ p.take (p.idxOf k)))))) → ((∀ {p : List PeriodicSubtileIndex}, ∀
            {k : PeriodicSubtileIndex}, ∀ {u : PeriodicSubtileIndex}, (k ∈ p) → ((u ∈ p) → ((u ≠
            k) →
        (u ∈ p.drop (p.idxOf k + 1) ++ p.take (p.idxOf k))))) → ((∀
            {p : List PeriodicSubtileIndex}, ∀ {k : PeriodicSubtileIndex}, (p.Nodup) → ((k ∈ p) → (k
        ∉ p.drop (p.idxOf k + 1) ++ p.take (p.idxOf k)))) → ((∀
            {R : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop}, (∀ {x y}, R x y → R y x) →
            (∀ {p : List PeriodicSubtileIndex}, List.IsChain R p → ∀ u ∈ p, ∀ v ∈ p,
        Relation.ReflTransGen R u v)) → (
        let SafeEdge (x y : PeriodicSubtileIndex) :=
        AllowedSubtileIncidence x y ∧ x ∉ D ∧ y ∉ D
        ∀ (z : PeriodicSubtileIndex), ∀ (u : PeriodicSubtileIndex), ∀ (v : PeriodicSubtileIndex),
            z ∈
        D → AllowedSubtileIncidence z u → AllowedSubtileIncidence z v → u ∉ D → v ∉ D →
        Relation.ReflTransGen SafeEdge u v)))))))))) ) := by
  classical
  intro D hD linkList Chain chain nodup center_free nonempty edge_mem_link wrap cut_chain mem_cut
      k_not_mem_cut chain_reach SafeEdge z u v hz hzu hzv hu hv
  let p := linkList z
  have hne : p ≠ [] := nonempty z
  have hchain : Chain p := chain z
  have hcenter : z ∉ p := center_free z
  have huP : u ∈ p := (edge_mem_link hzu).1
  have hvP : v ∈ p := (edge_mem_link hzv).1
  have mkSafeChain {q : List PeriodicSubtileIndex}
      (hc : List.IsChain AllowedSubtileIncidence q)
      (hs : ∀ w ∈ q, w ∉ D) : List.IsChain SafeEdge q := by
    induction q with
    | nil => exact .nil
    | cons x q ih =>
      cases q with
      | nil => exact .singleton _
      | cons y q =>
        rw [List.isChain_cons_cons] at hc ⊢
        refine ⟨⟨hc.1, hs x (by simp), hs y (by simp)⟩, ?_⟩
        exact ih hc.2 (by
          intro w hw
          exact hs w (by simp [hw]))
  have hsymmetric : ∀ {x y}, SafeEdge x y → SafeEdge y x := by
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  by_cases hex : ∃ k, k ∈ D ∧ k ∈ p
  · obtain ⟨k, hkD, hkP⟩ := hex
    have hzk : z ≠ k := by
      intro he
      subst k
      exact hcenter hkP
    let q := p.drop (p.idxOf k + 1) ++ p.take (p.idxOf k)
    have hqchain : List.IsChain AllowedSubtileIncidence q := by
      exact cut_chain hchain hne (wrap z) hkP
    have hkn : k ∉ q := by
      exact k_not_mem_cut (nodup z) hkP
    have hq_mem (w : PeriodicSubtileIndex) (hw : w ∈ q) : w ∈ p := by
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_of_mem_drop h
      · exact List.mem_of_mem_take h
    have hq_safe : ∀ w ∈ q, w ∉ D := by
      intro w hw hwD
      have hwp := hq_mem w hw
      have hwz : w ≠ z := by
        intro e
        subst w
        exact hcenter hwp
      have hwk : w ≠ k := by
        intro e
        subst w
        exact hkn hw
      have hsub : ({z, k, w} : Finset PeriodicSubtileIndex) ⊆ D := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact hz
        · exact hkD
        · exact hwD
      have hcard : ({z, k, w} : Finset PeriodicSubtileIndex).card = 3 := by
        have hzn : z ∉ ({k, w} : Finset PeriodicSubtileIndex) := by
          simp [hzk, hwz.symm]
        have hkn : k ∉ ({w} : Finset PeriodicSubtileIndex) := by
          simp [hwk.symm]
        simp only [Finset.card_insert_of_notMem hzn,
          Finset.card_insert_of_notMem hkn, Finset.card_singleton]
      have := Finset.card_le_card hsub
      rw [hcard] at this
      omega
    have hqu : u ∈ q := mem_cut hkP huP (by
      intro he
      subst u
      exact hu hkD)
    have hqv : v ∈ q := mem_cut hkP hvP (by
      intro he
      subst v
      exact hv hkD)
    exact chain_reach hsymmetric (mkSafeChain hqchain hq_safe) u hqu v hqv
  · have hp_safe : ∀ w ∈ p, w ∉ D := by
      intro w hw hwD
      exact hex ⟨w, hwD, hw⟩
    exact chain_reach hsymmetric (mkSafeChain hchain hp_safe) u huP v hvP

private theorem common_neighbor :
    (by
      classical
      exact
        ∀ {y : PeriodicSubtileIndex}, ∀ {z : PeriodicSubtileIndex}, AllowedSubtileIncidence y z → ∃
        (w : PeriodicSubtileIndex), AllowedSubtileIncidence y w ∧ AllowedSubtileIncidence z w ∧ w
        ≠ y ∧ w ≠ z ) := by
  classical
  intro y z h
  obtain ⟨f, g, hfg, hf, hg, huniq⟩ := P4677T2IncidenceLedger.2.2.2.2.2 y z h
  obtain ⟨i, hi⟩ := hf.1
  obtain ⟨j, hj⟩ := hf.2
  have hij : i ≠ j := by
    intro he
    subst j
    have : y = z := hi.symm.trans hj
    have hyy : AllowedSubtileIncidence y y := by simpa [this] using h
    exact (P4677T2IncidenceLedger.2.1 y) hyy
  have hk : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, and_imp, forall_exists_index,
        Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, not_true_eq_false] <;>
      first | exact ⟨0, by decide, by decide⟩
            | exact ⟨1, by decide, by decide⟩
            | exact ⟨2, by decide, by decide⟩
  obtain ⟨k, hki, hkj⟩ := hk
  let w := SixSubtileFaceVertices f k
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have := P4677T2IncidenceLedger.2.2.2.2.1 f i k hki.symm
    simpa [w, hi] using this
  · have := P4677T2IncidenceLedger.2.2.2.2.1 f j k hkj.symm
    simpa [w, hj] using this
  · intro he
    have he' : SixSubtileFaceVertices f i = SixSubtileFaceVertices f k := hi.trans he.symm
    exact hki ((P4677T2IncidenceLedger.2.2.2.1 f) he'.symm)
  · intro he
    have he' : SixSubtileFaceVertices f j = SixSubtileFaceVertices f k := hj.trans he.symm
    exact hkj ((P4677T2IncidenceLedger.2.2.2.1 f) he'.symm)

private theorem global_reach :
    (by
      classical
      exact
        (Finset PeriodicSubtileIndex) → (∀ (x : PeriodicSubtileIndex), ∀ (y :
            PeriodicSubtileIndex), Relation.ReflTransGen AllowedSubtileIncidence x y) ) := by
  classical
  intro D x y
  let R := fun s t : PeriodicSubtileIndex => AllowedSubtileIncidence s t
  let A := fun (z : Int × Int) => (⟨.A, z.1, z.2⟩ : PeriodicSubtileIndex)
  let g := fun (z : Int × Int) => (z.1, z.2 + z.1)
  have reverse {s t} (h : Relation.ReflTransGen R s t) :
      Relation.ReflTransGen R t s := by
    induction h with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single e.symm).trans ih
  have step (u v : Int × Int)
      (h : (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
        (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))) :
      Relation.ReflTransGen R (A (g u)) (A (g v)) := by
    rcases h with ⟨heq, hup | hdown⟩ | ⟨heq, hup | hdown⟩
    · have hh : g v = ((g u).1, (g u).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [hh]
      exact (Relation.ReflTransGen.single (AllowedSubtileIncidence.AB01 _ _)).trans
        (Relation.ReflTransGen.single (AllowedSubtileIncidence.AB _ _).symm)
    · have hh : g u = ((g v).1, (g v).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [hh]
      exact reverse ((Relation.ReflTransGen.single (AllowedSubtileIncidence.AB01 _ _)).trans
        (Relation.ReflTransGen.single (AllowedSubtileIncidence.AB _ _).symm))
    · have hh : g v = ((g u).1 + 1, (g u).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [hh]
      exact (Relation.ReflTransGen.single (AllowedSubtileIncidence.AB11 _ _)).trans
        (Relation.ReflTransGen.single (AllowedSubtileIncidence.AB _ _).symm)
    · have hh : g u = ((g v).1 + 1, (g v).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [hh]
      exact reverse ((Relation.ReflTransGen.single (AllowedSubtileIncidence.AB11 _ _)).trans
        (Relation.ReflTransGen.single (AllowedSubtileIncidence.AB _ _).symm))
  have intWalk {S : (Int × Int) → (Int × Int) → Prop}
      (hs : ∀ u v, S u v → S v u) (f : Int → Int × Int)
      (hstep : ∀ k, S (f k) (f (k + 1))) (m n : Int) :
      Relation.ReflTransGen S (f m) (f n) := by
    have rev {s t} (h : Relation.ReflTransGen S s t) :
        Relation.ReflTransGen S t s := by
      induction h with
      | refl => exact .refl
      | @tail b c hbc hst ih => exact ih.head (hs _ _ hst)
    have forward (m n : Int) (hmn : m ≤ n) :
        Relation.ReflTransGen S (f m) (f n) := by
      induction n, hmn using Int.leInduction with
      | base => exact .refl
      | succ n hn ih => exact ih.tail (hstep n)
    by_cases hmn : m ≤ n
    · exact forward m n hmn
    · exact rev (forward n m (by omega))
  let S := fun u v : Int × Int =>
    ((u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
      (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)))
  have ssym : ∀ u v, S u v → S v u := by
    intro u v h
    rcases h with ⟨h, e | e⟩ | ⟨h, e | e⟩
    · exact Or.inl ⟨h.symm, Or.inr e⟩
    · exact Or.inl ⟨h.symm, Or.inl e⟩
    · exact Or.inr ⟨h.symm, Or.inr e⟩
    · exact Or.inr ⟨h.symm, Or.inl e⟩
  have Aconnect (u v : Int × Int) :
      Relation.ReflTransGen R (A (g u)) (A (g v)) := by
    have vert := intWalk ssym (fun k => (u.1, k))
      (fun k => Or.inl ⟨rfl, Or.inl rfl⟩) u.2 v.2
    have horiz := intWalk ssym (fun k => (k, v.2))
      (fun k => Or.inr ⟨rfl, Or.inl rfl⟩) u.1 v.1
    have lift : ∀ {r s}, Relation.ReflTransGen S r s →
        Relation.ReflTransGen R (A (g r)) (A (g s)) := by
      intro r s h
      induction h with
      | refl => exact .refl
      | tail _ e ih => exact ih.trans (step _ _ e)
    exact lift (vert.trans horiz)
  have sameCoord (l₁ l₂ : SixSubtileLabel) (m n : Int) :
      Relation.ReflTransGen R (⟨l₁,m,n⟩ : PeriodicSubtileIndex) ⟨l₂,m,n⟩ := by
    simpa [R] using
      (P3161T1BlockTreeReachability (fun _ : Int × Int => True) m n trivial l₁ l₂)
  cases x with
  | mk lx mx nx =>
    cases y with
    | mk ly my ny =>
      let cx := (mx, nx - mx)
      let cy := (my, ny - my)
      have hc := Aconnect cx cy
      have hcx : g cx = (mx, nx) := by simp [g, cx]
      have hcy : g cy = (my, ny) := by simp [g, cy]
      rw [hcx, hcy] at hc
      exact (sameCoord lx .A mx nx).trans
        (hc.trans (sameCoord .A ly my ny))

private theorem reach_avoiding_from_local :
    (by
      classical
      exact
        ∀ (D : Finset PeriodicSubtileIndex), (D.card < (3 : ℕ)) → (
        let SafeEdge (x y : PeriodicSubtileIndex) :=
        AllowedSubtileIncidence x y ∧ x ∉ D ∧ y ∉ D
        (∀ (z : PeriodicSubtileIndex), ∀ (u : PeriodicSubtileIndex), ∀ (v :
            PeriodicSubtileIndex), (z
        ∈ D) → ((AllowedSubtileIncidence z u) → ((AllowedSubtileIncidence z v) → ((u ∉ D) → ((v ∉
        D) → (Relation.ReflTransGen SafeEdge u v)))))) → ((∀ {y : PeriodicSubtileIndex}, ∀
            {z : PeriodicSubtileIndex}, (AllowedSubtileIncidence y z) → (∃ w,
            AllowedSubtileIncidence
        y w ∧ AllowedSubtileIncidence z w ∧ w ≠ y ∧ w ≠ z)) → (∀ x ∉ D, ∀
            {y : PeriodicSubtileIndex}, Relation.ReflTransGen AllowedSubtileIncidence x y → y ∉ D →
        Relation.ReflTransGen SafeEdge x y))) ) := by
  classical
  intro D hD SafeEdge safeLink common_neighbor x hx
  let R := fun s t : PeriodicSubtileIndex => AllowedSubtileIncidence s t
  have main : ∀ {z}, Relation.ReflTransGen R x z →
      (z ∉ D → Relation.ReflTransGen SafeEdge x z) ∧
      (z ∈ D → ∀ t, R z t → t ∉ D → Relation.ReflTransGen SafeEdge x t) := by
    intro z h
    induction h with
    | refl =>
      constructor
      · intro hz
        exact .refl
      · intro hz
        exact (hx hz).elim
    | @tail y z hxy hyz ih =>
      rcases ih with ⟨ihSafe, ihDeleted⟩
      constructor
      · intro hz
        by_cases hy : y ∉ D
        · exact (ihSafe hy).tail ⟨hyz, hy, hz⟩
        · exact ihDeleted (by simpa using hy) z hyz hz
      · intro hz t hzt ht
        by_cases hy : y ∉ D
        · have hroute := ihSafe hy
          exact hroute.trans (safeLink z y t hz hyz.symm hzt hy ht)
        · have hyD : y ∈ D := by simpa using hy
          by_cases hyzEq : y = z
          · subst z
            exact ihDeleted hyD t hzt ht
          · obtain ⟨w, hyw, hzw, hwy, hwz⟩ := common_neighbor hyz
            have hwD : w ∉ D := by
              intro hw
              have hsub : ({y, z, w} : Finset PeriodicSubtileIndex) ⊆ D := by
                intro q hq
                simp only [Finset.mem_insert, Finset.mem_singleton] at hq
                rcases hq with rfl | rfl | rfl
                · exact hyD
                · exact hz
                · exact hw
              have hc := Finset.card_le_card hsub
              have hcard : ({y, z, w} : Finset PeriodicSubtileIndex).card = 3 := by
                simp [Finset.card_insert_of_notMem, Finset.mem_insert,
                  Finset.mem_singleton, hyzEq, hwy.symm, hwz.symm]
              omega
            have hwroute := ihDeleted hyD w hyw hwD
            exact hwroute.trans (safeLink z w t hz hzw hzt hwD ht)
  intro y hxy hy
  exact (main hxy).1 hy

private theorem closure_list :
    (by
      classical
      exact
        ∀ (D : Finset PeriodicSubtileIndex),
        let SafeEdge (x y : PeriodicSubtileIndex) :=
        AllowedSubtileIncidence x y ∧ x ∉ D ∧ y ∉ D
        ∀ {x : PeriodicSubtileIndex}, ∀ {y : PeriodicSubtileIndex}, Relation.ReflTransGen SafeEdge x
        y → x ∉ D → ∃ (p : List PeriodicSubtileIndex), p.head? = some x ∧ p.getLast? = some y ∧
        List.IsChain SafeEdge p ∧ ∀ w ∈ p, w ∉ D ) := by
  classical
  intro D SafeEdge x y h hx
  induction h with
  | refl =>
    exact ⟨[x], rfl, rfl, .singleton _, by simp [hx]⟩
  | @tail y z hxy hyz ih =>
    rcases ih with ⟨p, hhead, hlast, hp, hsafe⟩
    have hne : p ≠ [] := by
      intro he
      simp [he] at hhead
    have hlastEq : p.getLast hne = y := by
      have hh := List.getLast?_eq_getLast_of_ne_nil hne
      rw [hh] at hlast
      exact Option.some.inj hlast
    refine ⟨p ++ [z], ?_, ?_, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil _ hne]
      exact hhead
    · simp
    · apply List.IsChain.append hp (.singleton z)
      intro s hs t ht
      have hs' : s ∈ some (p.getLast hne) := by
        simpa [List.getLast?_eq_getLast_of_ne_nil hne] using hs
      have hsEq : s = p.getLast hne := by simpa using hs'.symm
      have ht' : t ∈ some z := by simpa using ht
      have htEq : t = z := by simpa using ht'.symm
      subst s
      subst t
      rw [hlastEq]
      exact hyz
    · intro w hw
      rcases List.mem_append.mp hw with hwp | hwz
      · exact hsafe w hwp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hwz
        subst w
        exact hyz.2.2

private theorem chain_pair :
    (by
      classical
      exact
        ∀ (D : Finset PeriodicSubtileIndex),
        let SafeEdge (x y : PeriodicSubtileIndex) :=
        AllowedSubtileIncidence x y ∧ x ∉ D ∧ y ∉ D
        ∀ (l₁ : List PeriodicSubtileIndex), ∀ (l₂ : List PeriodicSubtileIndex), ∀ (x :
            PeriodicSubtileIndex), ∀ (y : PeriodicSubtileIndex), List.IsChain SafeEdge (l₁ ++ x :: y
        :: l₂) → SafeEdge x y ) := by
  classical
  intro D SafeEdge l₁
  induction l₁ with
  | nil =>
    intro l₂ x y hc
    simp only [List.nil_append, List.isChain_cons_cons] at hc
    exact hc.1
  | cons z l ih =>
    intro l₂ x y hc
    have ht : List.IsChain SafeEdge (l ++ x :: y :: l₂) := by
      simpa [List.cons_append] using hc.tail
    exact ih l₂ x y ht

end ThreeConnectivityProof

theorem P4677T2ThreeConnected
    (D : Finset PeriodicSubtileIndex) (hD : D.card < 3)
    (a : PeriodicSubtileIndex) (ha : a ∉ D)
    (b : PeriodicSubtileIndex) (hb : b ∉ D) :
    ∃ p : List PeriodicSubtileIndex,
      p.head? = some a ∧ p.getLast? = some b ∧
      (∀ x ∈ p, x ∉ D) ∧
      ∀ x y : PeriodicSubtileIndex, ∀ l₁ l₂ : List PeriodicSubtileIndex,
        p = l₁ ++ x :: y :: l₂ → AllowedSubtileIncidence x y := by
-- BODY
  classical
  let linkList : PeriodicSubtileIndex → List PeriodicSubtileIndex := fun z =>
    match z with
    | ⟨.A,m,n⟩ =>
      [⟨.B,m,n⟩, ⟨.D,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m+1,n+1⟩,
       ⟨.E,m,n+1⟩, ⟨.B,m,n+1⟩, ⟨.F,m,n⟩, ⟨.C,m,n⟩]
    | ⟨.B,m,n⟩ =>
      [⟨.A,m-1,n-1⟩, ⟨.D,m-1,n-1⟩, ⟨.F,m,n-1⟩, ⟨.A,m,n-1⟩,
       ⟨.E,m,n⟩, ⟨.D,m,n⟩, ⟨.A,m,n⟩, ⟨.C,m,n⟩]
    | ⟨.C,m,n⟩ =>
      [⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.A,m,n⟩, ⟨.F,m,n⟩,
       ⟨.D,m-1,n⟩, ⟨.E,m-1,n⟩]
    | ⟨.D,m,n⟩ =>
      [⟨.A,m,n⟩, ⟨.B,m,n⟩, ⟨.E,m,n⟩, ⟨.C,m+1,n⟩,
       ⟨.F,m+1,n⟩, ⟨.B,m+1,n+1⟩]
    | ⟨.E,m,n⟩ =>
      [⟨.A,m,n-1⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩, ⟨.B,m,n⟩]
    | ⟨.F,m,n⟩ =>
      [⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.D,m-1,n⟩, ⟨.C,m,n⟩]
  let Chain := List.IsChain AllowedSubtileIncidence
  have chain (z : PeriodicSubtileIndex) : Chain (linkList z) := ThreeConnectivityProof.chain z
  have nodup (z : PeriodicSubtileIndex) : (linkList z).Nodup := by
    cases z with | mk l m n => cases l <;> simp [linkList]
  have center_free (z : PeriodicSubtileIndex) : z ∉ linkList z := by
    cases z with | mk l m n => cases l <;> simp [linkList]
  have nonempty (z : PeriodicSubtileIndex) : linkList z ≠ [] := by
    cases z with | mk l m n => cases l <;> simp [linkList]
  have adjacent (z : PeriodicSubtileIndex) :
      ∀ u ∈ linkList z, AllowedSubtileIncidence z u := ThreeConnectivityProof.adjacent z
  have edge_mem_link {z u : PeriodicSubtileIndex}
      (h : AllowedSubtileIncidence z u) : u ∈ linkList z ∧ z ∈ linkList u :=
          ThreeConnectivityProof.edge_mem_link (z := z) (u := u) h
  have wrap (z : PeriodicSubtileIndex) :
      AllowedSubtileIncidence ((linkList z).getLast (nonempty z))
        ((linkList z).head (nonempty z)) := ThreeConnectivityProof.wrap nonempty z
  have cut_chain {p : List PeriodicSubtileIndex} {k : PeriodicSubtileIndex}
      (hp : Chain p) (hne : p ≠ [])
      (hw : AllowedSubtileIncidence (p.getLast hne) (p.head hne)) (hk : k ∈ p) :
      Chain (p.drop (p.idxOf k + 1) ++ p.take (p.idxOf k)) := ThreeConnectivityProof.cut_chain (p
          := p) (k := k) hp hne hw hk
  have mem_cut {p : List PeriodicSubtileIndex} {k u : PeriodicSubtileIndex}
      (hk : k ∈ p) (hu : u ∈ p) (huk : u ≠ k) :
      u ∈ p.drop (p.idxOf k + 1) ++ p.take (p.idxOf k) := ThreeConnectivityProof.mem_cut D (p :=
          p) (k := k) (u := u) hk hu huk
  have k_not_mem_cut {p : List PeriodicSubtileIndex} {k : PeriodicSubtileIndex}
      (hn : p.Nodup) (hk : k ∈ p) :
      k ∉ p.drop (p.idxOf k + 1) ++ p.take (p.idxOf k) := ThreeConnectivityProof.k_not_mem_cut D
          (p := p) (k := k) hn hk
  have chain_reach {R : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop}
      (hsym : ∀ {x y}, R x y → R y x) :
      ∀ {p : List PeriodicSubtileIndex}, List.IsChain R p →
        ∀ u ∈ p, ∀ v ∈ p, Relation.ReflTransGen R u v := ThreeConnectivityProof.chain_reach (R :=
            R) hsym
  let SafeEdge (x y : PeriodicSubtileIndex) :=
    AllowedSubtileIncidence x y ∧ x ∉ D ∧ y ∉ D
  have safeLink (z u v : PeriodicSubtileIndex) (hz : z ∈ D)
      (hzu : AllowedSubtileIncidence z u) (hzv : AllowedSubtileIncidence z v)
      (hu : u ∉ D) (hv : v ∉ D) :
      Relation.ReflTransGen SafeEdge u v := ThreeConnectivityProof.safeLink D hD chain nodup
          center_free nonempty edge_mem_link wrap cut_chain mem_cut k_not_mem_cut chain_reach z u
          v hz hzu hzv hu hv
  have common_neighbor {y z : PeriodicSubtileIndex}
      (h : AllowedSubtileIncidence y z) :
      ∃ w, AllowedSubtileIncidence y w ∧ AllowedSubtileIncidence z w ∧
        w ≠ y ∧ w ≠ z := ThreeConnectivityProof.common_neighbor (y := y) (z := z) h
  have global_reach (x y : PeriodicSubtileIndex) :
      Relation.ReflTransGen AllowedSubtileIncidence x y := ThreeConnectivityProof.global_reach D x y
  have reach_avoiding_from_local
      (x : PeriodicSubtileIndex) (hx : x ∉ D) :
      ∀ {y}, Relation.ReflTransGen AllowedSubtileIncidence x y → y ∉ D →
        Relation.ReflTransGen SafeEdge x y := ThreeConnectivityProof.reach_avoiding_from_local D
            hD safeLink common_neighbor x hx
  have closure_list {x y : PeriodicSubtileIndex}
      (h : Relation.ReflTransGen SafeEdge x y) (hx : x ∉ D) :
      ∃ p : List PeriodicSubtileIndex, p.head? = some x ∧ p.getLast? = some y ∧
        List.IsChain SafeEdge p ∧ ∀ w ∈ p, w ∉ D := ThreeConnectivityProof.closure_list D (x :=
            x) (y := y) h hx
  have chain_pair : ∀ (l₁ l₂ : List PeriodicSubtileIndex) (x y : PeriodicSubtileIndex),
      List.IsChain SafeEdge (l₁ ++ x :: y :: l₂) → SafeEdge x y :=
          ThreeConnectivityProof.chain_pair D
  have havoiding : Relation.ReflTransGen SafeEdge a b := by
    apply reach_avoiding_from_local a ha (global_reach a b)
    exact hb
  obtain ⟨p, hphead, hplast, hpchain, hpsafe⟩ := closure_list havoiding ha
  refine ⟨p, hphead, hplast, hpsafe, ?_⟩
  intro x y l₁ l₂ heq
  exact (chain_pair l₁ l₂ x y (heq ▸ hpchain)).1

end ApollonianSuperharmonic

end
