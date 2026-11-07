/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeControlledInterchange
public import LeanPool.GoldbergSeymour.TashTreeFourUnusedColors
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Tash Tree Last Index Third Normal Form

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hbeta_pen_89.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (r : Fin T.length) (p :
        Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length) (hp : (↑p : ℕ) + (1 : ℕ) =
        T.length) (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)),
    let P : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); P.length = T.length - (1 : ℕ) → TreeSequenceInitialSegment P T → ColoredVertexSetElementary
        G phi (TreeSequenceVertexSet P) →
    ∀ u ∈ TreeSequenceVertexSet T,
    ∀ v ∈ TreeSequenceVertexSet T, u ≠ v →
    ∀ beta ∈ MissingColors G phi u, beta ∈ MissingColors G phi v → (
    ∀ w ∈ TreeSequenceVertexSet T, w = T.vertex (Fin.last T.length) ∨ w ∈ TreeSequenceVertexSet P)
        → (
    ∀ (i : Fin (T.length + (1 : ℕ))), beta ∈ MissingColors G phi (T.vertex i) → (↑i : ℕ) =
        T.length - (1 : ℕ) ∨ (↑i : ℕ) = T.length) → beta ∈ MissingColors G phi (T.vertex
        (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ G k e0 phi T hq hlast r p hr hp hlastval P hP_length hPprefix hPelementary u hu v hv
      huv beta hbu hbv hlast_or_prefix hlast_index
  let _ := Fintype.ofFinite V
  rcases hlast_or_prefix u hu with huLast | huPrefix
  · rcases hlast_or_prefix v hv with hvLast | hvPrefix
    · exact (huv (huLast.trans hvLast.symm)).elim
    · have hvindex : ∃ i : Fin (T.length + 1),
          i.val = T.length - 1 ∧ T.vertex i = v := by
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and] at hvPrefix
        obtain ⟨i, hi⟩ := hvPrefix
        let ii : Fin (T.length + 1) := ⟨i.val, by omega⟩
        have hq := hPprefix.2.1 i
        have heq : Fin.castLE (Nat.succ_le_succ hPprefix.1) i = ii := by
          apply Fin.ext
          rfl
        rw [heq] at hq
        have hidx := hlast_index ii (by
          rw [hq, hi]
          exact hbv)
        rcases hidx with hidx | hidx
        · exact ⟨ii, hidx, hq.trans hi⟩
        · have hiT : i.val < T.length := by
            have hh := i.isLt
            simp [hP_length] at hh
            omega
          have hii : ii.val = i.val := rfl
          have hiiT : ii.val < T.length := by simpa [ii] using hiT
          omega
      obtain ⟨i, hi, hiv⟩ := hvindex
      have hlastEq : T.vertex i = T.vertex ⟨T.length - 1, by omega⟩ := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa using hi
      have hvlast : v = T.vertex ⟨T.length - 1, by omega⟩ := hiv.symm.trans hlastEq
      simpa [hvlast] using hbv
  · rcases hlast_or_prefix v hv with hvLast | hvPrefix
    · have huindex : ∃ i : Fin (T.length + 1),
          i.val = T.length - 1 ∧ T.vertex i = u := by
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and] at huPrefix
        obtain ⟨i, hi⟩ := huPrefix
        let ii : Fin (T.length + 1) := ⟨i.val, by omega⟩
        have hq := hPprefix.2.1 i
        have heq : Fin.castLE (Nat.succ_le_succ hPprefix.1) i = ii := by
          apply Fin.ext
          rfl
        rw [heq] at hq
        have hidx := hlast_index ii (by
          rw [hq, hi]
          exact hbu)
        rcases hidx with hidx | hidx
        · exact ⟨ii, hidx, hq.trans hi⟩
        · have hiT : i.val < T.length := by
            have hh := i.isLt
            simp [hP_length] at hh
            omega
          have hii : ii.val = i.val := rfl
          have hiiT : ii.val < T.length := by simpa [ii] using hiT
          omega
      obtain ⟨i, hi, hiv⟩ := huindex
      have hlastEq : T.vertex i = T.vertex ⟨T.length - 1, by omega⟩ := by
        apply congrArg T.vertex
        apply Fin.ext
        simpa using hi
      have hulast : u = T.vertex ⟨T.length - 1, by omega⟩ := hiv.symm.trans hlastEq
      simpa [hulast] using hbu
    · exact (Finset.disjoint_left.mp
        (hPelementary huPrefix hvPrefix
          (by intro he; exact huv (he ▸ rfl)))) hbu hbv |>.elim

private theorem helper_hbeta_unused_158.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (hq : (2 : ℕ) < TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length)
      (r : Fin T.length) (p : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length)
      (hp : (↑p : ℕ) + (1 : ℕ) = T.length) (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)),
    TashTreeBadPair G k e0 phi T →
    let P : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => by omega)
        (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => by omega);
    P.length = T.length - (1 : ℕ) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) →
    ∀
      beta ∈
        MissingColors G phi
          (T.vertex (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))),
    TreeColorUnusedThrough phi T beta
      (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ))) := by
  classical
  intro V E _ _ _ G k e0 phi T hq hlast r p hr hp hlastval hbad P hP_length hPelementary beta
      hbeta_pen s hs1 hsj hcolor
  rcases hbad.2.1 s hs1 with ⟨i, c, hc, hmiss⟩
  have hcb : beta = c := by simpa [hcolor] using hc
  subst c
  have hslt : s.val < T.length - 1 := by simpa using hsj
  have his : i.val ≤ s.val := Nat.le_of_lt_succ i.isLt
  have hilt : i.val < T.length - 1 := by omega
  have hvne : T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))) ≠
        T.vertex ⟨T.length - 1, by omega⟩ := by
    intro he
    have he' := T.vertex_injective he
    have hiVal := congrArg Fin.val he'
    have hcast : (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))).val = i.val := rfl
    have hcast : (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))).val = i.val := rfl
    omega
  have hd := hPelementary
      (by rw [TreeSequenceVertexSet]
          exact Finset.mem_image.mpr ⟨
            ⟨i.val, by omega⟩, Finset.mem_univ _, by
              apply congrArg T.vertex; apply Fin.ext; rfl⟩)
      (by rw [TreeSequenceVertexSet]
          exact Finset.mem_image.mpr ⟨
            ⟨T.length - 1, by omega⟩, Finset.mem_univ _, rfl⟩) hvne
  exact (Finset.disjoint_left.mp hd) hmiss hbeta_pen

private theorem helper_halpha_unused_246.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (hq : (2 : ℕ) < TashTreePathIndex G T)
      (hlast : TashTreePathIndex G T = T.length) (gamma : Fin k) (r : Fin T.length)
      (p : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length)
      (hp : (↑p : ℕ) + (1 : ℕ) = T.length),
    phi (T.edge r) = some gamma →
    ∀ (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)),
    let P : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => by omega)
        (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => by omega);
    ∀ (hP_length : P.length = T.length - (1 : ℕ)) (beta : Fin k),
    let Q : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (2 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) => by omega)
        (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) => by omega);
    let edgeColor : Fin k :=
      (phi (T.edge (⟨T.length - (2 : ℕ), by omega⟩ : Fin T.length))).getD beta;
    ∀ (alpha : Fin k),
    alpha ≠ gamma →
    alpha ≠ edgeColor →
    alpha ∈ TreeFreeColors phi Q →
    ∀ (_ : Fin (Q.length + (1 : ℕ))),
    TreeColorUnusedThrough phi T alpha
      (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ))) := by
  classical
  intro V E _ _ G k e0 phi T hq hlast gamma r p hr hp hrgamma hlastval P hP_length beta Q edgeColor
      alpha halpha_ne_gamma halpha_ne_edge halpha_free mi s hs1 hsj
  let _ := Fintype.ofFinite V
  by_cases hsLast : s.val = T.length - 1
  · intro heq
    have hs_eq : s = ⟨T.length - 1, by omega⟩ := by
      apply Fin.ext
      exact hsLast
    rw [hs_eq] at heq
    have hr_eq : r = ⟨T.length - 1, by omega⟩ := by
      apply Fin.ext
      exact hlastval
    rw [hr_eq] at hrgamma
    have hh : some alpha = some gamma := heq.symm.trans hrgamma
    exact halpha_ne_gamma (Option.some.inj hh)
  · by_cases hsSecond : s.val = T.length - 2
    · intro heq
      have hs_eq : s = ⟨T.length - 2, by omega⟩ := by
        apply Fin.ext
        exact hsSecond
      rw [hs_eq] at heq
      cases hval : phi (T.edge ⟨T.length - 2, by omega⟩) with
      | none => simp [hval] at heq
      | some c =>
        have hc : phi (T.edge ⟨T.length - 2, by omega⟩) = some c := hval
        have : edgeColor = c := by simp [edgeColor, hc]
        have hac : alpha = c := Option.some.inj (heq.symm.trans hc)
        exact halpha_ne_edge (hac.trans this.symm)
    · have hsQ : s.val < Q.length := by
        have hQlen : Q.length = T.length - 2 := rfl
        have hsle : s.val ≤ T.length - 2 := by omega
        have hslt2 : s.val < T.length - 2 := by
          by_contra hn
          have he : s.val = T.length - 2 := by omega
          exact hsSecond he
        simpa only [hQlen] using hslt2
      have husedQ : alpha ∉ TreeUsedColors phi Q :=
        (Finset.mem_sdiff.mp halpha_free).2
      intro heq
      apply husedQ
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨s.val, by omega⟩, hs1, by
        simpa [Q, TreeSequencePrefix, Fin.castLE] using heq⟩

private theorem helper_hlSub_448.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0), IsProperEdgeColoring G
        phi →
    ∀ beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
    ∀ (alpha : Fin k), alpha ≠ beta → ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl (T.vertex (Fin.last T.length)))).Subsingleton := by
  classical
  intro V E _ _ G k e0 phi T hproper beta hbeta_last alpha halpha_ne_beta
  let _ := Fintype.ofFinite V
  let : Fintype
      ((TwoColorIncidenceGraph G phi beta alpha).neighborSet
        (Sum.inl (T.vertex (Fin.last T.length)))) := Fintype.ofFinite _
  have hd := MissingColorIncidenceEndpoint G phi beta alpha
    halpha_ne_beta.symm hproper (T.vertex (Fin.last T.length)) hbeta_last
  intro x hx y hy
  have hx' : x ∈ (TwoColorIncidenceGraph G phi beta alpha).neighborFinset
      (Sum.inl (T.vertex (Fin.last T.length))) := by
    apply (SimpleGraph.mem_neighborFinset
      (TwoColorIncidenceGraph G phi beta alpha)
      (Sum.inl (T.vertex (Fin.last T.length))) x).2
    simpa [TwoColorIncidenceGraph, or_comm] using hx
  have hy' : y ∈ (TwoColorIncidenceGraph G phi beta alpha).neighborFinset
      (Sum.inl (T.vertex (Fin.last T.length))) := by
    apply (SimpleGraph.mem_neighborFinset
      (TwoColorIncidenceGraph G phi beta alpha)
      (Sum.inl (T.vertex (Fin.last T.length))) y).2
    simpa [TwoColorIncidenceGraph, or_comm] using hy
  have hc : ((TwoColorIncidenceGraph G phi beta alpha).neighborFinset
      (Sum.inl (T.vertex (Fin.last T.length)))).card ≤ 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hd
  exact (Finset.card_le_one.mp hc) x hx' y hy'

private theorem helper_houtside_414.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (hq : (2 : ℕ) < TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (r
        : Fin T.length) (p : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length) (hp :
        (↑p : ℕ) + (1 : ℕ) = T.length) (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)),
        IsProperEdgeColoring G phi →
    let P : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by first  | omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by first  | omega
    ));
    ∀ (hP_length : P.length = T.length - (1 : ℕ)),
    ∀ v ∈ TreeSequenceVertexSet T,
    ∀ beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
    let Q : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) => (
    by first  | omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) => (
    by first  | omega
    ));
    ∀ (alpha : Fin k), alpha ≠ beta →
    ∀ (mi : Fin (Q.length + (1 : ℕ))) (hmq : (↑mi : ℕ) + (2 : ℕ) ≤ T.length),
        TwoColorPathComponent G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) ∧ Sum.inl (T.vertex (⟨(↑mi : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) ∈ TwoColorComponent G phi alpha beta (Sum.inl (T.vertex
        (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) ∧ ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl (T.vertex (⟨(↑mi : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))).Subsingleton ∧ ((TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))).Subsingleton ∧ beta ∈ MissingColors G (TwoColorComponentSwap
        G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) (T.vertex (⟨(↑mi : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) ∧ alpha ∈ MissingColors G (TwoColorComponentSwap G phi alpha
        beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) ∧ (
    ∀ (r_1 : Fin T.length), (1 : ℕ) ≤ (↑r_1 : ℕ) → (↑r_1 : ℕ) < T.length - (1 : ℕ) →
        TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) (T.edge r_1) = phi (T.edge r_1)) ∧ (
    ∀ (r_1 : Fin T.length), T.length - (1 : ℕ) ≤ (↑r_1 : ℕ) →
    ∀ (w : Fin ((↑r_1 : ℕ) + (1 : ℕ))) (c : Fin k), phi (T.edge r_1) = some c → c ∈ MissingColors
        G phi (T.vertex (w.castLT (Nat.lt_trans w.isLt (Nat.succ_lt_succ r_1.isLt)))) →
    ∃ (w' : Fin ((↑r_1 : ℕ) + (1 : ℕ))) (c' : Fin k), TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) (T.edge r_1) = some c' ∧ c' ∈ MissingColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) (T.vertex (w'.castLT (Nat.lt_trans w'.isLt (Nat.succ_lt_succ
        r_1.isLt))))) ∧ TashTreeMinimumBadPair G k e0 (TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) T → Sum.inl (T.vertex (Fin.last T.length)) ∉
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ G k e0 phi T hq hlast r p hr hp hlastval hproper P hP_length v hv beta
      hbeta_last Q alpha halpha_ne_beta mi hmq hswap
  by_contra hin
  obtain ⟨a, b, path, hpath, hsupport⟩ :=
    TwoColorComponentSpanningPath G phi alpha beta hproper
      (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
  have support_of_component {x : Sum V E} (hx : x ∈
      TwoColorComponent G phi alpha beta
        (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))) :
      x ∈ path.support := by
    change x ∈ {y | y ∈ path.support}
    rw [hsupport]
    exact hx
  have endpoint_of_subsingleton {x : Sum V E} (hx : x ∈
      TwoColorComponent G phi alpha beta
        (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩)))
      (hxSub : Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x)) :
      x = a ∨ x = b := by
    by_contra hend
    push Not at hend
    exact (hpath.isTrail.notMem_support_of_subsingleton_neighborSet
      hend.1 hend.2 hxSub) (support_of_component hx)
  have hmEnd := endpoint_of_subsingleton hswap.2.1 hswap.2.2.1
  have hpEnd := endpoint_of_subsingleton
    (by change Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) ∈
        TwoColorComponent G phi alpha beta
          (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
        change Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) ∈
          ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
            (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))).supp
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff])
    hswap.2.2.2.1
  have hlSub := @helper_hlSub_448 V E inferInstance inferInstance G k e0 phi T hproper beta
      hbeta_last alpha halpha_ne_beta
  have hlEnd := endpoint_of_subsingleton hin hlSub
  have hm_ne_last : (Sum.inl (T.vertex ⟨mi.val, by omega⟩) : Sum V E) ≠
      Sum.inl (T.vertex (Fin.last T.length)) := by
    intro he
    have hv : T.vertex ⟨mi.val, by omega⟩ =
        T.vertex (Fin.last T.length) := by simpa using he
    have hh := congrArg Fin.val (T.vertex_injective hv)
    have hmiVal : (⟨mi.val, by omega⟩ : Fin (T.length + 1)).val = mi.val := rfl
    have hlastVal : (Fin.last T.length).val = T.length := rfl
    omega
  have hp_ne_last : (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) : Sum V E) ≠
      Sum.inl (T.vertex (Fin.last T.length)) := by
    intro he
    have hv : T.vertex ⟨T.length - 1, by omega⟩ =
        T.vertex (Fin.last T.length) := by simpa using he
    have hh := congrArg Fin.val (T.vertex_injective hv)
    have hpenVal : (⟨T.length - 1, by omega⟩ : Fin (T.length + 1)).val = T.length - 1 := rfl
    have hlastVal : (Fin.last T.length).val = T.length := rfl
    omega
  have hm_ne_pen : (Sum.inl (T.vertex ⟨mi.val, by omega⟩) : Sum V E) ≠
      Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) := by
    intro he
    have hv : T.vertex ⟨mi.val, by omega⟩ =
        T.vertex ⟨T.length - 1, by omega⟩ := by simpa using he
    have hh := congrArg Fin.val (T.vertex_injective hv)
    have hmiVal : (⟨mi.val, by omega⟩ : Fin (T.length + 1)).val = mi.val := rfl
    have hpenVal : (⟨T.length - 1, by omega⟩ : Fin (T.length + 1)).val = T.length - 1 := rfl
    omega
  have endpoint_is_m_or_pen {x : Sum V E} (hx : x = a ∨ x = b) :
      x = Sum.inl (T.vertex ⟨mi.val, by omega⟩) ∨
      x = Sum.inl (T.vertex ⟨T.length - 1, by omega⟩) := by
    rcases hmEnd with hmA | hmB <;> rcases hpEnd with hpA | hpB
    · exact False.elim (hm_ne_pen (hmA.trans hpA.symm))
    · rcases hx with hxa | hxb
      · exact Or.inl (hxa.trans hmA.symm)
      · exact Or.inr (hxb.trans hpB.symm)
    · rcases hx with hxa | hxb
      · exact Or.inr (hxa.trans hpA.symm)
      · exact Or.inl (hxb.trans hmB.symm)
    · exact False.elim (hm_ne_pen (hmB.trans hpB.symm))
  rcases endpoint_is_m_or_pen hlEnd with hml | hpl
  · exact hm_ne_last hml.symm
  · exact hp_ne_last hpl.symm

private theorem helper_hbeta_last3_299.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (hq : (2 : ℕ) < TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (_
        : Fin k) (r : Fin T.length) (p : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) =
        T.length) (hp : (↑p : ℕ) + (1 : ℕ) = T.length) (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)),
        IsProperEdgeColoring G phi →
    let P : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    );
    ∀ (hP_length : P.length = T.length - (1 : ℕ)),
    ∀ v ∈ TreeSequenceVertexSet T,
    ∀ beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
    let Q : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) =>
    by omega
    );
    ∀ (alpha : Fin k), alpha ≠ beta →
    ∀ (mi : Fin (Q.length + (1 : ℕ))) (hmq : (↑mi : ℕ) + (2 : ℕ) ≤ T.length),
        TwoColorPathComponent G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) ∧ Sum.inl (T.vertex (⟨(↑mi : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) ∈ TwoColorComponent G phi alpha beta (Sum.inl (T.vertex
        (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) ∧ ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl (T.vertex (⟨(↑mi : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))).Subsingleton ∧ ((TwoColorIncidenceGraph G phi alpha
        beta).neighborSet (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))).Subsingleton ∧ beta ∈ MissingColors G (TwoColorComponentSwap
        G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) (T.vertex (⟨(↑mi : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) ∧ alpha ∈ MissingColors G (TwoColorComponentSwap G phi alpha
        beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) ∧ (
    ∀ (r_1 : Fin T.length), (1 : ℕ) ≤ (↑r_1 : ℕ) → (↑r_1 : ℕ) < T.length - (1 : ℕ) →
        TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) (T.edge r_1) = phi (T.edge r_1)) ∧ (
    ∀ (r_1 : Fin T.length), T.length - (1 : ℕ) ≤ (↑r_1 : ℕ) →
    ∀ (w : Fin ((↑r_1 : ℕ) + (1 : ℕ))) (c : Fin k), phi (T.edge r_1) = some c → c ∈ MissingColors
        G phi (T.vertex (w.castLT (Nat.lt_trans w.isLt (Nat.succ_lt_succ r_1.isLt)))) →
    ∃ (w' : Fin ((↑r_1 : ℕ) + (1 : ℕ))) (c' : Fin k), TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))) (T.edge r_1) = some c' ∧ c' ∈ MissingColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) (T.vertex (w'.castLT (Nat.lt_trans w'.isLt (Nat.succ_lt_succ
        r_1.isLt))))) ∧ TashTreeMinimumBadPair G k e0 (TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))))) T →
    let phi3 : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl
        (T.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))))); beta ∈ MissingColors G phi3 (T.vertex (Fin.last T.length))
  := by
  classical
  intro V E _ _ _ G k e0 phi T hq hlast gamma r p hr hp hlastval hproper P hP_length v hv beta
      hbeta_last Q alpha halpha_ne_beta mi hmq hswap phi3
  have houtside := @helper_houtside_414 V E inferInstance inferInstance inferInstance G k e0 phi T
      hq hlast r p hr hp hlastval hproper hP_length v hv beta hbeta_last alpha halpha_ne_beta mi hmq
      hswap
  have hmiss := TwoColorComponentSwapMissingBehavior G phi alpha beta
    halpha_ne_beta hproper
    (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
  dsimp only at hmiss
  exact (hmiss.1 _ houtside) ▸ hbeta_last

private theorem helper_branch_437.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [ Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (hq : (2 : ℕ) < TashTreePathIndex G T)
      (hlast : TashTreePathIndex G T = T.length) (gamma : Fin k) (r : Fin T.length)
      (p : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length)
      (hp : (↑p : ℕ) + (1 : ℕ) = T.length),
    gamma ∈ PresentColors G phi (T.vertex p) →
    ∀ (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)),
    (↑p : ℕ) = T.length - (1 : ℕ) →
    let P : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => by omega)
        (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => by omega);
    ∀ (hP_length : P.length = T.length - (1 : ℕ)) (beta : Fin k),
    let Q : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (2 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) => by omega)
        (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) => by omega);
    ∀ (alpha : Fin k),
    alpha ≠ gamma →
    ∀ (_ : Fin (Q.length + (1 : ℕ))),
    let phi3 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)))));
    beta ≠ gamma →
    gamma ∈ PresentColors G phi3 (T.vertex p) := by
  classical
  intro V E _ _ G k e0 phi T hq hlast gamma r p hr hp hpgamma hlastval hpval P hP_length beta Q
      alpha halpha_ne_gamma mi phi3 hbeta_ne_gamma
  let _ := Fintype.ofFinite V
  have hp_eq : p = ⟨T.length - 1, by omega⟩ := by
    apply Fin.ext
    exact hpval
  have hpold : gamma ∈ PresentColors G phi
      (T.vertex ⟨T.length - 1, by omega⟩) := by
    rw [hp_eq] at hpgamma
    exact hpgamma
  rcases (by simpa [PresentColors] using hpold) with ⟨e, he, hc⟩
  rw [hp_eq]
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, by
    by_cases hm : Sum.inr e ∈ TwoColorComponent G phi alpha beta
        (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
    · dsimp [phi3]
      simp [TwoColorComponentSwap, hc, hm, Ne.symm halpha_ne_gamma,
        Ne.symm hbeta_ne_gamma]
    · dsimp [phi3]
      simp [TwoColorComponentSwap, hc, hm]⟩

private theorem helper_branch_128.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), TashTreeMinimumBadPair G k e0 phi T →
    ∀ (hq : (2 : ℕ) < TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (gamma :
        Fin k) (r : Fin T.length) (p : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) =
        T.length) (hp : (↑p : ℕ) + (1 : ℕ) = T.length), phi (T.edge r) = some gamma → gamma ∈
        PresentColors G phi (T.vertex p) →
    ∀ (hlastval : (↑r : ℕ) = T.length - (1 : ℕ)), (↑p : ℕ) = T.length - (1 : ℕ) → TashTreeBadPair
        G k e0 phi T → IsProperEdgeColoring G phi →
    let P : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); P.length = T.length - (1 : ℕ) → TreeSequenceInitialSegment P T → ColoredVertexSetElementary
        G phi (TreeSequenceVertexSet P) →
    ∀ u ∈ TreeSequenceVertexSet T,
    ∀ v ∈ TreeSequenceVertexSet T, u ≠ v →
    ∀ beta ∈ MissingColors G phi u, beta ∈ MissingColors G phi v → (
    ∀ w ∈ TreeSequenceVertexSet T, w = T.vertex (Fin.last T.length) ∨ w ∈ TreeSequenceVertexSet P)
        → beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) → (¬
    ∃ (j : Fin (T.length + (1 : ℕ))), (↑j : ℕ) + (2 : ℕ) ≤ T.length ∧ beta ∈ MissingColors G phi
        (T.vertex j)) →
    ∃ (phi₃ : PartialEdgeColoring E k) (beta : Fin k) (j : Fin (T.length + (1 : ℕ))),
        TashTreeMinimumBadPair G k e0 phi₃ T ∧ phi₃ (T.edge r) = some gamma ∧ gamma ∈
        PresentColors G phi₃ (T.vertex p) ∧ (↑j : ℕ) + (2 : ℕ) ≤ T.length ∧ beta ∈ MissingColors G
        phi₃ (T.vertex j) ∧ beta ∈ MissingColors G phi₃ (T.vertex (Fin.last T.length)) := by
  classical
  intro V E _ _ _ G k e0 phi T hmin hq hlast gamma r p hr hp hrgamma hpgamma hlastval hpval hbad
      hproper P hP_length hPprefix hPelementary u hu v hv huv beta hbu hbv hlast_or_prefix
      hbeta_last hsmall
  have hlast_index : ∀ i : Fin (T.length + 1),
      beta ∈ MissingColors G phi (T.vertex i) →
      i.val = T.length - 1 ∨ i.val = T.length := by
    intro i hi
    by_cases he : i.val = T.length
    · exact Or.inr he
    · left
      by_contra hne
      exact hsmall ⟨i, by omega, hi⟩
  have hbeta_pen := @helper_hbeta_pen_89 V E inferInstance inferInstance G k e0 phi T hq hlast r p
      hr hp hlastval hP_length hPprefix hPelementary u hu v hv huv beta hbu hbv hlast_or_prefix
      hlast_index
  have hbeta_unused := @helper_hbeta_unused_158 V E inferInstance inferInstance inferInstance G k e0
      phi T hq hlast r p hr hp hlastval hbad hP_length hPelementary beta hbeta_pen
  have hfree4 : 4 ≤ (TreeFreeColors phi
      (TreeSequencePrefix T (T.length - 2) (by omega) (by omega))).card :=
    TashTreeFourUnusedColors G k e0 phi T hmin (T.length - 2) (by omega) (by omega)
  let Q := TreeSequencePrefix T (T.length - 2) (by omega) (by omega)
  have hfree4' : 4 ≤ (TreeFreeColors phi Q).card := by simpa [Q] using hfree4
  let freeMinusBeta := (TreeFreeColors phi Q).erase beta
  have hfreeMinus : 3 ≤ freeMinusBeta.card := by
    have hc : (TreeFreeColors phi Q).card - 1 ≤ freeMinusBeta.card := by
      simpa [freeMinusBeta] using
        (Finset.pred_card_le_card_erase :
          (TreeFreeColors phi Q).card - 1 ≤ freeMinusBeta.card)
    omega
  let freeMinusGamma := freeMinusBeta.erase gamma
  have hfreeMinusGamma : 2 ≤ freeMinusGamma.card := by
    have hc : freeMinusBeta.card - 1 ≤ freeMinusGamma.card := by
      simpa [freeMinusGamma] using
        (Finset.pred_card_le_card_erase : freeMinusBeta.card - 1 ≤ freeMinusGamma.card)
    omega
  let edgeColor := (phi (T.edge ⟨T.length - 2, by omega⟩)).getD beta
  let freeFinal := freeMinusGamma.erase edgeColor
  have hfreeFinal : 1 ≤ freeFinal.card := by
    have hc : freeMinusGamma.card - 1 ≤ freeFinal.card := by
      simpa [freeFinal] using
        (Finset.pred_card_le_card_erase : freeMinusGamma.card - 1 ≤ freeFinal.card)
    omega
  obtain ⟨alpha, halpha⟩ := Finset.card_pos.mp hfreeFinal
  have halpha_ne_gamma : alpha ≠ gamma :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp halpha).2).1
  have halpha_ne_edge : alpha ≠ edgeColor := (Finset.mem_erase.mp halpha).1
  have halpha_ne_beta : alpha ≠ beta := by
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp
      (Finset.mem_erase.mp halpha).2).2).1
  have halpha_free : alpha ∈ TreeFreeColors phi Q :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp
      (Finset.mem_erase.mp halpha).2).2).2
  have halpha_missing : alpha ∈ TreeMissingColors phi Q := by
    exact (Finset.mem_sdiff.mp halpha_free).1
  obtain ⟨m, hmQ, hma⟩ := by
    rw [TreeMissingColors] at halpha_missing
    simpa only [Finset.mem_biUnion] using halpha_missing
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hmQ
  obtain ⟨mi, hmi⟩ := hmQ
  have hmq : mi.val + 2 ≤ T.length := by
    have hm_lt : mi.val < Q.length + 1 := mi.isLt
    have hQlen : Q.length = T.length - 2 := rfl
    omega
  have hmaT : alpha ∈ MissingColors G phi (T.vertex
      ⟨mi.val, by omega⟩) := by
    have hqv := hmi
    simp [Q] at hqv
    have hQle : Q.length ≤ T.length := by
      change T.length - 2 ≤ T.length
      omega
    have hqv' : T.vertex ⟨mi.val, by omega⟩ = m := by
      simpa [Q, TreeSequencePrefix, Fin.castLE, Fin.castLT] using hmi
    rw [hqv']
    exact hma
  have halpha_unused := @helper_halpha_unused_246 V E inferInstance inferInstance G k e0 phi T hq
      hlast gamma r p hr hp hrgamma hlastval hP_length beta alpha halpha_ne_gamma halpha_ne_edge
      halpha_free mi
  have hmi_lt : mi.val < T.length - 1 := by omega
  have hswap := TashTreeControlledInterchange G k e0 phi T hmin
    ⟨mi.val, by omega⟩
    ⟨T.length - 1, by show T.length - 1 < T.length + 1; omega⟩
    hmi_lt (by change T.length - 1 < T.length; omega)
    alpha beta (by exact halpha_ne_beta) hmaT hbeta_pen halpha_unused hbeta_unused
  dsimp only at hswap
  let phi3 := TwoColorComponentSwap G phi alpha beta
    (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
  have hmin3 := hswap.2.2.2.2.2.2.2.2
  have hbeta_last3 := @helper_hbeta_last3_299 V E inferInstance inferInstance inferInstance G k e0
      phi T hq hlast gamma r p hr hp hlastval hproper hP_length v hv beta hbeta_last alpha
      halpha_ne_beta mi hmq hswap
  have hbeta_ne_gamma : beta ≠ gamma := by
    intro he
    subst beta
    obtain ⟨ii, hii⟩ := T.attaches r
    have hrs : r.succ = Fin.last T.length := by
      apply Fin.ext
      simpa using hr
    have hinc : Incident G (T.vertex (Fin.last T.length)) (T.edge r) := by
      rw [Incident, hii]
      simp [hrs]
    have hnotpresent : gamma ∉ PresentColors G phi (T.vertex (Fin.last T.length)) := by
      simpa [MissingColors] using hbeta_last
    apply hnotpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T.edge r, hinc, hrgamma⟩
  refine ⟨phi3, beta, ⟨mi.val, by omega⟩, hmin3, ?_, ?_, hmq,
    hswap.2.2.2.2.1, hbeta_last3⟩
  · have hr_eq : r = ⟨T.length - 1, by omega⟩ := by
      apply Fin.ext
      exact hlastval
    rw [hr_eq] at hrgamma ⊢
    by_cases hm : Sum.inr (T.edge ⟨T.length - 1, by omega⟩) ∈
        TwoColorComponent G phi alpha beta
          (Sum.inl (T.vertex ⟨T.length - 1, by omega⟩))
    · simp [phi3, TwoColorComponentSwap, hm, hrgamma,
          Ne.symm halpha_ne_gamma, Ne.symm hbeta_ne_gamma]
    · simp [phi3, TwoColorComponentSwap, hm, hrgamma]
  · exact @helper_branch_437 V E inferInstance inferInstance G k e0 phi T hq hlast gamma r p hr
      hp hpgamma hlastval hpval hP_length beta alpha halpha_ne_gamma mi hbeta_ne_gamma
theorem TashTreeLastIndexThirdNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (gamma : Fin k) (r : Fin T.length) (p : Fin (T.length + 1))
    (hr : r.val + 1 = T.length) (hp : p.val + 1 = T.length)
    (hrgamma : phi (T.edge r) = some gamma)
    (hpgamma : gamma ∈ PresentColors G phi (T.vertex p)) :
    ∃ (phi₃ : PartialEdgeColoring E k) (beta : Fin k) (j : Fin (T.length + 1)),
    TashTreeMinimumBadPair G k e0 phi₃ T ∧
      phi₃ (T.edge r) = some gamma ∧
        gamma ∈ PresentColors G phi₃ (T.vertex p) ∧
          j.val + 2 ≤ T.length ∧
            beta ∈ MissingColors G phi₃ (T.vertex j) ∧
              beta ∈ MissingColors G phi₃ (T.vertex (Fin.last T.length)) := by
  classical
  have hlen : 3 ≤ T.length := by omega
  have hlastval : r.val = T.length - 1 := by omega
  have hpval : p.val = T.length - 1 := by omega
  have hbad := hmin.1
  have hproper := hbad.1.2.2.2.1
  have hnot := hbad.2.2
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  have hP_length : P.length = T.length - 1 := by rfl
  have hPprefix : TreeSequenceInitialSegment P T := by
    refine ⟨by rw [hP_length]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hPelementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet P) := by
    apply TashTreeProperPrefixElementary G k e0 phi T P hmin hPprefix
    change T.length - 1 < T.length
    omega
  have hlastmem : T.vertex (Fin.last T.length) ∈
      TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hprefixmem (i : Fin (T.length + 1)) :
      T.vertex i ∈ TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hcommon : ∃ u : V, u ∈ TreeSequenceVertexSet T ∧
      ∃ v : V, v ∈ TreeSequenceVertexSet T ∧ u ≠ v ∧
        ∃ c : Fin k, c ∈ MissingColors G phi u ∧
          c ∈ MissingColors G phi v := by
    simp only [ColoredVertexSetElementary, not_forall, not_forall, not_forall] at hnot
    rcases hnot with ⟨u, hu, v, hv, huv, hd⟩
    rcases Finset.not_disjoint_iff.mp hd with ⟨beta, hbu, hbv⟩
    exact ⟨u, hu, v, hv, huv, beta, hbu, hbv⟩
  obtain ⟨u, hu, v, hv, huv, beta, hbu, hbv⟩ := hcommon
  have hlast_or_prefix (w : V) (hw : w ∈ TreeSequenceVertexSet T) :
      w = T.vertex (Fin.last T.length) ∨ w ∈ TreeSequenceVertexSet P := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hw ⊢
    obtain ⟨i, hi⟩ := hw
    by_cases hival : i.val = T.length
    · left
      rw [← hi]
      congr 1
      exact Fin.ext hival
    · right
      let q : Fin (P.length + 1) := ⟨i.val, by rw [hP_length]; omega⟩
      refine ⟨q, ?_⟩
      have hq := hPprefix.2.1 q
      have hqi : Fin.castLE (Nat.succ_le_succ hPprefix.1) q = i := by
        apply Fin.ext
        rfl
      rw [hqi] at hq
      exact hq.symm.trans hi
  have hbeta_last : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
    rcases hlast_or_prefix u hu with huLast | huPrefix
    · simpa [huLast] using hbu
    · rcases hlast_or_prefix v hv with hvLast | hvPrefix
      · simpa [hvLast] using hbv
      · have hd := hPelementary huPrefix hvPrefix
          (by intro he; exact huv (he ▸ rfl))
        exact (Finset.disjoint_left.mp hd) hbu hbv |>.elim
  by_cases hsmall : ∃ j : Fin (T.length + 1),
      j.val + 2 ≤ T.length ∧
      beta ∈ MissingColors G phi (T.vertex j)
  · obtain ⟨j, hj, hbeta_j⟩ := hsmall
    refine ⟨phi, beta, j, hmin, ?_, hpgamma, hj, hbeta_j, hbeta_last⟩
    simpa [hlastval] using hrgamma
  · exact @helper_branch_128 V E inferInstance inferInstance inferInstance G k e0 phi T hmin hq
      hlast gamma r p hr hp hrgamma hpgamma hlastval hpval hbad hproper hP_length hPprefix
      hPelementary u hu v hv huv beta hbu hbv hlast_or_prefix hbeta_last hsmall
end GoldbergSeymour

end
