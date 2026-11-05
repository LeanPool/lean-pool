/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TashTreeBadPair
public import LeanPool.GoldbergSeymour.TashTreePathIndex
public import LeanPool.GoldbergSeymour.TashTreeRankLess
public import LeanPool.GoldbergSeymour.TashTreeSuffixPath
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePreservesTashkinovTree
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentTashkinovSplice

/-!
# Tash Tree No Repeated Intersection Shortening

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem TashTreeNoRepeatedIntersectionShortening_branch_72.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), TashTreeMinimumBadPair G k e0 phi T → 2 < TashTreePathIndex G T → TashTreePathIndex
        G T < T.length →
    ∀ (beta epsilon : Fin k), epsilon ≠ beta →
    ∀ (i m : Fin (T.length + 1)), ↑i + 2 ≤ TashTreePathIndex G T → ↑m + 2 ≤ TashTreePathIndex G T
        → beta ∈ MissingColors G phi (T.vertex i) → beta ∈ MissingColors G phi (T.vertex (Fin.last
        T.length)) → epsilon ∈ MissingColors G phi (T.vertex m) → (
    ∃ (s : Fin (T.length + 1)), ↑s + 1 ≤ TashTreePathIndex G T ∧ Sum.inl (T.vertex s) ∈
        TwoColorComponent G phi epsilon beta (Sum.inl (T.vertex (Fin.last T.length)))) → (
    ∀ (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T.length), TashkinovTree G e0 phi (TreeSequencePrefix T q hq
        hqT)) → IsProperEdgeColoring G phi → (
    ∃ (t : Fin (T.length + 1)), ↑t + 2 ≤ TashTreePathIndex G T ∧ Sum.inl (T.vertex t) ∈
        TwoColorComponent G phi epsilon beta (Sum.inl (T.vertex (Fin.last T.length)))) → False := by
  classical
  intro V E _ _ _ G k e0 phi T hmin hq hbefore beta epsilon hne i m hi hm hbeta hlast hepsilon
      hmeets hTashPrefix hproper hsmall
  let S := TreeSequencePrefix T (TashTreePathIndex G T - 2) (by omega)
      (by omega)
  rcases hsmall with ⟨s, hs, hsm⟩
  have hq3 : 3 ≤ TashTreePathIndex G T := by omega
  have hqT : TashTreePathIndex G T - 2 ≤ T.length := by omega
  have hSlen : S.length = TashTreePathIndex G T - 2 := rfl
  have hiS : T.vertex i ∈ TreeSequenceVertexSet S := by
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨Fin.castLT i (by omega),
      Finset.mem_univ _, ?_⟩
    rfl
  have hmS : T.vertex m ∈ TreeSequenceVertexSet S := by
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨Fin.castLT m (by omega),
      Finset.mem_univ _, ?_⟩
    rfl
  have hlastOut : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet S := by
    intro hlastIn
    rw [TreeSequenceVertexSet] at hlastIn
    rcases Finset.mem_image.mp hlastIn with ⟨j, hj, heq⟩
    have hv : (Fin.castLE (Nat.succ_le_succ hqT) j : Fin (T.length + 1)) =
        Fin.last T.length := by
      apply T.vertex_injective
      simpa [S, TreeSequencePrefix] using heq
    have hvval := congrArg Fin.val hv
    simp only [Fin.castLE, Fin.last] at hvval
    omega
  have hbetaS : beta ∈ TreeMissingColors phi S := by
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨T.vertex i, hiS, hbeta⟩
  have hepsilonS : epsilon ∈ TreeMissingColors phi S := by
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨T.vertex m, hmS, hepsilon⟩
  have hmeetS : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi epsilon beta
        (Sum.inl (T.vertex (Fin.last T.length))) := by
    refine ⟨T.vertex s, ?_, hsm⟩
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨Fin.castLT s (by omega),
      Finset.mem_univ _, ?_⟩
    rfl
  obtain ⟨u, S', hu, hucomp, hSS', hlength, haugment, hlastVertex, hsplice⟩ :=
    TwoColorComponentTashkinovSplice G phi S epsilon beta
      (T.vertex (Fin.last T.length)) hproper hne hepsilonS hbetaS
      hlastOut hmeetS
  have hTashS : TashkinovTree G e0 phi S := hTashPrefix _ (by omega) (by omega)
  have hTashS' := TashkinovAugmentationSequencePreservesTashkinovTree
    G e0 phi S S' hTashS haugment
  have hnotElementary : ¬ ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet S') := by
    intro he
    have hv' : T.vertex i ∈ TreeSequenceVertexSet S' := by
      rw [TreeSequenceVertexSet]
      let ii : Fin (S.length + 1) := Fin.castLT i (by omega)
      refine Finset.mem_image.mpr ⟨Fin.castLE (Nat.succ_le_succ hSS'.1) ii,
        Finset.mem_univ _, ?_⟩
      rw [hSS'.2.1]
      rfl
    have hy' : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet S' := by
      rw [← hlastVertex, TreeSequenceVertexSet]
      exact Finset.mem_image.mpr ⟨Fin.last S'.length, Finset.mem_univ _, rfl⟩
    have hvne : T.vertex i ≠ T.vertex (Fin.last T.length) := by
      intro hvEq
      have hvEq' := T.vertex_injective hvEq
      have hvVal : i.val = T.length := by simpa using congrArg Fin.val hvEq'
      omega
    exact (Finset.disjoint_left.mp (he hv' hy' hvne)) hbeta hlast
  have hbad : TashTreeBadPair G k e0 phi S' := ⟨hmin.1.1, hTashS', hnotElementary⟩
  have hsuffix : TashTreeSuffixPath G S' (TashTreePathIndex G T - 1) := by
    refine ⟨by omega, by omega, ?_⟩
    intro r hr
    have hrbase : S.length ≤ r.val := by omega
    have hrne : r.val ≠ S.length := by omega
    have hrne' : r.val ≠ TashTreePathIndex G T - 2 := by omega
    simpa [hSlen, hrne'] using (hsplice r hrbase).2.2.2.2
  have hidx : TashTreePathIndex G S' ≤ TashTreePathIndex G T - 1 := by
    unfold TashTreePathIndex
    exact Nat.find_min' _ hsuffix
  apply (hmin.2 hbad)
  left
  omega

private theorem TashTreeNoRepeatedIntersectionShortening_branch_153.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), TashTreeMinimumBadPair G k e0 phi T → 2 < TashTreePathIndex G T → TashTreePathIndex
        G T < T.length →
    ∀ (beta epsilon : Fin k), epsilon ≠ beta →
    ∀ (i m : Fin (T.length + 1)), ↑i + 2 ≤ TashTreePathIndex G T → ↑m + 2 ≤ TashTreePathIndex G T
        → beta ∈ MissingColors G phi (T.vertex i) → beta ∈ MissingColors G phi (T.vertex (Fin.last
        T.length)) → epsilon ∈ MissingColors G phi (T.vertex m) → (
    ∃ (s : Fin (T.length + 1)), ↑s + 1 ≤ TashTreePathIndex G T ∧ Sum.inl (T.vertex s) ∈
        TwoColorComponent G phi epsilon beta (Sum.inl (T.vertex (Fin.last T.length)))) → (
    ∀ (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T.length), TashkinovTree G e0 phi (TreeSequencePrefix T q hq
        hqT)) → IsProperEdgeColoring G phi → (¬
    ∃ (t : Fin (T.length + 1)), ↑t + 2 ≤ TashTreePathIndex G T ∧ Sum.inl (T.vertex t) ∈
        TwoColorComponent G phi epsilon beta (Sum.inl (T.vertex (Fin.last T.length)))) → False := by
  classical
  intro V E _ _ _ G k e0 phi T hmin hq hbefore beta epsilon hne i m hi hm hbeta hlast hepsilon
      hmeets hTashPrefix hproper hsmall
  rcases hmeets with ⟨s, hs, hsm⟩
  have havoid :
    ∀ t : Fin (T.length + 1), t.val + 2 ≤ TashTreePathIndex G T → Sum.inl (T.vertex t) ∉
        TwoColorComponent G phi epsilon beta (Sum.inl (T.vertex (Fin.last T.length))) := by
    intro t ht htc
    apply hsmall
    exact ⟨t, ht, htc⟩
  have hsLast : s.val + 1 = TashTreePathIndex G T := by
    have hqone : TashTreePathIndex G T - 1 + 1 = TashTreePathIndex G T := by omega
    have hsnot : ¬ s.val + 2 ≤ TashTreePathIndex G T := by
      intro hh
      exact havoid s hh hsm
    omega
  let S := TreeSequencePrefix T (TashTreePathIndex G T - 1) (by omega) (by omega)
  have hq3 : 3 ≤ TashTreePathIndex G T := by omega
  have hqT : TashTreePathIndex G T - 1 ≤ T.length := by omega
  have hiBound : i.val < S.length + 1 := by change i.val < TashTreePathIndex G T - 1 + 1; omega
  have hmBound : m.val < S.length + 1 := by change m.val < TashTreePathIndex G T - 1 + 1; omega
  have hsBound : s.val < S.length + 1 := by change s.val < TashTreePathIndex G T - 1 + 1; omega
  have hiS : T.vertex i ∈ TreeSequenceVertexSet S := by
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨Fin.castLT i hiBound,
      Finset.mem_univ _, ?_⟩
    rfl
  have hmS : T.vertex m ∈ TreeSequenceVertexSet S := by
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨Fin.castLT m hmBound,
      Finset.mem_univ _, ?_⟩
    rfl
  have hlastOut : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet S := by
    intro hlastIn
    rw [TreeSequenceVertexSet] at hlastIn
    rcases Finset.mem_image.mp hlastIn with ⟨j, hj, heq⟩
    have hv : (Fin.castLE (Nat.succ_le_succ hqT) j : Fin (T.length + 1)) =
        Fin.last T.length := by
      apply T.vertex_injective
      simpa [S, TreeSequencePrefix] using heq
    have hvval := congrArg Fin.val hv
    simp only [Fin.castLE, Fin.last] at hvval
    omega
  have hbetaS : beta ∈ TreeMissingColors phi S := by
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨T.vertex i, hiS, hbeta⟩
  have hepsilonS : epsilon ∈ TreeMissingColors phi S := by
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨T.vertex m, hmS, hepsilon⟩
  have hmeetS : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi epsilon beta
        (Sum.inl (T.vertex (Fin.last T.length))) := by
    refine ⟨T.vertex s, ?_, hsm⟩
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨Fin.castLT s hsBound,
      Finset.mem_univ _, ?_⟩
    rfl
  obtain ⟨u, S', hu, hucomp, hSS', hlength, haugment, hlastVertex, hsplice⟩ :=
    TwoColorComponentTashkinovSplice G phi S epsilon beta
      (T.vertex (Fin.last T.length)) hproper hne hepsilonS hbetaS
      hlastOut hmeetS
  have hTashS : TashkinovTree G e0 phi S := hTashPrefix _ (by omega) (by omega)
  have hTashS' := TashkinovAugmentationSequencePreservesTashkinovTree
    G e0 phi S S' hTashS haugment
  have hbad : TashTreeBadPair G k e0 phi S' := by
    refine ⟨hmin.1.1, hTashS', ?_⟩
    intro he
    have hv' : T.vertex i ∈ TreeSequenceVertexSet S' := by
      rw [TreeSequenceVertexSet]
      let ii : Fin (S.length + 1) := Fin.castLT i (by omega)
      refine Finset.mem_image.mpr ⟨Fin.castLE (Nat.succ_le_succ hSS'.1) ii,
        Finset.mem_univ _, ?_⟩
      rw [hSS'.2.1]
      rfl
    have hy' : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet S' := by
      rw [← hlastVertex, TreeSequenceVertexSet]
      exact Finset.mem_image.mpr ⟨Fin.last S'.length, Finset.mem_univ _, rfl⟩
    have hvne : T.vertex i ≠ T.vertex (Fin.last T.length) := by
      intro hvEq
      have hvEq' := T.vertex_injective hvEq
      have hvVal : i.val = T.length := by simpa using congrArg Fin.val hvEq'
      omega
    exact (Finset.disjoint_left.mp (he hv' hy' hvne)) hbeta hlast
  have huLast : u = S.vertex (Fin.last S.length) := by
    rw [TreeSequenceVertexSet] at hu
    rcases Finset.mem_image.mp hu with ⟨j, hj, hjEq⟩
    by_contra hneLast
    have hjne : j.val ≠ S.length := by
      intro heq
      apply hneLast
      rw [← hjEq]
      congr 1
      apply Fin.ext
      exact heq
    have hjbound : j.val + 2 ≤ TashTreePathIndex G T := by
      have hjlt := j.isLt
      change j.val < TashTreePathIndex G T - 1 + 1 at hjlt
      have hqone : TashTreePathIndex G T - 1 + 1 = TashTreePathIndex G T := by omega
      rw [← hqone] at hjlt
      change j.val ≠ TashTreePathIndex G T - 1 at hjne
      omega
    apply havoid (Fin.castLT j (by  omega)) hjbound
    rw [← hjEq] at hucomp
    simpa [S, TreeSequencePrefix, Fin.castLE, Fin.castLT] using hucomp
  have hsuffix : TashTreeSuffixPath G S' (TashTreePathIndex G T - 1) := by
    refine ⟨by omega, by omega, ?_⟩
    intro r hr
    have hrbase : S.length ≤ r.val := by
      change TashTreePathIndex G T - 1 ≤ r.val
      exact hr
    by_cases hrfirst : r.val = S.length
    · have hrEq : r.castSucc = Fin.castLE (Nat.succ_le_succ hSS'.1) (Fin.last S.length) := by
        apply Fin.ext
        simp only [Fin.castSucc, Fin.castLE, Fin.last]
        exact hrfirst
      have hfirst := (hsplice r hrbase).2.2.2.2
      rw [hrfirst] at hfirst
      have hvertex : S'.vertex r.castSucc = u := by
        rw [hrEq, hSS'.2.1, huLast]
      rw [hvertex]
      simpa [hrfirst] using hfirst
    · have hrne' : r.val ≠ TashTreePathIndex G T - 1 := by
        intro heq
        apply hrfirst
        exact heq
      simpa [hrne', hrfirst] using (hsplice r hrbase).2.2.2.2
  have hidx : TashTreePathIndex G S' ≤ TashTreePathIndex G T - 1 := by
    unfold TashTreePathIndex
    exact Nat.find_min' _ hsuffix
  apply (hmin.2 hbad)
  left
  omega

theorem TashTreeNoRepeatedIntersectionShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (beta epsilon : Fin k) (hne : epsilon ≠ beta)
    (i m : Fin (T.length + 1))
    (hi : i.val + 2 ≤ TashTreePathIndex G T)
    (hm : m.val + 2 ≤ TashTreePathIndex G T)
    (hbeta : beta ∈ MissingColors G phi (T.vertex i))
    (hlast : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hepsilon : epsilon ∈ MissingColors G phi (T.vertex m))
    (hmeets : ∃ s : Fin (T.length + 1),
      s.val + 1 ≤ TashTreePathIndex G T ∧
      Sum.inl (T.vertex s) ∈
        TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))) :
    False := by
  classical
  have hTashPrefix : ∀ (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T.length),
      TashkinovTree G e0 phi (TreeSequencePrefix T q hq hqT) := by
    intro q hq hqT j hj
    rcases hmin.1.2.1 (Fin.castLE hqT j) hj with
      ⟨r, c, hcolor, hmissing⟩
    refine ⟨r, c, ?_, ?_⟩
    · exact hcolor
    · exact hmissing
  have hproper : IsProperEdgeColoring G phi := hmin.1.1.2.2.2.1
  by_cases hsmall : ∃ t : Fin (T.length + 1),
      t.val + 2 ≤ TashTreePathIndex G T ∧
        Sum.inl (T.vertex t) ∈ TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))
  · exact @TashTreeNoRepeatedIntersectionShortening_branch_72 V E inferInstance inferInstance
      inferInstance G k e0 phi T hmin hq hbefore beta epsilon hne i m hi hm hbeta hlast hepsilon
      hmeets hTashPrefix hproper hsmall
  · exact @TashTreeNoRepeatedIntersectionShortening_branch_153 V E inferInstance inferInstance
      inferInstance G k e0 phi T hmin hq hbefore beta epsilon hne i m hi hm hbeta hlast hepsilon
      hmeets hTashPrefix hproper hsmall
end GoldbergSeymour

end
