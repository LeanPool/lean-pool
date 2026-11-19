/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair

public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper

/-!
# Tash Tree Disjoint Component Normalization

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeDisjointComponentNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (p a b : Fin (T.length + 1)) (hp : p.val < T.length)
    (hap : a.val ≤ p.val) (hbp : b.val ≤ p.val)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex a))
    (hb : beta ∈ MissingColors G phi (T.vertex b))
    (hlast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hvertices : ∀ q : Fin (T.length + 1), q.val ≤ p.val →
      Sum.inl (T.vertex q) ∉
        TwoColorComponent G phi alpha beta
          (Sum.inl (T.vertex (Fin.last T.length))))
    (hedges : ∀ r : Fin T.length, r.val < p.val →
      Sum.inr (T.edge r) ∉
        TwoColorComponent G phi alpha beta
          (Sum.inl (T.vertex (Fin.last T.length)))) :
    let phi' := TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length)))
    TashTreeMinimumBadPair G k e0 phi' T ∧
      (∀ r : Fin T.length, r.val < p.val →
        phi' (T.edge r) = phi (T.edge r)) ∧
      alpha ∈ MissingColors G phi' (T.vertex a) ∧
      alpha ∈ MissingColors G phi' (T.vertex (Fin.last T.length)) := by
  classical
  dsimp only
  let z : Sum V E := Sum.inl (T.vertex (Fin.last T.length))
  let C := TwoColorComponent G phi alpha beta z
  let phi' := TwoColorComponentSwap G phi alpha beta z
  rcases hmin with ⟨hbad, hminimal⟩
  rcases hbad with ⟨htriple, hTash, hnotElementary⟩
  rcases htriple with ⟨hcritical, hchromatic, hdegree, hproper, hone⟩
  have hbehavior :=
    TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper z
  dsimp only at hbehavior
  have hroot : Sum.inl (T.vertex (Fin.last T.length)) ∈ C := by
    change z ∈ ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have haOutside : Sum.inl (T.vertex a) ∉ C := hvertices a hap
  have hbOutside : Sum.inl (T.vertex b) ∉ C := hvertices b hbp
  have ha' : alpha ∈ MissingColors G phi' (T.vertex a) := by
    rw [hbehavior.1 _ haOutside]
    exact ha
  have hb' : beta ∈ MissingColors G phi' (T.vertex b) := by
    rw [hbehavior.1 _ hbOutside]
    exact hb
  have hlast' : alpha ∈
      MissingColors G phi' (T.vertex (Fin.last T.length)) :=
    hbehavior.2.2.1 _ hroot hlast
  have hfixed : ∀ r : Fin T.length, r.val < p.val →
      phi' (T.edge r) = phi (T.edge r) := by
    intro r hr
    have hrOutside : Sum.inr (T.edge r) ∉ C := hedges r hr
    simp [phi', TwoColorComponentSwap, C, hrOutside]
  have hTash' : TashkinovTree G e0 phi' T := by
    intro r hr
    obtain ⟨w, c, he, hm⟩ := hTash r hr
    by_cases hrp : r.val < p.val
    · let q : Fin (T.length + 1) :=
        Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt))
      have hqp : q.val ≤ p.val := by
        dsimp [q]
        omega
      have hqOutside : Sum.inl (T.vertex q) ∉ C := hvertices q hqp
      refine ⟨w, c, (hfixed r hrp).trans he, ?_⟩
      change c ∈ MissingColors G phi' (T.vertex q)
      rw [hbehavior.1 _ hqOutside]
      exact hm
    · have hpr : p.val ≤ r.val := by omega
      have har : a.val ≤ r.val := le_trans hap hpr
      have hbr : b.val ≤ r.val := le_trans hbp hpr
      let wa : Fin (r.val + 1) := ⟨a.val, Nat.lt_succ_of_le har⟩
      let wb : Fin (r.val + 1) := ⟨b.val, Nat.lt_succ_of_le hbr⟩
      by_cases hca : c = alpha
      · by_cases heC : Sum.inr (T.edge r) ∈ C
        · refine ⟨wb, beta, ?_, ?_⟩
          · simp [phi', C, TwoColorComponentSwap, heC, he, hca]
          · simpa [wb] using hb'
        · refine ⟨wa, alpha, ?_, ?_⟩
          · simp [phi', C, TwoColorComponentSwap, heC, he, hca]
          · simpa [wa] using ha'
      · by_cases hcb : c = beta
        · by_cases heC : Sum.inr (T.edge r) ∈ C
          · refine ⟨wa, alpha, ?_, ?_⟩
            · simp [phi', C, TwoColorComponentSwap, heC, he, hcb]
            · simpa [wa] using ha'
          · refine ⟨wb, beta, ?_, ?_⟩
            · simp [phi', C, TwoColorComponentSwap, heC, he, hcb]
            · simpa [wb] using hb'
        · refine ⟨w, c, ?_, (hbehavior.2.2.2 _ c hca hcb).2 hm⟩
          by_cases heC : Sum.inr (T.edge r) ∈ C <;>
            simp [phi', C, TwoColorComponentSwap, heC, he, hca, hcb]
  have hproper' : IsProperEdgeColoring G phi' := by
    exact TwoColorComponentSwapProper G phi alpha beta hne hproper z
  have hone' : IsOneEdgeUncolored phi' e0 := by
    constructor
    · simp [phi', TwoColorComponentSwap, hone.1]
    · intro e he0
      obtain ⟨c, hc⟩ := hone.2 e he0
      by_cases heC : Sum.inr e ∈ C
      · by_cases hca : c = alpha
        · refine ⟨beta, ?_⟩
          simp [phi', C, TwoColorComponentSwap, heC, hc, hca]
        · by_cases hcb : c = beta
          · refine ⟨alpha, ?_⟩
            simp [phi', C, TwoColorComponentSwap, heC, hc, hcb]
          · refine ⟨c, ?_⟩
            simp [phi', C, TwoColorComponentSwap, heC, hc, hca, hcb]
      · exact ⟨c, by simpa [phi', C, TwoColorComponentSwap, heC] using hc⟩
  have htriple' : KTriple G k e0 phi' :=
    ⟨hcritical, hchromatic, hdegree, hproper', hone'⟩
  have haT : T.vertex a ∈ TreeSequenceVertexSet T := by
    rw [TreeSequenceVertexSet]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hlastT : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet T := by
    rw [TreeSequenceVertexSet]
    exact Finset.mem_image.mpr
      ⟨Fin.last T.length, Finset.mem_univ _, rfl⟩
  have hvertex_ne : T.vertex a ≠ T.vertex (Fin.last T.length) := by
    intro hav
    have hai := congrArg Fin.val (T.vertex_injective hav)
    simp only [Fin.val_last] at hai
    omega
  have hnotElementary' : ¬ ColoredVertexSetElementary G phi'
      (TreeSequenceVertexSet T) := by
    intro helem
    have hdisjoint := helem haT hlastT hvertex_ne
    exact (Finset.disjoint_left.mp hdisjoint) ha' hlast'
  have hminimum' : TashTreeMinimumBadPair G k e0 phi' T :=
    ⟨⟨htriple', hTash', hnotElementary'⟩, hminimal⟩
  exact ⟨hminimum', hfixed, ha', hlast'⟩

end GoldbergSeymour

end
