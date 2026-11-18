/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeControlledRepeatedSuffixContradiction
public import LeanPool.GoldbergSeymour.TashTreeDisjointComponentNormalization

/-!
# Tash Tree No Repeated Disjoint Reduction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeNoRepeatedDisjointReduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (beta gamma epsilon : Fin k)
    (hge : gamma ≠ beta) (heg : epsilon ≠ gamma) (heb : epsilon ≠ beta)
    (i m : Fin (T.length + 1))
    (hi : i.val + 2 ≤ TashTreePathIndex G T)
    (hm : m.val + 2 ≤ TashTreePathIndex G T)
    (hbeta : beta ∈ MissingColors G phi (T.vertex i))
    (hlast : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hepsilon : epsilon ∈ MissingColors G phi (T.vertex m))
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩))
    (hgammaUnused : TreeColorUnusedThrough phi T gamma
      ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩)
    (hepsilonUnused : TreeColorUnusedThrough phi T epsilon
      ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩)
    (havoid : ∀ s : Fin (T.length + 1),
      s.val + 1 ≤ TashTreePathIndex G T →
      Sum.inl (T.vertex s) ∉
        TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))) : False := by
  classical
  let qn := TashTreePathIndex G T
  let q : Fin (T.length + 1) := ⟨qn, Nat.lt_succ_of_lt hbefore⟩
  let p : Fin (T.length + 1) := ⟨qn - 1, by omega⟩
  let pr : Fin T.length := ⟨qn - 1, by omega⟩
  have hmin0 := hmin
  rcases hmin with ⟨hbad, hminimal⟩
  rcases hbad with ⟨htriple, htree, hnon⟩
  rcases htriple with ⟨hcritical, hchromatic, hdegree, hproper, hone⟩
  let z : Sum V E := Sum.inl (T.vertex (Fin.last T.length))
  let C := TwoColorComponent G phi epsilon beta z
  have hvertices : ∀ s : Fin (T.length + 1), s.val ≤ p.val →
      Sum.inl (T.vertex s) ∉ C := by
    intro s hs
    exact havoid s (by dsimp [p, qn] at *; omega)
  have hedgeAvoid : ∀ r : Fin T.length, r.val < p.val →
      Sum.inr (T.edge r) ∉ C := by
    intro r hr heC
    rcases T.attaches r with ⟨a, ha⟩
    let s : Fin (T.length + 1) :=
      ⟨a.val, by omega⟩
    have hinc : Incident G (T.vertex s) (T.edge r) := by
      have hs : s = Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt)) :=
        Fin.ext (by rfl)
      rw [hs, Incident, ha]
      simp
    by_cases hcol : phi (T.edge r) = some epsilon ∨
        phi (T.edge r) = some beta
    · have hsC : Sum.inl (T.vertex s) ∈ C := by
        change Sum.inl (T.vertex s) ∈
          ((TwoColorIncidenceGraph G phi epsilon beta).connectedComponentMk z).supp
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        have hadj : (TwoColorIncidenceGraph G phi epsilon beta).Adj
            (Sum.inl (T.vertex s)) (Sum.inr (T.edge r)) := by
          simp [TwoColorIncidenceGraph, hinc, hcol]
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).trans heC
      apply hvertices s
      · dsimp [s, p, pr, qn]
        have ha_le : a.val ≤ r.val := Nat.le_of_lt_succ a.isLt
        have hr' : r.val < qn - 1 := by simpa [p] using hr
        omega
      · exact hsC
    · let H := TwoColorIncidenceGraph G phi epsilon beta
      have hno : ∀ x, H.Reachable (Sum.inr (T.edge r)) x →
          x = Sum.inr (T.edge r) := by
        intro x hx
        rw [H.reachable_iff_reflTransGen] at hx
        induction hx with
        | refl => rfl
        | tail h ha ih =>
          subst ih
          rename_i c
          cases c <;> simp [H, TwoColorIncidenceGraph, hcol] at ha
      have hrch : H.Reachable (Sum.inr (T.edge r)) z := by
        apply SimpleGraph.ConnectedComponent.eq.mp
        exact heC
      have heq := hno _ hrch
      have hz : Sum.inl (T.vertex (Fin.last T.length)) =
          Sum.inr (T.edge r) := by simp [z] at heq
      exact Sum.inl_ne_inr hz
  have hcut : Sum.inr (T.edge pr) ∉ C := by
    intro heC
    rcases T.attaches pr with ⟨a, ha⟩
    let s : Fin (T.length + 1) :=
      ⟨a.val, by omega⟩
    have hinc : Incident G (T.vertex s) (T.edge pr) := by
      have hs : s = Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ pr.isLt)) :=
        Fin.ext (by rfl)
      rw [hs, Incident, ha]
      simp
    by_cases hcol : phi (T.edge pr) = some epsilon ∨
        phi (T.edge pr) = some beta
    · have hsC : Sum.inl (T.vertex s) ∈ C := by
        change Sum.inl (T.vertex s) ∈
          ((TwoColorIncidenceGraph G phi epsilon beta).connectedComponentMk z).supp
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        have hadj : (TwoColorIncidenceGraph G phi epsilon beta).Adj
            (Sum.inl (T.vertex s)) (Sum.inr (T.edge pr)) := by
          simp [TwoColorIncidenceGraph, hinc, hcol]
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).trans heC
      exact hvertices s (by
        dsimp [s, p, qn]
        have ha_le : a.val ≤ pr.val := Nat.le_of_lt_succ a.isLt
        omega) hsC
    · let H := TwoColorIncidenceGraph G phi epsilon beta
      have hno : ∀ x, H.Reachable (Sum.inr (T.edge pr)) x →
          x = Sum.inr (T.edge pr) := by
        intro x hx
        rw [H.reachable_iff_reflTransGen] at hx
        induction hx with
        | refl => rfl
        | tail h ha ih =>
          subst ih
          rename_i c
          cases c <;> simp [H, TwoColorIncidenceGraph, hcol] at ha
      have hrch : H.Reachable (Sum.inr (T.edge pr)) z := by
        apply SimpleGraph.ConnectedComponent.eq.mp
        exact heC
      have heq := hno _ hrch
      have hz : Sum.inl (T.vertex (Fin.last T.length)) =
          Sum.inr (T.edge pr) := by simp [z] at heq
      exact Sum.inl_ne_inr hz
  have hnorm := TashTreeDisjointComponentNormalization G k e0 phi T
      hmin0 p m i
      (by dsimp [p, qn]; omega) (by dsimp [p, qn]; omega)
      (by dsimp [p, qn]; omega) epsilon beta heb hepsilon hbeta hlast
      (by intro s hs; exact hvertices s hs)
      (by intro r hr; exact hedgeAvoid r hr)
  dsimp only at hnorm
  rcases hnorm with ⟨hmin', hfixed, hepsilon', hlast'⟩
  have hcut' : TwoColorComponentSwap G phi epsilon beta z (T.edge pr) =
      phi (T.edge pr) := by
    simp [TwoColorComponentSwap, hcut, z, C]
  have hepsilonUnused' : TreeColorUnusedThrough
      (TwoColorComponentSwap G phi epsilon beta z) T epsilon q := by
    intro r hr1 hrq
    by_cases hsmall : r.val < p.val
    · rw [hfixed r hsmall]
      exact hepsilonUnused r hr1 hrq
    · change r.val < qn at hrq
      change ¬ r.val < qn - 1 at hsmall
      have heq : r.val = pr.val := by dsimp [pr]; omega
      have hrp : r = pr := Fin.ext heq
      rw [hrp, hcut']
      have hh := hepsilonUnused r hr1 hrq
      simpa [hrp] using hh
  have hgammaUnused' : TreeColorUnusedThrough
      (TwoColorComponentSwap G phi epsilon beta z) T gamma q := by
    intro r hr1 hrq
    by_cases hsmall : r.val < p.val
    · rw [hfixed r hsmall]
      exact hgammaUnused r hr1 hrq
    · change r.val < qn at hrq
      change ¬ r.val < qn - 1 at hsmall
      have heq : r.val = pr.val := by dsimp [pr]; omega
      have hrp : r = pr := Fin.ext heq
      rw [hrp, hcut']
      have hh := hgammaUnused r hr1 hrq
      simpa [hrp] using hh
  have hgamma' : gamma ∈ MissingColors G
      (TwoColorComponentSwap G phi epsilon beta z) (T.vertex q) := by
    have hb := TwoColorComponentSwapMissingBehavior G phi epsilon beta heb hproper z
    dsimp only at hb
    exact (hb.2.2.2 (T.vertex q) gamma (by exact heg.symm) (by exact hge)).2 hgamma
  apply TashTreeControlledRepeatedSuffixContradiction G k e0
      (TwoColorComponentSwap G phi epsilon beta z) T hmin' hq hbefore m q
      (by dsimp [q, qn]; omega) (by exact hbefore) (by dsimp [q, qn]; omega)
      epsilon gamma heg hepsilon' hgamma' hepsilonUnused' hgammaUnused'
  exact hlast'

end GoldbergSeymour

end
