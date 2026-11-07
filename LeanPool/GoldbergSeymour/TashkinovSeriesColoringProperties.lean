/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Coloring properties of certified Tashkinov series

Every stage is proper and leaves exactly the distinguished edge uncolored.
Derived from the certificates in Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Every certified step preserves the two basic coloring properties. -/
theorem TashkinovSeriesStep.coloringProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {data : TashkinovSeriesData G k rounds e0}
    {i : Fin (rounds + 1)} (step : TashkinovSeriesStep G k rounds e0 input data i) :
    IsProperEdgeColoring G (data.coloring i) ∧ IsOneEdgeUncolored (data.coloring i) e0 := by
  cases step with
  | initial triple _ coloring _ _ _ _ _ _ _ _ =>
      rw [coloring]
      exact triple.2.2.2
  | SE _ _ _ _ _ _ choice _ coloring _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [coloring]
      exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
  | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ proper one _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨proper, one⟩
  | RE _ proper one _ _ _ coloring _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [coloring]
      exact ⟨proper, one⟩

/-- Every stage of a certified series is proper and has one uncolored edge. -/
theorem TashkinovSeries.coloringProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (i : Fin (rounds + 1)) :
    IsProperEdgeColoring G (series.data.coloring i) ∧
      IsOneEdgeUncolored (series.data.coloring i) e0 :=
  (series.certified i).coloringProperties

/-- A revisiting extension preserves the preceding stage's coloring. -/
theorem TashkinovSeries.revisitingStepColoring {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {rounds : ℕ}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (j : Fin rounds) (hj : series.data.kind j.succ = some TashkinovExtensionKind.RE) :
    series.data.coloring j.succ = series.data.coloring j.castSucc := by
  have hstep := series.certified j.succ
  generalize hslot : j.succ = slot at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored
      initialEdges initialKind initialVertex initialOutside
      initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero j hslot).elim
  | SE i prevProper prevOne prevClosed prevNotStrong noRE
      ch alternative coloring stored edges kind vertex
      outside delta gamma adjoined adjoinedExactly closed
      ordered strict =>
      have hbad := kind.symm.trans
        (by simpa [hslot] using hj)
      cases hbad
  | PE i prevProper prevOne prevClosed prevNotStrong noRE
      ch alternativeFails gamma gammaRule second
      secondProper secondOne secondStable exit coloring
      coloringProper coloringOne stored edges kind vertex
      outside delta gammaValue closed ordered strict =>
      have hbad := kind.symm.trans
        (by simpa [hslot] using hj)
      cases hbad
  | RE i prevProper prevOne prevClosed prevNotStrong cert
      coloring stored edges kind vertex outside delta gamma
      adjoined adjoinedExactly closed ordered strict =>
      have hi : i = j := by
        apply Fin.ext
        have hv := congrArg Fin.val hslot
        simp only [Fin.val_succ] at hv
        omega
      subst i
      simpa [hslot] using coloring

/-- A block containing only revisiting extensions has constant coloring. -/
theorem TashkinovSeries.revisitingIntervalColoring {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {rounds' : ℕ}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0 input)
    (a b : Fin (rounds' + 1)) (hab : a.val ≤ b.val)
    (hbetween : ∀ j : Fin (rounds' + 1), a.val < j.val → j.val ≤ b.val →
      series.data.kind j = some TashkinovExtensionKind.RE) :
    series.data.coloring b = series.data.coloring a := by
  have coloringAlong : ∀ m : ℕ, a.val ≤ m →
      m ≤ b.val → ∀ x : Fin (rounds' + 1),
      x.val = m →
        series.data.coloring x = series.data.coloring a := by
    intro m ham
    induction m, ham using Nat.le_induction with
    | base =>
        intro hmb x hx
        have hxa : x = a := by
          apply Fin.ext
          omega
        rw [hxa]
    | succ m ham ih =>
        intro hmb x hx
        let j : Fin rounds' := ⟨m, by
          have hbLt := b.isLt
          omega⟩
        have hjKind : series.data.kind j.succ =
            some TashkinovExtensionKind.RE := by
          apply hbetween j.succ
          · simp [j]
            omega
          · simp [j]
            omega
        have hstep := series.revisitingStepColoring j hjKind
        have hxj : x = j.succ := by
          apply Fin.ext
          simp [j, hx]
        calc
          series.data.coloring x =
              series.data.coloring j.succ := by rw [hxj]
          _ = series.data.coloring j.castSucc := hstep
          _ = series.data.coloring a :=
            ih (by omega) j.castSucc (by simp [j])
  exact coloringAlong b.val hab le_rfl b rfl

end GoldbergSeymour

end
