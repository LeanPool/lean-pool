/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidencePathFacts
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.TwoColorComponentColoringFacts
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo

/-!
# Outside-tree swaps of exit paths

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Colors along an exit path survive the outside-tree swap in the new color pair. -/
theorem outsideSwapExitEdgeColor {V E : Type*}
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (TjPrime : TreeSequence G e0)
    (rho1 : PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) {u x : V}
    (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u))
    (hgammaDelta : gammaN ≠ deltaN) (hbetaDelta : beta ≠ deltaN) (hgammaBeta : gammaN ≠ beta)
    (hexitPath : exitPath.IsPath)
    (hexitIntersection : ∀ w ∈ TreeSequenceVertexSet TjPrime,
      Sum.inl w ∈ exitPath.support → w = u) {g : E}
    (hgRho1 : rho1 g = some gammaN)
    (hgLast : exitPath.getVert (exitPath.length - 1) = Sum.inr g) {e : E}
    (he : Sum.inr e ∈ exitPath.support) (hcolor : rho1 e = some gammaN ∨ rho1 e = some deltaN) :
    OutsideTreeColorSwap TjPrime rho1 beta deltaN e = some gammaN ∨
      OutsideTreeColorSwap TjPrime rho1 beta deltaN e = some beta := by
  classical
  rcases hcolor with hgamma | hdelta
  · left
    by_cases heIncident : TreeIncidentEdge TjPrime e
    · simpa [OutsideTreeColorSwap, heIncident] using hgamma
    · simp only [OutsideTreeColorSwap, ite_eq_right heIncident]
      rw [ite_eq_right (by intro h; exact hgammaBeta (Option.some.inj (hgamma.symm.trans h)))]
      rw [ite_eq_right (by intro h; exact hgammaDelta (Option.some.inj (hgamma.symm.trans h)))]
      exact hgamma
  · have hnotIncident : ¬ TreeIncidentEdge TjPrime e := by
      rintro ⟨w, hwPrime, hwe⟩
      have hwu := hexitIntersection w hwPrime
        (incidencePathIncidentVertexMem exitPath hexitPath he hwe)
      subst w
      have heLast := incidencePathIncidentEndLast exitPath hexitPath he hwe
      have heg : e = g := Sum.inr.inj (heLast.symm.trans hgLast)
      subst e
      exact hgammaDelta (Option.some.inj (hgRho1.symm.trans hdelta))
    right
    simp only [OutsideTreeColorSwap, ite_eq_right hnotIncident]
    rw [ite_eq_right (by intro h; exact hbetaDelta (Option.some.inj (h.symm.trans hdelta)))]
    rw [ite_eq_left hdelta]

/-- At a vertex outside a closed tree, the new color pair comes from the old pair. -/
theorem outsideSwapEndpointColors {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (TjPrime : TreeSequence G e0)
    (rho1 : PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) {u x : V}
    (hclosure : ColoredVertexSetClosed G rho1 (TreeSequenceVertexSet TjPrime))
    (hgammaDelta : gammaN ≠ deltaN) (hbetaDelta : beta ≠ deltaN)
    (hbeta : beta ∈ MissingColors G rho1 u) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (hxPrime : x ∉ TreeSequenceVertexSet TjPrime) {e : E} (hxe : Incident G x e)
    (hcolor : OutsideTreeColorSwap TjPrime rho1 beta deltaN e = some gammaN ∨
      OutsideTreeColorSwap TjPrime rho1 beta deltaN e = some beta) :
    rho1 e = some gammaN ∨ rho1 e = some deltaN := by
  classical
  by_cases heIncident : TreeIncidentEdge TjPrime e
  · have hfixed : OutsideTreeColorSwap TjPrime rho1 beta deltaN e = rho1 e := by
      simp [OutsideTreeColorSwap, heIncident]
    obtain ⟨w, hwPrime, hwe⟩ := heIncident
    have hwx : w ≠ x := by
      intro hwx
      apply hxPrime
      simpa [← hwx] using hwPrime
    have hends : G.ends e = s(w, x) :=
      (Sym2.mem_and_mem_iff hwx).mp ⟨hwe, hxe⟩
    have heBoundary : e ∈ BoundaryEdges G
        (TreeSequenceVertexSet TjPrime) := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwPrime, x, hxPrime, hends⟩
    rcases hcolor with hgamma | hbetaColor
    · exact Or.inl (hfixed.symm.trans hgamma)
    · have hbetaOld : rho1 e = some beta :=
        hfixed.symm.trans hbetaColor
      exact False.elim
        ((hclosure heBoundary huPrime hbetaOld) hbeta)
  · unfold OutsideTreeColorSwap at hcolor
    rw [ite_eq_right heIncident] at hcolor
    by_cases hbetaOld : rho1 e = some beta
    · rw [ite_eq_left hbetaOld] at hcolor
      rcases hcolor with hdeltaGamma | hdeltaBeta
      · exact False.elim
          (hgammaDelta (Option.some.inj hdeltaGamma).symm)
      · exact False.elim
          (hbetaDelta (Option.some.inj hdeltaBeta).symm)
    · by_cases hdeltaOld : rho1 e = some deltaN
      · exact Or.inr hdeltaOld
      · rw [ite_eq_right hbetaOld, ite_eq_right hdeltaOld] at hcolor
        rcases hcolor with hgammaOld | hbetaOld'
        · exact Or.inl hgammaOld
        · exact False.elim (hbetaOld hbetaOld')

/-- An exit subpath becomes precisely a component after swapping colors outside a closed tree. -/
theorem outsideSwapExitPathComponent {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (TjPrime : TreeSequence G e0)
    (rho1 : PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) {terminalSupport u x : V}
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport) (Sum.inl x))
    (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u))
    (hclosure : ColoredVertexSetClosed G rho1 (TreeSequenceVertexSet TjPrime))
    (hgammaDelta : gammaN ≠ deltaN) (hbetaDelta : beta ≠ deltaN) (hgammaBeta : gammaN ≠ beta)
    (hbeta : beta ∈ MissingColors G rho1 u) (hpath : p.IsPath)
    (hcomponent : {y | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hxPrime : x ∉ TreeSequenceVertexSet TjPrime) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (hexitPath : exitPath.IsPath)
    (hfirstLast : p.getVert (p.length - 1) = exitPath.getVert 1)
    (hexitIntersection : ∀ w ∈ TreeSequenceVertexSet TjPrime,
      Sum.inl w ∈ exitPath.support → w = u)
    (hrho0Proper : IsProperEdgeColoring G (OutsideTreeColorSwap TjPrime rho1 beta deltaN))
    (hbetaRho0 : beta ∈ MissingColors G (OutsideTreeColorSwap TjPrime rho1 beta deltaN) u)
    {g : E} (hug : Incident G u g) (hgExit : Sum.inr g ∈ exitPath.support)
    (hgRho1 : rho1 g = some gammaN) :
    {y | y ∈ exitPath.support} = TwoColorComponent G
      (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u) := by
  classical
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  have hgLast := incidencePathIncidentEndLast exitPath hexitPath hgExit hug
  have hgRho0 : rho0 g = some gammaN := by
    simpa [rho0, OutsideTreeColorSwap, show TreeIncidentEdge TjPrime g from
      ⟨u, huPrime, hug⟩] using hgRho1
  have adjacent := incidenceWalkAdjacentOfEdgeColors exitPath
    (fun e he hc => outsideSwapExitEdgeColor TjPrime rho1 gammaN deltaN beta exitPath
      hgammaDelta hbetaDelta hgammaBeta hexitPath hexitIntersection hgRho1 hgLast he hc)
  have startUnique : ∀ z, (TwoColorIncidenceGraph G rho0 gammaN beta).Adj (Sum.inl x) z →
      z = exitPath.getVert 1 := by
    intro z hadj
    have oldAdj : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Adj (Sum.inl x) z := by
      cases z with
      | inl v => exact False.elim hadj
      | inr e =>
        exact ⟨hadj.1, outsideSwapEndpointColors TjPrime rho1 gammaN deltaN beta
          hclosure hgammaDelta hbetaDelta hbeta huPrime hxPrime hadj.1 hadj.2⟩
    exact (incidenceComponentPathEndNeighbor p hpath hcomponent oldAdj).trans hfirstLast
  have endUnique : ∀ z, (TwoColorIncidenceGraph G rho0 gammaN beta).Adj (Sum.inl u) z →
      z = exitPath.getVert (exitPath.length - 1) := by
    intro z hadj
    have leaf := TwoColorMissingVertexLeaf G k rho0 gammaN beta hgammaBeta hrho0Proper u
      (Or.inr hbetaRho0)
    exact (leaf hadj (show (TwoColorIncidenceGraph G rho0 gammaN beta).Adj (Sum.inl u)
      (Sum.inr g) from ⟨hug, Or.inl hgRho0⟩)).trans hgLast.symm
  exact degreeTwoPathSupportEqComponent exitPath hexitPath
    (TwoColorIncidenceDegreeAtMostTwo G rho0 gammaN beta hrho0Proper)
    adjacent startUnique endUnique

end GoldbergSeymour

end
