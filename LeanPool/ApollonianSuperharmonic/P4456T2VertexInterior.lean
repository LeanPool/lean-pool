/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

-- [TABLET NODE: P4456T2VertexInterior]

/-!
# P4456T2VertexInterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace VertexInteriorLemmas

private theorem hsector :
    ∀ (T : ProtoTile),
      ∀ (x : GaussianInt),
        ∀ (j : Fin (4 : ℕ)),
          ∀ (ε : ℝ),
            let δ : ℝ := min ε 1 / 4
            0 < δ →
              δ < 1 →
                let X : ℝ := (x.re : Int)
                let Y : ℝ := (x.im : Int)
                let Q : Fin 4 → ℝ × ℝ := fun k =>
                  if k = 0 then (X + δ, Y + δ)
                  else
                    if k = 1 then (X - δ, Y + δ)
                    else if k = 2 then (X - δ, Y - δ) else (X + δ, Y - δ)
                (∀ (k : Fin 4), Q k ∈ TileRealization T) →
                  LatticeVertexIncidentCell x j ∈ T.cells := by
  classical
  intro T x j ε δ hδpos hδone X Y Q hQreal
  -- Square membership in the corresponding open quadrant forces its base.
  fin_cases j
  · have hq := hQreal 0
    simp only [TileRealization, Set.mem_iUnion] at hq
    rcases hq with ⟨c, hc, hcp⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hcp
    rcases hcp with ⟨⟨hcrlo, hcilow⟩, ⟨hcrhi, hcihi⟩⟩
    have hcrloQ : (c.re : ℝ) ≤ (Q 0).1 := by
      simpa only [← GaussianInt.intCast_re] using hcrlo
    have hcrhiQ : (Q 0).1 ≤ (c.re : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_re] using hcrhi
    have hcilowQ : (c.im : ℝ) ≤ (Q 0).2 := by
      simpa only [← GaussianInt.intCast_im] using hcilow
    have hcihiQ : (Q 0).2 ≤ (c.im : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_im] using hcihi
    have hcrlo' : (c.re : ℝ) ≤ X + δ := by simpa [Q] using hcrloQ
    have hcrhi' : X + δ ≤ (c.re : ℝ) + 1 := by simpa [Q] using hcrhiQ
    have hcilow' : (c.im : ℝ) ≤ Y + δ := by simpa [Q] using hcilowQ
    have hcihi' : Y + δ ≤ (c.im : ℝ) + 1 := by simpa [Q] using hcihiQ
    simp only [X] at hcrlo' hcrhi'
    simp only [Y] at hcilow' hcihi'
    have hrelo : x.re - 1 < c.re := by
      have h : (x.re : ℝ) - 1 < (c.re : ℝ) := by
        linarith [hcrhi', hδpos]
      exact_mod_cast h
    have hrehi : c.re < x.re + 1 := by
      have h : (c.re : ℝ) < (x.re : ℝ) + 1 := by
        linarith [hcrlo', hδone]
      exact_mod_cast h
    have himlo : x.im - 1 < c.im := by
      have h : (x.im : ℝ) - 1 < (c.im : ℝ) := by
        linarith [hcihi', hδpos]
      exact_mod_cast h
    have himhi : c.im < x.im + 1 := by
      have h : (c.im : ℝ) < (x.im : ℝ) + 1 := by
        linarith [hcilow', hδone]
      exact_mod_cast h
    have hcre : c.re = x.re := by omega
    have hcim : c.im = x.im := by omega
    have hcEq : c = LatticeVertexIncidentCell x 0 := by
      ext <;> simp [LatticeVertexIncidentCell, hcre, hcim]
    change LatticeVertexIncidentCell x 0 ∈ T.cells
    simpa [hcEq] using hc
  · have hq := hQreal 1
    simp only [TileRealization, Set.mem_iUnion] at hq
    rcases hq with ⟨c, hc, hcp⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hcp
    rcases hcp with ⟨⟨hcrlo, hcilow⟩, ⟨hcrhi, hcihi⟩⟩
    have hcrloQ : (c.re : ℝ) ≤ (Q 1).1 := by
      simpa only [← GaussianInt.intCast_re] using hcrlo
    have hcrhiQ : (Q 1).1 ≤ (c.re : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_re] using hcrhi
    have hcilowQ : (c.im : ℝ) ≤ (Q 1).2 := by
      simpa only [← GaussianInt.intCast_im] using hcilow
    have hcihiQ : (Q 1).2 ≤ (c.im : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_im] using hcihi
    have hcrlo' : (c.re : ℝ) ≤ (x.re : ℝ) - δ := by
      simpa [Q, X] using hcrloQ
    have hcrhi' : (x.re : ℝ) - δ ≤ (c.re : ℝ) + 1 := by
      simpa [Q, X] using hcrhiQ
    have hcilow' : (c.im : ℝ) ≤ (x.im : ℝ) + δ := by
      simpa [Q, Y] using hcilowQ
    have hcihi' : (x.im : ℝ) + δ ≤ (c.im : ℝ) + 1 := by
      simpa [Q, Y] using hcihiQ
    have hrlo : x.re - 2 < c.re := by
      have h : (x.re : ℝ) - 2 < (c.re : ℝ) := by linarith [hcrhi', hδone]
      exact_mod_cast h
    have hrhi : c.re < x.re := by
      have h : (c.re : ℝ) < (x.re : ℝ) := by linarith [hcrlo', hδpos]
      exact_mod_cast h
    have hilo : x.im - 1 < c.im := by
      have h : (x.im : ℝ) - 1 < (c.im : ℝ) := by linarith [hcihi', hδpos]
      exact_mod_cast h
    have hihi : c.im < x.im + 1 := by
      have h : (c.im : ℝ) < (x.im : ℝ) + 1 := by linarith [hcilow', hδone]
      exact_mod_cast h
    have hcre : c.re = x.re - 1 := by omega
    have hcim : c.im = x.im := by omega
    have hcEq : c = LatticeVertexIncidentCell x 1 := by
      ext <;> simp [LatticeVertexIncidentCell, hcre, hcim]
    simpa [hcEq] using hc
  · have hq := hQreal 2
    simp only [TileRealization, Set.mem_iUnion] at hq
    rcases hq with ⟨c, hc, hcp⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hcp
    rcases hcp with ⟨⟨hcrlo, hcilow⟩, ⟨hcrhi, hcihi⟩⟩
    have hcrloQ : (c.re : ℝ) ≤ (Q 2).1 := by
      simpa only [← GaussianInt.intCast_re] using hcrlo
    have hcrhiQ : (Q 2).1 ≤ (c.re : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_re] using hcrhi
    have hcilowQ : (c.im : ℝ) ≤ (Q 2).2 := by
      simpa only [← GaussianInt.intCast_im] using hcilow
    have hcihiQ : (Q 2).2 ≤ (c.im : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_im] using hcihi
    have hcrlo' : (c.re : ℝ) ≤ (x.re : ℝ) - δ := by
      simpa [Q, X] using hcrloQ
    have hcrhi' : (x.re : ℝ) - δ ≤ (c.re : ℝ) + 1 := by
      simpa [Q, X] using hcrhiQ
    have hcilow' : (c.im : ℝ) ≤ (x.im : ℝ) - δ := by
      simpa [Q, Y] using hcilowQ
    have hcihi' : (x.im : ℝ) - δ ≤ (c.im : ℝ) + 1 := by
      simpa [Q, Y] using hcihiQ
    have hrlo : x.re - 2 < c.re := by
      have h : (x.re : ℝ) - 2 < (c.re : ℝ) := by linarith [hcrhi', hδone]
      exact_mod_cast h
    have hrhi : c.re < x.re := by
      have h : (c.re : ℝ) < (x.re : ℝ) := by linarith [hcrlo', hδpos]
      exact_mod_cast h
    have hilo : x.im - 2 < c.im := by
      have h : (x.im : ℝ) - 2 < (c.im : ℝ) := by linarith [hcihi', hδone]
      exact_mod_cast h
    have hihi : c.im < x.im := by
      have h : (c.im : ℝ) < (x.im : ℝ) := by linarith [hcilow', hδpos]
      exact_mod_cast h
    have hcre : c.re = x.re - 1 := by omega
    have hcim : c.im = x.im - 1 := by omega
    have hcEq : c = LatticeVertexIncidentCell x 2 := by
      ext <;> simp [LatticeVertexIncidentCell, hcre, hcim]
    simpa [hcEq] using hc
  · have hq := hQreal 3
    simp only [TileRealization, Set.mem_iUnion] at hq
    rcases hq with ⟨c, hc, hcp⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hcp
    rcases hcp with ⟨⟨hcrlo, hcilow⟩, ⟨hcrhi, hcihi⟩⟩
    have hcrloQ : (c.re : ℝ) ≤ (Q 3).1 := by
      simpa only [← GaussianInt.intCast_re] using hcrlo
    have hcrhiQ : (Q 3).1 ≤ (c.re : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_re] using hcrhi
    have hcilowQ : (c.im : ℝ) ≤ (Q 3).2 := by
      simpa only [← GaussianInt.intCast_im] using hcilow
    have hcihiQ : (Q 3).2 ≤ (c.im : ℝ) + 1 := by
      simpa only [← GaussianInt.intCast_im] using hcihi
    have hcrlo' : (c.re : ℝ) ≤ (x.re : ℝ) + δ := by
      simpa [Q, X] using hcrloQ
    have hcrhi' : (x.re : ℝ) + δ ≤ (c.re : ℝ) + 1 := by
      simpa [Q, X] using hcrhiQ
    have hcilow' : (c.im : ℝ) ≤ (x.im : ℝ) - δ := by
      simpa [Q, Y] using hcilowQ
    have hcihi' : (x.im : ℝ) - δ ≤ (c.im : ℝ) + 1 := by
      simpa [Q, Y] using hcihiQ
    have hrlo : x.re - 1 < c.re := by
      have h : (x.re : ℝ) - 1 < (c.re : ℝ) := by linarith [hcrhi', hδpos]
      exact_mod_cast h
    have hrhi : c.re < x.re + 1 := by
      have h : (c.re : ℝ) < (x.re : ℝ) + 1 := by linarith [hcrlo', hδone]
      exact_mod_cast h
    have hilo : x.im - 2 < c.im := by
      have h : (x.im : ℝ) - 2 < (c.im : ℝ) := by linarith [hcihi', hδone]
      exact_mod_cast h
    have hihi : c.im < x.im := by
      have h : (c.im : ℝ) < (x.im : ℝ) := by linarith [hcilow', hδpos]
      exact_mod_cast h
    have hcre : c.re = x.re := by omega
    have hcim : c.im = x.im - 1 := by omega
    have hcEq : c = LatticeVertexIncidentCell x 3 := by
      ext <;> simp [LatticeVertexIncidentCell, hcre, hcim]
    simpa [hcEq] using hc

end VertexInteriorLemmas

theorem P4456T2VertexInterior (T : ProtoTile) (hne : T.cells.Nonempty)
    (x : GaussianInt) (hx : x ∈ FootprintVertices T) :
    (GaussianRealPoint x ∈ interior (TileRealization T) ↔
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) ∧
    (x ∉ BoundaryFootprintVertices T ↔
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) := by
-- BODY
  classical
  have hsome : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := by
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨c, hc, hcase⟩
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [LatticeVertexIncidentCell, hc]⟩
    · refine ⟨1, ?_⟩
      simpa [LatticeVertexIncidentCell, sub_eq_add_neg] using hc
    · refine ⟨3, ?_⟩
      simpa [LatticeVertexIncidentCell, sub_eq_add_neg] using hc
    · refine ⟨2, ?_⟩
      simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using hc
  constructor
  · constructor
    · intro hinterior j
      by_contra hnot
      have hball : ∃ ε > 0,
          Metric.ball (GaussianRealPoint x) ε ⊆ TileRealization T :=
        Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinterior)
      obtain ⟨ε, hε, hsub⟩ := hball
      let δ : ℝ := min ε 1 / 4
      have hδpos : 0 < δ := by dsimp [δ]; positivity
      have hδeps : δ < ε := by dsimp [δ]; have := min_le_left ε 1; linarith
      have hδone : δ < 1 := by dsimp [δ]; have := min_le_right ε 1; linarith
      have hδabs : |δ| = δ := abs_of_pos hδpos
      let X : ℝ := (x.re : Int)
      let Y : ℝ := (x.im : Int)
      let Q : Fin 4 → ℝ × ℝ := fun k =>
        if k = 0 then (X + δ, Y + δ) else
        if k = 1 then (X - δ, Y + δ) else
        if k = 2 then (X - δ, Y - δ) else (X + δ, Y - δ)
      have hQball (k : Fin 4) : Q k ∈ Metric.ball (GaussianRealPoint x) ε := by
        fin_cases k <;>
          simp only [GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re,
              GaussianInt.intCast_im, Fin.isValue, Fin.mk_one, ↓reduceIte,
              Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_sub_cancel_left, abs_neg,
              hδabs, add_sub_cancel_left, max_self, Q, X, Y, Fin.reduceFinMk, Fin.reduceEq,
              Fin.zero_eta] <;> exact hδeps
      have hQreal (k : Fin 4) : Q k ∈ TileRealization T := hsub (hQball k)
      have hsector : LatticeVertexIncidentCell x j ∈ T.cells := VertexInteriorLemmas.hsector T x
          j ε hδpos hδone hQreal
      exact hnot hsector
    · intro hall
      have h0 : x ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 0
      have h1 : x - 1 ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 1
      have h2 : x - 1 - ⟨0, 1⟩ ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 2
      have h3 : x - ⟨0, 1⟩ ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 3
      have hsub : Metric.ball (GaussianRealPoint x) (1 / 2 : ℝ) ⊆ TileRealization T := by
        intro p hp
        have hpdist : dist p (GaussianRealPoint x) < (1 / 2 : ℝ) :=
          Metric.mem_ball.mp hp
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hpdist
        have hpx : |p.1 - (x.re : ℝ)| < (1 / 2 : ℝ) :=
          lt_of_le_of_lt (le_max_left _ _) hpdist
        have hpy : |p.2 - (x.im : ℝ)| < (1 / 2 : ℝ) :=
          lt_of_le_of_lt (le_max_right _ _) hpdist
        have hpx' : (x.re : ℝ) - 1 / 2 < p.1 ∧ p.1 < (x.re : ℝ) + 1 / 2 := by
          rcases abs_lt.mp hpx with ⟨hlo, hhi⟩
          constructor <;> linarith
        have hpy' : (x.im : ℝ) - 1 / 2 < p.2 ∧ p.2 < (x.im : ℝ) + 1 / 2 := by
          rcases abs_lt.mp hpy with ⟨hlo, hhi⟩
          constructor <;> linarith
        by_cases hleft : p.1 ≤ (x.re : ℝ)
        · by_cases hdown : p.2 ≤ (x.im : ℝ)
          · simp only [TileRealization, Set.mem_iUnion]
            refine ⟨LatticeVertexIncidentCell x 2, h2, ?_⟩
            change ((((LatticeVertexIncidentCell x 2).re : ℝ) ≤ p.1 ∧
              ((LatticeVertexIncidentCell x 2).im : ℝ) ≤ p.2) ∧
              (p.1 ≤ (LatticeVertexIncidentCell x 2).re + 1 ∧
                p.2 ≤ (LatticeVertexIncidentCell x 2).im + 1))
            have hre : ((LatticeVertexIncidentCell x 2).re : ℝ) = (x.re : ℝ) - 1 := by
              simp [LatticeVertexIncidentCell]
            have him : ((LatticeVertexIncidentCell x 2).im : ℝ) = (x.im : ℝ) - 1 := by
              simp [LatticeVertexIncidentCell]
            rw [hre, him]
            constructor <;> constructor <;> linarith [hpx'.1, hpy'.1, hpx'.2, hpy'.2]
          · simp only [TileRealization, Set.mem_iUnion]
            refine ⟨LatticeVertexIncidentCell x 1, h1, ?_⟩
            change ((((LatticeVertexIncidentCell x 1).re : ℝ) ≤ p.1 ∧
              ((LatticeVertexIncidentCell x 1).im : ℝ) ≤ p.2) ∧
              (p.1 ≤ (LatticeVertexIncidentCell x 1).re + 1 ∧
                p.2 ≤ (LatticeVertexIncidentCell x 1).im + 1))
            have hre : ((LatticeVertexIncidentCell x 1).re : ℝ) = (x.re : ℝ) - 1 := by
              simp [LatticeVertexIncidentCell]
            have him : ((LatticeVertexIncidentCell x 1).im : ℝ) = (x.im : ℝ) := by
              simp [LatticeVertexIncidentCell]
            rw [hre, him]
            constructor <;> constructor <;> linarith [hpx'.1, hpy'.1, hpx'.2, hpy'.2]
        · by_cases hdown : p.2 ≤ (x.im : ℝ)
          · simp only [TileRealization, Set.mem_iUnion]
            refine ⟨LatticeVertexIncidentCell x 3, h3, ?_⟩
            change ((((LatticeVertexIncidentCell x 3).re : ℝ) ≤ p.1 ∧
              ((LatticeVertexIncidentCell x 3).im : ℝ) ≤ p.2) ∧
              (p.1 ≤ (LatticeVertexIncidentCell x 3).re + 1 ∧
                p.2 ≤ (LatticeVertexIncidentCell x 3).im + 1))
            have hre : ((LatticeVertexIncidentCell x 3).re : ℝ) = (x.re : ℝ) := by
              simp [LatticeVertexIncidentCell]
            have him : ((LatticeVertexIncidentCell x 3).im : ℝ) = (x.im : ℝ) - 1 := by
              simp [LatticeVertexIncidentCell]
            rw [hre, him]
            constructor <;> constructor <;> linarith [hpx'.1, hpy'.1, hpx'.2, hpy'.2]
          · simp only [TileRealization, Set.mem_iUnion]
            refine ⟨LatticeVertexIncidentCell x 0, h0, ?_⟩
            change ((((LatticeVertexIncidentCell x 0).re : ℝ) ≤ p.1 ∧
              ((LatticeVertexIncidentCell x 0).im : ℝ) ≤ p.2) ∧
              (p.1 ≤ (LatticeVertexIncidentCell x 0).re + 1 ∧
                p.2 ≤ (LatticeVertexIncidentCell x 0).im + 1))
            have hre : ((LatticeVertexIncidentCell x 0).re : ℝ) = (x.re : ℝ) := by
              simp [LatticeVertexIncidentCell]
            have him : ((LatticeVertexIncidentCell x 0).im : ℝ) = (x.im : ℝ) := by
              simp [LatticeVertexIncidentCell]
            rw [hre, him]
            constructor <;> constructor <;> linarith [hpx'.1, hpy'.1, hpx'.2, hpy'.2]
      exact mem_interior_iff_mem_nhds.mpr
        (Metric.mem_nhds_iff.mpr ⟨1 / 2, by norm_num, hsub⟩)
  · constructor
    · intro hnotboundary
      by_contra hnotall
      push Not at hnotall
      exact hnotboundary (P3161T2IncidentBoundary T x hsome hnotall)
    · intro hall hboundary
      have h0 : x ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 0
      have h1 : x - 1 ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 1
      have h2 : x - 1 - ⟨0, 1⟩ ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 2
      have h3 : x - ⟨0, 1⟩ ∈ T.cells := by
        simpa [LatticeVertexIncidentCell] using hall 3
      simp only [BoundaryFootprintVertices, hne, ite_true,
        Set.mem_ofPred_eq] at hboundary
      rcases hboundary with ⟨e, he, hxe⟩
      simp only [BoundaryFootprintEdges, Set.mem_ofPred_eq] at he
      rcases he with ⟨z, (⟨rfl, hor⟩ | ⟨rfl, hver⟩)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
        rcases hxe with hxe | hxe
        · subst z
          rcases hor with ⟨_, hn⟩ | ⟨hn, _⟩
          · exact hn (by simpa [sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm] using h3)
          · exact hn h0
        · have hz : z = x - 1 := by
            have hx' : x = z + 1 := hxe
            exact (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hx')).symm
          subst z
          rcases hor with ⟨_, hn⟩ | ⟨hn, _⟩
          · exact hn (by simpa [sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm] using h2)
          · exact hn h1
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
        rcases hxe with hxe | hxe
        · subst z
          rcases hver with ⟨_, hn⟩ | ⟨hn, _⟩
          · exact hn h1
          · exact hn h0
        · have hz : z = x - ⟨0, 1⟩ := by
            have hx' : x = z + ⟨0, 1⟩ := hxe
            exact (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hx')).symm
          subst z
          rcases hver with ⟨_, hn⟩ | ⟨hn, _⟩
          · exact hn (by simpa [sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm] using h2)
          · exact hn (by simpa [sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm] using h3)

end ApollonianSuperharmonic

end
