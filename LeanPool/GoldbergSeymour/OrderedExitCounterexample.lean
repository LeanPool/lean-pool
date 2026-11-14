/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ElementaryClosedExitPairExtendsTriple
public import LeanPool.GoldbergSeymour.ElementaryClosedNoninterchangeableExitPair
public import LeanPool.GoldbergSeymour.ElementarySingleBoundaryInterchangeable
public import LeanPool.GoldbergSeymour.RutgersCounterexample

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# P2647_T1_Ordered Exit Counterexample

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2647_T1_OrderedExitCounterexample
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (presentation : RutgersClosedPresentation G k e0 original)
    (hproper : IsProperEdgeColoring G presentation.sigma)
    (helementary : ColoredVertexSetElementary G presentation.sigma
      (TreeSequenceVertexSet presentation.U))
    (hclosed : ColoredVertexSetClosed G presentation.sigma
      (TreeSequenceVertexSet presentation.U))
    (alpha beta : Fin k) (hcolors : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors presentation.sigma presentation.U)
    (hnot : ¬ TreeInterchangeable G presentation.U presentation.sigma alpha beta) :
    ∃ counterexample : RutgersCounterexample G k e0 original presentation,
      counterexample.alpha = alpha ∧ counterexample.beta = beta := by
  classical
  have missingClosed (c : Fin k)
      (hc : c ∈ TreeMissingColors presentation.sigma presentation.U) :
      BoundaryColorEdges G presentation.sigma
        (TreeSequenceVertexSet presentation.U) c = ∅ := by
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    simp only [BoundaryColorEdges, Finset.mem_filter] at hf
    exact hclosed hf.1 hv hf.2 hcv
  have halphaClosed : TreeColorSetClosed G presentation.sigma presentation.U {alpha} := by
    intro c hc
    have : c = alpha := Finset.mem_singleton.mp hc
    subst c
    exact missingClosed alpha halpha
  have hbeta : beta ∉ TreeMissingColors presentation.sigma presentation.U := by
    intro hb
    apply hnot
    apply ElementarySingleBoundaryInterchangeable G presentation.sigma
      presentation.U alpha beta hproper helementary (missingClosed alpha halpha)
    rw [missingClosed beta hb]
    simp
  obtain ⟨a1, b1, a2, b2, Q1, Q2, f1, f2, hx1, hx2, hd12,
    ha12, hb12, hf1, hf2, hi1, hi2, hs1, hs2⟩ :=
    ElementaryClosedNoninterchangeableExitPair G presentation.U presentation.sigma
      hproper helementary alpha beta hcolors halpha halphaClosed hnot
  obtain ⟨a3, b3, Q3, f3, hx3, hd13, hd23, ha31, ha32, hb31, hb32,
    hf3, hi3, hs3⟩ :=
    ElementaryClosedExitPairExtendsTriple G presentation.U presentation.sigma
      hproper helementary alpha beta hcolors halpha halphaClosed hbeta
      a1 b1 a2 b2 Q1 Q2 hx1 hx2 hd12 ha12 hb12
  let package : Fin 3 → Σ a b : V,
      (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk
        (Sum.inl a) (Sum.inl b) × E :=
    ![⟨a1, b1, Q1, f1⟩, ⟨a2, b2, Q2, f2⟩, ⟨a3, b3, Q3, f3⟩]
  let a := fun i => (package i).1
  let b := fun i => (package i).2.1
  let Q := fun i => (package i).2.2.1
  let f := fun i => (package i).2.2.2
  have exits : ∀ i, TreeExitPath presentation.U presentation.sigma
      alpha beta (a i) (b i) (Q i) := by
    intro i
    fin_cases i
    · simpa [a, b, Q, package] using hx1
    · simpa [a, b, Q, package] using hx2
    · simpa [a, b, Q, package] using hx3
  have boundary : ∀ i, f i ∈ BoundaryColorEdges G presentation.sigma
      (TreeSequenceVertexSet presentation.U) beta := by
    intro i
    fin_cases i
    · simpa [f, package] using hf1
    · simpa [f, package] using hf2
    · simpa [f, package] using hf3
  have incidence : ∀ i, Incident G (b i) (f i) := by
    intro i
    fin_cases i
    · simpa [b, f, package] using hi1
    · simpa [b, f, package] using hi2
    · simpa [b, f, package] using hi3
  have onWalk : ∀ i, Sum.inr (f i) ∈ (Q i).support := by
    intro i
    fin_cases i
    · simpa [f, Q, package] using hs1
    · simpa [f, Q, package] using hs2
    · simpa [f, Q, package] using hs3
  have disjoint : ∀ i j, i ≠ j → ∀ x, x ∈ (Q i).support → x ∉ (Q j).support := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact hd12
      | exact hd13
      | exact hd23
      | exact fun x hx hy => hd12 x hy hx
      | exact fun x hx hy => hd13 x hy hx
      | exact fun x hx hy => hd23 x hy hx
  have outsideDistinct : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact ha12
      | exact ha31
      | exact ha32
      | exact ha12.symm
      | exact ha31.symm
      | exact ha32.symm
  have insideDistinct : ∀ i j, i ≠ j → b i ≠ b j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact hb12
      | exact hb31
      | exact hb32
      | exact hb12.symm
      | exact hb31.symm
      | exact hb32.symm
  have positions : ∀ i, ∃ r : Fin (presentation.U.length + 1),
      presentation.U.vertex r = b i := by
    intro i
    have hv := (exits i).2.2.2.1
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] using hv
  choose rank hrank using positions
  have rankDistinct : ∀ i j, i ≠ j → (rank i).val ≠ (rank j).val := by
    intro i j hij heq
    apply insideDistinct i j hij
    rw [← hrank i, ← hrank j, Fin.ext heq]
  have sorted : ∃ i j l : Fin 3,
      (rank i).val < (rank j).val ∧ (rank j).val < (rank l).val := by
    have h01 := rankDistinct 0 1 (by decide)
    have h02 := rankDistinct 0 2 (by decide)
    have h12 := rankDistinct 1 2 (by decide)
    by_cases hij : (rank 0).val < (rank 1).val
    · by_cases hjl : (rank 1).val < (rank 2).val
      · exact ⟨0, 1, 2, hij, hjl⟩
      · by_cases hil : (rank 0).val < (rank 2).val
        · exact ⟨0, 2, 1, hil, by omega⟩
        · exact ⟨2, 0, 1, by omega, hij⟩
    · by_cases hil : (rank 0).val < (rank 2).val
      · exact ⟨1, 0, 2, by omega, hil⟩
      · by_cases hjl : (rank 1).val < (rank 2).val
        · exact ⟨1, 2, 0, hjl, by omega⟩
        · exact ⟨2, 1, 0, by omega, by omega⟩
  obtain ⟨i, j, l, hij, hjl⟩ := sorted
  have hneij : i ≠ j := by intro h; subst j; omega
  have hneil : i ≠ l := by intro h; subst l; omega
  have hnejl : j ≠ l := by intro h; subst l; omega
  refine ⟨{
    alpha := alpha
    beta := beta
    colorsDistinct := hcolors
    alphaMissing := halpha
    betaPresent := hbeta
    a1 := a i
    b1 := b i
    a2 := a j
    b2 := b j
    a3 := a l
    b3 := b l
    Q1 := Q i
    Q2 := Q j
    Q3 := Q l
    f1 := f i
    f2 := f j
    f3 := f l
    exit1 := exits i
    exit2 := exits j
    exit3 := exits l
    supportDisjoint12 := disjoint i j hneij
    supportDisjoint13 := disjoint i l hneil
    supportDisjoint23 := disjoint j l hnejl
    outsideDistinct12 := outsideDistinct i j hneij
    outsideDistinct13 := outsideDistinct i l hneil
    outsideDistinct23 := outsideDistinct j l hnejl
    insideDistinct12 := insideDistinct i j hneij
    insideDistinct13 := insideDistinct i l hneil
    insideDistinct23 := insideDistinct j l hnejl
    insideOrder12 := ⟨rank i, rank j, hrank i, hrank j, hij⟩
    insideOrder23 := ⟨rank j, rank l, hrank j, hrank l, hjl⟩
    boundary1 := boundary i
    boundary2 := boundary j
    boundary3 := boundary l
    incident1 := incidence i
    incident2 := incidence j
    incident3 := incidence l
    edgeOnWalk1 := onWalk i
    edgeOnWalk2 := onWalk j
    edgeOnWalk3 := onWalk l
  }, rfl, rfl⟩

end GoldbergSeymour

end
