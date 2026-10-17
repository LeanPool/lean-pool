/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSelectionPackage
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreePackage

/-!
# RootClauseBCloseSelection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The candidate range and its good scales -/

/-- **The joint candidate range** `[n+4, m-1] ∩ ℤ`: the printed Step-7a range
widened at the top to the bad set's own domain, so that a good scale as close
to `m` as the bad set allows is available. -/
def rootClauseBCandidates (n m : ℤ) : Finset ℤ := Finset.Icc (n + 4) (m - 1)

theorem card_rootClauseBCandidates (n m : ℤ) :
    (rootClauseBCandidates n m).card = (m - n - 4).toNat := by
  rw [rootClauseBCandidates, Int.card_Icc]
  congr 1
  ring

/-- The good scales of the joint candidate range. -/
def rootClauseBGoodScales (B : Finset ℤ) (n m : ℤ) : Finset ℤ :=
  rootClauseBCandidates n m \ B

theorem mem_rootClauseBGoodScales_iff {B : Finset ℤ} {n m j : ℤ} :
    j ∈ rootClauseBGoodScales B n m ↔ (n + 4 ≤ j ∧ j ≤ m - 1) ∧ j ∉ B := by
  rw [rootClauseBGoodScales, Finset.mem_sdiff, rootClauseBCandidates, Finset.mem_Icc]

/-- **Non-emptiness** under the separation `|𝓑| + 7 ≤ m - n`; the range has
`m-n-4` candidates, so `|𝓑| + 5 ≤ m - n` would already do. -/
theorem rootClauseBGoodScales_nonempty {B : Finset ℤ} {n m : ℤ}
    (hsep : (B.card : ℤ) + 7 ≤ m - n) :
    (rootClauseBGoodScales B n m).Nonempty := by
  have hunion : (rootClauseBGoodScales B n m).card + B.card =
      (rootClauseBCandidates n m ∪ B).card :=
    Finset.card_sdiff_add_card _ _
  have hle : (rootClauseBCandidates n m).card ≤ (rootClauseBCandidates n m ∪ B).card :=
    Finset.card_le_card Finset.subset_union_left
  have hcard := card_rootClauseBCandidates n m
  refine Finset.card_pos.mp ?_
  omega

/-! ## 2. The two extrema, with their sharp gaps -/

/-- **The joint good pair.**

From the proved separation alone: two good scales `j ≤ k` inside `[n+4, m-1]`,
the lower one within `|𝓑| + 4` of the bottom and the upper one within `|𝓑| + 1`
of the top.  They are the minimum and the maximum of the SAME good-scale set,
so `j ≤ k` needs no argument beyond `Finset.min'_le_max'`. -/
theorem exists_rootClauseBGoodPair {B : Finset ℤ} {n m : ℤ}
    (hsep : (B.card : ℤ) + 7 ≤ m - n) :
    ∃ j k : ℤ, n + 4 ≤ j ∧ j ≤ k ∧ k ≤ m - 1 ∧ j ∉ B ∧ k ∉ B ∧
      j - n ≤ (B.card : ℤ) + 4 ∧ m - k ≤ (B.card : ℤ) + 1 := by
  have hne := rootClauseBGoodScales_nonempty (B := B) (n := n) (m := m) hsep
  set S := rootClauseBGoodScales B n m with hS
  set j := S.min' hne with hjdef
  set k := S.max' hne with hkdef
  have hjmem := mem_rootClauseBGoodScales_iff.mp (S.min'_mem hne)
  have hkmem := mem_rootClauseBGoodScales_iff.mp (S.max'_mem hne)
  have hjk : j ≤ k := S.min'_le_max' hne
  -- minimality: every scale below `j` in the range is bad
  have hsubLo : Finset.Ico (n + 4) j ⊆ B := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    by_contra hiB
    have hiS : i ∈ S :=
      mem_rootClauseBGoodScales_iff.mpr
        ⟨⟨hi.1, by linarith only [hi.2, hjmem.1.2]⟩, hiB⟩
    have := S.min'_le i hiS
    omega
  -- maximality: every scale above `k` in the range is bad
  have hsubHi : Finset.Ioc k (m - 1) ⊆ B := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    by_contra hiB
    have hiS : i ∈ S :=
      mem_rootClauseBGoodScales_iff.mpr
        ⟨⟨by linarith only [hi.1, hkmem.1.1], hi.2⟩, hiB⟩
    have := S.le_max' i hiS
    omega
  have hcardLo := Finset.card_le_card hsubLo
  have hcardHi := Finset.card_le_card hsubHi
  rw [Int.card_Ico] at hcardLo
  rw [Int.card_Ioc] at hcardHi
  have hlo := hjmem.1.1
  have hhi := hkmem.1.2
  exact ⟨j, k, hjmem.1.1, hjk, hkmem.1.2, hjmem.2, hkmem.2, by omega, by omega⟩

/-! ## 3. The Step-3 instantiation: both good -/

/-- **The two cap scales of the clause-(B) chain, at the Step-3 bad set.**

At every printed lattice centre `z`'s `StepThreeWindowsAndBudget` delivers the
separation, and the joint pigeonhole turns it into two scales `j ≤ k` whose
GOOD membership holds at `ω` — exactly the gate of
`StepSevenLambdaGoodEvent.ae_stepSevenLambdaCaps` at `j` and at `k`.  Setting
the chain's free scales to `n' := j - 1` (the Caccioppoli leg) and `k_chain:= k
- 1` (the coarse-graining leg) puts BOTH clause-(B) records on produced cubes. -/
theorem exists_rootClauseBCapScales {M : ABKModel d} {delta : ℝ} {n m : ℤ}
    {omega : Cutoff.CutoffSample d}
    (hbudget : StepThreeWindowsAndBudget M delta n m omega) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) :
    ∃ j k : ℤ, n + 4 ≤ j ∧ j ≤ k ∧ k ≤ m - 1 ∧
      j - n ≤ ((stepThreeBadSet M delta n m
        (Support.triadicLatticePoint n v) omega).card : ℤ) + 4 ∧
      m - k ≤ ((stepThreeBadSet M delta n m
        (Support.triadicLatticePoint n v) omega).card : ℤ) + 1 ∧
      omega ∈ stepThreeGoodEvent M delta j (Support.triadicLatticePoint n v) ∧
      omega ∈ stepThreeGoodEvent M delta k (Support.triadicLatticePoint n v) := by
  obtain ⟨-, -, -, hsep⟩ := hbudget v hv
  rw [StepOneBadSetSeparation] at hsep
  obtain ⟨j, k, hjlo, hjk, hkhi, hjB, hkB, hgapLo, hgapHi⟩ :=
    exists_rootClauseBGoodPair hsep
  exact ⟨j, k, hjlo, hjk, hkhi, hgapLo, hgapHi,
    mem_stepThreeGoodEvent_of_notMem_stepThreeBadSet (by omega) (by omega) hjB,
    mem_stepThreeGoodEvent_of_notMem_stepThreeBadSet (by omega) (by omega) hkB⟩

end

end Algsuperdiff.Section4.Provider.Regularity
