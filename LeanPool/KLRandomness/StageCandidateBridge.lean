/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StagePreHorizon
public import LeanPool.KLRandomness.HorizonAvoidance
public import LeanPool.KLRandomness.LateDropBound

/-!
# Concrete candidate coordinates and stage cutoffs

The pre-horizon theorem labels the pool by `Fin (r^8)`. The executable
finite statistics use the pool list's own `Fin G.length` enumeration. These
representations yield exactly the same affine block, including its matrix.

One explicit cutoff avoids the old block supports and every query on every
branch through every earlier protected horizon. A good pool beyond that
cutoff therefore supplies both disjointness and all future-preservation
conditions needed when the selected candidate is appended to the stages.
-/

@[expose] public section

namespace Klr.StageCandidateBridge

open MeasureTheory SparseListSearch StageChoice StagePreHorizon

/-- Transporting the pool-length equality does not change the embedded
affine block. The complete matrix agrees, not only its support or event. -/
theorem block_poolLabel_eq {M m r : ℕ} (G : List ℕ)
    (hGM : G.length = M) (hG : G.Nodup) (a : Entry)
    (ha : GoodEntry M m r a) (ha' : GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) :
    StageCandidate.block (poolLabel G hGM) (poolLabel_injective G hGM hG) a ha y =
      StageCandidate.block G.get hG.injective_get a ha' y := by
  subst M
  rfl

/-- The selected executable entry is good at the actual pool-list length. -/
theorem candidate_goodEntry {τ θ : ℚ} {r : ℕ} {G : List ℕ} {L : CodeList}
    (hGM : G.length = SparseParameters.blockSize r)
    (hL : L ∈ SparseListConstruction.construct τ θ r) (q : Fin L.length) :
    GoodEntry G.length (SparseParameters.supportSize r) r (L.get q) := by
  rw [hGM]
  exact (SparseListConstruction.construct_spec hL).2.1 _ (List.get_mem L q)

/-- The candidate supplied by the analytic selection theorem is exactly
the block used by the finite code and rank interpreters. -/
theorem candidate_eq_block {τ θ : ℚ} {r : ℕ} {G : List ℕ} {L : CodeList}
    (hGM : G.length = SparseParameters.blockSize r) (hG : G.Nodup)
    (hL : L ∈ SparseListConstruction.construct τ θ r) (q : Fin L.length)
    (ha : GoodEntry G.length (SparseParameters.supportSize r) r (L.get q))
    (y : Fin r → ZMod 2) :
    candidate hGM hG hL q y = StageCandidate.block G.get hG.injective_get (L.get q) ha y :=
  block_poolLabel_eq G hGM hG (L.get q)
    ((SparseListConstruction.construct_spec hL).2.1 _ (List.get_mem L q)) ha y

/-- The direct finite-statistics block uses only positions in the actual pool. -/
theorem block_support_subset_pool {m r : ℕ} (G : List ℕ) (hG : G.Nodup)
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) :
    (StageCandidate.block G.get hG.injective_get a ha y).support ⊆ G.toFinset := by
  intro p hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
  exact List.mem_toFinset.mpr (List.get_mem G j)

/-- The selected block inherits the pool program's lower position cutoff. -/
theorem candidate_support_ge_of_goodPool {τ θ : ℚ} {r ℓ z : ℕ}
    {G : List ℕ} {L : CodeList} {π : ℕ → ScanRule} {H : ℕ → Set Cantor} {η : ℝ}
    (hG : PoolConstruction.GoodPool π H ℓ η z τ (SparseParameters.blockSize r) G)
    (hL : L ∈ SparseListConstruction.construct τ θ r) (q : Fin L.length)
    (y : Fin r → ZMod 2) :
    ∀ p ∈ (candidate hG.1 hG.2.1 hL q y).support, z ≤ p := by
  intro p hp
  exact hG.2.2.1 p (List.mem_toFinset.mp (candidate_support_subset hG.1 hG.2.1 hL q y hp))

/-- A pool beyond `z + 1` gives a strict cutoff, when that convention is convenient. -/
theorem candidate_support_gt_of_goodPool {τ θ : ℚ} {r ℓ z : ℕ}
    {G : List ℕ} {L : CodeList} {π : ℕ → ScanRule} {H : ℕ → Set Cantor} {η : ℝ}
    (hG : PoolConstruction.GoodPool π H ℓ η (z + 1) τ (SparseParameters.blockSize r) G)
    (hL : L ∈ SparseListConstruction.construct τ θ r) (q : Fin L.length)
    (y : Fin r → ZMod 2) :
    ∀ p ∈ (candidate hG.1 hG.2.1 hL q y).support, z < p :=
  candidate_support_ge_of_goodPool hG hL q y

/-- The input-space low-drop event has the exact form required by the
stage estimates and their later-stage comparison theorem. -/
theorem lowDropInput_eq (s : BettingStrategy) (H : Set Cantor) (C : AffineBlock) :
    lowDropInput s H C =
      s.normalize.scan.observationMap ⁻¹' Hᶜ ∩ LateDropBound.hasDrop C s.normalize.scan := by
  simp only [lowDropInput, Set.preimage_inter, Set.preimage_compl,
    NoDrop.observationMap_preimage_noDropTranscripts, LateDropBound.hasDrop]

/-- Full positive unread rank on the high part forces a missed coordinate
of every pool containing the support. This inclusion is pointwise. -/
theorem high_noDrop_subset_highMissInput (s : BettingStrategy) (H : Set Cantor)
    (G : List ℕ) (C : AffineBlock) (hCG : C.support ⊆ G.toFinset) (hr : 0 < C.rank) :
    s.normalize.scan.observationMap ⁻¹' H ∩ NoDrop.noDropEvent C s.normalize.scan ⊆
      highMissInput s H G := by
  intro X hX
  have ht : s.normalize.scan.observationMap X ∈ NoDrop.noDropTranscripts C s.normalize.scan := by
    change X ∈ s.normalize.scan.observationMap ⁻¹' NoDrop.noDropTranscripts C s.normalize.scan
    rw [NoDrop.observationMap_preimage_noDropTranscripts]
    exact hX.2
  have hm := StageRank.noDropTranscripts_subset_missed C s.normalize.scan G.toFinset hCG hr ht
  obtain ⟨b, hb, hnb⟩ :=
    (PoolQuery.missedCount_pos_iff s.normalize.scan G.toFinset _).mp hm
  exact ⟨hX.1, b, List.mem_toFinset.mp hb, hnb⟩

theorem measure_high_noDrop_le_highMissInput (μ : Measure Cantor)
    (s : BettingStrategy) (H : Set Cantor) (G : List ℕ) (C : AffineBlock)
    (hCG : C.support ⊆ G.toFinset) (hr : 0 < C.rank) :
    μ (s.normalize.scan.observationMap ⁻¹' H ∩ NoDrop.noDropEvent C s.normalize.scan) ≤
      μ (highMissInput s H G) :=
  measure_mono (high_noDrop_subset_highMissInput s H G C hCG hr)

theorem measureReal_high_noDrop_le_highMissInput (μ : Measure Cantor) [IsFiniteMeasure μ]
    (s : BettingStrategy) (H : Set Cantor) (G : List ℕ) (C : AffineBlock)
    (hCG : C.support ⊆ G.toFinset) (hr : 0 < C.rank) :
    μ.real (s.normalize.scan.observationMap ⁻¹' H ∩ NoDrop.noDropEvent C s.normalize.scan) ≤
      μ.real (highMissInput s H G) :=
  measureReal_mono (high_noDrop_subset_highMissInput s H G C hCG hr)

/-- Old supports and every earlier protected all-branch query set. Stage
`j` protected scans `0, ..., j` through its horizon `V j`. -/
def stagePositions (B : ℕ → AffineBlock) (π : ℕ → ScanRule) (V : ℕ → ℕ)
    (n : ℕ) : Finset ℕ :=
  PrefixStage.prefixSupport B n ∪ (Finset.range n).biUnion
    (fun j => HorizonAvoidance.familyPositions (fun i : Fin (j + 1) => π i) (fun _ => V j))

/-- A strict upper bound for everything that the next support must avoid. -/
def stageCutoff (B : ℕ → AffineBlock) (π : ℕ → ScanRule) (V : ℕ → ℕ) (n : ℕ) : ℕ :=
  (stagePositions B π V n).sup id + 1

theorem lt_stageCutoff_of_mem (B : ℕ → AffineBlock) (π : ℕ → ScanRule)
    (V : ℕ → ℕ) (n : ℕ) {p : ℕ} (hp : p ∈ stagePositions B π V n) :
    p < stageCutoff B π V n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hp)

theorem old_support_subset_stagePositions (B : ℕ → AffineBlock) (π : ℕ → ScanRule)
    (V : ℕ → ℕ) (n j : ℕ) (hj : j < n) :
    (B j).support ⊆ stagePositions B π V n := by
  intro p hp
  exact Finset.mem_union_left _ ((PrefixStage.mem_prefixSupport B n p).mpr ⟨j, hj, hp⟩)

theorem queryPositions_subset_stagePositions (B : ℕ → AffineBlock) (π : ℕ → ScanRule)
    (V : ℕ → ℕ) (n j : ℕ) (hj : j < n) (i : ℕ) (hi : i ≤ j) :
    HorizonAvoidance.queryPositions (π i) (V j) ⊆ stagePositions B π V n := by
  intro p hp
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  exact HorizonAvoidance.queryPositions_subset_familyPositions
    (fun i : Fin (j + 1) => π i) (fun _ => V j) ⟨i, Nat.lt_succ_of_le hi⟩ hp

theorem old_support_lt_stageCutoff (B : ℕ → AffineBlock) (π : ℕ → ScanRule)
    (V : ℕ → ℕ) (n j : ℕ) (hj : j < n) (p : ℕ) (hp : p ∈ (B j).support) :
    p < stageCutoff B π V n :=
  lt_stageCutoff_of_mem B π V n (old_support_subset_stagePositions B π V n j hj hp)

theorem query_lt_stageCutoff (B : ℕ → AffineBlock) (π : ℕ → ScanRule)
    (V : ℕ → ℕ) (n j : ℕ) (hj : j < n) (i : ℕ) (hi : i ≤ j)
    (v : List Bool) (hv : v.length < V j) : (π i).query v < stageCutoff B π V n :=
  lt_stageCutoff_of_mem B π V n (queryPositions_subset_stagePositions B π V n j hj i hi
    (HorizonAvoidance.query_mem_queryPositions (π i) (V j) v hv))

/-- The explicit cutoff simultaneously guarantees disjointness from every
old block and full unread rank through every old protected horizon. -/
theorem consequences_of_stageCutoff_le (B : ℕ → AffineBlock) (π : ℕ → ScanRule)
    (V : ℕ → ℕ) (n : ℕ) (C : AffineBlock)
    (hC : ∀ p ∈ C.support, stageCutoff B π V n ≤ p) :
    (∀ j < n, Disjoint (B j).support C.support) ∧
      ∀ j < n, ∀ i ≤ j, ∀ v : List Bool, v.length ≤ V j → C.UnreadFullRank (π i) v := by
  have hd : Disjoint (stagePositions B π V n) C.support := by
    apply Finset.disjoint_left.mpr
    intro p hp hpC
    exact (not_lt_of_ge (hC p hpC)) (lt_stageCutoff_of_mem B π V n hp)
  constructor
  · intro j hj
    exact hd.mono_left (old_support_subset_stagePositions B π V n j hj)
  · intro j hj i hi v hv
    exact HorizonAvoidance.unreadFullRank_of_disjoint C (π i) (V j)
      (hd.mono_left (queryPositions_subset_stagePositions B π V n j hj i hi)) v hv

/-- A good pool above the concrete stage cutoff discharges all support
separation and horizon-preservation requirements for the selected candidate. -/
theorem candidate_preserves_prior_horizons {τ θ : ℚ} {r ℓ z : ℕ}
    {G : List ℕ} {L : CodeList} {π : ℕ → ScanRule} {H : ℕ → Set Cantor} {η : ℝ}
    (hG : PoolConstruction.GoodPool π H ℓ η z τ (SparseParameters.blockSize r) G)
    (hL : L ∈ SparseListConstruction.construct τ θ r) (q : Fin L.length)
    (y : Fin r → ZMod 2) (B : ℕ → AffineBlock) (V : ℕ → ℕ) (n : ℕ)
    (hz : stageCutoff B π V n ≤ z) :
    (∀ j < n, Disjoint (B j).support (candidate hG.1 hG.2.1 hL q y).support) ∧
      ∀ j < n, ∀ i ≤ j, ∀ v : List Bool, v.length ≤ V j →
        (candidate hG.1 hG.2.1 hL q y).UnreadFullRank (π i) v :=
  consequences_of_stageCutoff_le B π V n _
    (fun p hp => hz.trans (candidate_support_ge_of_goodPool hG hL q y p hp))

end Klr.StageCandidateBridge
