/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.NoDrop
public import LeanPool.KLRandomness.PrefixStage
public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension

/-!
# The infinite law of disjoint affine blocks

Each finite set of input coordinates meets only finitely many disjoint blocks.
Its law is therefore determined by a sufficiently long finite stage.  These
finite-coordinate laws form a projective family, from which Mathlib's
Kolmogorov extension construction gives the actual infinite probability law.
No consistency or infinite-law premise is assumed.
-/

@[expose] public section

namespace Klr.BlockProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A position belongs to at most one member of a disjoint block family. -/
theorem index_eq_of_mem (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    {q i j : ℕ} (hi : q ∈ (B i).support) (hj : q ∈ (B j).support) : i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (hdis h) hi hj

/-- One greater than the block owning a coordinate, or zero if the coordinate is free. -/
noncomputable def coordinateCutoff (B : ℕ → AffineBlock) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, q ∈ (B k).support then h.choose + 1 else 0

theorem coordinateCutoff_of_mem (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    {q k : ℕ} (hq : q ∈ (B k).support) : coordinateCutoff B q = k + 1 := by
  rw [coordinateCutoff, dite_eq_left ⟨k, hq⟩]
  exact congrArg (· + 1) (index_eq_of_mem B hdis (q := q)
    (Exists.choose_spec (show ∃ i, q ∈ (B i).support from ⟨k, hq⟩)) hq)

/-- A finite stage containing every block which meets a given finite coordinate set. -/
noncomputable def cutoff (B : ℕ → AffineBlock) (G : Finset ℕ) : ℕ :=
  G.sup (coordinateCutoff B)

@[simp] theorem cutoff_empty (B : ℕ → AffineBlock) : cutoff B ∅ = 0 := rfl

theorem cutoff_mono (B : ℕ → AffineBlock) {G H : Finset ℕ} (h : G ⊆ H) :
    cutoff B G ≤ cutoff B H := Finset.sup_mono h

theorem index_lt_cutoff_of_mem (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    {G : Finset ℕ} {q k : ℕ} (hG : q ∈ G) (hB : q ∈ (B k).support) :
    k < cutoff B G := by
  have h := Finset.le_sup (f := coordinateCutoff B) hG
  rw [coordinateCutoff_of_mem B hdis hB] at h
  exact Nat.lt_of_succ_le h

theorem disjoint_of_cutoff_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (G : Finset ℕ) {k : ℕ} (hk : cutoff B G ≤ k) : Disjoint G (B k).support := by
  apply Finset.disjoint_left.mpr
  intro q hG hB
  exact (not_lt_of_ge hk) (index_lt_cutoff_of_mem B hdis hG hB)

theorem dependsOn_restrict_preimage (G : Finset ℕ) (S : Set (G → Bool)) :
    DependsOn (fun X : Cantor => X ∈ G.restrict ⁻¹' S) (G : Set ℕ) := by
  intro X Y hXY
  have he : G.restrict X = G.restrict Y := funext fun i => hXY i.val i.property
  change (G.restrict X ∈ S) = (G.restrict Y ∈ S)
  rw [he]

theorem exists_restrict_preimage (G : Finset ℕ) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (G : Set ℕ)) :
    ∃ S : Set (G → Bool), A = G.restrict ⁻¹' S := by
  obtain ⟨P, hP⟩ := dependsOn_iff_exists_comp.mp hA
  refine ⟨{x | P x}, ?_⟩
  ext X
  exact iff_of_eq (congrFun hP X)

/-- The finite-coordinate marginal obtained after every block meeting those coordinates
has been imposed. -/
noncomputable def marginal (B : ℕ → AffineBlock) (G : Finset ℕ) : Measure (G → Bool) :=
  (PrefixStage.law B (cutoff B G)).map G.restrict

theorem marginal_isProbabilityMeasure (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (G : Finset ℕ) :
    IsProbabilityMeasure (marginal B G) := by
  let : IsProbabilityMeasure (PrefixStage.law B (cutoff B G)) :=
    PrefixStage.law_isProbabilityMeasure B hdis _
  unfold marginal
  infer_instance

/-- The finite-coordinate laws are consistent. This is proved from disjoint-support
independence of the actual finite stages. -/
theorem marginal_projective (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) (marginal B) := by
  intro I J hJI
  ext S hS
  change ((PrefixStage.law B (cutoff B J)).map J.restrict) S =
    (((PrefixStage.law B (cutoff B I)).map I.restrict).map
      (Finset.restrict₂ (π := fun _ : ℕ => Bool) hJI)) S
  rw [Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℕ => Bool) hJI)
      I.measurable_restrict,
    Measure.map_apply J.measurable_restrict hS,
    Measure.map_apply ((Finset.measurable_restrict₂ (X := fun _ : ℕ => Bool) hJI).comp
      I.measurable_restrict) hS]
  change PrefixStage.law B (cutoff B J) (J.restrict ⁻¹' S) =
    PrefixStage.law B (cutoff B I) (J.restrict ⁻¹' S)
  exact (PrefixStage.law_apply_eq_of_disjoint B hdis (cutoff_mono B hJI)
    J (J.restrict ⁻¹' S) (dependsOn_restrict_preimage J S)
    (fun k hk _ => disjoint_of_cutoff_le B hdis J hk)).symm

/-- The actual infinite law of independent uniform affine-block solutions and fair free
coordinates, constructed from its proved coherent finite-stage marginals. -/
noncomputable def law (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) : Measure Cantor := by
  let _ : ∀ G, IsProbabilityMeasure (marginal B G) := marginal_isProbabilityMeasure B hdis
  exact projectiveLimit (α := fun _ : ℕ => Bool) (marginal B) (marginal_projective B hdis)

instance law_isProbabilityMeasure (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    IsProbabilityMeasure (law B hdis) := by
  let : ∀ G, IsProbabilityMeasure (marginal B G) := marginal_isProbabilityMeasure B hdis
  unfold law
  infer_instance

theorem law_isProjectiveLimit (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    IsProjectiveLimit (law B hdis) (marginal B) := by
  let : ∀ G, IsProbabilityMeasure (marginal B G) := marginal_isProbabilityMeasure B hdis
  exact isProjectiveLimit_projectiveLimit (marginal_projective B hdis)

/-- Exact finite-coordinate marginals of the constructed infinite law. -/
theorem law_map_restrict (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (G : Finset ℕ) :
    (law B hdis).map G.restrict = marginal B G :=
  law_isProjectiveLimit B hdis G

/-- Every event on finitely many coordinates has exactly its stabilized finite-stage mass. -/
theorem law_apply_eq_cutoff (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (G : Finset ℕ) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (G : Set ℕ)) :
    law B hdis A = PrefixStage.law B (cutoff B G) A := by
  obtain ⟨S, rfl⟩ := exists_restrict_preimage G A hA
  rw [← Measure.map_apply G.measurable_restrict S.toFinite.measurableSet,
    law_map_restrict, marginal,
    Measure.map_apply G.measurable_restrict S.toFinite.measurableSet]

/-- Any sufficiently late finite stage already has the final law on a finite set of coordinates. -/
theorem law_apply_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (G : Finset ℕ) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (G : Set ℕ))
    (n : ℕ) (hn : cutoff B G ≤ n) : law B hdis A = PrefixStage.law B n A := by
  rw [law_apply_eq_cutoff B hdis G A hA]
  exact (PrefixStage.law_apply_eq_of_disjoint B hdis hn G A hA
    (fun k hk _ => disjoint_of_cutoff_le B hdis G hk)).symm

/-- Every individual block equation holds with probability one under the infinite law. -/
theorem law_block_event (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (k : ℕ) :
    law B hdis (B k).event = 1 := by
  let n := max (cutoff B (B k).support) (k + 1)
  rw [law_apply_eq_stage B hdis (B k).support (B k).event (B k).dependsOn_event
    n (Nat.le_max_left _ _)]
  exact PrefixStage.law_block_event B hdis n k
    (lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _))

/-- The constructed law almost surely satisfies all countably many affine constraints. -/
theorem ae_all_blocks (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    ∀ᵐ X ∂law B hdis, ∀ k, X ∈ (B k).event := by
  apply ae_all_iff.mpr
  intro k
  apply ae_iff.mpr
  change law B hdis (B k).eventᶜ = 0
  rw [measure_compl (B k).measurableSet_event (measure_ne_top _ _),
    measure_univ, law_block_event, tsub_self]

/-- The intersection of all block constraints has full measure. -/
theorem law_familyEvent (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    law B hdis (AffineBlock.familyEvent B) = 1 := by
  have hc : law B hdis (AffineBlock.familyEvent B)ᶜ = 0 :=
    ae_iff.mp (ae_all_blocks B hdis)
  simpa only [compl_compl, measure_univ, hc, tsub_zero] using
    measure_compl (AffineBlock.measurableSet_familyEvent B).compl
      (show law B hdis (AffineBlock.familyEvent B)ᶜ ≠ ∞ by rw [hc]; exact ENNReal.zero_ne_top)

/-- The infinite block law and stage `j` agree on a finite adaptive transcript whenever
every block from `j` onward still has full unread rank after that transcript. -/
theorem law_inputEvent_eq_of_fullRank (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) (v : List Bool)
    (hfull : ∀ k, j ≤ k → (B k).UnreadFullRank π v) :
    law B hdis (StoppingTranscript.inputEvent π v) =
      PrefixStage.law B j (StoppingTranscript.inputEvent π v) := by
  let n := max (cutoff B (π.queriedPositions v)) j
  rw [law_apply_eq_stage B hdis (π.queriedPositions v)
    (StoppingTranscript.inputEvent π v) (π.dependsOn_inputEvent v) n (Nat.le_max_left _ _)]
  exact PrefixStage.law_transcript_eq_of_fullRank B hdis j n (Nat.le_max_right _ _) π v
    (fun k hk _ => hfull k hk)

/-- The infinite/finite comparison also holds for unbounded prefix-free stopping unions,
provided every not-yet-imposed block retains full rank at each stopping transcript. -/
theorem law_unionEvent_eq_of_fullRank (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) {W : Set (List Bool)}
    (hW : StoppingTranscript.PrefixFree W)
    (hfull : ∀ v ∈ W, ∀ k, j ≤ k → (B k).UnreadFullRank π v) :
    law B hdis (StoppingTranscript.unionEvent π W) =
      PrefixStage.law B j (StoppingTranscript.unionEvent π W) := by
  apply StoppingTranscript.measure_unionEvent_eq _ _ π hW
  intro v hv
  exact law_inputEvent_eq_of_fullRank B hdis j π v (hfull v hv)

end Klr.BlockProduct
