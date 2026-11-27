/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineCodeCoverage
public import LeanPool.KLRandomness.StageFiniteProbability
public import LeanPool.KLRandomness.PrefixStage

/-!
# Finite code headers for the previous affine constraints

Every finite-support affine block has a valid finite code. We choose those
codes non-effectively for the already constructed blocks and place them in
the fixed stage header. The resulting executable finite-stage law is exactly
the original conditional law. This choice does not claim a computable global
enumeration of the block construction.
-/

@[expose] public section

noncomputable section

namespace Klr.StagePrefixCode

/-- A finite valid code for one already fixed affine block. -/
def code (B : AffineBlock) : AffineCode.Data :=
  (AffineCode.exists_valid_code_of_affineBlock B).choose

@[simp] theorem rank_code (B : AffineBlock) : AffineCode.rank (code B) = B.rank :=
  (AffineCode.exists_valid_code_of_affineBlock B).choose_spec.1

@[simp] theorem valid_code (B : AffineBlock) : AffineCode.valid (code B) = true :=
  (AffineCode.exists_valid_code_of_affineBlock B).choose_spec.2.1

@[simp] theorem event_code (B : AffineBlock) : AffineCode.event (code B) = B.event :=
  (AffineCode.exists_valid_code_of_affineBlock B).choose_spec.2.2

/-- The fixed finite header for a finite ordered family of earlier blocks. -/
def header {n : ℕ} (old : Fin n → AffineBlock) : List AffineCode.Data :=
  List.ofFn fun i => code (old i)

@[simp] theorem length_header {n : ℕ} (old : Fin n → AffineBlock) :
    (header old).length = n := List.length_ofFn

theorem valid_of_mem_header {n : ℕ} (old : Fin n → AffineBlock)
    {c : AffineCode.Data} (hc : c ∈ header old) : AffineCode.valid c = true := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact valid_code (old i)

/-- No information about the previous constraint event is lost by encoding. -/
theorem event_header {n : ℕ} (old : Fin n → AffineBlock) :
    StageFiniteProbability.event (header old) = AffineBlock.familyEvent old := by
  ext X
  constructor
  · intro h i
    have hi := h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rwa [event_code] at hi
  · intro h c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    rw [event_code]
    exact h i

/-- The executable finite header represents the actual old conditional law. -/
theorem law_header {n : ℕ} (old : Fin n → AffineBlock) :
    StageFiniteProbability.law (header old) = AffineBlock.finiteStageLaw old := by
  unfold StageFiniteProbability.law AffineBlock.finiteStageLaw
  rw [event_header]

theorem sum_rank_header {n : ℕ} (old : Fin n → AffineBlock) :
    ((header old).map AffineCode.rank).sum = ∑ i, (old i).rank := by
  simp only [header, List.map_ofFn, List.sum_ofFn, Function.comp_apply, rank_code]

/-- The previous prefix of any block sequence has a finite valid header. -/
def prefixHeader (B : ℕ → AffineBlock) (n : ℕ) : List AffineCode.Data :=
  header (PrefixStage.prefixFamily B n)

@[simp] theorem length_prefixHeader (B : ℕ → AffineBlock) (n : ℕ) :
    (prefixHeader B n).length = n := length_header _

theorem event_prefixHeader (B : ℕ → AffineBlock) (n : ℕ) :
    StageFiniteProbability.event (prefixHeader B n) = PrefixStage.prefixEvent B n :=
  event_header _

theorem law_prefixHeader (B : ℕ → AffineBlock) (n : ℕ) :
    StageFiniteProbability.law (prefixHeader B n) = PrefixStage.law B n :=
  law_header _

/-- The finite old data can always be fixed before the trial rank. Neither
pairwise disjointness nor effectiveness of the infinite sequence is needed
for the representation itself. -/
theorem exists_prefix_header (B : ℕ → AffineBlock) (n : ℕ) :
    ∃ cs : List AffineCode.Data, cs.length = n ∧
      (∀ c ∈ cs, AffineCode.valid c = true) ∧
      StageFiniteProbability.event cs = PrefixStage.prefixEvent B n ∧
      StageFiniteProbability.law cs = PrefixStage.law B n :=
  ⟨prefixHeader B n, length_prefixHeader B n, fun _ hc => valid_of_mem_header _ hc,
    event_prefixHeader B n, law_prefixHeader B n⟩

end Klr.StagePrefixCode
