/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.DistinctDistances.S4CertificateKernelReplay

/-!
# Reused summaries of the long geometric rows

The moment row and the two interval rows contain thousands of coefficients from the
same fixed grid. Check their unit-weight packed summaries once and multiply whole
chunks by the certificate weight. The interval bounds change only the right-hand
side when its denominator divides the common coefficient denominator.
-/

@[expose] public section

namespace Esgk.FarkasPackedCheck

open PackTrie

/-- Scale the packed coefficients of a trie, retaining its occupied chunks. -/
noncomputable def PackTrie.scale (weight : Nat) (trie : PackTrie) : PackTrie :=
  PackTrie.rec .zero (fun n ↦ .leaf (weight * n)) (fun _ _ left right ↦ .node left right) trie

private theorem scale_addLeaf (weight coefficient : Nat) (trie : PackTrie) :
    (addLeaf coefficient trie).scale weight =
      addLeaf (weight * coefficient) (trie.scale weight) := by
  induction trie with
  | zero => rfl
  | leaf value =>
    exact congrArg PackTrie.leaf (Nat.mul_add weight coefficient value)
  | node left right ihLeft ihRight =>
    exact congrArg₂ PackTrie.node ihLeft ihRight

private theorem scale_add (weight : Nat) (left right : PackTrie) :
    (left.add right).scale weight = (left.scale weight).add (right.scale weight) := by
  induction left generalizing right with
  | zero => rfl
  | leaf coefficient => exact scale_addLeaf weight coefficient right
  | node leftBranch rightBranch ihLeft ihRight =>
    cases right with
    | zero => rfl
    | leaf coefficient => exact scale_addLeaf weight coefficient (.node leftBranch rightBranch)
    | node left' right' => exact congrArg₂ PackTrie.node (ihLeft left') (ihRight right')

private theorem scale_single (weight depth chunk coefficient : Nat) :
    (single depth chunk coefficient).scale weight = single depth chunk (weight * coefficient) := by
  induction depth generalizing chunk with
  | zero => rfl
  | succ depth ih =>
    change (bif Nat.blt chunk (2 ^ depth) then PackTrie.node (single depth chunk coefficient) .zero
      else PackTrie.node .zero (single depth (chunk - 2 ^ depth) coefficient)).scale weight =
      (bif Nat.blt chunk (2 ^ depth)
        then PackTrie.node (single depth chunk (weight * coefficient)) .zero
        else PackTrie.node .zero (single depth (chunk - 2 ^ depth) (weight * coefficient)))
    cases Nat.blt chunk (2 ^ depth) with
    | false =>
      exact congrArg (PackTrie.node .zero) (ih _)
    | true =>
      exact congrArg (fun trie ↦ PackTrie.node trie .zero) (ih _)

private theorem map_pairUp {α β : Type} (combine : α → α → α) (merge : β → β → β)
    (map : α → β) (preserves : ∀ a b, map (combine a b) = merge (map a) (map b))
    (items : List α) (pending : Option α) :
    (pairUp combine items pending).map map =
      pairUp merge (items.map map) (pending.map map) := by
  induction items generalizing pending with
  | nil => cases pending <;> rfl
  | cons item items ih =>
    cases pending with
    | none => exact ih (some item)
    | some previous =>
      change map (combine previous item) :: (pairUp combine items none).map map =
        merge (map previous) (map item) :: pairUp merge (items.map map) none
      exact congrArg₂ List.cons (preserves previous item) (ih none)

private theorem map_balFold {α β : Type} (combine : α → α → α) (merge : β → β → β)
    (map : α → β) (preserves : ∀ a b, map (combine a b) = merge (map a) (map b))
    (empty : α) (rounds : Nat) (items : List α) :
    map (balFold combine empty rounds items) =
      balFold merge (map empty) rounds (items.map map) := by
  induction rounds generalizing items with
  | zero =>
    change map (items.foldr combine empty) = (items.map map).foldr merge (map empty)
    induction items with
    | nil => rfl
    | cons item items inductionHypothesis =>
      exact (preserves item _).trans (congrArg (merge (map item)) inductionHypothesis)
  | succ rounds ih =>
    rcases items with _ | ⟨first, _ | ⟨second, items⟩⟩
    · rfl
    · rfl
    · change map (balFold combine empty rounds (pairUp combine (first :: second :: items) none)) =
        balFold merge (map empty) rounds (pairUp merge ((first :: second :: items).map map) none)
      exact (ih _).trans
        (congrArg (balFold merge (map empty) rounds)
          (map_pairUp combine merge map preserves _ none))

private theorem listMap_to_map {α β : Type} (map : α → β) (entries : List α) :
    listMap map entries = entries.map map := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => exact congrArg (List.cons (map entry)) ih

private theorem scale_packEntries (width length depth weight : Nat) (entries : List (Nat × Nat)) :
    (packEntries width length depth 1 entries).scale weight =
      packEntries width length depth weight entries := by
  unfold packEntries
  rw [map_balFold PackTrie.add PackTrie.add (PackTrie.scale weight) (scale_add weight)]
  change balFold PackTrie.add .zero 64 _ = _
  congr 1
  simp only [listMap_to_map, List.map_map]
  apply List.map_congr_left
  intro entry _
  rw [Function.comp_apply, scale_single, Nat.one_mul, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.mul_assoc]

private theorem scale_costEntries (width variableCount weight : Nat)
    (entries : List (Nat × Nat))
    (valid : ∀ entry ∈ entries, entry.1 < variableCount) :
    weight * costEntries width variableCount 1 entries =
      costEntries width variableCount weight entries := by
  unfold costEntries
  rw [map_balFold Nat.add Nat.add (weight * ·) (Nat.mul_add weight)]
  change balFold Nat.add 0 64 _ = _
  congr 1
  simp only [listMap_to_map, List.map_map]
  apply List.map_congr_left
  intro entry membership
  simp only [Function.comp_apply, Nat.blt_eq.mpr (valid entry membership), Bool.cond_true,
    Nat.add_zero, Nat.one_mul]

/-- Rescale each quantity of a checked unit-weight summary for a row with valid indices. -/
noncomputable def PackedSummary.scaleWeight (weight : Nat)
    (summary : PackedSummary) : PackedSummary :=
  ⟨weight * summary.cost, (weight : Int) * summary.rhs,
    summary.positive.scale weight, summary.negative.scale weight⟩

end Esgk.FarkasPackedCheck

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def rowSummary (weight : Nat) (row : Option Row) : PackedSummary :=
  replaySummary 256 params.box (fun _ : Unit ↦ row) (.leaf weight ())

private noncomputable def rowIndicesChecked (row : Option Row) : Bool :=
  Option.rec false
    (fun row ↦ row.pos.all (fun entry ↦ Nat.blt entry.1 params.nv) &&
      row.neg.all (fun entry ↦ Nat.blt entry.1 params.nv)) row

private theorem rescaleRow {row : Option Row} {summary : PackedSummary}
    (checked : rowSummary 1 row = summary) (indices : rowIndicesChecked row = true)
    (weight : Nat) (updateRhs : Int → Int) :
    ({ summary with rhs := updateRhs summary.rhs }).scaleWeight weight =
      rowSummary weight (row.map fun row ↦ { row with rhs := updateRhs row.rhs }) := by
  cases row with
  | none => cases indices
  | some row =>
    obtain ⟨positive, negative⟩ := Bool.and_eq_true_iff.mp indices
    have validPositive (entry) (membership : entry ∈ row.pos) : entry.1 < params.nv :=
      Nat.blt_eq.mp (List.all_eq_true.mp positive entry membership)
    have validNegative (entry) (membership : entry ∈ row.neg) : entry.1 < params.nv :=
      Nat.blt_eq.mp (List.all_eq_true.mp negative entry membership)
    rw [← checked]
    change PackedSummary.mk
      (weight * (costEntries 256 params.nv 1 row.pos + costEntries 256 params.nv 1 row.neg))
      ((weight : Int) * updateRhs ((1 : Int) * row.rhs))
      ((packEntries 256 (chunkLen params.nv 4) 4 1 row.pos).scale weight)
      ((packEntries 256 (chunkLen params.nv 4) 4 1 row.neg).scale weight) = _
    rw [Nat.mul_add, scale_costEntries _ _ _ _ validPositive,
      scale_costEntries _ _ _ _ validNegative, Int.one_mul, scale_packEntries, scale_packEntries]
    rfl

private theorem rescaleUnchangedRow {row : Option Row} {summary : PackedSummary}
    (checked : rowSummary 1 row = summary) (indices : rowIndicesChecked row = true)
    (weight : Nat) : summary.scaleWeight weight = rowSummary weight row := by
  have verified := rescaleRow checked indices weight id
  cases row <;> exact verified

/-! ### Moment and interval rows -/

/-- The unit-weight summary of the long moment row, whose coefficients are case independent. -/
noncomputable def momentUnitSummary : PackedSummary := s4_summary% 0, (s4_rows% "1 mlo")

/-- The unit-weight summary of the lower-bound row in case 0. -/
noncomputable def lowerUnitSummary : PackedSummary := s4_summary% 0, (s4_rows% "1 caselo")

/-- The unit-weight summary of the upper-bound row in case 0. -/
noncomputable def upperUnitSummary : PackedSummary := s4_summary% 0, (s4_rows% "1 casehi")

private theorem momentUnitSummary_eq :
    rowSummary 1 (buildIntWithSharedDenominator params 0 0 .mlo) = momentUnitSummary := by
  s4_check_equality

private theorem lowerUnitSummary_eq :
    rowSummary 1 (buildIntWithSharedDenominator params (caseY.get 0) (caseY.get 1) .caselo) =
      lowerUnitSummary := by
  s4_check_equality

private theorem upperUnitSummary_eq :
    rowSummary 1 (buildIntWithSharedDenominator params (caseY.get 0) (caseY.get 1) .casehi) =
      upperUnitSummary := by
  s4_check_equality

private theorem momentIndices :
    rowIndicesChecked (buildIntWithSharedDenominator params 0 0 .mlo) = true := by
  -- Check the indices of the fixed 1,283-point grid row by kernel reduction.
  decide +kernel

private theorem lowerIndices :
    rowIndicesChecked (buildIntWithSharedDenominator params (caseY.get 0) (caseY.get 1)
      .caselo) = true := by
  -- Check the indices of the fixed 1,283-point grid row by kernel reduction.
  decide +kernel

private theorem upperIndices :
    rowIndicesChecked (buildIntWithSharedDenominator params (caseY.get 0) (caseY.get 1)
      .casehi) = true := by
  -- Check the indices of the fixed 1,283-point grid row by kernel reduction.
  decide +kernel

/-- The checked common denominator of the coefficients of each interval-bound row. -/
def gridCoefficientDenominator : Nat := 16384000000000000

private def entriesDenominator : List (Nat × ℚ) → Nat :=
  List.rec 1 (fun entry _ accumulated ↦ Nat.lcm entry.2.den accumulated)

private theorem rowDenominator_eq (entries : List (Nat × ℚ)) (rhs : ℚ) :
    QRow.den ⟨entries, rhs⟩ = Nat.lcm (entriesDenominator entries) rhs.den := by
  induction entries with
  | nil => exact (Nat.lcm_one_left _).symm
  | cons entry entries ih =>
    change Nat.lcm entry.2.den (QRow.den ⟨entries, rhs⟩) =
      Nat.lcm (Nat.lcm entry.2.den (entriesDenominator entries)) rhs.den
    rw [ih, Nat.lcm_assoc]

private theorem lowerDenominator :
    (params.build (caseY.get 0) (caseY.get 1) .caselo).map
      (fun row ↦ (entriesDenominator row.ent, row.den)) =
      some (gridCoefficientDenominator, gridCoefficientDenominator) := by
  s4_check_equality

private theorem upperDenominator :
    (params.build (caseY.get 0) (caseY.get 1) .casehi).map
      (fun row ↦ (entriesDenominator row.ent, row.den)) =
      some (gridCoefficientDenominator, gridCoefficientDenominator) := by
  s4_check_equality

private theorem replaceScaledRhs (lower upper : ℚ) (tag : Tag) (rhs : ℚ) (denominator : Nat)
    (denominators : (params.build (caseY.get 0) (caseY.get 1) tag).map
      (fun row ↦ (entriesDenominator row.ent, row.den)) = some (denominator, denominator))
    (updated : params.build lower upper tag =
      (params.build (caseY.get 0) (caseY.get 1) tag).map fun row ↦ { row with rhs })
    (divides : rhs.den ∣ denominator) :
    buildIntWithSharedDenominator params lower upper tag =
      (buildIntWithSharedDenominator params (caseY.get 0) (caseY.get 1) tag).map
        fun row ↦ { row with rhs := QRow.scaleNumerator denominator rhs } := by
  unfold buildIntWithSharedDenominator
  rw [updated]
  generalize params.build (caseY.get 0) (caseY.get 1) tag = base at denominators ⊢
  cases base with
  | none => cases denominators
  | some row =>
    have equal := Option.some.inj denominators
    have entries : entriesDenominator row.ent = denominator := congrArg Prod.fst equal
    have original : row.den = denominator := congrArg Prod.snd equal
    have scaled : QRow.den { row with rhs } = denominator := by
      rw [rowDenominator_eq, entries]
      exact Nat.lcm_eq_left_iff_dvd.mpr divides
    simp only [Option.map_some, Option.bind_some, original, scaled]
    cases denominator <;> rfl

private theorem lowerBuild_eq (parameters : Params) (lower upper oldLower oldUpper : ℚ) :
    parameters.build lower upper .caselo =
      (parameters.build oldLower oldUpper .caselo).map
        fun row ↦ { row with rhs := wid - lower + 4 } := by
  change parameters.rowCaseLo lower = (parameters.rowCaseLo oldLower).map _
  unfold Params.rowCaseLo
  split <;> rfl

private theorem upperBuild_eq (parameters : Params) (lower upper oldLower oldUpper : ℚ) :
    parameters.build lower upper .casehi =
      (parameters.build oldLower oldUpper .casehi).map
        fun row ↦ { row with rhs := upper - wid - 4 } := by
  change parameters.rowCaseHi upper = (parameters.rowCaseHi oldUpper).map _
  unfold Params.rowCaseHi
  split <;> rfl

/-- Replay a tree using unit-weight summaries for its long geometric rows. -/
noncomputable def replaySummaryWithCachedRows (lower upper : ℚ) (rows : WTree Tag) :
    PackedSummary :=
  let build := buildIntWithSharedDenominator params lower upper
  let original (weight : Nat) (tag : Tag) :=
    replaySummary 256 params.box build (.leaf weight tag)
  rows.rec (motive := fun _ ↦ PackedSummary)
    (fun weight tag ↦ match tag with
      | .mlo => momentUnitSummary.scaleWeight weight
      | .caselo =>
        let rhs := wid - lower + 4
        if rhs.den ∣ gridCoefficientDenominator then
          ({ lowerUnitSummary with
            rhs := QRow.scaleNumerator gridCoefficientDenominator rhs }).scaleWeight weight
        else original weight tag
      | .casehi =>
        let rhs := upper - wid - 4
        if rhs.den ∣ gridCoefficientDenominator then
          ({ upperUnitSummary with
            rhs := QRow.scaleNumerator gridCoefficientDenominator rhs }).scaleWeight weight
        else original weight tag
      | other => original weight other)
    (fun _ _ left right ↦ left.combine right)

private theorem cachedLeaf_eq (lower upper : ℚ) (weight : Nat) (tag : Tag) :
    replaySummaryWithCachedRows lower upper (.leaf weight tag) =
      rowSummary weight (buildIntWithSharedDenominator params lower upper tag) := by
  cases tag <;> try rfl
  case mlo => exact rescaleUnchangedRow momentUnitSummary_eq momentIndices weight
  case caselo =>
    change (if (wid - lower + 4).den ∣ gridCoefficientDenominator then _ else _) = _
    split
    · rename_i divides
      rw [replaceScaledRhs lower upper .caselo (wid - lower + 4) gridCoefficientDenominator
        lowerDenominator (lowerBuild_eq params lower upper _ _) divides]
      exact rescaleRow lowerUnitSummary_eq lowerIndices weight
        (fun _ ↦ QRow.scaleNumerator gridCoefficientDenominator (wid - lower + 4))
    · rfl
  case casehi =>
    change (if (upper - wid - 4).den ∣ gridCoefficientDenominator then _ else _) = _
    split
    · rename_i divides
      rw [replaceScaledRhs lower upper .casehi (upper - wid - 4) gridCoefficientDenominator
        upperDenominator (upperBuild_eq params lower upper _ _) divides]
      exact rescaleRow upperUnitSummary_eq upperIndices weight
        (fun _ ↦ QRow.scaleNumerator gridCoefficientDenominator (upper - wid - 4))
    · rfl

/-- Cached replay gives exactly the same result as the original packed checker. -/
theorem replaySummary_eq_of_cached {lower upper : ℚ} {rows : WTree Tag}
    {summary : PackedSummary} (verified : replaySummaryWithCachedRows lower upper rows = summary) :
    replaySummary 256 params.box (buildIntWithSharedDenominator params lower upper) rows =
      summary := by
  have same (tree : WTree Tag) : replaySummaryWithCachedRows lower upper tree =
      replaySummary 256 params.box (buildIntWithSharedDenominator params lower upper) tree := by
    induction tree with
    | leaf weight tag => exact cachedLeaf_eq lower upper weight tag
    | node left right ihLeft ihRight =>
      exact congrArg₂ PackedSummary.combine ihLeft ihRight
  exact (same rows).symm.trans verified

end Esgk.S4
