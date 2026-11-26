/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateChecker

/-!
# Kernel replay for coverage chunks

In kernel reduction, an array's optional lookup checks the backing list's length
before walking to the index. List lookup combines the bounds check and access in
one traversal. The replay also reads rejection column bits directly from the
packed prefix and shares node bounds checks across pruning and transitions.
The equality with the original checker holds for arbitrary claims and bounds.
-/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

private def listLookup (entries : Array α) (index : Nat) : Option α :=
  entries.toList[index]?

private theorem listLookup_eq (entries : Array α) (index : Nat) :
    listLookup entries index = entries[index]? :=
  Array.getElem?_toList

private def listLookupDefault (entries : Array α) (index : Nat) (fallback : α) : α :=
  (listLookup entries index).getD fallback

private theorem listLookupDefault_eq (entries : Array α) (index : Nat) (fallback : α) :
    listLookupDefault entries index fallback = entries.getD index fallback := by
  rw [listLookupDefault, listLookup_eq, Array.getD_eq_getD_getElem?]

private def groupedLookup (groups : Array (Array α)) (identifier : Nat) : Option α :=
  match listLookup groups (identifier / 64) with
  | none => none
  | some group => listLookup group (identifier % 64)

private theorem groupedLookup_eq (groups : Array (Array α)) (identifier : Nat) :
    groupedLookup groups identifier =
      (match groups[identifier / 64]? with
      | none => none
      | some group => group[identifier % 64]?) := by
  simp only [groupedLookup, listLookup_eq]

private def replayNodeAt (claims : BranchClaims) (identifier : Nat) : NodeClaim :=
  (groupedLookup claims.nodeGroups identifier).getD defaultNodeClaim

private theorem replayNodeAt_eq (claims : BranchClaims) (identifier : Nat) :
    replayNodeAt claims identifier = claims.nodeAt identifier := by
  simp only [replayNodeAt, groupedLookup_eq, BranchClaims.nodeAt, Array.getD_eq_getD_getElem?]
  cases claims.nodeGroups[identifier / 64]? <;> rfl

private def replayRowChoice (centre : Vertex) (index : Nat) : SearchRowChoice :=
  listLookupDefault (listLookupDefault searchRowChoices centre.val #[]) index ⟨0, 0⟩

private theorem replayRowChoice_eq (centre : Vertex) (index : Nat) :
    replayRowChoice centre index = (searchRowChoices.getD centre.val #[]).getD index ⟨0, 0⟩ := by
  simp only [replayRowChoice, listLookupDefault_eq]

private def replayRowIndices (rows : UInt64) (offset : Nat) : List Nat :=
  let word := ((rows >>> UInt64.ofNat offset) &&& 31).toNat
  (listLookupDefault fiveBitIndices word []).map fun index => offset + index

private theorem replayRowIndices_eq (rows : UInt64) (offset : Nat) :
    replayRowIndices rows offset = rowIndexWord rows offset := by
  simp only [replayRowIndices, rowIndexWord, listLookupDefault_eq]

private def replayPatternMatch (identifier : Nat) (code : UInt64) : Bool :=
  match groupedLookup densePatternSummaryGroups identifier with
  | none => false
  | some summary => (summary.mask &&& code) == summary.mask

private theorem replayPatternMatch_eq (identifier : Nat) (code : UInt64) :
    replayPatternMatch identifier code = patternIdentifierPackedMatchesB identifier code := by
  have lookup_eq : groupedLookup densePatternSummaryGroups identifier =
      densePatternSummaryLookup identifier := by
    rw [groupedLookup_eq, densePatternSummaryLookup]
    cases densePatternSummaryGroups[identifier / 64]? <;> rfl
  simp only [replayPatternMatch, patternIdentifierPackedMatchesB,
    lookup_eq]
  rfl

private def replayHardMatch (identifier : Nat) (code : UInt64) : Bool :=
  match groupedLookup denseHardSummaryGroups identifier with
  | none => false
  | some summary => summary.code == code

private theorem replayHardMatch_eq (identifier : Nat) (code : UInt64) :
    replayHardMatch identifier code = hardIdentifierPackedMatchesB identifier code := by
  have lookup_eq : groupedLookup denseHardSummaryGroups identifier =
      denseHardSummaryLookup identifier := by
    rw [groupedLookup_eq, denseHardSummaryLookup]
    cases denseHardSummaryGroups[identifier / 64]? <;> rfl
  simp only [replayHardMatch, hardIdentifierPackedMatchesB,
    lookup_eq]
  rfl

private def replayActiveRow
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (cursor : LocalCursor) (index : Nat) : LocalCursor :=
  if !cursor.ok then cursor
  else
    let choice := replayRowChoice centre index
    let nextCode := addRowCode claim.code choice.rowMask centre
    let nextPairState := pairState.add choice.pairMask
    if bitSetB claim.patternRows index then
      match cursor.patternOrigins with
      | [] => ⟨false, [], cursor.childIds, cursor.hardOrigins⟩
      | patternIdentifier :: patternIdentifiers =>
          ⟨replayPatternMatch patternIdentifier nextCode,
            patternIdentifiers, cursor.childIds, cursor.hardOrigins⟩
    else if remaining.isEmpty then
      match cursor.hardOrigins with
      | [] => ⟨false, cursor.patternOrigins, cursor.childIds, []⟩
      | hardIdentifier :: hardIdentifiers =>
          ⟨replayHardMatch hardIdentifier nextCode,
            cursor.patternOrigins, cursor.childIds, hardIdentifiers⟩
    else
      match cursor.childIds with
      | [] => ⟨false, cursor.patternOrigins, [], cursor.hardOrigins⟩
      | childId :: childIds =>
          let child := replayNodeAt claims childId
          let childValid := decide (childId < identifier) &&
            decide (childId < claims.nodeCount) &&
            (child.depth == claim.depth + 1) && (child.code == nextCode) &&
            (child.pairOnce == nextPairState.seenOnce) &&
            (child.pairTwice == nextPairState.seenTwice)
          ⟨childValid, cursor.patternOrigins, childIds, cursor.hardOrigins⟩

private theorem replayActiveRow_eq
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState) :
    replayActiveRow claims identifier claim centre remaining pairState =
      processRow claims identifier claim centre remaining pairState := by
  funext cursor index
  simp only [replayActiveRow, processRow, replayPatternMatch_eq, replayHardMatch_eq,
    replayNodeAt_eq, replayRowChoice_eq]
  rfl

private def findWord (wordIndex : Nat) : List NodeWordClaim → Nat → NodeWordClaim
  | [], _ | _, 0 => emptyNodeWordClaim wordIndex
  | word :: rest, fuel + 1 =>
      if word.wordIndex = wordIndex then word else findWord wordIndex rest fuel

private theorem findWord_eq
    (entries : Array NodeWordClaim) (wordIndex position fuel : Nat) :
    findWord wordIndex (entries.toList.drop position) fuel =
      nodeWordClaimAtAux entries wordIndex position fuel := by
  induction fuel generalizing position with
  | zero =>
      cases entries.toList.drop position <;> rfl
  | succ fuel induction =>
      have head_eq : entries[position]? = (entries.toList.drop position).head? := by
        rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, Array.getElem?_toList]
      cases suffix_eq : entries.toList.drop position with
      | nil =>
          simp only [nodeWordClaimAtAux, head_eq, suffix_eq, List.head?_nil, findWord]
      | cons word rest =>
          have tail_eq : entries.toList.drop (position + 1) = rest := by
            rw [List.drop_add_one_eq_tail_drop, suffix_eq, List.tail_cons]
          simp only [nodeWordClaimAtAux, head_eq, suffix_eq, List.head?_cons,
            findWord, ← induction, tail_eq]

private def replayWordAt (claim : NodeClaim) (wordIndex : Nat) : NodeWordClaim :=
  findWord wordIndex claim.wordClaims.toList 7

private theorem replayWordAt_eq (claim : NodeClaim) (wordIndex : Nat) :
    replayWordAt claim wordIndex = claim.wordAt wordIndex :=
  findWord_eq claim.wordClaims wordIndex 0 7

private def replayActiveWord
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (wordIndex : Nat) : Bool :=
  let wordClaim := replayWordAt claim wordIndex
  let initial : LocalCursor := ⟨true, wordClaim.patternOrigins, wordClaim.childIds,
    wordClaim.hardOrigins⟩
  let result := (replayRowIndices claim.activeRows (5 * wordIndex)).foldl
    (replayActiveRow claims identifier claim centre remaining pairState) initial
  result.ok && result.patternOrigins.isEmpty && result.childIds.isEmpty &&
    result.hardOrigins.isEmpty

private theorem replayActiveWord_eq
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState) :
    replayActiveWord claims identifier claim centre remaining pairState =
      nodeWordValidB claims identifier claim centre remaining pairState := by
  funext wordIndex
  simp only [replayActiveWord, nodeWordValidB, processFiveRows, replayActiveRow_eq,
    replayRowIndices_eq, replayWordAt_eq]

private theorem shiftAmount_eq (index : Nat) (bound : index < 64) :
    (UInt64.ofNat index).toNat % 64 = index := by
  have capacity : 64 ≤ UInt64.size := by decide
  have wordBound : index < UInt64.size := Nat.lt_of_lt_of_le bound capacity
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt wordBound, Nat.mod_eq_of_lt bound]

private theorem bitSetB_eq_testBit (code : UInt64) (index : Nat) (bound : index < 64) :
    bitSetB code index = code.toNat.testBit index := by
  have test_eq :
      code.toNat.testBit index = decide ((code.toNat >>> index) % 2 = 1) := by
    rw [← Nat.add_zero index, ← Nat.testBit_shiftRight, Nat.testBit_zero, Nat.add_zero]
  rw [Bool.eq_iff_iff, test_eq]
  change (((code >>> UInt64.ofNat index) &&& 1) != 0) = true ↔ _
  rw [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight,
    shiftAmount_eq index bound, UInt64.toNat_one, UInt64.toNat_zero, Nat.and_one_is_mod,
    decide_eq_true_eq]
  omega

-- Extracting a row and testing target t gives the bit at 8 * centre + t.
private theorem rowFromCode_bit (code : UInt64) (centre target : Vertex) :
    bitSetB (rowFromCode code centre) target.val = code.toNat.testBit (varIndex centre target) := by
  have targetBound : target.val < 64 := by omega
  have shiftBound : 8 * centre.val < 64 := by omega
  have mask : (255 : Nat).testBit target.val = true := by
    change (2 ^ 8 - 1).testBit target.val = true
    simp only [Nat.testBit_two_pow_sub_one, target.isLt, decide_true]
  rw [bitSetB_eq_testBit _ _ targetBound, rowFromCode, UInt64.toNat_and, UInt64.toNat_shiftRight,
    shiftAmount_eq _ shiftBound]
  change ((code.toNat >>> (8 * centre.val)) &&& 255).testBit target.val = _
  rw [Nat.testBit_and, mask, Bool.and_true, Nat.testBit_shiftRight]
  rfl

private def replayColumnCount (claim : NodeClaim) (target : Vertex) : Nat :=
  (assignedCentres claim.depth).countP fun centre =>
    claim.code.toNat.testBit (varIndex centre target)

private theorem replayColumnCount_eq (claim : NodeClaim) (target : Vertex) :
    replayColumnCount claim target =
      assignmentColumnCount (assignmentsFromCode claim.code claim.depth) target := by
  simp only [replayColumnCount, assignmentColumnCount, ← List.countP_eq_length_filter,
    assignmentsFromCode, List.countP_map, Function.comp_def, rowFromCode_bit]

private def replayRejectedRow
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (index target : Nat) : Bool :=
  if htarget : target < 8 then
    let targetVertex : Vertex := ⟨target, htarget⟩
    let row := (replayRowChoice centre index).rowMask
    let count := replayColumnCount claim targetVertex + if bitSetB row target then 1 else 0
    decide (4 < count) ||
      decide (count + remainingColumnCapacity remaining targetVertex < 4)
  else false

private theorem replayRejectedRow_eq
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex) (index target : Nat) :
    replayRejectedRow claim centre remaining index target =
      rejectedRowValidB claim centre remaining index target := by
  simp only [replayRejectedRow, rejectedRowValidB, replayRowChoice_eq, replayColumnCount_eq,
    assignmentColumnCount, ← List.countP_eq_length_filter, List.countP_cons]

private def replayRejection
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (cursor : RejectionCursor) (index : Nat) : RejectionCursor :=
  if !cursor.ok then cursor
  else
    match cursor.targets with
    | [] => ⟨false, []⟩
    | target :: targets => ⟨replayRejectedRow claim centre remaining index target, targets⟩

private theorem replayRejection_eq
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex) :
    replayRejection claim centre remaining = processRejectedRow claim centre remaining := by
  funext cursor index
  simp only [replayRejection, processRejectedRow, replayRejectedRow_eq]
  rfl

private def replayRejectedWord (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (indices targets : List Nat) : Bool :=
  let result := indices.foldl (replayRejection claim centre remaining) ⟨true, targets⟩
  result.ok && result.targets.isEmpty

private theorem replayRejectedWord_eq
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex) (indices targets : List Nat) :
    replayRejectedWord claim centre remaining indices targets =
      rejectedWordValidB claim centre remaining indices targets := by
  simp only [replayRejectedWord, rejectedWordValidB, replayRejection_eq]

private def replayPruning (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex) :
    Bool :=
  match groupedLookup conflictCoverGroups claim.conflictCoverId with
  | none => false
  | some cover =>
      let incompatible := cover.incompatibleRows
      let inactive := claim.rejectedRows ||| incompatible
      let legalRows : UInt64 := 34359738367
      if cover.centre != centre.val ||
          (cover.requiredPairs &&& claim.pairTwice) != cover.requiredPairs ||
          (claim.patternRows &&& claim.activeRows) != claim.patternRows ||
          (claim.rejectedRows &&& incompatible) != 0 ||
          (claim.activeRows &&& inactive) != 0 ||
          (claim.activeRows ||| inactive) != legalRows then false
      else
        (List.range 7).all fun wordIndex =>
          replayRejectedWord claim centre remaining
            (replayRowIndices claim.rejectedRows (5 * wordIndex))
            (replayWordAt claim wordIndex).rejectionTargets

private def replayNode (claims : BranchClaims) (identifier : Nat) : Bool :=
  if identifier < claims.nodeCount then
    let claim := replayNodeAt claims identifier
    if claim.depth < searchCentres.length then
      let centre := searchCentres.getD claim.depth 0
      let remaining := searchCentres.drop (claim.depth + 1)
      let pairState : PairState := ⟨claim.pairOnce, claim.pairTwice⟩
      replayPruning claim centre remaining &&
        (List.range 7).all (replayActiveWord claims identifier claim centre remaining pairState)
    else false
  else false

private theorem replayNode_eq (claims : BranchClaims) (identifier : Nat) :
    replayNode claims identifier = nodeLocalValidB claims identifier := by
  have lookup_eq (coverIdentifier : Nat) :
      groupedLookup conflictCoverGroups coverIdentifier = conflictCoverLookup coverIdentifier := by
    rw [groupedLookup_eq, conflictCoverLookup]
    cases conflictCoverGroups[coverIdentifier / 64]? <;> rfl
  by_cases bounds : identifier < claims.nodeCount
  · by_cases depth : (claims.nodeAt identifier).depth < searchCentres.length
    · simp only [replayNode, replayNodeAt_eq, nodeLocalValidB, nodePruningValidB,
        nodeTransitionsValidB, ite_eq_left bounds, ite_eq_left depth, replayPruning, lookup_eq,
        replayActiveWord_eq, replayRejectedWord_eq, replayRowIndices_eq, replayWordAt_eq]
      rfl
    · simp only [replayNode, replayNodeAt_eq, nodeLocalValidB, nodePruningValidB,
        nodeTransitionsValidB, ite_eq_left bounds, ite_eq_right depth, Bool.false_and]
  · simp only [replayNode, nodeLocalValidB, nodePruningValidB, nodeTransitionsValidB,
      ite_eq_right bounds, Bool.false_and]

private def replayChunk (claims : BranchClaims) (start count : Nat) : Bool :=
  (List.range count).all fun offset =>
    replayNode claims (start + offset)

private theorem replayChunk_eq (claims : BranchClaims) (start count : Nat) :
    replayChunk claims start count = nodeClaimChunkValidB claims start count := by
  simp only [replayChunk, nodeClaimChunkValidB, replayNode_eq]

/-- Decidability via the faster kernel replay. The fact files install this instance locally
and use `import all` so the kernel can reduce the private replay definitions. -/
@[instance_reducible] public def nodeChunkReplayDecidable (claims : BranchClaims)
    (start count : Nat) : Decidable (nodeClaimChunkValidB claims start count = true) :=
  decidable_of_iff (replayChunk claims start count = true) (by rw [replayChunk_eq])

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
