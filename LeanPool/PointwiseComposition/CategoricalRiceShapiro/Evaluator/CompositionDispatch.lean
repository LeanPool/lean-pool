/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CellEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CellCongruence
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.TableLookupEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.PartialRecursive.CanonicalComposition

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Fixed component indices and evaluator-cell reconstruction

When the index under evaluation has constructor number `5`, the eager branches
of `codeEvaluatorCell` collapse to the composition branch, and a successful cell
yields the two table lookups that branch performs:
`eval_codeEvaluatorCell_succ_of_tag_five`.

For the canonical index of a composed program the two component indices are
known natural numbers.  `eval_codeEvaluatorCell_succ_of_canonicalPartrecCompIndex`
replaces the decoded queries by the constant codes of those numbers, so that a
later argument can reason with fixed indices rather than with decoder terms.
The replacement is a graph equivalence at the given assignment, not a
definitional one: `eval_codeTableLookup_query_congr` performs it, and
`eval_iff_codeConst_of_eval` supplies its hypothesis.

The outer lookup needs one further step.  Transporting the payload equivalence
under `codeLift` produces `codeLift (codeConst (n := r) fCode)`, which is
evaluation-equivalent but not definitionally equal to the arity-`r + 1` constant
the statement asks for; `eval_codeLift_codeConst_iff` closes that gap.

These results are forward extraction from a successful cell over `𝐏𝐀⁻`.  They
construct no cell, so the eager evaluation of the unused branches is not an
obstacle for them.

The composition reverse theorem,
`eval_codeEvaluatorCell_succ_of_component_lookups`, does construct a cell.
`codeIfPos` is a sum of products
containing both of its branches, so an evaluation of the cell needs a value for
every branch, not only the composition branch.  Over `𝐏𝐀`,
`eval_codeEvaluatorCell_exists_of_values` gives the entire eager cell a value;
positive fuel and tag `5` force the composition branch in that evaluation, and
`eval_unique` identifies the cell value with the value of the composition branch
built from the two component lookups.

The pairing analogue,
`eval_codeEvaluatorCell_succ_of_pair_component_lookups`, starts from a standard
constructor-`4` index and successful lookups at its two decoded payloads.  It
constructs the eager cell with the same existence theorem, forces the pairing
branch using positive fuel and the decoded tag, and identifies the result with
`pair a b + 1`.  Its decoder-reading and branch-selection lemmas remain private.
This result does not transport certificates between stages or prove persistence
for recursively referenced subcodes.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.ArithmeticCode

open CategoricalRiceShapiro.PartialRecursive

/-- A successful evaluator cell whose index has constructor number `5` performs
the two lookups of the composition branch. -/
theorem eval_codeEvaluatorCell_succ_of_tag_five {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    {r : ℕ} (dtable dn : Code r) (y : M) (v : Fin r → M)
    (htag :
      Semiformula.Evalb ((5 : M) :> v)
        (code (codePartrecTag (codeUnpair₂ (codeListLength dtable)))))
    (hcell : Semiformula.Evalb ((y + 1) :> v) (code (codeEvaluatorCell dtable dn))) :
    ∃ x : M,
      Semiformula.Evalb ((x + 1) :> v)
          (code
            (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
              (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) ∧
        Semiformula.Evalb ((y + 1) :> x :> v)
          (code
            (codeTableLookup (codeLift dtable) (codeLift (codeUnpair₁ (codeListLength dtable)))
              (codeLift (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable))))
              (codeHead (n := r)))) :=
  by
  have hposS : ∀ a : M, (0 : M) < a + 1 := fun a =>
    lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hne54 : ¬((5 : M) = (4 : M)) :=
    by
    have h5 : (5 : M) = (4 : M) + 1 := by norm_num
    rw [h5]
    exact (_root_.ne_of_lt (lt_add_one _)).symm
  simp only [codeEvaluatorCell] at hcell
  obtain ⟨kf, hkf, hkcase⟩ := eval_codeIfPos_cases _ _ _ (y + 1) v hcell
  rcases hkcase with ⟨-, hbig⟩ | ⟨-, hzero⟩
  · obtain ⟨e4, he4, h4case⟩ := eval_codeIfPos_cases _ _ _ (y + 1) v hbig
    rw [eval_codeEq_iff] at he4
    obtain ⟨a4, b4, ha4, hb4, hc4⟩ := he4
    have ha45 : a4 = (5 : M) := eval_unique ha4 htag
    have hb44 : b4 = (4 : M) :=
      by
      have h := (eval_codeConst_iff 4 b4 v).mp hb4
      simpa using h
    have he40 : e4 = 0 := by
      rcases hc4 with ⟨heq, -⟩ | ⟨-, h0⟩
      · exact absurd (by rw [← ha45, ← hb44]; exact heq) hne54
      · exact h0
    rcases h4case with ⟨hpos, -⟩ | ⟨-, hrest⟩
    · exact absurd (he40 ▸ hpos) (_root_.lt_irrefl 0)
    · obtain ⟨e5, he5, h5case⟩ := eval_codeIfPos_cases _ _ _ (y + 1) v hrest
      rw [eval_codeEq_iff] at he5
      obtain ⟨a5, b5, ha5, hb5, hc5⟩ := he5
      have ha55 : a5 = (5 : M) := eval_unique ha5 htag
      have hb55 : b5 = (5 : M) :=
        by
        have h := (eval_codeConst_iff 5 b5 v).mp hb5
        simpa using h
      have he51 : e5 = 1 := by
        rcases hc5 with ⟨-, h1⟩ | ⟨hne, -⟩
        · exact h1
        · exact absurd (by rw [ha55, hb55]) hne
      rcases h5case with ⟨-, hcomp5⟩ | ⟨h0, -⟩
      · exact
          (eval_codeCompEvaluatorCell_succ_iff dtable (codeUnpair₁ (codeListLength dtable))
                (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable)))
                (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn y v).mp
            hcomp5
      · exact absurd (he51 ▸ h0) _root_.one_ne_zero
  · exfalso
    have hz0 : y + 1 = ((0 : ℕ) : M) := (eval_codeConst_iff 0 (y + 1) v).mp hzero
    simp only [Nat.cast_zero] at hz0
    exact absurd hz0 (ne_of_gt (hposS y))

/-- The dispatcher step at the canonical composition index, still with decoded
queries.  Used only by the theorem below, which replaces those queries by the
constant codes of the two component indices. -/
private theorem eval_codeEvaluatorCell_succ_decoded {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r) (fCode gCode : ℕ) (y : M) (v : Fin r → M)
    (hcode :
      Semiformula.Evalb ((canonicalPartrecCompIndex fCode gCode : M) :> v)
        (code (codeUnpair₂ (codeListLength dtable))))
    (hcell : Semiformula.Evalb ((y + 1) :> v) (code (codeEvaluatorCell dtable dn))) :
    ∃ x : M,
      Semiformula.Evalb ((x + 1) :> v)
          (code
            (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
              (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) ∧
        Semiformula.Evalb ((y + 1) :> x :> v)
          (code
            (codeTableLookup (codeLift dtable) (codeLift (codeUnpair₁ (codeListLength dtable)))
              (codeLift (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable))))
              (codeHead (n := r)))) :=
  eval_codeEvaluatorCell_succ_of_tag_five dtable dn y v
    (eval_codePartrecTag_canonicalPartrecCompIndex (codeUnpair₂ (codeListLength dtable)) fCode
      gCode v hcode)
    hcell

/-- Fixed component indices for canonical program composition.

From a successful evaluator cell whose index is the canonical index of the
composition of `fCode` and `gCode`, the inner lookup runs the constant `gCode`
and the outer lookup the constant `fCode`, both at their own arities. -/
theorem eval_codeEvaluatorCell_succ_of_canonicalPartrecCompIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r) (fCode gCode : ℕ) (y : M) (v : Fin r → M)
    (hcode :
      Semiformula.Evalb ((canonicalPartrecCompIndex fCode gCode : M) :> v)
        (FFL.FirstOrder.Arithmetic.code
          (codeUnpair₂ (codeListLength dtable))))
    (hcell :
      Semiformula.Evalb ((y + 1) :> v)
        (FFL.FirstOrder.Arithmetic.code
          (codeEvaluatorCell dtable dn))) :
    ∃ x : M,
      Semiformula.Evalb ((x + 1) :> v)
          (FFL.FirstOrder.Arithmetic.code
            (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
              (codeConst (n := r) gCode) dn)) ∧
        Semiformula.Evalb ((y + 1) :> (x :> v))
          (FFL.FirstOrder.Arithmetic.code
            (codeTableLookup (codeLift dtable) (codeLift (codeUnpair₁ (codeListLength dtable)))
              (codeConst (n := r + 1) fCode) (codeHead (n := r)))) := by
  obtain ⟨x, hinner, houter⟩ :=
    eval_codeEvaluatorCell_succ_decoded dtable dn fCode gCode y v hcode hcell
  refine ⟨x, ?_, ?_⟩
  · -- the inner query has the graph of the constant `gCode` at this assignment
    have hg :=
      eval_codePartrecPayload₂_canonicalPartrecCompIndex (codeUnpair₂ (codeListLength dtable))
        fCode gCode v hcode
    refine (eval_codeTableLookup_query_congr dtable _ _ _ dn (x + 1) v ?_).mp hinner
    intro z
    exact eval_iff_codeConst_of_eval _ gCode v (by simpa using hg) z
  · -- the outer query, first as a lifted constant, then at the larger arity
    have hf :=
      eval_codePartrecPayload₁_canonicalPartrecCompIndex (codeUnpair₂ (codeListLength dtable))
        fCode gCode v hcode
    have hlift :=
      (eval_codeTableLookup_query_congr (codeLift dtable)
            (codeLift (codeUnpair₁ (codeListLength dtable)))
            (codeLift (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable))))
            (codeLift (codeConst (n := r) fCode)) (codeHead (n := r)) (y + 1) (x :> v) ?_).mp
        houter
    · refine
        (eval_codeTableLookup_query_congr (codeLift dtable)
              (codeLift (codeUnpair₁ (codeListLength dtable)))
              (codeLift (codeConst (n := r) fCode)) (codeConst (n := r + 1) fCode)
              (codeHead (n := r)) (y + 1) (x :> v) ?_).mp
          hlift
      intro z
      exact eval_codeLift_codeConst_iff fCode z x v
    · intro z
      rw [eval_codeLift_iff, eval_codeLift_iff]
      exact eval_iff_codeConst_of_eval _ fCode v (by simpa using hf) z

/-- Reverse direction of `eval_codeEvaluatorCell_succ_of_canonicalPartrecCompIndex`,
with positive fuel as an additional hypothesis: at the canonical index of the
composition of `fCode` and `gCode`, the two component lookups give the evaluator
cell the value `y + 1`.

The lookups are first returned to the decoded queries, and
`eval_codeCompEvaluatorCell_succ_iff` gives the composition branch the value
`y + 1`.  Values of `dtable` and `dn` are read from the inner lookup, and
`eval_codeEvaluatorCell_exists_of_values` gives the entire cell some value `z`.
Positive fuel and tag `5` select the composition branch in that evaluation, so
`z = y + 1` by `eval_unique`.

`𝐏𝐀` is the only theory assumption; `eval_codeEvaluatorCell_exists_of_values`
assumes it.  `𝐈Σ 1` is installed inside the proof and supplies `𝐏𝐀⁻` through
Foundation's instance chain, and the index enters through
`ORingStructure.numeral`. -/
theorem eval_codeEvaluatorCell_succ_of_component_lookups {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ} (dtable dn : Code r) (fCode gCode : ℕ) (x y : M) (v : Fin r → M)
    (hcode :
      Semiformula.Evalb
        ((ORingStructure.numeral (canonicalPartrecCompIndex fCode gCode) : M) :> v)
        (FFL.FirstOrder.Arithmetic.code
          (codeUnpair₂ (codeListLength dtable))))
    (hfuel :
      ∃ k : M,
        0 < k ∧
          Semiformula.Evalb (k :> v)
            (FFL.FirstOrder.Arithmetic.code
              (codeUnpair₁ (codeListLength dtable))))
    (hinner :
      Semiformula.Evalb ((x + 1) :> v)
        (FFL.FirstOrder.Arithmetic.code
          (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
            (codeConst (n := r) gCode) dn)))
    (houter :
      Semiformula.Evalb ((y + 1) :> (x :> v))
        (FFL.FirstOrder.Arithmetic.code
          (codeTableLookup (codeLift dtable) (codeLift (codeUnpair₁ (codeListLength dtable)))
            (codeConst (n := r + 1) fCode) (codeHead (n := r))))) :
    Semiformula.Evalb ((y + 1) :> v)
      (FFL.FirstOrder.Arithmetic.code
        (codeEvaluatorCell dtable dn)) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  simp only [numeral_eq_natCast_app] at hcode
  have htag :=
    eval_codePartrecTag_canonicalPartrecCompIndex (codeUnpair₂ (codeListLength dtable)) fCode
      gCode v hcode
  have hf :=
    eval_codePartrecPayload₁_canonicalPartrecCompIndex (codeUnpair₂ (codeListLength dtable))
      fCode gCode v hcode
  have hg :=
    eval_codePartrecPayload₂_canonicalPartrecCompIndex (codeUnpair₂ (codeListLength dtable))
      fCode gCode v hcode
  have hinnerDecoded :
    Semiformula.Evalb ((x + 1) :> v)
      (code
        (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) :=
    by
    refine (eval_codeTableLookup_query_congr dtable _ _ _ dn (x + 1) v ?_).mpr hinner
    intro z
    exact eval_iff_codeConst_of_eval _ gCode v (by simpa using hg) z
  have houterLifted :=
    (eval_codeTableLookup_query_congr (codeLift dtable)
          (codeLift (codeUnpair₁ (codeListLength dtable))) (codeLift (codeConst (n := r) fCode))
          (codeConst (n := r + 1) fCode) (codeHead (n := r)) (y + 1) (x :> v)
          (fun z => eval_codeLift_codeConst_iff fCode z x v)).mpr
      houter
  have houterDecoded :
    Semiformula.Evalb ((y + 1) :> x :> v)
      (code
        (codeTableLookup (codeLift dtable) (codeLift (codeUnpair₁ (codeListLength dtable)))
          (codeLift (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable))))
          (codeHead (n := r)))) :=
    by
    refine
      (eval_codeTableLookup_query_congr (codeLift dtable)
            (codeLift (codeUnpair₁ (codeListLength dtable)))
            (codeLift (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable))))
            (codeLift (codeConst (n := r) fCode)) (codeHead (n := r)) (y + 1) (x :> v) ?_).mpr
        houterLifted
    intro z
    rw [eval_codeLift_iff, eval_codeLift_iff]
    exact eval_iff_codeConst_of_eval _ fCode v (by simpa using hf) z
  have hcomp :=
    (eval_codeCompEvaluatorCell_succ_iff dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn y v).mpr
      ⟨x, hinnerDecoded, houterDecoded⟩
        -- values of `dtable` and `dn`, read from the inner lookup
  have hsubArg :
    ∀ (A B : Code r) (w : M),
      Semiformula.Evalb (w :> v) (code (codeSub A B)) →
        ∃ a : M, Semiformula.Evalb (a :> v) (code A) :=
    by
    intro A B w h
    obtain ⟨⟨b, -, hbody⟩, -⟩ := (eval_codeRfindPos_iff _ w v).mp h
    obtain ⟨p, q, hp, -, -⟩ := (eval_codeOr_iff _ _ b (w :> v)).mp hbody
    obtain ⟨e₁, e₂, -, he₂, -⟩ := (eval_codeEq_iff _ _ p (w :> v)).mp hp
    exact ⟨e₂, (eval_codeLift_iff A e₂ w v).mp he₂⟩
  rw [codeTableLookup_eq] at hinner
  obtain ⟨o, ho⟩ := hsubArg _ _ _ hinner
  obtain ⟨l, hl, -⟩ := eval_codeIfPos_cases _ _ _ o v ho
  rw [codeListDrop_eq_comp, eval_comp_iff] at hl
  obtain ⟨w, -, hw⟩ := hl
  have hindex : Semiformula.Evalb (w 0 :> v) (code dn) := hw 0
  obtain ⟨o', ho'⟩ := hsubArg _ _ _ (hw 1)
  obtain ⟨l', hl', -⟩ := eval_codeIfPos_cases _ _ _ o' v ho'
  rw [codeListDrop_eq_comp, eval_comp_iff] at hl'
  obtain ⟨w', -, hw'⟩ := hl'
  have htable : Semiformula.Evalb (w' 1 :> v) (code dtable) :=
    hw'
      1
        -- the entire eager cell has some value `z`
  obtain ⟨z, hz⟩ :=
    eval_codeEvaluatorCell_exists_of_values dtable dn (w' 1) (w 0) v htable hindex
  have hne54 : ¬((5 : M) = (4 : M)) :=
    by
    have h5 : (5 : M) = (4 : M) + 1 := by norm_num
    rw [h5]
    exact (_root_.ne_of_lt (lt_add_one _)).symm
  obtain ⟨k, hk, hkv⟩ := hfuel
  have hcell := hz
  simp only [codeEvaluatorCell] at hcell
  obtain ⟨kf, hkf, hkcase⟩ := eval_codeIfPos_cases _ _ _ z v hcell
  have hkfk : kf = k := eval_unique hkf hkv
  rcases hkcase with ⟨-, hbig⟩ | ⟨hkf0, -⟩
  · obtain ⟨e4, he4, h4case⟩ := eval_codeIfPos_cases _ _ _ z v hbig
    rw [eval_codeEq_iff] at he4
    obtain ⟨a4, b4, ha4, hb4, hc4⟩ := he4
    have ha45 : a4 = (5 : M) := eval_unique ha4 htag
    have hb44 : b4 = (4 : M) :=
      by
      have h := (eval_codeConst_iff 4 b4 v).mp hb4
      simpa using h
    have he40 : e4 = 0 := by
      rcases hc4 with ⟨heq, -⟩ | ⟨-, h0⟩
      · exact absurd (by rw [← ha45, ← hb44]; exact heq) hne54
      · exact h0
    rcases h4case with ⟨hpos, -⟩ | ⟨-, hrest⟩
    · exact absurd (he40 ▸ hpos) (_root_.lt_irrefl 0)
    · obtain ⟨e5, he5, h5case⟩ := eval_codeIfPos_cases _ _ _ z v hrest
      rw [eval_codeEq_iff] at he5
      obtain ⟨a5, b5, ha5, hb5, hc5⟩ := he5
      have ha55 : a5 = (5 : M) := eval_unique ha5 htag
      have hb55 : b5 = (5 : M) :=
        by
        have h := (eval_codeConst_iff 5 b5 v).mp hb5
        simpa using h
      have he51 : e5 = 1 := by
        rcases hc5 with ⟨-, h1⟩ | ⟨hne, -⟩
        · exact h1
        · exact absurd (by rw [ha55, hb55]) hne
      rcases h5case with ⟨-, hcomp5⟩ | ⟨h0, -⟩
      · rw [eval_unique hcomp5 hcomp] at hz
        exact hz
      · exact absurd (he51 ▸ h0) _root_.one_ne_zero
  · exact absurd (hkfk ▸ hkf0) (ne_of_gt hk)

variable {M : Type*} [ORingStructure M]

/-- The parity bit as a remainder. -/
private theorem bodd_toNat_eq_mod_two (n : ℕ) : n.bodd.toNat = n % 2 := by
  rw [Nat.mod_two_of_bodd]

/-- The production tag decoder, written with remainders. -/
private theorem partrecCodeTag_eq (q : ℕ) :
    partrecCodeTag q = if q < 4 then q else 4 + 2 * ((q - 4) % 2) + Nat.div2 (q - 4) % 2 := by
  simp only [partrecCodeTag, bodd_toNat_eq_mod_two]

/-- The constructor number of a standard index, read inside a model. -/
private theorem eval_codePartrecTag_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodeTag q : ℕ) : M) :> v) (code (codePartrecTag d)) :=
  by
  have h4 : Semiformula.Evalb (((4 : ℕ) : M) :> v) (code (codeConst (n := r) 4)) :=
    eval_codeConst 4 v
  have h2 : Semiformula.Evalb (((2 : ℕ) : M) :> v) (code (codeConst (n := r) 2)) :=
    eval_codeConst 2 v
  have hrr := eval_codeSub_natCast d (codeConst 4) q 4 v hd (by simpa using h4)
  have hbodd0 := eval_codeBodd_natCast (codeSub d (codeConst 4)) (q - 4) v hrr
  have hbodd1 :=
    eval_codeBodd_natCast (codeDiv2 (codeSub d (codeConst 4))) (Nat.div2 (q - 4)) v
      (eval_codeDiv2_natCast _ (q - 4) v hrr)
  have hmul :
    Semiformula.Evalb ((((2 * ((q - 4) % 2) : ℕ)) : M) :> v)
      (code (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4))))) :=
    by
    refine (eval_codeMul_iff _ _ _ v).mpr ⟨_, _, h2, hbodd0, ?_⟩
    push_cast
    norm_num
  have hadd1 :
    Semiformula.Evalb ((((4 + 2 * ((q - 4) % 2) : ℕ)) : M) :> v)
      (code
        (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4)))))) :=
    by
    refine (eval_codeAdd_iff _ _ _ v).mpr ⟨_, _, h4, hmul, ?_⟩
    push_cast
    norm_num
  have hbig :
    Semiformula.Evalb ((((4 + 2 * ((q - 4) % 2) + Nat.div2 (q - 4) % 2 : ℕ)) : M) :> v)
      (code
        (codeAdd
          (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4)))))
          (codeBodd (codeDiv2 (codeSub d (codeConst 4)))))) :=
    by
    refine (eval_codeAdd_iff _ _ _ v).mpr ⟨_, _, hadd1, hbodd1, ?_⟩
    push_cast
    norm_num
  rw [partrecCodeTag_eq]
  simp only [codePartrecTag]
  by_cases hq : q < 4
  · have hlt1 : Semiformula.Evalb ((1 : M) :> v) (code (codeLt d (codeConst 4))) :=
      by
      refine (eval_codeLt_iff _ _ _ v).mpr ⟨_, _, hd, by simpa using h4, Or.inl ⟨?_, rfl⟩⟩
      exact_mod_cast hq
    rw [ite_eq_left hq]
    exact
      eval_codeIfPos_of _ _ _ (1 : M) (((q : ℕ)) : M) _ _ v hlt1 hd hbig
        (Or.inl ⟨_root_.zero_lt_one, rfl⟩)
  · have hlt0 : Semiformula.Evalb ((0 : M) :> v) (code (codeLt d (codeConst 4))) :=
      by
      refine (eval_codeLt_iff _ _ _ v).mpr ⟨_, _, hd, by simpa using h4, Or.inr ⟨?_, rfl⟩⟩
      intro hc
      exact hq (by exact_mod_cast hc)
    rw [ite_eq_right hq]
    exact eval_codeIfPos_of _ _ _ (0 : M) (((q : ℕ)) : M) _ _ v hlt0 hd hbig (Or.inr ⟨rfl, rfl⟩)

/-- The payload of a standard compound index, read inside a model. -/
private theorem eval_codePartrecPayload_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload q : ℕ) : M) :> v) (code (codePartrecPayload d)) :=
  by
  have h4 : Semiformula.Evalb (((4 : ℕ) : M) :> v) (code (codeConst (n := r) 4)) :=
    eval_codeConst 4 v
  have hrr := eval_codeSub_natCast d (codeConst 4) q 4 v hd (by simpa using h4)
  simpa only [codePartrecPayload, partrecCodePayload] using
    eval_codeDiv2_natCast _ _ v (eval_codeDiv2_natCast _ (q - 4) v hrr)

/-- The first subcode of a standard index, read inside a model. -/
private theorem eval_codePartrecPayload₁_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₁ q : ℕ) : M) :> v) (code (codePartrecPayload₁ d)) :=
  eval_codeUnpair₁_natCast (codePartrecPayload d) _ v (eval_codePartrecPayload_natCast d q v hd)

/-- The second subcode of a standard index, read inside a model. -/
private theorem eval_codePartrecPayload₂_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₂ q : ℕ) : M) :> v) (code (codePartrecPayload₂ d)) :=
  eval_codeUnpair₂_natCast (codePartrecPayload d) _ v (eval_codePartrecPayload_natCast d q v hd)

/-- A successful evaluator cell whose constructor number is `4` is the value of
the pairing branch.  Adapted from the accepted external tag-4 probe. -/
private theorem cell_pair_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r) (v : Fin r → M)
    (z k tag : M) (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hkpos : 0 < k)
    (htag :
      Semiformula.Evalb (tag :> v)
        (code (codePartrecTag (codeUnpair₂ (codeListLength dtable)))))
    (h4 : tag = ((4 : ℕ) : M))
    (hcell : Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn))) :
    Semiformula.Evalb (z :> v)
      (code
        (codePairEvaluatorCell dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) :=
  by
  have hc :
    ∀ (m : ℕ) (w : Fin r → M),
      Semiformula.Evalb (((m : ℕ) : M) :> w) (code (codeConst (n := r) m)) :=
    fun m w => eval_codeConst m w
  have hval :
    ∀ (m : ℕ) (x : M),
      Semiformula.Evalb (x :> v) (code (codeConst (n := r) m)) → x = ((m : ℕ) : M) :=
    fun m x hx => eval_unique hx (hc m v)
  simp only [codeEvaluatorCell] at hcell
  obtain ⟨f0, hf0, hc0⟩ := eval_codeIfPos_cases _ _ _ z v hcell
  have hf0k : f0 = k := eval_unique hf0 hk
  rcases hc0 with ⟨-, hbig⟩ | ⟨h0, -⟩
  swap
  · exact absurd (hf0k ▸ h0 : k = 0) (ne_of_gt hkpos)
  obtain ⟨e4, he4, hcase4⟩ := eval_codeIfPos_cases _ _ _ z v hbig
  rw [eval_codeEq_iff] at he4
  obtain ⟨x, y, hx, hy, hxy⟩ := he4
  have hxt : x = tag := eval_unique hx htag
  have hy4 : y = ((4 : ℕ) : M) := hval 4 y hy
  have he41 : e4 = 1 := by
    rcases hxy with ⟨-, h1⟩ | ⟨hne, -⟩
    · exact h1
    · exact absurd (by rw [hxt, hy4]; exact h4) hne
  rcases hcase4 with ⟨-, hpair⟩ | ⟨h0, -⟩
  · exact hpair
  · exact absurd (he41 ▸ h0 : (1 : M) = 0) _root_.one_ne_zero

/-- Fixed component lookups build the whole pairing cell.

For a standard index `q` of constructor number `4`, two successful component
lookups at the constant codes of its two subcodes — both at the same fuel and the
same argument, as pairing requires — give the entire eager evaluator cell the
value `pair a b + 1`.  Nothing about the cell's own success is assumed. -/
theorem eval_codeEvaluatorCell_succ_of_pair_component_lookups [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    {r : ℕ} (dtable dn : Code r) (q : ℕ) (htagq : partrecCodeTag q = 4) (a b : M)
    (v : Fin r → M)
    (hcode :
      Semiformula.Evalb (((q : ℕ) : M) :> v) (code (codeUnpair₂ (codeListLength dtable))))
    (hfuel :
      ∃ k : M, 0 < k ∧ Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hfirst :
      Semiformula.Evalb ((a + 1) :> v)
        (code
          (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
            (codeConst (n := r) (partrecCodePayload₁ q)) dn)))
    (hsecond :
      Semiformula.Evalb ((b + 1) :> v)
        (code
          (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
            (codeConst (n := r) (partrecCodePayload₂ q)) dn))) :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pair a b + 1) :> v)
      (code (codeEvaluatorCell dtable dn)) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- the decoded readings of the standard index
  have htag := eval_codePartrecTag_natCast (codeUnpair₂ (codeListLength dtable)) q v hcode
  rw [htagq] at htag
  have hp₁ := eval_codePartrecPayload₁_natCast (codeUnpair₂ (codeListLength dtable)) q v hcode
  have hp₂ := eval_codePartrecPayload₂_natCast (codeUnpair₂ (codeListLength dtable)) q v hcode
  have hfirstD :
    Semiformula.Evalb ((a + 1) :> v)
      (code
        (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable))) dn)) :=
    by
    refine (eval_codeTableLookup_query_congr dtable _ _ _ dn (a + 1) v ?_).mpr hfirst
    intro z
    exact eval_iff_codeConst_of_eval _ (partrecCodePayload₁ q) v hp₁ z
  have hsecondD :
    Semiformula.Evalb ((b + 1) :> v)
      (code
        (codeTableLookup dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) :=
    by
    refine (eval_codeTableLookup_query_congr dtable _ _ _ dn (b + 1) v ?_).mpr hsecond
    intro z
    exact eval_iff_codeConst_of_eval _ (partrecCodePayload₂ q) v hp₂ z
  have hsecondL :
    Semiformula.Evalb ((b + 1) :> a :> v)
      (code
        (codeTableLookup (codeLift dtable) (codeLift (codeUnpair₁ (codeListLength dtable)))
          (codeLift (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))))
          (codeLift dn))) :=
    (eval_codeTableLookup_congr_at (codeLift dtable)
          (codeLift (codeUnpair₁ (codeListLength dtable)))
          (codeLift (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable)))) (codeLift dn)
          dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn (b + 1) (a :> v) v
          (fun z => eval_codeLift_iff _ z a v) (fun z => eval_codeLift_iff _ z a v)
          (fun z => eval_codeLift_iff _ z a v) (fun z => eval_codeLift_iff _ z a v)).mpr
      hsecondD
  have hpair :=
    (eval_codePairEvaluatorCell_succ_iff dtable (codeUnpair₁ (codeListLength dtable))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn
          (FFL.FirstOrder.Arithmetic.pair a b) v).mpr
      ⟨a, b, hfirstD, hsecondL, rfl⟩
        -- values for the table and the argument code, read off a component lookup
  have hsubArg :
    ∀ (A B : Code r) (w : M),
      Semiformula.Evalb (w :> v) (code (codeSub A B)) →
        ∃ x : M, Semiformula.Evalb (x :> v) (code A) :=
    by
    intro A B w h
    obtain ⟨⟨c, -, hbody⟩, -⟩ := (eval_codeRfindPos_iff _ w v).mp h
    obtain ⟨p, s, hp, -, -⟩ := (eval_codeOr_iff _ _ c (w :> v)).mp hbody
    obtain ⟨e₁, e₂, -, he₂, -⟩ := (eval_codeEq_iff _ _ p (w :> v)).mp hp
    exact ⟨e₂, (eval_codeLift_iff A e₂ w v).mp he₂⟩
  have hfirstRaw := hfirst
  rw [codeTableLookup_eq] at hfirstRaw
  obtain ⟨o, ho⟩ := hsubArg _ _ _ hfirstRaw
  obtain ⟨l, hl, -⟩ := eval_codeIfPos_cases _ _ _ o v ho
  rw [codeListDrop_eq_comp, eval_comp_iff] at hl
  obtain ⟨w, -, hw⟩ := hl
  have hindex : Semiformula.Evalb (w 0 :> v) (code dn) := hw 0
  obtain ⟨o', ho'⟩ := hsubArg _ _ _ (hw 1)
  obtain ⟨l', hl', -⟩ := eval_codeIfPos_cases _ _ _ o' v ho'
  rw [codeListDrop_eq_comp, eval_comp_iff] at hl'
  obtain ⟨w', -, hw'⟩ := hl'
  have htable : Semiformula.Evalb (w' 1 :> v) (code dtable) :=
    hw'
      1
        -- the eager whole cell has some value, forced into the pairing branch
  obtain ⟨z, hz⟩ :=
    eval_codeEvaluatorCell_exists_of_values dtable dn (w' 1) (w 0) v htable hindex
  obtain ⟨k, hkpos, hkv⟩ := hfuel
  have hbranch :=
    cell_pair_branch dtable dn v z k (((4 : ℕ) : M)) hkv hkpos (by simpa using htag) rfl hz
  rw [eval_unique hbranch hpair] at hz
  exact hz

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
