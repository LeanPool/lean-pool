/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.PartialRecursive.CanonicalComposition
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CellEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.HistoryEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Structural bridges for the primitive-recursion constructor

Constructor number `6` is primitive recursion.  This file supplies structural
infrastructure for it, in two parts.

The first part, in `CategoricalRiceShapiro.PartialRecursive`, defines
`canonicalPartrecPrecIndex fCode gCode`, the canonical index of the primitive
recursion whose base program is named by `fCode` and whose step program is named
by `gCode`.  It proves the decoder and ranking facts for that index: its closed
form `2 * (2 * Nat.pair fCode gCode) + 1 + 4`, its constructor number `6`, its
payload `Nat.pair fCode gCode` with components `fCode` and `gCode`, and the strict
bounds `fCode < canonicalPartrecPrecIndex fCode gCode` and
`gCode < canonicalPartrecPrecIndex fCode gCode`.  It also proves the
corresponding readings of the payload, the constructor number and the two
components inside a model of `𝐏𝐀⁻`.

The second part, in `CategoricalRiceShapiro.Evaluator`, proves the zero and
successor success equivalences for the primitive-recursion evaluator cell
`codePrecEvaluatorCell`, over `𝐏𝐀` and `𝐈𝐎𝐩𝐞𝐧`.  For a zero recursion argument,
when the argument evaluates to `⟪z, 0⟫`, the cell succeeds with `y + 1` exactly
when the base lookup does.  For a successor recursion argument, when the argument
evaluates to `⟪z, a + 1⟫`, the cell succeeds with `y + 1` exactly when, for one
intermediate value `x`, the lookup of the same index at the previous fuel on
`⟪z, a⟫` succeeds with `x + 1` and the step-program lookup at the current fuel on
`⟪z, ⟪a, x⟫⟫` succeeds with `y + 1`.

The first part also proves, for an arbitrary natural number `q` with
constructor number `6`, that `q` is the canonical primitive-recursion index of
its decoded payload components, `q = canonicalPartrecPrecIndex
(partrecCodePayload₁ q) (partrecCodePayload₂ q)`, and that both decoded payloads
are strictly smaller than `q`.

`eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator` identifies the
same-index lookup of the successor equivalence, in the history before the cell
at `k + 1, q` and at input `⟪z, a + 1⟫`, with a successful `codeHistoryEvaluator`
evaluation at stage `k` on `⟪z, a⟫`, through
`eval_predecessor_lookup_succ_iff_codeHistoryEvaluator`.

This is structural infrastructure.  The file proves neither tag-6 persistence of
the evaluator certificate nor persistence for every standard index.
-/

@[expose] public section

namespace CategoricalRiceShapiro
namespace PartialRecursive

open Encodable Denumerable

open CategoricalRiceShapiro.ArithmeticCode

/-- The index of the primitive recursion whose base program is named by `fCode`
and whose step program is named by `gCode`. -/
def canonicalPartrecPrecIndex (fCode gCode : ℕ) : ℕ :=
  Encodable.encode
    (Nat.Partrec.Code.prec (Denumerable.ofNat Nat.Partrec.Code fCode)
      (Denumerable.ofNat Nat.Partrec.Code gCode))

/-- The closed form of the canonical primitive-recursion index. -/
theorem canonicalPartrecPrecIndex_eq (fCode gCode : ℕ) :
    canonicalPartrecPrecIndex fCode gCode = 2 * (2 * Nat.pair fCode gCode) + 1 + 4 :=
  by
  unfold canonicalPartrecPrecIndex
  rw [Nat.Partrec.Code.encodeCode_eq]
  simp only [Nat.Partrec.Code.encodeCode]
  simp only [← Nat.Partrec.Code.encodeCode_eq, Denumerable.encode_ofNat]

/-- The base subindex is below the canonical primitive-recursion index. -/
theorem canonicalPartrecPrecIndex_base_lt (fCode gCode : ℕ) :
    fCode < canonicalPartrecPrecIndex fCode gCode :=
  by
  unfold canonicalPartrecPrecIndex
  simpa only [Denumerable.encode_ofNat] using
    (Nat.Partrec.Code.encode_lt_prec (Denumerable.ofNat Nat.Partrec.Code fCode)
        (Denumerable.ofNat Nat.Partrec.Code gCode)).1

/-- The step subindex is below the canonical primitive-recursion index. -/
theorem canonicalPartrecPrecIndex_step_lt (fCode gCode : ℕ) :
    gCode < canonicalPartrecPrecIndex fCode gCode :=
  by
  unfold canonicalPartrecPrecIndex
  simpa only [Denumerable.encode_ofNat] using
    (Nat.Partrec.Code.encode_lt_prec (Denumerable.ofNat Nat.Partrec.Code fCode)
        (Denumerable.ofNat Nat.Partrec.Code gCode)).2

/-- The payload of the canonical primitive-recursion index is the pair of the
base and step subindices. -/
theorem partrecCodePayload_canonicalPartrecPrecIndex (fCode gCode : ℕ) :
    partrecCodePayload (canonicalPartrecPrecIndex fCode gCode) = Nat.pair fCode gCode :=
  by
  have hsub : canonicalPartrecPrecIndex fCode gCode - 4 = 2 * (2 * Nat.pair fCode gCode) + 1 :=
    by rw [canonicalPartrecPrecIndex_eq]; omega
  simp only [partrecCodePayload, hsub, Nat.div2_val]
  omega

/-- The canonical primitive-recursion index has constructor number `6`.
`bodd.toNat` and `% 2` are related by `Nat.mod_two_of_bodd`. -/
theorem canonicalPartrecPrecIndex_constructor_number (fCode gCode : ℕ) :
    partrecCodeTag (canonicalPartrecPrecIndex fCode gCode) = 6 :=
  by
  have hb : ∀ n : ℕ, n.bodd.toNat = n % 2 := fun n => by rw [Nat.mod_two_of_bodd]
  have hlt : ¬(canonicalPartrecPrecIndex fCode gCode < 4) := by
    rw [canonicalPartrecPrecIndex_eq]; omega
  have hsub : canonicalPartrecPrecIndex fCode gCode - 4 = 2 * (2 * Nat.pair fCode gCode) + 1 :=
    by rw [canonicalPartrecPrecIndex_eq]; omega
  simp only [partrecCodeTag, hlt, ite_false, hsub, hb, Nat.div2_val]
  omega

/-- The first subcode of the canonical primitive-recursion index is the base
program. -/
theorem canonicalPartrecPrecIndex_base_index (fCode gCode : ℕ) :
    partrecCodePayload₁ (canonicalPartrecPrecIndex fCode gCode) = fCode := by
  simp only [partrecCodePayload₁, partrecCodePayload_canonicalPartrecPrecIndex, Nat.unpair_pair]

/-- The second subcode of the canonical primitive-recursion index is the step
program. -/
theorem canonicalPartrecPrecIndex_step_index (fCode gCode : ℕ) :
    partrecCodePayload₂ (canonicalPartrecPrecIndex fCode gCode) = gCode := by
  simp only [partrecCodePayload₂, partrecCodePayload_canonicalPartrecPrecIndex, Nat.unpair_pair]

/-- A natural number `q` of constructor number `6` is the canonical
primitive-recursion index of its two payload components. -/
theorem partrecCode_eq_canonicalPartrecPrecIndex_of_tag_six (q : ℕ)
    (hq : partrecCodeTag q = 6) :
    q = canonicalPartrecPrecIndex (partrecCodePayload₁ q) (partrecCodePayload₂ q) :=
  by
  have hb : ∀ n : ℕ, n.bodd.toNat = n % 2 := fun n => by rw [Nat.mod_two_of_bodd]
  have h4 : ¬q < 4 := by
    intro hlt
    simp only [partrecCodeTag, hlt, ite_true] at hq
    omega
  simp only [partrecCodeTag, h4, ite_false, hb, Nat.div2_val] at hq
  rw [canonicalPartrecPrecIndex_eq]
  simp only [partrecCodePayload₁, partrecCodePayload₂, Nat.pair_unpair, partrecCodePayload,
    Nat.div2_val]
  omega

/-- Both payload components of a natural number `q` of constructor number `6`
are strictly smaller than `q`. -/
theorem partrecCodePayloads_lt_of_tag_six (q : ℕ) (hq : partrecCodeTag q = 6) :
    partrecCodePayload₁ q < q ∧ partrecCodePayload₂ q < q :=
  by
  have hindex := partrecCode_eq_canonicalPartrecPrecIndex_of_tag_six q hq
  have hbase :=
    canonicalPartrecPrecIndex_base_lt (partrecCodePayload₁ q) (partrecCodePayload₂ q)
  have hstep :=
    canonicalPartrecPrecIndex_step_lt (partrecCodePayload₁ q) (partrecCodePayload₂ q)
  rw [← hindex] at hbase hstep
  exact ⟨hbase, hstep⟩

/-!
### Evaluation in an arbitrary model -/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

/-- The payload of the canonical primitive-recursion index, read inside a model. -/
theorem eval_codePartrecPayload_canonicalPartrecPrecIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecPrecIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb (((Nat.pair fCode gCode : ℕ) : M) :> v) (code (codePartrecPayload d)) :=
  by
  simpa only [partrecCodePayload_canonicalPartrecPrecIndex] using
    IndexDecoder.eval_codePartrecPayload_natCast d (canonicalPartrecPrecIndex fCode gCode) v hd

/-- The constructor number of the canonical primitive-recursion index, read
inside a model: it is `6`, the number of primitive recursion. -/
theorem eval_codePartrecTag_canonicalPartrecPrecIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecPrecIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb ((6 : M) :> v) (code (codePartrecTag d)) :=
  by
  simpa only [Nat.succ_eq_add_one, canonicalPartrecPrecIndex_constructor_number,
    Nat.cast_ofNat] using
    IndexDecoder.eval_codePartrecTag_natCast d (canonicalPartrecPrecIndex fCode gCode) v hd

/-- The base subcode of the canonical primitive-recursion index, read inside a
model. -/
theorem eval_codePartrecPayload₁_canonicalPartrecPrecIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecPrecIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb (((fCode : ℕ) : M) :> v) (code (codePartrecPayload₁ d)) :=
  by
  simpa only [canonicalPartrecPrecIndex_base_index] using
    IndexDecoder.eval_codePartrecPayload₁_natCast d (canonicalPartrecPrecIndex fCode gCode) v hd

/-- The step subcode of the canonical primitive-recursion index, read inside a
model. -/
theorem eval_codePartrecPayload₂_canonicalPartrecPrecIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecPrecIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb (((gCode : ℕ) : M) :> v) (code (codePartrecPayload₂ d)) :=
  by
  simpa only [canonicalPartrecPrecIndex_step_index] using
    IndexDecoder.eval_codePartrecPayload₂_natCast d (canonicalPartrecPrecIndex fCode gCode) v hd

end PartialRecursive
end CategoricalRiceShapiro

/-!
### Part B: success semantics of the primitive-recursion cell -/

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

variable {M : Type*} [ORingStructure M]

/-- **Zero recursion argument.**  When the argument code `dn` evaluates to
`⟪z, 0⟫`, the primitive-recursion cell succeeds with output `y + 1` exactly when
the base lookup succeeds with output `y + 1`: the table at fuel `k' + 1`, the
base program `dcf`, and input `z`. -/
theorem eval_codePrecEvaluatorCell_succ_iff_of_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ}
    (dtable dk' dq dcf dcg dn : Code r) (table k' qv cf cg z y : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk' : Semiformula.Evalb (k' :> v) (code dk')) (hq : Semiformula.Evalb (qv :> v) (code dq))
    (hcf : Semiformula.Evalb (cf :> v) (code dcf))
    (hcg : Semiformula.Evalb (cg :> v) (code dcg))
    (hn : Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair z 0 :> v) (code dn)) :
    Semiformula.Evalb ((y + 1) :> v) (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      Semiformula.Evalb ((y + 1) :> v)
        (code (codeTableLookup dtable (codeSucc dk') dcf (codeUnpair₁ dn))) :=
  by
  have ht : Semiformula.Evalb ((0 : M) :> v) (code (codeUnpair₂ dn)) :=
    by
    have h := eval_codeUnpair₂ dn _ v hn
    rwa [FFL.FirstOrder.Arithmetic.pi₂_pair] at h
  constructor
  · intro hcell
    simp only [codePrecEvaluatorCell] at hcell
    obtain ⟨f, hf, hcase⟩ := eval_codeIfPos_cases _ _ _ _ v hcell
    have hf0 : f = 0 := eval_unique hf ht
    rcases hcase with ⟨hpos, -⟩ | ⟨-, hbase⟩
    · exact absurd hpos (by rw [hf0]; exact _root_.lt_irrefl 0)
    · exact hbase
  · intro hbase
    obtain ⟨w, hw⟩ :=
      eval_codePrecEvaluatorCell_exists dtable dk' dq dcf dcg dn table k' qv cf cg _ v htable
        hk' hq hcf hcg hn
    have hw' := hw
    simp only [codePrecEvaluatorCell] at hw'
    obtain ⟨f, hf, hcase⟩ := eval_codeIfPos_cases _ _ _ _ v hw'
    have hf0 : f = 0 := eval_unique hf ht
    rcases hcase with ⟨hpos, -⟩ | ⟨-, hwbase⟩
    · exact absurd hpos (by rw [hf0]; exact _root_.lt_irrefl 0)
    · have hwy : w = y + 1 := eval_unique hwbase hbase
      rw [hwy] at hw
      exact hw

/-- **Successor recursion argument.**  When the argument code `dn` evaluates to
`⟪z, a + 1⟫`, the primitive-recursion cell succeeds with output `y + 1` exactly
when, for one intermediate value `x`, the predecessor lookup of the same index
`dq` at fuel `k'` on `⟪z, a⟫` succeeds with output `x + 1`, and the step lookup
of `dcg` at fuel `k' + 1` on `⟪z, ⟪a, x⟫⟫` succeeds with output `y + 1`. -/
theorem eval_codePrecEvaluatorCell_succ_iff_of_succ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ}
    (dtable dk' dq dcf dcg dn : Code r) (table k' qv cf cg z a y : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk' : Semiformula.Evalb (k' :> v) (code dk')) (hq : Semiformula.Evalb (qv :> v) (code dq))
    (hcf : Semiformula.Evalb (cf :> v) (code dcf))
    (hcg : Semiformula.Evalb (cg :> v) (code dcg))
    (hn : Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair z (a + 1) :> v) (code dn)) :
    Semiformula.Evalb ((y + 1) :> v) (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      ∃ x : M,
        Semiformula.Evalb ((x + 1) :> v)
            (code
              (codeTableLookup dtable dk' dq
                (codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1))))) ∧
          Semiformula.Evalb ((y + 1) :> x :> v)
            (code
              (codeTableLookup (codeLift dtable) (codeLift (codeSucc dk')) (codeLift dcg)
                (codePair (codeLift (codeUnpair₁ dn))
                  (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1)))
                    (codeHead (n := r)))))) :=
  by
  have ht : Semiformula.Evalb ((a + 1) :> v) (code (codeUnpair₂ dn)) :=
    by
    have h := eval_codeUnpair₂ dn _ v hn
    rwa [FFL.FirstOrder.Arithmetic.pi₂_pair] at h
  have hnz : ¬(a + 1 = (0 : M)) := ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  constructor
  · intro hcell
    simp only [codePrecEvaluatorCell] at hcell
    obtain ⟨f, hf, hcase⟩ := eval_codeIfPos_cases _ _ _ _ v hcell
    have hfa : f = a + 1 := eval_unique hf ht
    rcases hcase with ⟨-, hstep⟩ | ⟨hf0, -⟩
    · exact (eval_codeOptionBind_succ_iff _ _ y v).mp hstep
    · exact absurd (by rw [← hfa]; exact hf0) hnz
  · intro hx
    have hstep := (eval_codeOptionBind_succ_iff _ _ y v).mpr hx
    obtain ⟨w, hw⟩ :=
      eval_codePrecEvaluatorCell_exists dtable dk' dq dcf dcg dn table k' qv cf cg _ v htable
        hk' hq hcf hcg hn
    have hw' := hw
    simp only [codePrecEvaluatorCell] at hw'
    obtain ⟨f, hf, hcase⟩ := eval_codeIfPos_cases _ _ _ _ v hw'
    have hfa : f = a + 1 := eval_unique hf ht
    rcases hcase with ⟨-, hwstep⟩ | ⟨hf0, -⟩
    · have hwy : w = y + 1 := eval_unique hwstep hstep
      rw [hwy] at hw
      exact hw
    · exact absurd (by rw [← hfa]; exact hf0) hnz

/-- The predecessor lookup reads the argument `pair z a` from `pair z (a + 1)`. -/
theorem eval_prec_predecessor_argument [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (s qCode z a : M) :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pair z a) :>
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code
        (codePair (codeUnpair₁ (Code.proj (2 : Fin 3)))
          (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1)))) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hproj :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z (a + 1) :>
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have h1 := eval_codeUnpair₁ (Code.proj (2 : Fin 3)) _ _ hproj
  rw [FFL.FirstOrder.Arithmetic.pi₁_pair] at h1
  have h2 := eval_codeUnpair₂ (Code.proj (2 : Fin 3)) _ _ hproj
  rw [FFL.FirstOrder.Arithmetic.pi₂_pair] at h2
  have hone :
    Semiformula.Evalb ((1 : M) :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code (codeConst (n := 3) 1)) :=
    by rw [eval_codeConst_iff]; simp
  have h3 := eval_codeSub _ (codeConst 1) (a + 1) 1 _ h2 hone
  rw [add_sub_self] at h3
  exact eval_codePair _ _ z a _ h1 h3


/-!
### The same-index lookup of the successor branch -/

-- The history code contains the whole evaluator-cell code.

/-- **The same-index lookup of the primitive-recursion successor branch.**  With
the input `pair z (a + 1)`, the predecessor lookup of
`eval_codePrecEvaluatorCell_succ_iff_of_succ`, at the dispatcher's decremented
stage and program index and at the input `pair z a`, succeeds with output
`x + 1` exactly when `codeHistoryEvaluator` succeeds at `x + 1, k, q, pair z a`. -/
theorem eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (k z a x : M) (q : ℕ) :
    Semiformula.Evalb
        ((x + 1) :> ![k + 1, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z (a + 1)])
        (code
          (codeTableLookup codeEvaluatorHistoryBeforeCell
            (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
              (codeConst 1))
            (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codePair (codeUnpair₁ (Code.proj (2 : Fin 3)))
              (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1))))) ↔
      Semiformula.Evalb ![x + 1, k, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z a]
        (code codeHistoryEvaluator) :=
  eval_predecessor_lookup_succ_iff_codeHistoryEvaluator k _ _ x q _
    (eval_prec_predecessor_argument (k + 1) ((q : ℕ) : M) z a)

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
