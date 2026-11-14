/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CompositionDispatch
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Certificate

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The tag-4 induction case of certificate persistence

`evalnCertificateFormula_natCode_persist_of_tag_four` concerns a standard index
`q` whose constructor number `partrecCodeTag q` is `4`.  It proves that the raw
evaluator certificate for `q` persists from a stage `s` to every stage `t ≥ s`,
assuming the same persistence for every standard index `p < q`, whatever the
constructor number of `p`.  The persistence predicate is written out in both the
hypothesis and the conclusion.  The theory assumptions are `𝐏𝐀` and `𝐈𝐎𝐩𝐞𝐧`;
the proof obtains `𝐏𝐀⁻` from `𝐏𝐀` with `models_of_subtheory`.

The proof decomposes a successful source cell into certificates for the two
payload subcodes at stage `s`, applies the induction hypothesis once to each,
rebuilds the two table lookups at stage `t` with
`eval_prefix_lookup_succ_of_codeHistoryEvaluator`, and reconstructs the target
cell with `eval_codeEvaluatorCell_succ_of_pair_component_lookups`.  The shared
helpers bound both payloads strictly below `q` and decompose the pairing branch.
The shared decoder readings and dispatcher branch theorem come from
`Evaluator.CompositionDispatch`.  The fuel and the
program index that the cell reads are supplied by the generic public readings
`eval_codeEvaluatorCell_fuel` and `eval_codeEvaluatorCell_index` of
`Evaluator.HistoryEvaluation`.

The file states one induction case.  It proves neither the cases for the other
constructor numbers nor persistence for all standard indices.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.ArithmeticCode

namespace CategoricalRiceShapiro
namespace Evaluator

variable {M : Type*} [ORingStructure M]

/-- Both subcodes of a standard constructor-`4` index lie strictly below it. -/
theorem tagFour_payloads_lt (q : ℕ) (hq : partrecCodeTag q = 4) :
    partrecCodePayload₁ q < q ∧ partrecCodePayload₂ q < q :=
  by
  have h4 : 4 ≤ q := by
    rcases Nat.lt_or_ge q 4 with hlt | hge
    · rw [partrecCodeTag_eq, ite_eq_left hlt] at hq
      omega
    · exact hge
  have hdd : partrecCodePayload q ≤ q - 4 :=
    by
    simp only [partrecCodePayload, Nat.div2_val]
    exact le_trans (Nat.div_le_self ((q - 4) / 2) 2) (Nat.div_le_self (q - 4) 2)
  have h1 : partrecCodePayload₁ q ≤ partrecCodePayload q :=
    Nat.unpair_left_le (partrecCodePayload q)
  have h2 : partrecCodePayload₂ q ≤ partrecCodePayload q :=
    Nat.unpair_right_le (partrecCodePayload q)
  omega

/-!
### Forward decomposition of a source tag-4 cell -/

/-- A successful source cell at a standard constructor-`4` index yields a
history success for each subcode at the same stage, and the Cantor pair of the
two outputs. -/
theorem tagFour_source_subcode_histories [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (q : ℕ) (hq : partrecCodeTag q = 4) (s u y : M) (hs : 0 < s)
    (hcell :
      Semiformula.Evalb ((y + 1) :> ![s, ((q : ℕ) : M), u])
        (code (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))))) :
    ∃ a b : M,
      Semiformula.Evalb ![a + 1, s, ((partrecCodePayload₁ q : ℕ) : M), u]
          (code codeHistoryEvaluator) ∧
        Semiformula.Evalb ![b + 1, s, ((partrecCodePayload₂ q : ℕ) : M), u]
            (code codeHistoryEvaluator) ∧
          y = FFL.FirstOrder.Arithmetic.pair a b :=
  by
  have hk := eval_codeEvaluatorCell_fuel s ((q : ℕ) : M) u
  have hidx := eval_codeEvaluatorCell_index s ((q : ℕ) : M) u
  have htag :
    Semiformula.Evalb (((4 : ℕ) : M) :> ![s, ((q : ℕ) : M), u])
      (code (codePartrecTag (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) :=
    by
    have h := eval_codePartrecTag_natCast _ q ![s, ((q : ℕ) : M), u] hidx
    rwa [hq] at h
  have hbranch :=
    cell_pair_branch codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))
      ![s, ((q : ℕ) : M), u] (y + 1) s (((4 : ℕ) : M)) hk hs htag rfl hcell
  obtain ⟨a, b, hla, hlb, hy⟩ :=
    (eval_codePairEvaluatorCell_succ_iff codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (Code.proj (2 : Fin 3)) y ![s, ((q : ℕ) : M), u]).mp
      hbranch
  have hp1 := eval_codePartrecPayload₁_natCast _ q ![s, ((q : ℕ) : M), u] hidx
  have hp2 := eval_codePartrecPayload₂_natCast _ q ![s, ((q : ℕ) : M), u] hidx
  have hq1 := eval_iff_codeConst_of_eval _ (partrecCodePayload₁ q) ![s, ((q : ℕ) : M), u] hp1
  have hq2 := eval_iff_codeConst_of_eval _ (partrecCodePayload₂ q) ![s, ((q : ℕ) : M), u] hp2
  have hlaC :=
    (eval_codeTableLookup_query_congr codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeConst (n := 3) (partrecCodePayload₁ q)) (Code.proj (2 : Fin 3)) (a + 1)
          ![s, ((q : ℕ) : M), u] hq1).mp
      hla
  have hlbC :=
    (eval_codeTableLookup_congr_at (codeLift codeEvaluatorHistoryBeforeCell)
          (codeLift (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeLift
            (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))))
          (codeLift (Code.proj (2 : Fin 3))) codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst (n := 3) (partrecCodePayload₂ q)) (Code.proj (2 : Fin 3)) (b + 1)
          (a :> ![s, ((q : ℕ) : M), u]) ![s, ((q : ℕ) : M), u]
          (fun z => eval_codeLift_iff _ z a _) (fun z => eval_codeLift_iff _ z a _)
          (fun z => (eval_codeLift_iff _ z a _).trans (hq2 z))
          (fun z => eval_codeLift_iff _ z a _)).mp
      hlb
  have hlt := tagFour_payloads_lt q hq
  have hpre1 :
    FFL.FirstOrder.Arithmetic.pair s ((partrecCodePayload₁ q : ℕ) : M) <
      FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s (by exact_mod_cast hlt.1)
  have hpre2 :
    FFL.FirstOrder.Arithmetic.pair s ((partrecCodePayload₂ q : ℕ) : M) <
      FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s (by exact_mod_cast hlt.2)
  exact
    ⟨a, b,
      eval_codeHistoryEvaluator_succ_of_prefix_lookup s ((q : ℕ) : M) u a
        (partrecCodePayload₁ q) hpre1 hlaC,
      eval_codeHistoryEvaluator_succ_of_prefix_lookup s ((q : ℕ) : M) u b
        (partrecCodePayload₂ q) hpre2 hlbC,
      hy⟩

/-!
### The tag-4 strong-induction case -/

/-- **Tag-4 induction case of certificate persistence.**  For a standard index
`q` of constructor number `4`, persistence of the certificate for `q` from stage
`s` to any later stage `t` follows from persistence for every strictly smaller
standard index, whatever its constructor number.  The persistence predicate is
written out in both the hypothesis and the conclusion. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_four [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (q : ℕ) (hq : partrecCodeTag q = 4)
    (ih :
      ∀ p : ℕ,
        p < q →
          ∀ s t u y : M,
            s ≤ t →
              Semiformula.Evalb ![s, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4) →
                Semiformula.Evalb ![t, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∀ s t u y : M,
      s ≤ t →
        Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- (1) arbitrary stages, argument and output, and a source certificate
  intro s t u y hst source_certificate
  have source_history :=
    (evalnCertificateFormula_eval_history_iff s ((q : ℕ) : M) u y).mp source_certificate
  obtain ⟨hus, source_cell⟩ :=
    (eval_codeHistoryEvaluator_succ_iff_cell s ((q : ℕ) : M) u y).mp source_history
  have hs : (0 : M) < s :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
  have ht : (0 : M) < t := lt_of_lt_of_le hs hst
  obtain ⟨a, b, payload₁_history_at_s, payload₂_history_at_s, hy⟩ :=
    tagFour_source_subcode_histories q hq s u y hs source_cell
  have payload₁_lt : partrecCodePayload₁ q < q := (tagFour_payloads_lt q hq).1
  have payload₂_lt : partrecCodePayload₂ q < q :=
    (tagFour_payloads_lt q hq).2
      -- (7) source payload histories to source payload certificates
  have payload₁_certificate_at_s :=
    (evalnCertificateFormula_eval_history_iff s ((partrecCodePayload₁ q : ℕ) : M) u a).mpr
      payload₁_history_at_s
  have payload₂_certificate_at_s :=
    (evalnCertificateFormula_eval_history_iff s ((partrecCodePayload₂ q : ℕ) : M) u b).mpr
      payload₂_history_at_s
  have payload₁_certificate_at_t :=
    ih (partrecCodePayload₁ q) payload₁_lt s t u a hst payload₁_certificate_at_s
  have payload₂_certificate_at_t :=
    ih (partrecCodePayload₂ q) payload₂_lt s t u b hst payload₂_certificate_at_s
  have payload₁_history_at_t :=
    (evalnCertificateFormula_eval_history_iff t ((partrecCodePayload₁ q : ℕ) : M) u a).mp
      payload₁_certificate_at_t
  have payload₂_history_at_t :=
    (evalnCertificateFormula_eval_history_iff t ((partrecCodePayload₂ q : ℕ) : M) u b).mp
      payload₂_certificate_at_t
  have payload₁_prefix :
    FFL.FirstOrder.Arithmetic.pair t
        ((partrecCodePayload₁ q : ℕ) : M) <
      FFL.FirstOrder.Arithmetic.pair t ((q : ℕ) : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right t
      (by exact_mod_cast payload₁_lt)
  have payload₂_prefix :
    FFL.FirstOrder.Arithmetic.pair t
        ((partrecCodePayload₂ q : ℕ) : M) <
      FFL.FirstOrder.Arithmetic.pair t ((q : ℕ) : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right t
      (by exact_mod_cast payload₂_lt)
        -- (10) target prefix/table lookups through the public converse bridge
  have payload₁_lookup_at_t :=
    eval_prefix_lookup_succ_of_codeHistoryEvaluator t ((q : ℕ) : M) u a (partrecCodePayload₁ q)
      payload₁_prefix payload₁_history_at_t
  have payload₂_lookup_at_t :=
    eval_prefix_lookup_succ_of_codeHistoryEvaluator t ((q : ℕ) : M) u b (partrecCodePayload₂ q)
      payload₂_prefix payload₂_history_at_t
  have target_cell :=
    eval_codeEvaluatorCell_succ_of_pair_component_lookups codeEvaluatorHistoryBeforeCell
      (Code.proj (2 : Fin 3)) q hq a b ![t, ((q : ℕ) : M), u]
      (eval_codeEvaluatorCell_index t ((q : ℕ) : M) u)
      ⟨t, ht, eval_codeEvaluatorCell_fuel t ((q : ℕ) : M) u⟩ payload₁_lookup_at_t
      payload₂_lookup_at_t
  rw [← hy] at target_cell
  have target_history :=
    (eval_codeHistoryEvaluator_succ_iff_cell t ((q : ℕ) : M) u y).mpr
      ⟨lt_of_lt_of_le hus hst, target_cell⟩
        -- (15) target history success to the target certificate
  exact (evalnCertificateFormula_eval_history_iff t ((q : ℕ) : M) u y).mpr target_history

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
