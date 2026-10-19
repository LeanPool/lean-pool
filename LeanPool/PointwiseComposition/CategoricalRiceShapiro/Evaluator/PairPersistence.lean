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
cell with `eval_codeEvaluatorCell_succ_of_pair_component_lookups`.  The private
helpers relate `partrecCodeTag` to its remainder form, bound both payloads
strictly below `q`, and read the decoders inside a model.  The fuel and the
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

/-!
### Decoder bridge and ranking, over `ℕ` -/

/-- Production's tag decoder, written with remainders.  `bodd.toNat` and `% 2`
are related by `Nat.mod_two_of_bodd`, not assumed definitionally equal. -/
private theorem tagFour_tag_remainders (q : ℕ) :
    partrecCodeTag q = if q < 4 then q else 4 + 2 * ((q - 4) % 2) + Nat.div2 (q - 4) % 2 :=
  by
  have hb : ∀ n : ℕ, n.bodd.toNat = n % 2 := fun n => by rw [Nat.mod_two_of_bodd]
  simp only [partrecCodeTag, hb]

/-- Both subcodes of a standard constructor-`4` index lie strictly below it. -/
private theorem tagFour_payloads_lt (q : ℕ) (hq : partrecCodeTag q = 4) :
    partrecCodePayload₁ q < q ∧ partrecCodePayload₂ q < q :=
  by
  have h4 : 4 ≤ q := by
    rcases Nat.lt_or_ge q 4 with hlt | hge
    · rw [tagFour_tag_remainders, ite_eq_left hlt] at hq
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
### Decoder readings inside a model -/

/-- The constructor number of a standard index, read inside a model. -/
private theorem tagFour_read_tag [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
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
  rw [tagFour_tag_remainders]
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

/-- The payload of a standard index, read inside a model. -/
private theorem tagFour_read_payload [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload q : ℕ) : M) :> v) (code (codePartrecPayload d)) :=
  by
  have h4 : Semiformula.Evalb (((4 : ℕ) : M) :> v) (code (codeConst (n := r) 4)) :=
    eval_codeConst 4 v
  have hrr := eval_codeSub_natCast d (codeConst 4) q 4 v hd (by simpa using h4)
  simpa only [codePartrecPayload, partrecCodePayload] using
    eval_codeDiv2_natCast _ _ v (eval_codeDiv2_natCast _ (q - 4) v hrr)

/-- The first subcode of a standard index, read inside a model. -/
private theorem tagFour_read_payload₁ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₁ q : ℕ) : M) :> v) (code (codePartrecPayload₁ d)) :=
  eval_codeUnpair₁_natCast (codePartrecPayload d) _ v (tagFour_read_payload d q v hd)

/-- The second subcode of a standard index, read inside a model. -/
private theorem tagFour_read_payload₂ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₂ q : ℕ) : M) :> v) (code (codePartrecPayload₂ d)) :=
  eval_codeUnpair₂_natCast (codePartrecPayload d) _ v (tagFour_read_payload d q v hd)

/-!
### The pairing branch of the dispatcher -/

/-- A successful evaluator cell whose constructor number is `4` is the value of
its pairing branch. -/
private theorem tagFour_pair_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r)
    (v : Fin r → M) (z k tag : M)
    (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
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
  have hval :
    ∀ (m : ℕ) (x : M),
      Semiformula.Evalb (x :> v) (code (codeConst (n := r) m)) → x = ((m : ℕ) : M) :=
    fun m x hx => eval_unique hx (eval_codeConst m v)
  simp only [codeEvaluatorCell] at hcell
  obtain ⟨f0, hf0, hc0⟩ := eval_codeIfPos_cases _ _ _ z v hcell
  have hf0k : f0 = k := eval_unique hf0 hk
  rcases hc0 with ⟨-, hbig⟩ | ⟨h0, -⟩
  swap
  · exact absurd (hf0k ▸ h0 : k = 0) (ne_of_gt hkpos)
  obtain ⟨e4, he4, hcase4⟩ := eval_codeIfPos_cases _ _ _ z v hbig
  rw [eval_codeEq_iff] at he4
  obtain ⟨x, w, hx, hw, hxw⟩ := he4
  have hxt : x = tag := eval_unique hx htag
  have hw4 : w = ((4 : ℕ) : M) := hval 4 w hw
  have he41 : e4 = 1 := by
    rcases hxw with ⟨-, h1⟩ | ⟨hne, -⟩
    · exact h1
    · exact absurd (by rw [hxt, hw4]; exact h4) hne
  rcases hcase4 with ⟨-, hpair⟩ | ⟨h0, -⟩
  · exact hpair
  · exact absurd (he41 ▸ h0 : (1 : M) = 0) _root_.one_ne_zero

/-!
### Forward decomposition of a source tag-4 cell -/

/-- A successful source cell at a standard constructor-`4` index yields a
history success for each subcode at the same stage, and the Cantor pair of the
two outputs. -/
private theorem tagFour_source_subcode_histories [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
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
    have h := tagFour_read_tag _ q ![s, ((q : ℕ) : M), u] hidx
    rwa [hq] at h
  have hbranch :=
    tagFour_pair_branch codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))
      ![s, ((q : ℕ) : M), u] (y + 1) s (((4 : ℕ) : M)) hk hs htag rfl hcell
  obtain ⟨a, b, hla, hlb, hy⟩ :=
    (eval_codePairEvaluatorCell_succ_iff codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (Code.proj (2 : Fin 3)) y ![s, ((q : ℕ) : M), u]).mp
      hbranch
  have hp1 := tagFour_read_payload₁ _ q ![s, ((q : ℕ) : M), u] hidx
  have hp2 := tagFour_read_payload₂ _ q ![s, ((q : ℕ) : M), u] hidx
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
