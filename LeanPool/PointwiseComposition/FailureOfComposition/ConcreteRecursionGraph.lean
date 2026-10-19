/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEvaluatorGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Arithmetic graph equations for actual primitive-recursion program indices.
The equations hold over arbitrary PA models, including nonstandard inputs. -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.PartialRecursive

open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace ConcreteEvaluator

variable {M : Type*} [ORingStructure M]

/-- At a positive stage, zero-argument primitive recursion is the base program,
with the caller's argument bound imposed by the concrete evaluator. -/
theorem evaln_tag_six_zero_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 6) (s z y : M) (hs : 0 < s) :
    Semiformula.Evalb
        ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      FFL.FirstOrder.Arithmetic.pair z 0 < s ∧
        Semiformula.Evalb ![s, (partrecCodePayload₁ q : M), z, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- the argument codes of the primitive-recursion branch of the dispatcher, named once
  set dtable : Code 3 := codeEvaluatorHistoryBeforeCell with hdtable
  set dk' : Code 3 :=
    codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)) (codeConst 1) with
    hdk'
  set dq : Code 3 := codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell) with hdq
  set dcf : Code 3 :=
    codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcf
  set dcg : Code 3 :=
    codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcg
  set dn : Code 3 := Code.proj (2 : Fin 3) with hdn
  obtain ⟨Hs, hHs, _⟩ :=
    eval_codeEvaluatorHistoryBeforeCell_exists s (q : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have hidx_s :=
    eval_codeEvaluatorCell_index s (q : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have htag_s := tagSix_read_tag _ q hq _ hidx_s
  have hn_s :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z 0 :>
        ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have source_equivalence :
    Semiformula.Evalb
        ((y + 1) :>
          ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      Semiformula.Evalb
        ((y + 1) :>
          ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeTableLookup dtable (codeSucc dk') dcf (codeUnpair₁ dn))) :=
    eval_codePrecEvaluatorCell_succ_iff_of_zero dtable dk' dq dcf dcg dn Hs (s - 1)
      ((q : ℕ) : M) ((partrecCodePayload₁ q : ℕ) : M) ((partrecCodePayload₂ q : ℕ) : M) z y
      ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0] hHs
      (tagSix_decremented_fuel s ((q : ℕ) : M)
        (FFL.FirstOrder.Arithmetic.pair z 0))
      hidx_s (tagSix_read_payload₁ _ q hq _ hidx_s) (tagSix_read_payload₂ _ q hq _ hidx_s) hn_s
  have lookup_equivalence :
    Semiformula.Evalb
        ((y + 1) :>
          ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeTableLookup dtable (codeSucc dk') dcf (codeUnpair₁ dn))) ↔
      Semiformula.Evalb ((y + 1) :> ![s, (q : M), z])
        (code
          (codeTableLookup codeEvaluatorHistoryBeforeCell
            (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst (n := 3) (partrecCodePayload₁ q)) (Code.proj (2 : Fin 3)))) :=
    eval_codeTableLookup_congr_at _ _ _ _ _ _ _ _ _ _ _
      (tagSix_table_congr s (q : M)
        (FFL.FirstOrder.Arithmetic.pair z 0) z)
      (tagSix_key_congr s (q : M)
        (FFL.FirstOrder.Arithmetic.pair z 0) z hs)
      (tagSix_query_congr s (FFL.FirstOrder.Arithmetic.pair z 0) z
        q hq)
      (tagSix_argument_congr s (q : M) z)
  have payload₁_lt : partrecCodePayload₁ q < q := (partrecCodePayloads_lt_of_tag_six q hq).1
  have prefix_s :
    FFL.FirstOrder.Arithmetic.pair s (partrecCodePayload₁ q : M) <
      FFL.FirstOrder.Arithmetic.pair s (q : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast payload₁_lt)
  constructor
  · intro hc
    have hh :=
      (evalnCertificateFormula_eval_history_iff s (q : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
        hc
    obtain ⟨hu, hcell⟩ :=
      (eval_codeHistoryEvaluator_succ_iff_cell s (q : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
        hh
    have hb :=
      tagSix_prec_branch _ _ _ (y + 1) s
        (eval_codeEvaluatorCell_fuel s (q : M)
          (FFL.FirstOrder.Arithmetic.pair z 0))
        hs htag_s hcell
    have hl := lookup_equivalence.mp (source_equivalence.mp hb)
    have hf :=
      eval_codeHistoryEvaluator_succ_of_prefix_lookup s (q : M) z y (partrecCodePayload₁ q)
        prefix_s hl
    exact
      ⟨hu, (evalnCertificateFormula_eval_history_iff s (partrecCodePayload₁ q : M) z y).mpr hf⟩
  · rintro ⟨hu, hc⟩
    have hf :=
      (evalnCertificateFormula_eval_history_iff s (partrecCodePayload₁ q : M) z y).mp hc
    have hl :=
      eval_prefix_lookup_succ_of_codeHistoryEvaluator s (q : M) z y (partrecCodePayload₁ q)
        prefix_s hf
    have hb := source_equivalence.mpr (lookup_equivalence.mpr hl)
    obtain ⟨w, hw⟩ :=
      eval_codeEvaluatorCell_exists_of_values dtable dn Hs
        (FFL.FirstOrder.Arithmetic.pair z 0)
        ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0] hHs hn_s
    have hbw :=
      tagSix_prec_branch _ _ _ w s
        (eval_codeEvaluatorCell_fuel s (q : M)
          (FFL.FirstOrder.Arithmetic.pair z 0))
        hs htag_s hw
    have hwy : w = y + 1 := eval_unique hbw hb
    rw [hwy] at hw
    exact
      (evalnCertificateFormula_eval_history_iff s (q : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) y).mpr
        ((eval_codeHistoryEvaluator_succ_iff_cell s (q : M)
              (FFL.FirstOrder.Arithmetic.pair z 0) y).mpr
          ⟨hu, hw⟩)

/-- A successor recursion computation at stage `k + 1` consists of the
predecessor computation at stage `k` and the step computation at stage `k + 1`. -/
theorem evaln_tag_six_succ_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 6) (k z a y : M) :
    Semiformula.Evalb
        ![k + 1, (q : M),
          FFL.FirstOrder.Arithmetic.pair z (a + 1), y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      FFL.FirstOrder.Arithmetic.pair z (a + 1) < k + 1 ∧
        ∃ x : M,
          Semiformula.Evalb
              ![k, (q : M), FFL.FirstOrder.Arithmetic.pair z a, x]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
            Semiformula.Evalb
              ![k + 1, (partrecCodePayload₂ q : M),
                FFL.FirstOrder.Arithmetic.pair z
                  (FFL.FirstOrder.Arithmetic.pair a x),
                y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- the argument codes of the primitive-recursion branch, named once
  set dtable : Code 3 := codeEvaluatorHistoryBeforeCell with hdtable
  set dk' : Code 3 :=
    codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)) (codeConst 1) with
    hdk'
  set dq : Code 3 := codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell) with hdq
  set dcf : Code 3 :=
    codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcf
  set dcg : Code 3 :=
    codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcg
  set dn : Code 3 := Code.proj (2 : Fin 3) with hdn
  set u : M := FFL.FirstOrder.Arithmetic.pair z (a + 1) with hu
  have hs : (0 : M) < k + 1 :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le k)
      (lt_add_one k)
        -- readings at the source stage
  obtain ⟨Hs, hHs, hHistS⟩ := eval_codeEvaluatorHistoryBeforeCell_exists (k + 1) ((q : ℕ) : M) u
  have hidx_s := eval_codeEvaluatorCell_index (k + 1) ((q : ℕ) : M) u
  have htag_s := tagSix_read_tag _ q hq _ hidx_s
  have hn_s : Semiformula.Evalb (u :> ![k + 1, ((q : ℕ) : M), u]) (code dn) :=
    (eval_proj_iff _ _ _).mpr rfl
  have source_equivalence :
    Semiformula.Evalb ((y + 1) :> ![k + 1, ((q : ℕ) : M), u])
        (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      ∃ x : M,
        Semiformula.Evalb ((x + 1) :> ![k + 1, ((q : ℕ) : M), u])
            (code
              (codeTableLookup dtable dk' dq
                (codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1))))) ∧
          Semiformula.Evalb ((y + 1) :> x :> ![k + 1, ((q : ℕ) : M), u])
            (code
              (codeTableLookup (codeLift dtable) (codeLift (codeSucc dk')) (codeLift dcg)
                (codePair (codeLift (codeUnpair₁ dn))
                  (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1)))
                    (codeHead (n := 3)))))) :=
    eval_codePrecEvaluatorCell_succ_iff_of_succ dtable dk' dq dcf dcg dn Hs (k + 1 - 1)
      ((q : ℕ) : M) ((partrecCodePayload₁ q : ℕ) : M) ((partrecCodePayload₂ q : ℕ) : M) z a y
      ![k + 1, ((q : ℕ) : M), u] hHs (tagSix_decremented_fuel (k + 1) ((q : ℕ) : M) u) hidx_s
      (tagSix_read_payload₁ _ q hq _ hidx_s) (tagSix_read_payload₂ _ q hq _ hidx_s) hn_s
  have hpayload₂_lt : partrecCodePayload₂ q < q := (partrecCodePayloads_lt_of_tag_six q hq).2
  have hrow_step :
    ∀ s : M,
      FFL.FirstOrder.Arithmetic.pair s
          ((partrecCodePayload₂ q : ℕ) : M) <
        FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    fun s =>
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast hpayload₂_lt)
  have hstep_bridge (x : M) :
    ∀ s : M,
      (0 : M) < s →
        ∀ H : M,
          Semiformula.Evalb (H :> ![s, ((q : ℕ) : M), u]) (code dtable) →
            Semiformula.Evalb
                ![H,
                  FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M)]
                (code codeEvaluatorHistory) →
              (Semiformula.Evalb ((y + 1) :> x :> ![s, ((q : ℕ) : M), u])
                  (code
                    (codeTableLookup (codeLift dtable) (codeLift (codeSucc dk')) (codeLift dcg)
                      (codePair (codeLift (codeUnpair₁ dn))
                        (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1)))
                          (codeHead (n := 3)))))) ↔
                Semiformula.Evalb
                  ![y + 1, s, ((partrecCodePayload₂ q : ℕ) : M),
                    FFL.FirstOrder.Arithmetic.pair z
                      (FFL.FirstOrder.Arithmetic.pair a x)]
                  (code codeHistoryEvaluator)) :=
    by
    intro s hspos H hH hHist
    exact
      eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history (codeLift dtable)
        (codeLift (codeSucc dk')) (codeLift dcg) _ (x :> ![s, ((q : ℕ) : M), u])
        (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M)) H s
        (FFL.FirstOrder.Arithmetic.pair z
          (FFL.FirstOrder.Arithmetic.pair a x))
        y (partrecCodePayload₂ q) hHist (hrow_step s) ((eval_codeLift_iff _ _ _ _).mpr hH)
        ((eval_codeLift_iff _ _ _ _).mpr (tagSix_base_key s ((q : ℕ) : M) u hspos))
        ((eval_codeLift_iff _ _ _ _).mpr
          (tagSix_read_payload₂ _ q hq _ (eval_codeEvaluatorCell_index s ((q : ℕ) : M) u)))
        (tagSix_step_argument s ((q : ℕ) : M) z a x)
  constructor
  · intro hc
    have hh := (evalnCertificateFormula_eval_history_iff (k + 1) (q : M) u y).mp hc
    obtain ⟨hu, hcell⟩ := (eval_codeHistoryEvaluator_succ_iff_cell (k + 1) (q : M) u y).mp hh
    have hb :=
      tagSix_prec_branch _ _ _ (y + 1) (k + 1) (eval_codeEvaluatorCell_fuel (k + 1) (q : M) u)
        hs htag_s hcell
    obtain ⟨x, hp, hg⟩ := source_equivalence.mp hb
    have hph := (eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator k z a x q).mp hp
    have hgh := (hstep_bridge x (k + 1) hs Hs hHs hHistS).mp hg
    exact
      ⟨hu, x,
        (evalnCertificateFormula_eval_history_iff k (q : M)
              (FFL.FirstOrder.Arithmetic.pair z a) x).mpr
          hph,
        (evalnCertificateFormula_eval_history_iff (k + 1) (partrecCodePayload₂ q : M)
              (FFL.FirstOrder.Arithmetic.pair z
                (FFL.FirstOrder.Arithmetic.pair a x))
              y).mpr
          hgh⟩
  · rintro ⟨hu, x, hp, hg⟩
    have hph :=
      (evalnCertificateFormula_eval_history_iff k (q : M)
            (FFL.FirstOrder.Arithmetic.pair z a) x).mp
        hp
    have hgh :=
      (evalnCertificateFormula_eval_history_iff (k + 1) (partrecCodePayload₂ q : M)
            (FFL.FirstOrder.Arithmetic.pair z
              (FFL.FirstOrder.Arithmetic.pair a x))
            y).mp
        hg
    have hpl := (eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator k z a x q).mpr hph
    have hgl := (hstep_bridge x (k + 1) hs Hs hHs hHistS).mpr hgh
    have hb := source_equivalence.mpr ⟨x, hpl, hgl⟩
    obtain ⟨w, hw⟩ :=
      eval_codeEvaluatorCell_exists_of_values dtable dn Hs u ![k + 1, (q : M), u] hHs hn_s
    have hbw :=
      tagSix_prec_branch _ _ _ w (k + 1) (eval_codeEvaluatorCell_fuel (k + 1) (q : M) u) hs
        htag_s hw
    have hwy : w = y + 1 := eval_unique hbw hb
    rw [hwy] at hw
    exact
      (evalnCertificateFormula_eval_history_iff (k + 1) (q : M) u y).mpr
        ((eval_codeHistoryEvaluator_succ_iff_cell (k + 1) (q : M) u y).mpr ⟨hu, hw⟩)

/-- Primitive recursion at zero realizes the base graph in every PA model. -/
theorem eventualGraph_prec_zero_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (fCode gCode : ℕ)
    (z y : M) :
    (eventualGraph (canonicalPartrecPrecIndex fCode gCode)).val.Evalb
        ![FFL.FirstOrder.Arithmetic.pair z 0, y] ↔
      (eventualGraph fCode).val.Evalb ![z, y] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  let q := canonicalPartrecPrecIndex fCode gCode
  have hq : partrecCodeTag q = 6 := canonicalPartrecPrecIndex_constructor_number fCode gCode
  have hf : partrecCodePayload₁ q = fCode := canonicalPartrecPrecIndex_base_index fCode gCode
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    have hu :=
      ((eval_codeHistoryEvaluator_succ_iff_cell s (q : M) (FFL.FirstOrder.Arithmetic.pair z 0)
              y).mp
          ((evalnCertificateFormula_eval_history_iff s (q : M)
                (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
            hs)).1
    have hpos : (0 : M) < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) hu
    have hc := ((evaln_tag_six_zero_iff q hq s z y hpos).mp hs).2
    rw [hf] at hc
    exact
      (eventualGraph_eval fCode _).mpr
        ⟨s, by
          simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
            hc⟩
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval fCode _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    let t := s + FFL.FirstOrder.Arithmetic.pair z 0 + 1
    have hst : s ≤ t := le_trans le_self_add (le_of_lt (lt_add_one _))
    have hu : FFL.FirstOrder.Arithmetic.pair z 0 < t :=
      lt_of_le_of_lt le_add_self (lt_add_one _)
    have hpos : (0 : M) < t := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) hu
    have hc := evalnCertificateFormula_natCode_persist fCode s t z y hst hs
    rw [← hf] at hc
    have hr := (evaln_tag_six_zero_iff q hq t z y hpos).mpr ⟨hu, hc⟩
    exact
      (eventualGraph_eval q _).mpr
        ⟨t, by
          simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
            hr⟩

/-- Primitive recursion at a successor realizes the predecessor-then-step
graph in every PA model. The recursion argument may be nonstandard. -/
theorem eventualGraph_prec_succ_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (fCode gCode : ℕ)
    (z a y : M) :
    (eventualGraph (canonicalPartrecPrecIndex fCode gCode)).val.Evalb
        ![FFL.FirstOrder.Arithmetic.pair z (a + 1), y] ↔
      ∃ x : M,
        (eventualGraph (canonicalPartrecPrecIndex fCode gCode)).val.Evalb
            ![FFL.FirstOrder.Arithmetic.pair z a, x] ∧
          (eventualGraph gCode).val.Evalb
            ![FFL.FirstOrder.Arithmetic.pair z (FFL.FirstOrder.Arithmetic.pair a x), y] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  let q := canonicalPartrecPrecIndex fCode gCode
  have hq : partrecCodeTag q = 6 := canonicalPartrecPrecIndex_constructor_number fCode gCode
  have hg : partrecCodePayload₂ q = gCode := canonicalPartrecPrecIndex_step_index fCode gCode
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    have hu :=
      ((eval_codeHistoryEvaluator_succ_iff_cell s (q : M)
              (FFL.FirstOrder.Arithmetic.pair z (a + 1)) y).mp
          ((evalnCertificateFormula_eval_history_iff s (q : M)
                (FFL.FirstOrder.Arithmetic.pair z (a + 1)) y).mp
            hs)).1
    have hpos : (0 : M) < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) hu
    have hpred : s - 1 + 1 = s := tagSix_succ_pred hpos
    have hh := evaln_tag_six_succ_iff q hq (s - 1) z a y
    rw [hpred] at hh
    obtain ⟨_, x, hp, hf⟩ := hh.mp hs
    rw [hg] at hf
    exact
      ⟨x,
        (eventualGraph_eval q _).mpr
          ⟨s - 1, by
            simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
              hp⟩,
        (eventualGraph_eval gCode _).mpr
          ⟨s, by
            simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
              hf⟩⟩
  · rintro ⟨x, hp, hf⟩
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp hp
    obtain ⟨t, ht⟩ := (eventualGraph_eval gCode _).mp hf
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
    let k := s + t + FFL.FirstOrder.Arithmetic.pair z (a + 1)
    have hsk : s ≤ k := le_trans le_self_add le_self_add
    have htk : t ≤ k + 1 :=
      le_trans (le_trans le_add_self le_self_add) (le_of_lt (lt_add_one _))
    have hu : FFL.FirstOrder.Arithmetic.pair z (a + 1) < k + 1 :=
      lt_of_le_of_lt le_add_self (lt_add_one _)
    have hs' :=
      evalnCertificateFormula_natCode_persist q s k (FFL.FirstOrder.Arithmetic.pair z a) x hsk
        hs
    have ht' :=
      evalnCertificateFormula_natCode_persist gCode t (k + 1)
        (FFL.FirstOrder.Arithmetic.pair z (FFL.FirstOrder.Arithmetic.pair a x)) y htk ht
    rw [← hg] at ht'
    have hr := (evaln_tag_six_succ_iff q hq k z a y).mpr ⟨hu, x, hs', ht'⟩
    exact
      (eventualGraph_eval q _).mpr
        ⟨k + 1, by
          simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
            hr⟩

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
