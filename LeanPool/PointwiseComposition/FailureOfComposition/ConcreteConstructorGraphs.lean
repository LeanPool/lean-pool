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
Constructor equations for the concrete evaluator over arbitrary models of PA.
Shared decoder and forward pairing helpers come from production
PairPersistence; the public results remove fuel and synchronize component
computations using unconditional persistence.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteEvaluator

variable {M : Type*} [ORingStructure M]

/-- At a common stage, pairing computes the pair of its component outputs. -/
theorem evalnCertificateFormula_tag_four_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 4) (s u y : M) :
    Semiformula.Evalb ![s, (q : M), u, y] (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      ∃ a b : M,
        Semiformula.Evalb ![s, (partrecCodePayload₁ q : M), u, a]
            (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          Semiformula.Evalb ![s, (partrecCodePayload₂ q : M), u, b]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
            y = FFL.FirstOrder.Arithmetic.pair a b :=
  by
  constructor
  · intro h
    have hh := (evalnCertificateFormula_eval_history_iff s (q : M) u y).mp h
    obtain ⟨hus, hcell⟩ := (eval_codeHistoryEvaluator_succ_iff_cell s (q : M) u y).mp hh
    have hs : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
    obtain ⟨a, b, ha, hb, hy⟩ := tagFour_source_subcode_histories q hq s u y hs hcell
    exact
      ⟨a, b, (evalnCertificateFormula_eval_history_iff _ _ _ _).mpr ha,
        (evalnCertificateFormula_eval_history_iff _ _ _ _).mpr hb, hy⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    have ha' :=
      (evalnCertificateFormula_eval_history_iff s (partrecCodePayload₁ q : M) u a).mp ha
    have hb' :=
      (evalnCertificateFormula_eval_history_iff s (partrecCodePayload₂ q : M) u b).mp hb
    have hus :=
      ((eval_codeHistoryEvaluator_succ_iff_cell s (partrecCodePayload₁ q : M) u a).mp ha').1
    have hs : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
    have hlt := tagFour_payloads_lt q hq
    have hp₁ :
      FFL.FirstOrder.Arithmetic.pair s (partrecCodePayload₁ q : M) <
        FFL.FirstOrder.Arithmetic.pair s (q : M) :=
      FFL.FirstOrder.Arithmetic.pair_lt_pair_right s (by exact_mod_cast hlt.1)
    have hp₂ :
      FFL.FirstOrder.Arithmetic.pair s (partrecCodePayload₂ q : M) <
        FFL.FirstOrder.Arithmetic.pair s (q : M) :=
      FFL.FirstOrder.Arithmetic.pair_lt_pair_right s (by exact_mod_cast hlt.2)
    have hl₁ := eval_prefix_lookup_succ_of_codeHistoryEvaluator s (q : M) u a _ hp₁ ha'
    have hl₂ := eval_prefix_lookup_succ_of_codeHistoryEvaluator s (q : M) u b _ hp₂ hb'
    have hc :=
      eval_codeEvaluatorCell_succ_of_pair_component_lookups codeEvaluatorHistoryBeforeCell
        (Code.proj (2 : Fin 3)) q hq a b ![s, (q : M), u]
        (eval_codeEvaluatorCell_index s (q : M) u)
        ⟨s, hs, eval_codeEvaluatorCell_fuel s (q : M) u⟩ hl₁ hl₂
    exact
      (evalnCertificateFormula_eval_history_iff _ _ _ _).mpr
        ((eval_codeHistoryEvaluator_succ_iff_cell _ _ _ _).mpr ⟨hus, hc⟩)

/-- Mathlib's pairing constructor, in its fixed natural-number encoding. -/
def canonicalPartrecPairIndex (fCode gCode : ℕ) : ℕ :=
  Encodable.encode
    (Nat.Partrec.Code.pair (Denumerable.ofNat Nat.Partrec.Code fCode)
      (Denumerable.ofNat Nat.Partrec.Code gCode))

theorem canonicalPartrecPairIndex_eq (f g : ℕ) :
    canonicalPartrecPairIndex f g = 4 * Nat.pair f g + 4 :=
  by
  unfold canonicalPartrecPairIndex
  rw [Nat.Partrec.Code.encodeCode_eq]
  simp only [Nat.Partrec.Code.encodeCode, ← Nat.Partrec.Code.encodeCode_eq,
    Denumerable.encode_ofNat]
  omega

theorem canonicalPartrecPairIndex_tag (f g : ℕ) :
    partrecCodeTag (canonicalPartrecPairIndex f g) = 4 :=
  by
  have hb : ∀ n : ℕ, n.bodd.toNat = n % 2 := fun n => by rw [Nat.mod_two_of_bodd]
  rw [canonicalPartrecPairIndex_eq]
  simp only [partrecCodeTag, hb, Nat.div2_val]
  split_ifs <;> omega

theorem canonicalPartrecPairIndex_payload (f g : ℕ) :
    partrecCodePayload (canonicalPartrecPairIndex f g) = Nat.pair f g :=
  by
  rw [canonicalPartrecPairIndex_eq]
  simp only [partrecCodePayload, Nat.div2_val]
  omega

theorem canonicalPartrecPairIndex_left (f g : ℕ) :
    partrecCodePayload₁ (canonicalPartrecPairIndex f g) = f := by
  simp only [partrecCodePayload₁, canonicalPartrecPairIndex_payload, Nat.unpair_pair]

theorem canonicalPartrecPairIndex_right (f g : ℕ) :
    partrecCodePayload₂ (canonicalPartrecPairIndex f g) = g := by
  simp only [partrecCodePayload₂, canonicalPartrecPairIndex_payload, Nat.unpair_pair]

/-- Pairing equation with component stages synchronized internally in PA. -/
theorem eventualGraph_pair_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (f g : ℕ) (u y : M) :
    (eventualGraph (canonicalPartrecPairIndex f g)).val.Evalb ![u, y] ↔
      ∃ a b : M,
        (eventualGraph f).val.Evalb ![u, a] ∧
          (eventualGraph g).val.Evalb ![u, b] ∧ y = FFL.FirstOrder.Arithmetic.pair a b :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval _ _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    obtain ⟨a, b, ha, hb, hy⟩ :=
      (evalnCertificateFormula_tag_four_iff (canonicalPartrecPairIndex f g)
            (canonicalPartrecPairIndex_tag f g) s u y).mp
        hs
    rw [canonicalPartrecPairIndex_left] at ha
    rw [canonicalPartrecPairIndex_right] at hb
    refine
      ⟨a, b, (eventualGraph_eval _ _).mpr ⟨s, ?_⟩, (eventualGraph_eval _ _).mpr ⟨s, ?_⟩, hy⟩
    · simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using ha
    · simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using hb
  · rintro ⟨a, b, ha, hb, hy⟩
    obtain ⟨s, hs⟩ := (eventualGraph_eval _ _).mp ha
    obtain ⟨t, ht⟩ := (eventualGraph_eval _ _).mp hb
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
    have hs' := evalnCertificateFormula_natCode_persist f s (s + t) u a le_self_add hs
    have ht' := evalnCertificateFormula_natCode_persist g t (s + t) u b le_add_self ht
    apply (eventualGraph_eval _ _).mpr
    refine ⟨s + t, ?_⟩
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply (evalnCertificateFormula_tag_four_iff _ (canonicalPartrecPairIndex_tag f g) _ _ _).mpr
    simpa only [canonicalPartrecPairIndex_left, canonicalPartrecPairIndex_right] using
      (show
        ∃ a b : M,
          Semiformula.Evalb ![s + t, (f : M), u, a]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
            Semiformula.Evalb ![s + t, (g : M), u, b]
                (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
              y = FFL.FirstOrder.Arithmetic.pair a b
        from ⟨a, b, hs', ht', hy⟩)

/-- The natural encoding of a pair constructor is the canonical pairing index. -/
theorem encode_pair_eq (f g : Nat.Partrec.Code) :
    Encodable.encode (Nat.Partrec.Code.pair f g) =
      canonicalPartrecPairIndex (Encodable.encode f) (Encodable.encode g) :=
  by simp only [canonicalPartrecPairIndex, Denumerable.ofNat_encode]

/-- Same-stage pairing equation in terms of the actual syntax constructors. -/
theorem evalnCertificateFormula_pair_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (f g : Nat.Partrec.Code) (s u y : M) :
    Semiformula.Evalb ![s, (Encodable.encode (Nat.Partrec.Code.pair f g) : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      ∃ a b : M,
        Semiformula.Evalb ![s, (Encodable.encode f : M), u, a]
            (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          Semiformula.Evalb ![s, (Encodable.encode g : M), u, b]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
            y = FFL.FirstOrder.Arithmetic.pair a b :=
  by
  rw [encode_pair_eq]
  simpa only [canonicalPartrecPairIndex_left, canonicalPartrecPairIndex_right] using
    evalnCertificateFormula_tag_four_iff
      (canonicalPartrecPairIndex (Encodable.encode f) (Encodable.encode g))
      (canonicalPartrecPairIndex_tag _ _) s u y

/-- Eventual pairing equation for Mathlib's actual syntax constructors. -/
theorem eventualGraph_pair_code_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (f g : Nat.Partrec.Code)
    (u y : M) :
    (eventualGraph (Encodable.encode (Nat.Partrec.Code.pair f g))).val.Evalb ![u, y] ↔
      ∃ a b : M,
        (eventualGraph (Encodable.encode f)).val.Evalb ![u, a] ∧
          (eventualGraph (Encodable.encode g)).val.Evalb ![u, b] ∧
            y = FFL.FirstOrder.Arithmetic.pair a b :=
  by
  rw [encode_pair_eq]
  exact eventualGraph_pair_eval _ _ _ _

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
