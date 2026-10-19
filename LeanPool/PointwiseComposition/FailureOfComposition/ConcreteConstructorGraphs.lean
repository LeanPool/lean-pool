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
The local decoder and forward pairing helpers are reproduced from production
PairPersistence; the new public results remove fuel and synchronize component
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
