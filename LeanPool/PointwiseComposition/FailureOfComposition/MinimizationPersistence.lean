/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.PersistenceInduction

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Persistence for constructor 7 of the existing Mathlib-index history evaluator.
The subsidiary-index premise is discharged by the external induction on indices;
the same-index recursive lookup is handled by PA induction on the source stage.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

open CategoricalRiceShapiro.ArithmeticCode

open CategoricalRiceShapiro.PartialRecursive

namespace CategoricalRiceShapiro
namespace Evaluator

variable {M : Type*} [ORingStructure M]

private theorem bodd_toNat_eq_mod_two (n : ℕ) : n.bodd.toNat = n % 2 := by
  rw [Nat.mod_two_of_bodd]

/-- The production tag decoder, written with remainders. -/
private theorem partrecCodeTag_eq (q : ℕ) :
    partrecCodeTag q = if q < 4 then q else 4 + 2 * ((q - 4) % 2) + Nat.div2 (q - 4) % 2 := by
  simp only [partrecCodeTag, bodd_toNat_eq_mod_two]

/-- The constructor number of a standard index, read inside a model. -/
private theorem read_tag [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ) (v : Fin r → M)
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
private theorem read_payload [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload q : ℕ) : M) :> v) (code (codePartrecPayload d)) :=
  by
  have h4 : Semiformula.Evalb (((4 : ℕ) : M) :> v) (code (codeConst (n := r) 4)) :=
    eval_codeConst 4 v
  have hrr := eval_codeSub_natCast d (codeConst 4) q 4 v hd (by simpa using h4)
  simpa only [codePartrecPayload, partrecCodePayload] using
    eval_codeDiv2_natCast _ _ v (eval_codeDiv2_natCast _ (q - 4) v hrr)

private theorem min_succ_pred [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : M} (hk : 0 < k) : k - 1 + 1 = k :=
  FFL.FirstOrder.Arithmetic.sub_add_self_of_le
    (FFL.FirstOrder.Arithmetic.one_le_of_zero_lt k hk)

/-- The decremented fuel, as the dispatcher computes it. -/
private theorem min_decremented_fuel [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u : M) :
    Semiformula.Evalb ((s - 1) :> ![s, qCode, u])
      (code
        (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst 1))) :=
  by
  have hone : Semiformula.Evalb ((1 : M) :> ![s, qCode, u]) (code (codeConst (n := 3) 1)) :=
    by
    have h := eval_codeConst (M := M) (k := 3) 1 ![s, qCode, u]
    have hcast : (((1 : ℕ)) : M) = (1 : M) := by simp
    rwa [hcast] at h
  exact
    eval_codeSub _ (codeConst 1) s (1 : M) ![s, qCode, u]
      (eval_codeEvaluatorCell_fuel s qCode u) hone

/-- The key of the base lookup is the fuel. -/
private theorem min_base_key [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (s qCode u : M)
    (hs : 0 < s) :
    Semiformula.Evalb (s :> ![s, qCode, u])
      (code
        (codeSucc
          (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst 1)))) :=
  by
  refine (eval_codeSucc_iff _ _ _).mpr ⟨s - 1, min_decremented_fuel s qCode u, ?_⟩
  exact (min_succ_pred hs).symm

private theorem ifpos_select [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (df dg dh : Code r) (v : Fin r → M)
    (z a : M) (ha : Semiformula.Evalb (a :> v) (code df))
    (hz : Semiformula.Evalb (z :> v) (code (codeIfPos df dg dh))) :
    (0 < a → Semiformula.Evalb (z :> v) (code dg)) ∧
      (a = 0 → Semiformula.Evalb (z :> v) (code dh)) :=
  by
  obtain ⟨b, hb, hcase⟩ := eval_codeIfPos_cases df dg dh z v hz
  have hba := eval_unique hb ha
  subst b
  rcases hcase with ⟨hp, hg⟩ | ⟨h0, hh⟩
  · exact ⟨fun _ => hg, fun h0 => False.elim ((ne_of_gt hp) h0)⟩
  · exact ⟨fun hp => False.elim ((ne_of_gt hp) h0), fun _ => hh⟩

private theorem min_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r) (v : Fin r → M)
    (z k : M) (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hkpos : 0 < k)
    (htag :
      Semiformula.Evalb ((7 : M) :> v)
        (code (codePartrecTag (codeUnpair₂ (codeListLength dtable)))))
    (hcell : Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn))) :
    Semiformula.Evalb (z :> v)
      (code
        (codeRfindEvaluatorCell dtable
          (codeSub (codeUnpair₁ (codeListLength dtable)) (codeConst 1))
          (codeUnpair₂ (codeListLength dtable))
          (codePartrecPayload (codeUnpair₂ (codeListLength dtable))) dn)) :=
  by
  have heq (n : ℕ) (hn : (7 : M) ≠ (n : M)) :
    Semiformula.Evalb ((0 : M) :> v)
      (code (codeEq (codePartrecTag (codeUnpair₂ (codeListLength dtable))) (codeConst n))) :=
    (eval_codeEq_iff _ _ _ v).mpr ⟨7, n, htag, eval_codeConst n v, Or.inr ⟨hn, rfl⟩⟩
  have h4 := heq 4 (by norm_num)
  have h5 := heq 5 (by norm_num)
  have h6 := heq 6 (by norm_num)
  have h7 :
    Semiformula.Evalb ((1 : M) :> v)
      (code (codeEq (codePartrecTag (codeUnpair₂ (codeListLength dtable))) (codeConst 7))) :=
    (eval_codeEq_iff _ _ _ v).mpr
      ⟨7, 7, htag, by simpa using eval_codeConst (M := M) 7 v, Or.inl ⟨rfl, rfl⟩⟩
  simp only [codeEvaluatorCell] at hcell
  have hc := (ifpos_select _ _ _ v z k hk hcell).1 hkpos
  have hc := (ifpos_select _ _ _ v z 0 h4 hc).2 rfl
  have hc := (ifpos_select _ _ _ v z 0 h5 hc).2 rfl
  have hc := (ifpos_select _ _ _ v z 0 h6 hc).2 rfl
  exact (ifpos_select _ _ _ v z 1 h7 hc).1 _root_.zero_lt_one

private theorem min_payload_lt (q : ℕ) (hq : partrecCodeTag q = 7) : partrecCodePayload q < q :=
  by
  have hq4 : ¬q < 4 := by
    intro hlt
    simp only [partrecCodeTag, hlt, ite_true] at hq
    omega
  simp only [partrecCodePayload, Nat.div2_val]
  omega

/-- Success of the minimization branch: the subsidiary program returns a value;
zero terminates the search, and a positive result makes the recursive lookup. -/
private theorem min_cell_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ}
    (dtable dk' dq dcf dn : Code r) (table k' qv u y : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk' : Semiformula.Evalb (k' :> v) (code dk')) (hq : Semiformula.Evalb (qv :> v) (code dq))
    (hn : Semiformula.Evalb (u :> v) (code dn)) :
    Semiformula.Evalb ((y + 1) :> v) (code (codeRfindEvaluatorCell dtable dk' dq dcf dn)) ↔
      ∃ x : M,
        Semiformula.Evalb ((x + 1) :> v)
            (code
              (codeTableLookup dtable (codeSucc dk') dcf
                (codePair (codeUnpair₁ dn) (codeUnpair₂ dn)))) ∧
          ((0 < x ∧
              Semiformula.Evalb ((y + 1) :> x :> v)
                (code
                  (codeTableLookup (codeLift dtable) (codeLift dk') (codeLift dq)
                    (codePair (codeLift (codeUnpair₁ dn))
                      (codeSucc (codeLift (codeUnpair₂ dn))))))) ∨
            (x = 0 ∧ y = FFL.FirstOrder.Arithmetic.pi₂ u)) :=
  by
  have hz := eval_codeUnpair₁ dn u v hn
  have hm := eval_codeUnpair₂ dn u v hn
  have hL (x : M) (X : Code r) (a : M) (h : Semiformula.Evalb (a :> v) (code X)) :
    Semiformula.Evalb (a :> x :> v) (code (codeLift X)) := (eval_codeLift_iff X a x v).mpr h
  have hs (x : M) :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₂ u + 1) :> x :> v)
      (code (codeSucc (codeLift (codeUnpair₂ dn)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨_, hL x _ _ hm, rfl⟩
  simp only [codeRfindEvaluatorCell, eval_codeOptionBind_succ_iff]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  constructor
  · intro h
    obtain ⟨a, ha, hcase⟩ := eval_codeIfPos_cases _ _ _ _ (x :> v) h
    have hax : a = x := (eval_codeHead_iff _ _).mp ha
    subst a
    rcases hcase with ⟨hx, hr⟩ | ⟨hx, hr⟩
    · exact Or.inl ⟨hx, hr⟩
    · exact Or.inr ⟨hx, add_right_cancel (eval_unique hr (hs x))⟩
  · rintro (⟨hx, hr⟩ | ⟨hx, hy⟩)
    · exact
        eval_codeIfPos_of _ _ _ x (y + 1) (FFL.FirstOrder.Arithmetic.pi₂ u + 1) _ (x :> v)
          ((eval_codeHead_iff _ _).mpr rfl) hr (hs x) (Or.inl ⟨hx, rfl⟩)
    · obtain ⟨o, ho⟩ :=
        eval_codeTableLookup_exists_of_values (codeLift dtable) (codeLift dk') (codeLift dq)
          (codePair (codeLift (codeUnpair₁ dn)) (codeSucc (codeLift (codeUnpair₂ dn)))) table k'
          qv
          (FFL.FirstOrder.Arithmetic.pair (FFL.FirstOrder.Arithmetic.pi₁ u)
            (FFL.FirstOrder.Arithmetic.pi₂ u + 1))
          (x :> v) (hL x _ _ htable) (hL x _ _ hk') (hL x _ _ hq)
          (eval_codePair _ _ _ _ (x :> v) (hL x _ _ hz) (hs x))
      exact
        eval_codeIfPos_of _ _ _ x o (FFL.FirstOrder.Arithmetic.pi₂ u + 1) _ (x :> v)
          ((eval_codeHead_iff _ _).mpr rfl) ho (hs x) (Or.inr ⟨hx, by rw [hy]⟩)

private abbrev min_table : Code 3 :=
  codeEvaluatorHistoryBeforeCell

private abbrev min_prev : Code 3 :=
  codeSub (codeUnpair₁ (codeListLength min_table)) (codeConst 1)

private abbrev min_index : Code 3 :=
  codeUnpair₂ (codeListLength min_table)

private abbrev min_subindex : Code 3 :=
  codePartrecPayload min_index

private abbrev min_input : Code 3 :=
  Code.proj (2 : Fin 3)

/-- The complete tag-7 equation for the existing raw computation formula,
valid at arbitrary stages and arguments of every model of PA. -/
theorem evalnCertificateFormula_tag_seven_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 7) (s u y : M) (hs : 0 < s) :
    Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      u < s ∧
        ∃ x : M,
          Semiformula.Evalb ![s, ((partrecCodePayload q : ℕ) : M), u, x]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
            ((0 < x ∧
                Semiformula.Evalb
                  ![s - 1, ((q : ℕ) : M),
                    FFL.FirstOrder.Arithmetic.pair (FFL.FirstOrder.Arithmetic.pi₁ u)
                      (FFL.FirstOrder.Arithmetic.pi₂ u + 1),
                    y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4)) ∨
              (x = 0 ∧ y = FFL.FirstOrder.Arithmetic.pi₂ u)) :=
  by
  obtain ⟨H, hH, hHist⟩ := eval_codeEvaluatorHistoryBeforeCell_exists s ((q : ℕ) : M) u
  have hn : Semiformula.Evalb (u :> ![s, ((q : ℕ) : M), u]) (code min_input) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hi := eval_codeEvaluatorCell_index s ((q : ℕ) : M) u
  have hp := read_payload min_index q ![s, ((q : ℕ) : M), u] hi
  have htag :
    Semiformula.Evalb ((7 : M) :> ![s, ((q : ℕ) : M), u]) (code (codePartrecTag min_index)) :=
    by
    have h := read_tag min_index q ![s, ((q : ℕ) : M), u] hi
    simpa only [hq, Nat.cast_ofNat] using h
  have hprev : s - 1 < s := by
    have h := lt_add_one (s - 1)
    rwa [min_succ_pred hs] at h
  have hz := eval_codeUnpair₁ min_input u ![s, ((q : ℕ) : M), u] hn
  have hm := eval_codeUnpair₂ min_input u ![s, ((q : ℕ) : M), u] hn
  have harg :
    Semiformula.Evalb (u :> ![s, ((q : ℕ) : M), u])
      (code (codePair (codeUnpair₁ min_input) (codeUnpair₂ min_input))) :=
    by
    have h := eval_codePair _ _ _ _ ![s, ((q : ℕ) : M), u] hz hm
    rwa [FFL.FirstOrder.Arithmetic.pair_unpair] at h
  have hsub (x : M) :
    Semiformula.Evalb ((x + 1) :> ![s, ((q : ℕ) : M), u])
        (code
          (codeTableLookup min_table (codeSucc min_prev) min_subindex
            (codePair (codeUnpair₁ min_input) (codeUnpair₂ min_input)))) ↔
      Semiformula.Evalb ![s, ((partrecCodePayload q : ℕ) : M), u, x]
        (evalnCertificateFormula : ArithmeticSemisentence 4) :=
    by
    rw [evalnCertificateFormula_eval_history_iff]
    exact
      eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history min_table
        (codeSucc min_prev) min_subindex _ ![s, ((q : ℕ) : M), u]
        (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M)) H s u x (partrecCodePayload q) hHist
        (FFL.FirstOrder.Arithmetic.pair_lt_pair_right s (by exact_mod_cast min_payload_lt q hq))
        hH (min_base_key s ((q : ℕ) : M) u hs) hp harg
  have hrec (x : M) :
    Semiformula.Evalb ((y + 1) :> x :> ![s, ((q : ℕ) : M), u])
        (code
          (codeTableLookup (codeLift min_table) (codeLift min_prev) (codeLift min_index)
            (codePair (codeLift (codeUnpair₁ min_input))
              (codeSucc (codeLift (codeUnpair₂ min_input)))))) ↔
      Semiformula.Evalb
        ![s - 1, ((q : ℕ) : M),
          FFL.FirstOrder.Arithmetic.pair (FFL.FirstOrder.Arithmetic.pi₁ u)
            (FFL.FirstOrder.Arithmetic.pi₂ u + 1),
          y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) :=
    by
    rw [evalnCertificateFormula_eval_history_iff]
    apply
      eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history (codeLift min_table)
        (codeLift min_prev) (codeLift min_index) _ (x :> ![s, ((q : ℕ) : M), u])
        (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M)) H (s - 1) _ y q hHist
        (FFL.FirstOrder.Arithmetic.pair_lt_pair_left hprev _)
        ((eval_codeLift_iff _ _ _ _).mpr hH)
        ((eval_codeLift_iff _ _ _ _).mpr (min_decremented_fuel s ((q : ℕ) : M) u))
        ((eval_codeLift_iff _ _ _ _).mpr hi)
    exact
      eval_codePair _ _ _ _ (x :> ![s, ((q : ℕ) : M), u]) ((eval_codeLift_iff _ _ _ _).mpr hz)
        ((eval_codeSucc_iff _ _ _).mpr ⟨_, (eval_codeLift_iff _ _ _ _).mpr hm, rfl⟩)
  have hbranch :=
    min_cell_iff min_table min_prev min_index min_subindex min_input H (s - 1) ((q : ℕ) : M) u y
      ![s, ((q : ℕ) : M), u] hH (min_decremented_fuel s ((q : ℕ) : M) u) hi hn
  have hbranch' :
    Semiformula.Evalb ((y + 1) :> ![s, ((q : ℕ) : M), u])
        (code (codeRfindEvaluatorCell min_table min_prev min_index min_subindex min_input)) ↔
      ∃ x : M,
        Semiformula.Evalb ![s, ((partrecCodePayload q : ℕ) : M), u, x]
            (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          ((0 < x ∧
              Semiformula.Evalb
                ![s - 1, ((q : ℕ) : M),
                  FFL.FirstOrder.Arithmetic.pair (FFL.FirstOrder.Arithmetic.pi₁ u)
                    (FFL.FirstOrder.Arithmetic.pi₂ u + 1),
                  y]
                (evalnCertificateFormula : ArithmeticSemisentence 4)) ∨
            (x = 0 ∧ y = FFL.FirstOrder.Arithmetic.pi₂ u)) :=
    by
    rw [hbranch]
    exact
      exists_congr fun x =>
        and_congr (hsub x) (or_congr (and_congr_right fun _ => hrec x) Iff.rfl)
  rw [evalnCertificateFormula_eval_history_iff, eval_codeHistoryEvaluator_succ_iff_cell]
  apply and_congr_right
  intro _
  constructor
  · intro hc
    apply hbranch'.mp
    exact
      min_branch min_table min_input ![s, ((q : ℕ) : M), u] (y + 1) s
        (eval_codeEvaluatorCell_fuel s ((q : ℕ) : M) u) hs htag hc
  · intro h
    have hb := hbranch'.mpr h
    obtain ⟨w, hw⟩ :=
      eval_codeEvaluatorCell_exists_of_values min_table min_input H u ![s, ((q : ℕ) : M), u] hH
        hn
    have hb' :=
      min_branch min_table min_input ![s, ((q : ℕ) : M), u] w s
        (eval_codeEvaluatorCell_fuel s ((q : ℕ) : M) u) hs htag hw
    have he := eval_unique hb' hb
    rwa [he] at hw

private theorem min_successor_persistence [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 7)
    (ih :
      ∀ p : ℕ,
        p < q →
          ∀ s t u y : M,
            s ≤ t →
              Semiformula.Evalb ![s, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4) →
                Semiformula.Evalb ![t, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4))
    (k : M)
    (hpred :
      ∀ t u y : M,
        k ≤ t →
          Semiformula.Evalb ![k, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) →
            Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∀ t u y : M,
      k + 1 ≤ t →
        Semiformula.Evalb ![k + 1, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  intro t u y hkt hc
  have hk : (0 : M) < k + 1 :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le k) (lt_add_one k)
  have ht : (0 : M) < t := lt_of_lt_of_le hk hkt
  obtain ⟨hus, x, hx, hcase⟩ :=
    (evalnCertificateFormula_tag_seven_iff q hq (k + 1) u y hk).mp hc
  apply (evalnCertificateFormula_tag_seven_iff q hq t u y ht).mpr
  refine
    ⟨lt_of_lt_of_le hus hkt, x,
      ih (partrecCodePayload q) (min_payload_lt q hq) (k + 1) t u x hkt hx, ?_⟩
  rcases hcase with ⟨hpos, hrec⟩ | hz
  · left
    refine ⟨hpos, hpred (t - 1) _ y ?_ ?_⟩
    · apply le_of_add_le_add_right (a := (1 : M))
      rwa [min_succ_pred ht]
    · simpa only [add_sub_self] using hrec
  · exact Or.inr hz

/-- Constructor-7 persistence of the accepted computation formula. The only
premise is persistence for strictly smaller standard program indices. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_seven [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (q : ℕ) (hq : partrecCodeTag q = 7)
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
            (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  certificate_persistence_of_stage_induction q
    (evalnCertificateFormula_natCode_persist_of_stage_zero q)
    (min_successor_persistence q hq ih)

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
