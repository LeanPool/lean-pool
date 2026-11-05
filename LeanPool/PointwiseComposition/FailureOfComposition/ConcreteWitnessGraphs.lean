/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Certificate
public import LeanPool.PointwiseComposition.FailureOfComposition.ComputationSearchIndices

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
PA-model equations for the four base program indices of the repository's
arithmetized Mathlib evaluator. These equations quantify over all elements of
an arbitrary PA model, including the fuel and input; they are not merely
standard-natural-number equations.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.ArithmeticCode

open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace ConcreteWitnessGraphs

variable {M : Type*} [ORingStructure M]

private theorem positive_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (a b c : Code r) (v : Fin r → M)
    (z k : M) (ha : Semiformula.Evalb (k :> v) (code a)) (hk : 0 < k)
    (h : Semiformula.Evalb (z :> v) (code (codeIfPos a b c))) :
    Semiformula.Evalb (z :> v) (code b) :=
  by
  obtain ⟨k', hk', hh⟩ := eval_codeIfPos_cases a b c z v h
  have he : k' = k := eval_unique hk' ha
  rcases hh with ⟨_, hb⟩ | ⟨hz, _⟩
  · exact hb
  · exact False.elim ((ne_of_gt hk) (he ▸ hz))

private theorem zero_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (a b c : Code r) (v : Fin r → M) (z : M)
    (ha : Semiformula.Evalb ((0 : M) :> v) (code a))
    (h : Semiformula.Evalb (z :> v) (code (codeIfPos a b c))) :
    Semiformula.Evalb (z :> v) (code c) :=
  by
  obtain ⟨k', hk', hh⟩ := eval_codeIfPos_cases a b c z v h
  have he : k' = 0 := eval_unique hk' ha
  rcases hh with ⟨hp, _⟩ | ⟨_, hc⟩
  · exact False.elim ((_root_.lt_irrefl (0 : M)) (he ▸ hp))
  · exact hc

private theorem equal_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (a b c : Code r) (v : Fin r → M) (z : M)
    (q : ℕ) (ha : Semiformula.Evalb ((q : M) :> v) (code a))
    (h : Semiformula.Evalb (z :> v) (code (codeIfPos (codeEq a (codeConst q)) b c))) :
    Semiformula.Evalb (z :> v) (code b) :=
  by
  apply positive_branch _ _ _ v z 1 _ _root_.zero_lt_one h
  exact (eval_codeEq_iff _ _ _ v).mpr ⟨q, q, ha, eval_codeConst q v, Or.inl ⟨rfl, rfl⟩⟩

private theorem unequal_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (a b c : Code r) (v : Fin r → M) (z : M)
    (q n : ℕ) (hqn : q ≠ n) (ha : Semiformula.Evalb ((q : M) :> v) (code a))
    (h : Semiformula.Evalb (z :> v) (code (codeIfPos (codeEq a (codeConst n)) b c))) :
    Semiformula.Evalb (z :> v) (code c) :=
  by
  apply zero_branch _ _ _ v z _ h
  refine (eval_codeEq_iff _ _ _ v).mpr ⟨q, n, ha, eval_codeConst n v, Or.inr ⟨?_, rfl⟩⟩
  exact_mod_cast hqn

/-- The tag decoder agrees with the index below four in every PA model. -/
theorem eval_base_tag [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ) (hq : q < 4)
    (v : Fin r → M) (hd : Semiformula.Evalb ((q : M) :> v) (code d)) :
    Semiformula.Evalb ((q : M) :> v) (code (codePartrecTag d)) :=
  by
  obtain ⟨z, hz⟩ := eval_codePartrecTag_exists_of_value d (q : M) v hd
  have hlt : Semiformula.Evalb ((1 : M) :> v) (code (codeLt d (codeConst 4))) :=
    by
    refine (eval_codeLt_iff _ _ _ v).mpr ⟨q, (4 : ℕ), hd, eval_codeConst 4 v, Or.inl ⟨?_, rfl⟩⟩
    exact_mod_cast hq
  have hd' :=
    positive_branch _ _ _ v z 1 hlt _root_.zero_lt_one
      (show Semiformula.Evalb (z :> v) (code (codeIfPos (codeLt d (codeConst 4)) d _)) from hz)
  have hzq : z = q := eval_unique hd' hd
  simpa only [hzq] using hz

/-- Output of the four base programs, interpreted in an arbitrary PA model. -/
noncomputable def baseOutput [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (u : M) : M :=
  if q = 0 then 0
  else
    if q = 1 then u + 1
    else if q = 2 then FFL.FirstOrder.Arithmetic.pi₁ u else FFL.FirstOrder.Arithmetic.pi₂ u

private theorem cell_base_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r)
    (v : Fin r → M) (z k : M) (q : ℕ) (hq : q < 4)
    (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hkpos : 0 < k)
    (hindex : Semiformula.Evalb ((q : M) :> v) (code (codeUnpair₂ (codeListLength dtable))))
    (hcell : Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn))) :
    Semiformula.Evalb (z :> v) (code (codeBaseEvaluatorCell dtable dn)) :=
  by
  have htag := eval_base_tag _ q hq v hindex
  simp only [codeEvaluatorCell] at hcell
  have h0 := positive_branch _ _ _ v z k hk hkpos hcell
  have h4 := unequal_branch _ _ _ v z q 4 (by omega) htag h0
  have h5 := unequal_branch _ _ _ v z q 5 (by omega) htag h4
  have h6 := unequal_branch _ _ _ v z q 6 (by omega) htag h5
  exact unequal_branch _ _ _ v z q 7 (by omega) htag h6

private theorem cell_base_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ} (dtable dn : Code r)
    (v : Fin r → M) (z k u : M) (q : ℕ) (hq : q < 4)
    (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hkpos : 0 < k)
    (hindex : Semiformula.Evalb ((q : M) :> v) (code (codeUnpair₂ (codeListLength dtable))))
    (hu : Semiformula.Evalb (u :> v) (code dn))
    (hcell : Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn))) :
    z = baseOutput q u + 1 :=
  by
  have htag := eval_base_tag _ q hq v hindex
  have hbase := cell_base_branch dtable dn v z k q hq hk hkpos hindex hcell
  simp only [codeBaseEvaluatorCell] at hbase
  have h0 := positive_branch _ _ _ v z k hk hkpos hbase
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · have hz := equal_branch _ _ _ v z 0 htag h0
    have hval := (eval_codeConst_iff 1 z v).mp hz
    simpa [baseOutput] using hval
  · have h1 := unequal_branch _ _ _ v z 1 0 (by decide) htag h0
    have hz := equal_branch _ _ _ v z 1 htag h1
    have hs : Semiformula.Evalb ((u + 1) :> v) (code (codeSucc dn)) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨u, hu, rfl⟩
    have hss : Semiformula.Evalb (((u + 1) + 1) :> v) (code (codeSucc (codeSucc dn))) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨u + 1, hs, rfl⟩
    simpa [baseOutput] using eval_unique hz hss
  · have h1 := unequal_branch _ _ _ v z 2 0 (by decide) htag h0
    have h2 := unequal_branch _ _ _ v z 2 1 (by decide) htag h1
    have hz := equal_branch _ _ _ v z 2 htag h2
    have hp := eval_codeUnpair₁ dn u v hu
    have hs :
      Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₁ u + 1) :> v)
        (code (codeSucc (codeUnpair₁ dn))) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨_, hp, rfl⟩
    simpa [baseOutput] using eval_unique hz hs
  · have h1 := unequal_branch _ _ _ v z 3 0 (by decide) htag h0
    have h2 := unequal_branch _ _ _ v z 3 1 (by decide) htag h1
    have h3 := unequal_branch _ _ _ v z 3 2 (by decide) htag h2
    have hz := equal_branch _ _ _ v z 3 htag h3
    have hp := eval_codeUnpair₂ dn u v hu
    have hs :
      Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₂ u + 1) :> v)
        (code (codeSucc (codeUnpair₂ dn))) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨_, hp, rfl⟩
    simpa [baseOutput] using eval_unique hz hs

/-- Exact graph equation for every base program and arbitrary model arguments. -/
theorem base_computation_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (hq : q < 4)
    (s u y : M) :
    Semiformula.Evalb ![s, (q : M), u, y] (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      u < s ∧ y = baseOutput q u :=
  by
  rw [evalnCertificateFormula_eval_history_iff, eval_codeHistoryEvaluator_succ_iff_cell]
  constructor
  · rintro ⟨hus, hcell⟩
    have hs : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
    have he :=
      cell_base_value codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)) ![s, (q : M), u]
        (y + 1) s u q hq (eval_codeEvaluatorCell_fuel s (q : M) u) hs
        (eval_codeEvaluatorCell_index s (q : M) u) ((eval_proj_iff _ _ _).mpr rfl) hcell
    exact ⟨hus, add_right_cancel he⟩
  · rintro ⟨hus, rfl⟩
    have hs : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
    obtain ⟨H, hH, _⟩ := eval_codeEvaluatorHistoryBeforeCell_exists s (q : M) u
    obtain ⟨z, hz⟩ :=
      eval_codeEvaluatorCell_exists_of_values codeEvaluatorHistoryBeforeCell
        (Code.proj (2 : Fin 3)) H u ![s, (q : M), u] hH ((eval_proj_iff _ _ _).mpr rfl)
    have he :=
      cell_base_value codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)) ![s, (q : M), u] z
        s u q hq (eval_codeEvaluatorCell_fuel s (q : M) u) hs
        (eval_codeEvaluatorCell_index s (q : M) u) ((eval_proj_iff _ _ _).mpr rfl) hz
    exact ⟨hus, by simpa only [he] using hz⟩

/-- Persistence for constructor numbers zero through three needs no induction. -/
theorem evalnCertificateFormula_natCode_persist_of_lt_four [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (q : ℕ) (hq : q < 4) (s t u y : M) (hst : s ≤ t)
    (h :
      Semiformula.Evalb ![s, (q : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    Semiformula.Evalb ![t, (q : M), u, y]
      (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  rw [base_computation_iff q hq] at h ⊢
  exact ⟨lt_of_lt_of_le h.1 hst, h.2⟩

/-- Removing fuel yields the exact total graph for each base program. -/
theorem base_unbounded_computation_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (hq : q < 4)
    (u y : M) :
    (∃ s : M,
        Semiformula.Evalb ![s, (q : M), u, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4)) ↔
      y = baseOutput q u :=
  by
  simp only [base_computation_iff q hq]
  exact ⟨fun ⟨_, _, hy⟩ => hy, fun hy => ⟨u + 1, lt_add_one u, hy⟩⟩

/-- Mathlib's existing identity program has index 48 in its fixed numbering. -/
theorem identityIndex_eq : FailureOfComposition.Kleene.identityIndex = 48 :=
  rfl

/-- The concrete identity program computes at every fuel exceeding its input. -/
theorem identity_computation [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s u : M) (hus : u < s) :
    Semiformula.Evalb ![s, (FailureOfComposition.Kleene.identityIndex : M), u, u]
      (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  rw [identityIndex_eq, evalnCertificateFormula_eval_history_iff]
  apply (eval_codeHistoryEvaluator_succ_iff_cell s (48 : M) u u).mpr
  refine ⟨hus, ?_⟩
  have hs : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
  have hleft :=
    (base_computation_iff 2 (by decide) s u (FFL.FirstOrder.Arithmetic.pi₁ u)).mpr
      ⟨hus, by simp [baseOutput]⟩
  have hright :=
    (base_computation_iff 3 (by decide) s u (FFL.FirstOrder.Arithmetic.pi₂ u)).mpr
      ⟨hus, by simp [baseOutput]⟩
  rw [evalnCertificateFormula_eval_history_iff] at hleft hright
  have hl :=
    eval_prefix_lookup_succ_of_codeHistoryEvaluator s (48 : M) u
      (FFL.FirstOrder.Arithmetic.pi₁ u) 2
      (FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
        (by exact_mod_cast (show (2 : ℕ) < 48 by norm_num)))
      hleft
  have hr :=
    eval_prefix_lookup_succ_of_codeHistoryEvaluator s (48 : M) u
      (FFL.FirstOrder.Arithmetic.pi₂ u) 3
      (FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
        (by exact_mod_cast (show (3 : ℕ) < 48 by norm_num)))
      hright
  have hcell :=
    eval_codeEvaluatorCell_succ_of_pair_component_lookups codeEvaluatorHistoryBeforeCell
      (Code.proj (2 : Fin 3)) 48 (by decide) (FFL.FirstOrder.Arithmetic.pi₁ u)
      (FFL.FirstOrder.Arithmetic.pi₂ u) ![s, (48 : M), u]
      (eval_codeEvaluatorCell_index s (48 : M) u)
      ⟨s, hs, eval_codeEvaluatorCell_fuel s (48 : M) u⟩
      (by
        change
          Semiformula.Evalb _
            (code (codeTableLookup _ _ (codeConst (partrecCodePayload₁ 48)) _))
        rw [show partrecCodePayload₁ 48 = 2 from
            by
            change (Nat.unpair (Nat.pair 2 3)).1 = 2
            simp only [Nat.unpair_pair]]
        exact hl)
      (by
        change
          Semiformula.Evalb _
            (code (codeTableLookup _ _ (codeConst (partrecCodePayload₂ 48)) _))
        rw [show partrecCodePayload₂ 48 = 3 from
            by
            change (Nat.unpair (Nat.pair 2 3)).2 = 3
            simp only [Nat.unpair_pair]]
        exact hr)
  simpa only [FFL.FirstOrder.Arithmetic.pair_unpair] using hcell

end ConcreteWitnessGraphs
end FailureOfComposition

end

end PointwiseComposition
