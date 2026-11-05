/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.HistoryEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CompositionDispatch

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The raw evaluator certificate

`evalnGraphFormula` names the graph of `codeHistoryEvaluator` as a Sigma-one
semisentence, and `evalnCertificateFormula` reorders and shifts its arguments so
that the four places read `stage`, `index`, `input`, `output`, with the output
recorded as its successor.  `evalnCertificateFormula_eval_history_iff` is the
bridge between the two presentations; it is a substitution identity and needs no
arithmetic theory.

`evalnCertificateFormula_canonicalPartrecCompIndex_forward` decomposes a
certificate for a canonical composition index into a certificate for the inner
index followed by one for the outer index, at the same stage.
`evalnCertificateFormula_canonicalPartrecCompIndex_reverse` reconstructs the
certificate for the composition index from two component certificates that are
already at one supplied stage.
`evalnCertificateFormula_canonicalPartrecCompIndex_iff` packages these two
directions as an equivalence at one supplied stage.  None of these theorems
brings certificates supplied at unrelated stages to a common stage, and none
concerns first-success minimality or standard-model semantics.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open CategoricalRiceShapiro.PartialRecursive

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

/-- The graph of `codeHistoryEvaluator`, as a Sigma-one semisentence. -/
def evalnGraphFormula : Σ₁.Semisentence 4 :=
  .mkSigma (FFL.FirstOrder.Arithmetic.code codeHistoryEvaluator)
    (code_sigma_one codeHistoryEvaluator)

/-- The raw evaluator certificate: the graph formula with its places reordered
to `stage`, `index`, `input`, `output`, the output shifted by one. -/
def evalnCertificateFormula : Σ₁.Semisentence 4 :=
  evalnGraphFormula.rew
    (Rew.subst
      ![(‘#3 + 1’ : ArithmeticSemiterm Empty 4), (#0 : ArithmeticSemiterm Empty 4),
        (#1 : ArithmeticSemiterm Empty 4), (#2 : ArithmeticSemiterm Empty 4)])

/-- The certificate formula is the graph of `codeHistoryEvaluator` with the
places reordered.  This is a substitution identity: it holds in an arbitrary
structure and needs no arithmetic theory. -/
theorem evalnCertificateFormula_eval_history_iff {M : Type*} [ORingStructure M]
    (s qCode u y : M) :
    Semiformula.Evalb ![s, qCode, u, y] (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      Semiformula.Evalb ![y + 1, s, qCode, u]
        (FFL.FirstOrder.Arithmetic.code codeHistoryEvaluator) :=
  by
  have hb :
    (fun x : Fin 4 =>
        Semiterm.val ![s, qCode, u, y] (Empty.elim : Empty → M)
          ((Rew.subst ![(‘#3 + 1’ : ArithmeticSemiterm Empty 4), #0, #1, #2])
            (#x : Semiterm ℒₒᵣ Empty 4))) =
      ![y + 1, s, qCode, u] :=
    by
    funext x
    refine Fin.cases ?_ ?_ x
    · simp
    · intro i1
      refine Fin.cases ?_ ?_ i1
      · simp
      · intro i2
        refine Fin.cases ?_ ?_ i2
        · simp
        · intro i3
          refine Fin.cases ?_ (fun i4 => Fin.elim0 i4) i3
          simp
  have hf :
    (fun x : Empty =>
        Semiterm.val ![s, qCode, u, y] (Empty.elim : Empty → M)
          ((Rew.subst ![(‘#3 + 1’ : ArithmeticSemiterm Empty 4), #0, #1, #2]) (&x))) =
      Empty.elim :=
    funext (fun x => x.elim)
  simp only [evalnCertificateFormula, evalnGraphFormula, HierarchySymbol.Semiformula.val_rew,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_rew, Function.comp_def, hb, hf]

variable {M : Type*} [ORingStructure M]

/-- The history read before the cell depends only on the first two arguments. -/
private theorem beforeCell_iff [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode a b z : M) :
    Semiformula.Evalb (z :> ![s, qCode, a])
        (FFL.FirstOrder.Arithmetic.code
          codeEvaluatorHistoryBeforeCell) ↔
      Semiformula.Evalb (z :> ![s, qCode, b])
        (FFL.FirstOrder.Arithmetic.code
          codeEvaluatorHistoryBeforeCell) := by
  have hp :
    ∀ c : M,
      Semiformula.Evalb
        (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, c])
        (FFL.FirstOrder.Arithmetic.code
          (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    fun c =>
    eval_codePair _ _ s qCode ![s, qCode, c] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff, eval_comp_iff]
  constructor
  · rintro ⟨w, hw, hwi⟩
    refine ⟨w, hw, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    have h0 := hwi 0
    simp only [Matrix.cons_val_fin_one] at h0 ⊢
    rw [eval_unique h0 (hp a)]
    exact hp b
  · rintro ⟨w, hw, hwi⟩
    refine ⟨w, hw, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    have h0 := hwi 0
    simp only [Matrix.cons_val_fin_one] at h0 ⊢
    rw [eval_unique h0 (hp b)]
    exact hp a

-- The history-evaluator code contains the whole evaluator-cell code.

/-- A certificate for a canonical composition index decomposes, at the same
stage, into a certificate for the inner index and one for the outer index.

`𝐏𝐀` is the only theory assumption.  The indices enter the statement through
`ORingStructure.numeral`, which needs no theory, rather than through the
numeral cast, whose `NatCast` instance is not reachable from `𝐏𝐀` by instance
search; `𝐈Σ 1` is installed inside the proof and supplies `𝐈Σ₀`, `𝐈𝐎𝐩𝐞𝐧` and
`𝐏𝐀⁻` through Foundation's instance chain. -/
theorem evalnCertificateFormula_canonicalPartrecCompIndex_forward [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s u y : M)
    (fCode gCode : ℕ)
    (h :
      Semiformula.Evalb
        ![s, (ORingStructure.numeral (canonicalPartrecCompIndex fCode gCode) : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∃ x : M,
      Semiformula.Evalb ![s, (ORingStructure.numeral gCode : M), u, x]
          (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
        Semiformula.Evalb ![s, (ORingStructure.numeral fCode : M), x, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  simp only [numeral_eq_natCast_app] at h ⊢
  rw [evalnCertificateFormula_eval_history_iff] at h
  obtain ⟨hcode, hcell⟩ := eval_codeHistoryEvaluator_succ_extract_cell s _ u y h
  obtain ⟨x, hinner, houter⟩ :=
    eval_codeEvaluatorCell_succ_of_canonicalPartrecCompIndex codeEvaluatorHistoryBeforeCell
      (Code.proj (2 : Fin 3)) fCode gCode y ![s, (canonicalPartrecCompIndex fCode gCode : M), u]
      (by simpa using hcode) hcell
  have hgl :
    FFL.FirstOrder.Arithmetic.pair s (gCode : M) <
      FFL.FirstOrder.Arithmetic.pair s
        (canonicalPartrecCompIndex fCode gCode : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast canonicalPartrecCompIndex_inner_lt fCode gCode)
  have hfl :
    FFL.FirstOrder.Arithmetic.pair s (fCode : M) <
      FFL.FirstOrder.Arithmetic.pair s
        (canonicalPartrecCompIndex fCode gCode : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast canonicalPartrecCompIndex_outer_lt fCode gCode)
  refine ⟨x, ?_, ?_⟩
  · rw [evalnCertificateFormula_eval_history_iff]
    exact eval_codeHistoryEvaluator_succ_of_prefix_lookup s _ u x gCode hgl hinner
  · rw [evalnCertificateFormula_eval_history_iff]
    refine
      eval_codeHistoryEvaluator_succ_of_prefix_lookup s _ x y fCode hfl
        ?_
          -- transport the lifted outer lookup from arity four to arity three
    refine
      (eval_codeTableLookup_congr_at (codeLift codeEvaluatorHistoryBeforeCell)
            (codeLift (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)))
            (codeConst (n := 4) fCode) (codeHead (n := 3)) codeEvaluatorHistoryBeforeCell
            (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst (n := 3) fCode) (Code.proj (2 : Fin 3)) (y + 1)
            (x :> ![s, (canonicalPartrecCompIndex fCode gCode : M), u])
            ![s, (canonicalPartrecCompIndex fCode gCode : M), x] ?_ ?_ ?_ ?_).mp
        houter
    · intro z
      rw [eval_codeLift_iff]
      exact beforeCell_iff s _ u x z
    · intro z
      rw [eval_codeLift_iff]
      refine eval_codeUnpair₁_congr_at _ _ z _ _ ?_
      intro w
      exact eval_codeListLength_congr_at _ _ w _ _ (fun c => beforeCell_iff s _ u x c)
    · intro z
      rw [eval_codeConst_iff, eval_codeConst_iff]
    · intro z
      rw [eval_codeHead_iff, eval_proj_iff]
      simp

-- The history-evaluator code contains the whole evaluator-cell code.

/-- Two component certificates at one supplied stage reconstruct the certificate
for their canonical composition at that same stage. -/
theorem evalnCertificateFormula_canonicalPartrecCompIndex_reverse [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s u x y : M)
    (fCode gCode : ℕ)
    (hinner :
      Semiformula.Evalb ![s, (ORingStructure.numeral gCode : M), u, x]
        (evalnCertificateFormula : ArithmeticSemisentence 4))
    (houter :
      Semiformula.Evalb ![s, (ORingStructure.numeral fCode : M), x, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    Semiformula.Evalb
      ![s, (ORingStructure.numeral (canonicalPartrecCompIndex fCode gCode) : M), u, y]
      (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  simp only [numeral_eq_natCast_app] at hinner houter ⊢
  rw [evalnCertificateFormula_eval_history_iff] at hinner houter ⊢
        -- the strict input bound of the inner lookup, and positive fuel
  obtain ⟨hus, -⟩ := (eval_codeHistoryEvaluator_succ_iff_cell s _ u x).mp hinner
  have hs0 : 0 < s :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) hus
  have hgl :
    FFL.FirstOrder.Arithmetic.pair s (gCode : M) <
      FFL.FirstOrder.Arithmetic.pair s
        (canonicalPartrecCompIndex fCode gCode : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast canonicalPartrecCompIndex_inner_lt fCode gCode)
  have hfl :
    FFL.FirstOrder.Arithmetic.pair s (fCode : M) <
      FFL.FirstOrder.Arithmetic.pair s
        (canonicalPartrecCompIndex fCode gCode : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast canonicalPartrecCompIndex_outer_lt fCode gCode)
        -- both component lookups at the stage of the composition index
  have hinnerL := eval_prefix_lookup_succ_of_codeHistoryEvaluator s _ u x gCode hgl hinner
  have houterL := eval_prefix_lookup_succ_of_codeHistoryEvaluator s _ x y fCode hfl houter
  have houterLifted :
    Semiformula.Evalb ((y + 1) :> (x :> ![s, (canonicalPartrecCompIndex fCode gCode : M), u]))
      (FFL.FirstOrder.Arithmetic.code
        (codeTableLookup (codeLift codeEvaluatorHistoryBeforeCell)
          (codeLift (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeConst (n := 4) fCode) (codeHead (n := 3)))) :=
    by
    refine
      (eval_codeTableLookup_congr_at (codeLift codeEvaluatorHistoryBeforeCell)
            (codeLift (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)))
            (codeConst (n := 4) fCode) (codeHead (n := 3)) codeEvaluatorHistoryBeforeCell
            (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst (n := 3) fCode) (Code.proj (2 : Fin 3)) (y + 1)
            (x :> ![s, (canonicalPartrecCompIndex fCode gCode : M), u])
            ![s, (canonicalPartrecCompIndex fCode gCode : M), x] ?_ ?_ ?_ ?_).mpr
        houterL
    · intro z
      rw [eval_codeLift_iff]
      exact beforeCell_iff s _ u x z
    · intro z
      rw [eval_codeLift_iff]
      refine eval_codeUnpair₁_congr_at _ _ z _ _ ?_
      intro w
      exact eval_codeListLength_congr_at _ _ w _ _ (fun c => beforeCell_iff s _ u x c)
    · intro z
      rw [eval_codeConst_iff, eval_codeConst_iff]
    · intro z
      rw [eval_codeHead_iff, eval_proj_iff]
      simp
        -- both Cantor components of the length of the history before the cell
  have hlencomp :
    Semiformula.Evalb (s :> ![s, (canonicalPartrecCompIndex fCode gCode : M), u])
        (FFL.FirstOrder.Arithmetic.code
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))) ∧
      Semiformula.Evalb
        ((canonicalPartrecCompIndex fCode gCode : M) :>
          ![s, (canonicalPartrecCompIndex fCode gCode : M), u])
        (FFL.FirstOrder.Arithmetic.code
          (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))) :=
    by
    obtain ⟨H, hH⟩ :=
      eval_codeEvaluatorHistory_exists
        (FFL.FirstOrder.Arithmetic.pair s
          (canonicalPartrecCompIndex fCode gCode : M))
    have hbefore :
      Semiformula.Evalb (H :> ![s, (canonicalPartrecCompIndex fCode gCode : M), u])
        (FFL.FirstOrder.Arithmetic.code
          codeEvaluatorHistoryBeforeCell) :=
      by
      rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff]
      refine
        ⟨![FFL.FirstOrder.Arithmetic.pair s
              (canonicalPartrecCompIndex fCode gCode : M)],
          by simpa using hH, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simpa using
        eval_codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)) s _
          ![s, (canonicalPartrecCompIndex fCode gCode : M), u] ((eval_proj_iff _ _ _).mpr rfl)
          ((eval_proj_iff _ _ _).mpr rfl)
    have hself :
      Semiformula.Evalb (H :> ![H])
        (FFL.FirstOrder.Arithmetic.code
          (Code.proj (0 : Fin 1))) :=
      (eval_proj_iff _ _ _).mpr rfl
    obtain ⟨len, hlen⟩ :=
      eval_codeListLength_exists_of_value (Code.proj (0 : Fin 1)) H ![H] hself
    have hlenv :
      len =
        FFL.FirstOrder.Arithmetic.pair s
          (canonicalPartrecCompIndex fCode gCode : M) :=
      eval_codeEvaluatorHistory_length_unique _ H len hH hlen
    have hgraph :
      ∀ z : M,
        Semiformula.Evalb (z :> ![H])
            (FFL.FirstOrder.Arithmetic.code
              (Code.proj (0 : Fin 1))) ↔
          Semiformula.Evalb (z :> ![s, (canonicalPartrecCompIndex fCode gCode : M), u])
            (FFL.FirstOrder.Arithmetic.code
              codeEvaluatorHistoryBeforeCell) :=
      by
      intro z
      constructor
      · intro hz
        rw [eval_unique hz hself]
        exact hbefore
      · intro hz
        rw [eval_unique hz hbefore]
        exact hself
    have hlen' := (eval_codeListLength_congr_at _ _ len _ _ hgraph).mp hlen
    rw [hlenv] at hlen'
    have h₁ := eval_codeUnpair₁ _ _ _ hlen'
    have h₂ := eval_codeUnpair₂ _ _ _ hlen'
    rw [FFL.FirstOrder.Arithmetic.pi₁_pair] at h₁
    rw [FFL.FirstOrder.Arithmetic.pi₂_pair] at h₂
    exact
      ⟨h₁, h₂⟩
        -- the canonical cell has the value `y + 1`
  have hcell :=
    eval_codeEvaluatorCell_succ_of_component_lookups codeEvaluatorHistoryBeforeCell
      (Code.proj (2 : Fin 3)) fCode gCode x y
      ![s, (canonicalPartrecCompIndex fCode gCode : M), u]
      (by rw [numeral_eq_natCast_app]; exact hlencomp.2) ⟨s, hs0, hlencomp.1⟩ hinnerL
      houterLifted
  exact (eval_codeHistoryEvaluator_succ_iff_cell s _ u y).mpr ⟨hus, hcell⟩

/-- A certificate for a canonical composition index at a supplied stage is
equivalent to an inner certificate followed by an outer certificate at that
same stage. -/
theorem evalnCertificateFormula_canonicalPartrecCompIndex_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s u y : M)
    (fCode gCode : ℕ) :
    Semiformula.Evalb
        ![s, (ORingStructure.numeral (canonicalPartrecCompIndex fCode gCode) : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      ∃ x : M,
        Semiformula.Evalb ![s, (ORingStructure.numeral gCode : M), u, x]
            (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          Semiformula.Evalb ![s, (ORingStructure.numeral fCode : M), x, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  constructor
  · intro h
    exact evalnCertificateFormula_canonicalPartrecCompIndex_forward (M := M) s u y fCode gCode h
  · rintro ⟨x, hinner, houter⟩
    exact
      evalnCertificateFormula_canonicalPartrecCompIndex_reverse (M := M) s u x y fCode gCode
        hinner houter

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
