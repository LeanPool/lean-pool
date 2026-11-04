/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.History
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.RecursionEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CellCongruence
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.CellEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The length of a constructed evaluation history

Except in the results described in the paragraphs below, every length
evaluation here is either supplied by a premise or reassembled from drop
evaluations supplied by premises.  `length_of_drops` constructs only
the `codeRfindPos` presentation from those existing drop witnesses; it
constructs no drop evaluation, and the uniqueness result only identifies the
value of a supplied length evaluation.

Four results are of the opposite kind, and each asserts totality over `𝐏𝐀`.
`eval_codeEvaluatorRow_exists_of_value` gives the row of a table a value at any
value of the table.  `eval_codeEvaluatorTableStep_exists_of_value` composes that
row totality with `eval_codeListSnoc_exists_of_values`, giving the extended table
a value.  `eval_codeEvaluatorHistory_exists` gives the history a value at every
stage, without a premise.  `eval_codeHistoryEvaluator_exists` gives the lookup
in the history one step past the pair of the first two arguments a value at
every argument triple, composing history totality with
`eval_codeTableLookup_exists_of_values`.  The row and history results are the
only results here that directly use the generic existence theorem for
`codePrec`.

Four generic readings, over `𝐏𝐀` and `𝐈𝐎𝐩𝐞𝐧`, identify the arguments that the
evaluator cell reads at an arbitrary argument triple `s, qCode, u`.
`eval_codeEvaluatorHistoryBeforeCell_exists` is a further totality result,
derived from `eval_codeEvaluatorHistory_exists`: it gives
`codeEvaluatorHistoryBeforeCell` a value and identifies it with the history at
`pair s qCode`.  `eval_codeEvaluatorHistoryBeforeCell_length` proves that the
length of that history is `pair s qCode`, using
`eval_codeEvaluatorHistory_length_unique`.  `eval_codeEvaluatorCell_fuel` and
`eval_codeEvaluatorCell_index` read the two components of that length as `s` and
`qCode`.  None of the four depends on the constructor number of `qCode`.

Two results relate a `codeHistoryEvaluator` evaluation at an earlier stage to a
lookup of the same row in the history at a later stage.
`eval_codeHistoryEvaluator_succ_of_prefix_lookup` derives the earlier
evaluation from the later lookup: it descends one stage at a time with
`getAt_step_down`, and every history evaluation it uses is supplied.
`eval_prefix_lookup_succ_of_codeHistoryEvaluator` derives the later lookup from
the earlier evaluation: it ascends one stage at a time with `getAt_step_up`,
which shows that the snoc step preserves an entry below the last row.  History
totality gives each later stage a value, and
`eval_codeListLength_exists_of_value` gives the extended histories their
lengths.

`eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history` is the
earlier-row bridge.  For a history `H` evaluated at a row count `N`, a stage `k`
and a standard index `q` with `pair k q < N`, a successful lookup in `H` at
`k`, `q` and an input `u` is exactly a successful `codeHistoryEvaluator`
evaluation at `k`, `q`, `u`.  Every code is supplied with its value, and the
proof uses no certificate persistence: it descends with `getAt_descend` and
ascends with `getAt_step_up`.  `input_lt_of_codeTableLookup_succ_of_history`
derives `u < k` from such a lookup, and
`eval_predecessor_lookup_succ_iff_codeHistoryEvaluator` specializes the bridge
to the history before the cell at `k + 1, q`, read at the decremented stage
`k`.

`eval_codeHistoryEvaluator_succ_iff_cell` characterizes a successful lookup:
`codeHistoryEvaluator` has a successor value at `s, qCode, u` exactly when
`u < s` and the evaluator cell of the history one step earlier has that value
at index `u`.  The bound is strict because the row appended at the pair of `s`
and `qCode` holds the cells at the indices below `s`; the row recursion also
evaluates its step at the terminal index, but that value is not part of the
row.  The forward direction is the extraction argument of
`eval_codeHistoryEvaluator_succ_extract_cell`.  The reverse direction
constructs the eager row and the history that appends it, using
`eval_codeEvaluatorHistory_exists` and `eval_codeListLength_exists_of_value`,
and locates the supplied cell in them with `chain_match`.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open HierarchySymbol

variable {M : Type*} [ORingStructure M]

/-- The iterated-tail recursion that `codeListDrop` applies to its index and
its list. -/
private def dropCore : Code 2 :=
  codePrec (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3)))

/-- `codeListDrop` applies `dropCore` to its two arguments. -/
private theorem codeListDrop_eq_dropCore {n : ℕ} (dlist didx : Code n) :
    codeListDrop dlist didx = dropCore.comp ![didx, dlist] :=
  rfl

/-- The graph of a code is a Sigma-one relation of the whole assignment. -/
private theorem definable_code_graph {m : ℕ} (A : Code m) :
    Σ-[1].Definable (fun w : Fin (m + 1) → M => Semiformula.Evalb w (code A)) :=
  by
  refine
    ⟨HierarchySymbol.Semiformula.mkSigma
        ((Rew.emb : Rew ℒₒᵣ Empty (m + 1) M (m + 1)) ▹ (code A))
        (Hierarchy.rew _ (code_sigma_one A)),
      ?_⟩
  intro w
  simp

/-!
### Reading a supplied length evaluation -/

/-- A supplied length evaluation exhibits the drop of the list at its own value
as zero, and every earlier drop as nonzero. -/
private theorem drops_of_length [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (X : Code r) (Hv n : M) (v : Fin r → M)
    (hX : Semiformula.Evalb (Hv :> v) (code X))
    (hlen : Semiformula.Evalb (n :> v) (code (codeListLength X))) :
    Semiformula.Evalb ((0 : M) :> n :> ![Hv]) (code dropCore) ∧
      ∀ t : M, t < n → ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> ![Hv]) (code dropCore) :=
  by
  have harg :
    ∀ t z : M,
      Semiformula.Evalb (z :> t :> v) (code (codeListDrop (codeLift X) (codeHead (n := r)))) →
        Semiformula.Evalb (z :> t :> ![Hv]) (code dropCore) :=
    by
    intro t z hz
    rw [codeListDrop_eq_dropCore, eval_comp_iff] at hz
    obtain ⟨w, hw, hwi⟩ := hz
    have h0 : w 0 = t := by
      have := hwi 0
      simp only [Matrix.cons_val_zero] at this
      exact eval_unique this ((eval_codeHead_iff _ _).mpr rfl)
    have h1 : w 1 = Hv := by
      have := hwi 1
      simp only [Matrix.cons_val_one] at this
      exact eval_unique this ((eval_codeLift_iff X _ _ v).mpr hX)
    have hshape : w = (t :> ![Hv]) := by
      funext j
      refine Fin.cases ?_ ?_ j
      · simpa using h0
      · intro j'
        refine Fin.cases ?_ (fun j'' => Fin.elim0 j'') j'
        simpa using h1
    rw [hshape] at hw
    exact hw
  rw [codeListLength, eval_codeRfindPos_iff] at hlen
  obtain ⟨⟨y, hy, hbody⟩, hmin⟩ := hlen
  constructor
  · rw [eval_codeInv_iff] at hbody
    obtain ⟨e, he, hcase⟩ := hbody
    rcases hcase with ⟨he0, -⟩ | ⟨-, hy0⟩
    · exact harg n 0 (he0 ▸ he)
    · exact absurd hy0 (ne_of_gt hy)
  · intro t ht
    have hb := hmin t ht
    rw [eval_codeInv_iff] at hb
    obtain ⟨e, he, hcase⟩ := hb
    rcases hcase with ⟨-, h01⟩ | ⟨hne, -⟩
    · exact absurd h01.symm _root_.one_ne_zero
    · exact ⟨e, hne, harg t e he⟩

/-!
### The cons layer and the iterated tail -/

/-- Both arguments of a successfully evaluated `codePair` have values. -/
private theorem codePair_args [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (A B : Code r) (p : M) (v : Fin r → M)
    (h : Semiformula.Evalb (p :> v) (code (codePair A B))) :
    ∃ a b : M, Semiformula.Evalb (a :> v) (code A) ∧ Semiformula.Evalb (b :> v) (code B) :=
  by
  rw [codePair] at h
  obtain ⟨f, hf, -⟩ := eval_codeIfPos_cases _ _ _ _ _ h
  rw [eval_codeLt_iff] at hf
  obtain ⟨a, b, ha, hb, -⟩ := hf
  exact ⟨a, b, ha, hb⟩

/-- A successfully evaluated cons is the successor of the pair of two values
that its argument codes take. -/
private theorem codeListCons_args [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ} (A B : Code r) (c : M)
    (v : Fin r → M) (h : Semiformula.Evalb (c :> v) (code (codeListCons A B))) :
    ∃ a b : M,
      Semiformula.Evalb (a :> v) (code A) ∧
        Semiformula.Evalb (b :> v) (code B) ∧ c = FFL.FirstOrder.Arithmetic.pair a b + 1 :=
  by
  rw [codeListCons, eval_codeSucc_iff] at h
  obtain ⟨p, hp, hc⟩ := h
  obtain ⟨a, b, ha, hb⟩ := codePair_args A B p v hp
  exact ⟨a, b, ha, hb, by rw [hc, eval_unique hp (eval_codePair A B a b v ha hb)]⟩

/-- A successfully evaluated cons is nonzero. -/
private theorem codeListCons_ne_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (A B : Code r) (c : M)
    (v : Fin r → M) (h : Semiformula.Evalb (c :> v) (code (codeListCons A B))) : c ≠ 0 :=
  by
  rw [codeListCons, eval_codeSucc_iff] at h
  obtain ⟨p, -, hc⟩ := h
  rw [hc]
  exact fun hcon => (zero_ne_add_one p) hcon.symm

/-- The tail of a value known to be a successor of a pair is the pair's second
component. -/
private theorem eval_tail_of_pair_succ [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ} (d : Code r) (w x l z : M)
    (v : Fin r → M) (hw : Semiformula.Evalb (w :> v) (code d))
    (hwv : w = FFL.FirstOrder.Arithmetic.pair x l + 1)
    (hz : Semiformula.Evalb (z :> v) (code (codeListTail d))) : z = l :=
  by
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (codeConst (n := r) 1)) := by
    rw [eval_codeConst_iff]; simp
  have hsub := eval_codeSub d (codeConst 1) w 1 v hw hone
  rw [hwv, add_sub_self] at hsub
  have hu :=
    eval_codeUnpair₂ (codeSub d (codeConst 1)) (FFL.FirstOrder.Arithmetic.pair x l) v hsub
  rw [FFL.FirstOrder.Arithmetic.pi₂_pair] at hu
  exact eval_unique hz (by rw [codeListTail]; exact hu)

/-!
### The iterated tail of a fixed list -/

/-- Dropping no entries returns the list. -/
private theorem dropCore_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (Hv z : M)
    (h : Semiformula.Evalb (z :> (0 : M) :> ![Hv]) (code dropCore)) : z = Hv :=
  by
  have h0 :=
    eval_codePrec_zero (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3))) z ![Hv] h
  simpa using (eval_proj_iff (0 : Fin 1) z ![Hv]).mp h0

/-- Dropping one more entry takes the tail of the previous drop. -/
private theorem dropCore_succ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (Hv t z : M)
    (h : Semiformula.Evalb (z :> (t + 1) :> ![Hv]) (code dropCore)) :
    ∃ w : M,
      Semiformula.Evalb (w :> t :> ![Hv]) (code dropCore) ∧
        Semiformula.Evalb (z :> t :> w :> ![Hv])
          (code (codeListTail (Code.proj (1 : Fin 3)))) :=
  eval_codePrec_succ (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3))) t z ![Hv] h

/-!
### The recursion that appends one row -/

/-- The recursion inside the table step of `codeEvaluatorHistory`, written out.
The private core of `codeListSnoc` is reached through its public equation. -/
private def historySnocCore : Code 3 :=
  codePrec (codeListCons (codeEvaluatorRow (Code.proj (1 : Fin 2))) (codeListNil (n := 2)))
    (codeListCons
      (codeSub
        (codeListGetOptional (codeLift (codeLift (Code.proj (1 : Fin 2))))
          (codeSub (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))
            (codeSucc (Code.proj (0 : Fin 4)))))
        (codeConst 1))
      (Code.proj (1 : Fin 4)))

/-- The table step binds the length of the previous history as the recursion
argument of `historySnocCore`. -/
private theorem codeEvaluatorTableStep_eq :
    codeEvaluatorTableStep (Code.proj (1 : Fin 2)) =
      codeBind (codeListLength (Code.proj (1 : Fin 2))) historySnocCore :=
  by
  rw [codeEvaluatorTableStep, codeListSnoc_eq_bind]
  rfl

/-- `historySnocCore` written out as a primitive recursion, so that the
recursion eliminators apply without unfolding the definition. -/
private theorem historySnocCore_eq :
    historySnocCore =
      codePrec (codeListCons (codeEvaluatorRow (Code.proj (1 : Fin 2))) (codeListNil (n := 2)))
        (codeListCons
          (codeSub
            (codeListGetOptional (codeLift (codeLift (Code.proj (1 : Fin 2))))
              (codeSub (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))
                (codeSucc (Code.proj (0 : Fin 4)))))
            (codeConst 1))
          (Code.proj (1 : Fin 4))) :=
  rfl

/-!
### Matching the append recursion against the iterated tail -/

/-- The matching condition between the append recursion and the iterated tail,
as a Sigma-one condition on the drop index. -/
private theorem definable_match (Pc : Code 3) (w₀ w₁ b H bound : M) :
    Σ-[1].DefinablePred
      (fun i : M =>
        i ≤ b →
          i ≤ bound →
            ∃ a p : M,
              a + i = b ∧
                Semiformula.Evalb ![p, a, w₀, w₁] (code Pc) ∧
                  Semiformula.Evalb ![p, i, H] (code dropCore)) := by
  have hS :
    Σ-[1].Definable (fun w : Fin 3 → M => Semiformula.Evalb ![w 0, w 1, w₀, w₁] (code Pc)) :=
    by
    refine
      ((definable_code_graph (M := M) Pc).retractiont (f :=
            ![(#0 : ArithmeticSemiterm M 3), #1, &w₀, &w₁])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#0 : ArithmeticSemiterm M 3), #1, &w₀, &w₁] j)) =
        ![w 0, w 1, w₀, w₁] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ ?_ j1
        · simp
        · intro j2
          refine Fin.cases ?_ ?_ j2
          · simp
          · intro j3
            refine Fin.cases ?_ (fun j4 => Fin.elim0 j4) j3
            simp
    rw [he]
  have hD :
    Σ-[1].Definable (fun w : Fin 3 → M => Semiformula.Evalb ![w 0, w 2, H] (code dropCore)) :=
    by
    refine
      ((definable_code_graph (M := M) dropCore).retractiont (f :=
            ![(#0 : ArithmeticSemiterm M 3), #2, &H])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#0 : ArithmeticSemiterm M 3), #2, &H] j)) =
        ![w 0, w 2, H] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ ?_ j1
        · simp
        · intro j2
          refine Fin.cases ?_ (fun j3 => Fin.elim0 j3) j2
          simp
    rw [he]
  have hbody :
    Σ-[1].Definable
      (fun w : Fin 3 → M =>
        w 1 + w 2 = b ∧
          Semiformula.Evalb ![w 0, w 1, w₀, w₁] (code Pc) ∧
            Semiformula.Evalb ![w 0, w 2, H] (code dropCore)) :=
    (by definability : Σ-[1].Definable (fun w : Fin 3 → M => w 1 + w 2 = b)).and (hS.and hD)
  have hex :
    Σ-[1].Definable
      (fun v : Fin 1 → M =>
        ∃ a p : M,
          a + v 0 = b ∧
            Semiformula.Evalb ![p, a, w₀, w₁] (code Pc) ∧
              Semiformula.Evalb ![p, v 0, H] (code dropCore)) :=
    HierarchySymbol.Definable.exs (HierarchySymbol.Definable.exs hbody)
  exact
    HierarchySymbol.Definable.imp (by definability)
      (HierarchySymbol.Definable.imp (by definability) hex)

-- The graph formula of the recursions compared here contains the whole
-- evaluator-cell code, so unifying it against the recursion eliminators
-- exceeds the default heartbeat limit.

/-- A recursion whose step conses onto the previous value runs through the same
values as the iterated tail of its result, in opposite directions.

Every evaluation used here is supplied: the recursion values come from a
successful evaluation of the recursion, and the drop values from a supplied
bounded family. -/
private theorem chain_match [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (base : Code 2) (hdc : Code 4) (w₀ w₁ b H bound : M)
    (htop :
      Semiformula.Evalb ![H, b, w₀, w₁]
        (code (codePrec base (codeListCons hdc (Code.proj (1 : Fin 4))))))
    (hdrop : ∀ t : M, t ≤ bound → ∃ z : M, Semiformula.Evalb ![z, t, H] (code dropCore))
    (i : M) :
    i ≤ b →
      i ≤ bound →
        ∃ a p : M,
          a + i = b ∧
            Semiformula.Evalb ![p, a, w₀, w₁]
                (code (codePrec base (codeListCons hdc (Code.proj (1 : Fin 4))))) ∧
              Semiformula.Evalb ![p, i, H] (code dropCore) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  refine
    InductionOnHierarchy.succ_induction Σ 1
      (definable_match (codePrec base (codeListCons hdc (Code.proj (1 : Fin 4)))) w₀ w₁ b H
        bound)
      ?_ ?_ i
  · intro _ h0n
    refine ⟨b, H, add_zero b, htop, ?_⟩
    obtain ⟨z, hz⟩ := hdrop 0 h0n
    have hzH : z = H := dropCore_zero H z hz
    rw [hzH] at hz
    exact hz
  · intro c IH hc1 hc2
    have hcm : c ≤ b := le_trans le_self_add hc1
    have hcn : c ≤ bound := le_trans le_self_add hc2
    obtain ⟨a, p, hac, hsa, hdi⟩ := IH hcm hcn
    have hapos : 0 < a :=
      by
      rcases
        eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le a) with
        h0 | hpos
      · exfalso
        rw [← h0, zero_add] at hac
        rw [← hac] at hc1
        exact absurd hc1 (by simp)
      · exact hpos
    have hpred : a - 1 + 1 = a :=
      sub_add_self_of_le
        (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hapos)
    obtain ⟨q, hsq, hstep⟩ :=
      eval_codePrec_succ _ _ (a - 1) p ![w₀, w₁] (by rw [hpred]; exact hsa)
    obtain ⟨x, l, -, hl, hpv⟩ := codeListCons_args _ _ p _ hstep
    have hlq : l = q := eval_unique hl ((eval_proj_iff _ _ _).mpr rfl)
    obtain ⟨z, hz⟩ := hdrop (c + 1) hc2
    obtain ⟨w, hw, htail⟩ := dropCore_succ H c z hz
    have hwp : w = p := eval_unique hw hdi
    refine ⟨a - 1, q, ?_, hsq, ?_⟩
    · calc
        a - 1 + (c + 1) = (a - 1 + 1) + c := by rw [add_comm c 1, ← add_assoc]
        _ = a + c := by rw [hpred]
        _ = b := hac
    · have hzq : z = q :=
        eval_tail_of_pair_succ (Code.proj (1 : Fin 3)) w x q z ![c, w, H]
          ((eval_proj_iff _ _ _).mpr rfl) (by rw [hwp, hpv, hlq]) htail
      rw [hzq] at hz
      exact hz

-- The drop recursion's graph formula is large; unifying it against the
-- recursion eliminator exceeds the default heartbeat limit.

/-- The drops of a list below a supplied drop index are themselves supplied. -/
private theorem drop_prefix [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (H bnd z : M)
    (hz : Semiformula.Evalb ![z, bnd, H] (code dropCore)) :
    ∀ t : M, t ≤ bnd → ∃ y : M, Semiformula.Evalb ![y, t, H] (code dropCore) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  have hD :
    Σ-[1].Definable (fun w : Fin 3 → M => Semiformula.Evalb ![w 0, w 1, H] (code dropCore)) :=
    by
    refine
      ((definable_code_graph (M := M) dropCore).retractiont (f :=
            ![(#0 : ArithmeticSemiterm M 3), #1, &H])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#0 : ArithmeticSemiterm M 3), #1, &H] j)) =
        ![w 0, w 1, H] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ ?_ j1
        · simp
        · intro j2
          refine Fin.cases ?_ (fun j3 => Fin.elim0 j3) j2
          simp
    rw [he]
  have hdef :
    Σ-[1].DefinablePred
      (fun j : M =>
        j ≤ bnd → ∃ t y : M, t + j = bnd ∧ Semiformula.Evalb ![y, t, H] (code dropCore)) :=
    by
    have hbody :
      Σ-[1].Definable
        (fun w : Fin 3 → M =>
          w 1 + w 2 = bnd ∧ Semiformula.Evalb ![w 0, w 1, H] (code dropCore)) :=
      (by definability : Σ-[1].Definable (fun w : Fin 3 → M => w 1 + w 2 = bnd)).and hD
    exact
      HierarchySymbol.Definable.imp (by definability)
        (HierarchySymbol.Definable.exs (HierarchySymbol.Definable.exs hbody))
  have hstep :
    ∀ j : M, j ≤ bnd → ∃ t y : M, t + j = bnd ∧ Semiformula.Evalb ![y, t, H] (code dropCore) :=
    by
    refine InductionOnHierarchy.succ_induction Σ 1 hdef ?_ ?_
    · intro _
      exact ⟨bnd, z, add_zero bnd, hz⟩
    · intro j IH hj
      obtain ⟨t, y, htj, hy⟩ := IH (le_trans le_self_add hj)
      have htpos : 0 < t :=
        by
        rcases
          eq_or_lt_of_le
            (FFL.FirstOrder.Arithmetic.zero_le t) with
          h0 | hp
        · exfalso
          rw [← h0, zero_add] at htj
          rw [← htj] at hj
          exact absurd hj (by simp)
        · exact hp
      have hpred : t - 1 + 1 = t :=
        sub_add_self_of_le
          (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp htpos)
      obtain ⟨w, hw, -⟩ := dropCore_succ H (t - 1) y (by rw [hpred]; exact hy)
      refine ⟨t - 1, w, ?_, hw⟩
      calc
        t - 1 + (j + 1) = (t - 1 + 1) + j := by rw [add_comm j 1, ← add_assoc]
        _ = t + j := by rw [hpred]
        _ = bnd := htj
  intro t ht
  obtain ⟨t', y, ht', hy⟩ := hstep (bnd - t) (by simp)
  have hbt : t + (bnd - t) = bnd := add_tsub_self_of_le ht
  have htt : t' = t := add_right_cancel (ht'.trans hbt.symm)
  rw [htt] at hy
  exact ⟨y, hy⟩

-- The drop recursion's graph formula is large; unifying it against the
-- recursion eliminator exceeds the default heartbeat limit.

/-- Once a drop of a list vanishes, every later supplied drop vanishes too. -/
private theorem drops_zero_from [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (H c bound : M)
    (hc : Semiformula.Evalb ![(0 : M), c, H] (code dropCore))
    (hdrop : ∀ t : M, t ≤ bound → ∃ z : M, Semiformula.Evalb ![z, t, H] (code dropCore)) (t : M)
    (hct : c ≤ t) (htb : t ≤ bound) : Semiformula.Evalb ![(0 : M), t, H] (code dropCore) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  have hdef :
    Σ-[1].DefinablePred
      (fun r : M => c ≤ r → r ≤ bound → Semiformula.Evalb ![(0 : M), r, H] (code dropCore)) :=
    by
    have hD :
      Σ-[1].Definable
        (fun w : Fin 1 → M => Semiformula.Evalb ![(0 : M), w 0, H] (code dropCore)) :=
      by
      refine
        ((definable_code_graph (M := M) dropCore).retractiont (f :=
              ![&(0 : M), (#0 : ArithmeticSemiterm M 1), &H])).of_iff
          ?_
      intro w
      have he :
        (fun j => Semiterm.val w id (![&(0 : M), (#0 : ArithmeticSemiterm M 1), &H] j)) =
          ![(0 : M), w 0, H] :=
        by
        funext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro j1
          refine Fin.cases ?_ ?_ j1
          · simp
          · intro j2
            refine Fin.cases ?_ (fun j3 => Fin.elim0 j3) j2
            simp
      rw [he]
    exact
      HierarchySymbol.Definable.imp (by definability)
        (HierarchySymbol.Definable.imp (by definability) hD)
  refine InductionOnHierarchy.succ_induction Σ 1 hdef ?_ ?_ t hct htb
  · intro hc0 _
    have hcz : c = 0 := le_antisymm hc0 (FFL.FirstOrder.Arithmetic.zero_le c)
    rw [hcz] at hc
    exact hc
  · intro r IH hcr hrb
    rcases lt_or_ge r c with hlt | hle
    · have hceq : c = r + 1 :=
        le_antisymm hcr (FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hlt)
      rw [hceq] at hc
      exact hc
    · have hprev := IH hle (le_trans le_self_add hrb)
      obtain ⟨z', hz'⟩ := hdrop (r + 1) hrb
      obtain ⟨w, hw, htail⟩ := dropCore_succ H r z' hz'
      have hw0 : w = 0 := eval_unique hw hprev
      have hone : Semiformula.Evalb ((1 : M) :> ![r, w, H]) (code (codeConst (n := 3) 1)) := by
        rw [eval_codeConst_iff]; simp
      have hsub :=
        eval_codeSub (Code.proj (1 : Fin 3)) (codeConst 1) w 1 ![r, w, H]
          ((eval_proj_iff _ _ _).mpr rfl) hone
      have hw1 : w - 1 = 0 := by
        rw [hw0]
        exact FFL.FirstOrder.Arithmetic.zero_sub 1
      rw [hw1] at hsub
      have hu :=
        eval_codeUnpair₂ (codeSub (Code.proj (1 : Fin 3)) (codeConst 1)) 0 ![r, w, H] hsub
      have hpi : FFL.FirstOrder.Arithmetic.pi₂ (0 : M) = 0 :=
        le_antisymm (by simpa using FFL.FirstOrder.Arithmetic.pi₂_le_self (0 : M))
          (FFL.FirstOrder.Arithmetic.zero_le _)
      rw [hpi] at hu
      have hz0 : z' = 0 := eval_unique htail (by rw [codeListTail]; exact hu)
      rw [hz0] at hz'
      exact hz'

/-- Supplied drop evaluations reassemble into a length evaluation, in any
presentation of the list as a code.  Only the minimization is built here; the
drops themselves are always premises. -/
private theorem length_of_drops [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (X : Code r) (Hv n : M) (v : Fin r → M)
    (hX : Semiformula.Evalb (Hv :> v) (code X))
    (h0 : Semiformula.Evalb ((0 : M) :> n :> ![Hv]) (code dropCore))
    (hn :
      ∀ t : M, t < n → ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> ![Hv]) (code dropCore)) :
    Semiformula.Evalb (n :> v) (code (codeListLength X)) :=
  by
  have harg :
    ∀ t z : M,
      Semiformula.Evalb (z :> t :> ![Hv]) (code dropCore) →
        Semiformula.Evalb (z :> t :> v)
          (code (codeListDrop (codeLift X) (codeHead (n := r)))) :=
    by
    intro t z hz
    rw [codeListDrop_eq_dropCore, eval_comp_iff]
    refine ⟨![t, Hv], hz, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using (eval_codeHead_iff (M := M) t (t :> v)).mpr rfl
    · intro j
      refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
      simpa using (eval_codeLift_iff X Hv t v).mpr hX
  rw [codeListLength, eval_codeRfindPos_iff]
  refine ⟨⟨1, by simp, ?_⟩, ?_⟩
  · exact (eval_codeInv_iff _ _ _).mpr ⟨0, harg n 0 h0, Or.inl ⟨rfl, rfl⟩⟩
  · intro t ht
    obtain ⟨e, hne, he⟩ := hn t ht
    exact (eval_codeInv_iff _ _ _).mpr ⟨e, harg t e he, Or.inr ⟨hne, rfl⟩⟩

/-- A history whose length evaluation disagrees with its index. -/
private theorem definable_bad :
    Σ-[1].DefinablePred
      (fun m : M =>
        ∃ H n : M,
          Semiformula.Evalb ![H, m] (code codeEvaluatorHistory) ∧
            Semiformula.Evalb ![n, H] (code (codeListLength (Code.proj (0 : Fin 1)))) ∧
              ¬n = m) :=
  by
  have hH :
    Σ-[1].Definable
      (fun w : Fin 3 → M => Semiformula.Evalb ![w 1, w 2] (code codeEvaluatorHistory)) :=
    by
    refine
      ((definable_code_graph (M := M) codeEvaluatorHistory).retractiont (f :=
            ![(#1 : ArithmeticSemiterm M 3), #2])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#1 : ArithmeticSemiterm M 3), #2] j)) = ![w 1, w 2] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
        simp
    rw [he]
  have hL :
    Σ-[1].Definable
      (fun w : Fin 3 → M =>
        Semiformula.Evalb ![w 0, w 1] (code (codeListLength (Code.proj (0 : Fin 1))))) :=
    by
    refine
      ((definable_code_graph (M := M) (codeListLength (Code.proj (0 : Fin 1)))).retractiont
            (f := ![(#0 : ArithmeticSemiterm M 3), #1])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#0 : ArithmeticSemiterm M 3), #1] j)) = ![w 0, w 1] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
        simp
    rw [he]
  exact
    HierarchySymbol.Definable.exs
      (HierarchySymbol.Definable.exs (hH.and (hL.and (by definability))))

/-- Every value of the append recursion is a cons, hence nonzero. -/
private theorem snoc_value_ne_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (m₁ H' a p : M)
    (hp : Semiformula.Evalb ![p, a, m₁, H'] (code historySnocCore)) : p ≠ 0 := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  rw [historySnocCore_eq] at hp
  rcases eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le a) with
    h0 | hpos
  · rw [← h0] at hp
    exact codeListCons_ne_zero _ _ p _ (eval_codePrec_zero _ _ p ![m₁, H'] hp)
  · have hpred : a - 1 + 1 = a :=
      sub_add_self_of_le
        (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hpos)
    obtain ⟨q, -, hstep⟩ := eval_codePrec_succ _ _ (a - 1) p ![m₁, H'] (by rw [hpred]; exact hp)
    exact codeListCons_ne_zero _ _ p _ hstep

-- The same evaluator-cell code appears here through `historySnocCore`.

/-- A supplied length evaluation of one table step is one more than the length
of the history it extends. -/
private theorem length_step [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (m₁ H' H₀ n₀ : M)
    (hsnoc : Semiformula.Evalb ![H₀, m₁, m₁, H'] (code historySnocCore))
    (hd0 : Semiformula.Evalb ![(0 : M), n₀, H₀] (code dropCore))
    (hdn : ∀ t : M, t < n₀ → ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb ![e, t, H₀] (code dropCore)) :
    n₀ = m₁ + 1 := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
        -- the drop chain does not run out before the recursion does
  have hdrop : ∀ t : M, t ≤ n₀ → ∃ z : M, Semiformula.Evalb ![z, t, H₀] (code dropCore) :=
    by
    intro t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · obtain ⟨e, -, he⟩ := hdn t hlt
      exact ⟨e, he⟩
    · exact ⟨0, hd0⟩
  rw [historySnocCore_eq] at hsnoc
  have hgt : m₁ < n₀ := by
    by_contra hcon
    have hle : n₀ ≤ m₁ := not_lt.mp hcon
    obtain ⟨a, p, -, hsa, hdc⟩ := chain_match _ _ m₁ H' m₁ H₀ n₀ hsnoc hdrop n₀ hle le_rfl
    exact
      snoc_value_ne_zero m₁ H' a p (by rw [historySnocCore_eq]; exact hsa)
        (eval_unique hdc hd0)
          -- and it runs out immediately afterwards
  have hle : n₀ ≤ m₁ + 1 := by
    by_contra hcon
    have hlt : m₁ + 1 < n₀ := not_le.mp hcon
    obtain ⟨a, p, hac, hsa, hdc⟩ :=
      chain_match _ _ m₁ H' m₁ H₀ n₀ hsnoc hdrop m₁ le_rfl (le_of_lt hgt)
    have ha0 : a = 0 := by
      have : a + m₁ = 0 + m₁ := by rw [hac, zero_add]
      exact add_right_cancel this
    rw [ha0] at hsa
    have hbase := eval_codePrec_zero _ _ p ![m₁, H'] hsa
    obtain ⟨r, l, -, hnil, hpv⟩ := codeListCons_args _ _ p _ hbase
    have hl0 : l = 0 := by
      simpa [codeListNil] using (eval_zero_iff (M := M) l ![m₁, H']).mp hnil
    obtain ⟨e, hne, he⟩ := hdn (m₁ + 1) hlt
    obtain ⟨w, hw, htail⟩ := dropCore_succ H₀ m₁ e he
    have hwp : w = p := eval_unique hw hdc
    have hel : e = l :=
      eval_tail_of_pair_succ (Code.proj (1 : Fin 3)) w r l e ![m₁, w, H₀]
        ((eval_proj_iff _ _ _).mpr rfl) (by rw [hwp, hpv]) htail
    exact hne (by rw [hel, hl0])
  exact
    le_antisymm hle
      (FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hgt)

/-!
### The length of a constructed history -/

-- The history code contains the whole evaluator-cell code.

/-- A supplied length evaluation of the history at `m` has the value `m`.

Existence is never asserted: the length evaluation is a premise, and the proof
only identifies its value.  `codeListLength` is a minimization, and the generic
existence theorem for `codePrec` is not used here. -/
theorem eval_codeEvaluatorHistory_length_unique [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (m H n : M)
    (hH : Semiformula.Evalb ![H, m] (code codeEvaluatorHistory))
    (hLength : Semiformula.Evalb ![n, H] (code (codeListLength (Code.proj (0 : Fin 1))))) :
    n = m := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  by_contra hne
  obtain ⟨m₀, ⟨H₀, n₀, hH₀, hL₀, hne₀⟩, hleast⟩ :=
    InductionOnHierarchy.least_number Σ 1 (definable_bad (M := M)) (x := m)
      ⟨H, n, hH, hLength, hne⟩
  have hself : Semiformula.Evalb (H₀ :> ![H₀]) (code (Code.proj (0 : Fin 1))) :=
    (eval_proj_iff _ _ _).mpr rfl
  obtain ⟨hd0, hdn⟩ := drops_of_length _ H₀ n₀ ![H₀] hself hL₀
  rcases
    eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le m₀) with
    hzero | hpos
  · -- the empty history has no nonzero drop at index zero
    refine hne₀ ?_
    rw [← hzero] at hH₀ ⊢
    have hnil : H₀ = 0 :=
      by
      have h0 :=
        eval_codePrec_zero _ _ H₀ ![] (by rw [codeEvaluatorHistory] at hH₀; simpa using hH₀)
      simpa [codeListNil] using (eval_zero_iff (M := M) H₀ ![]).mp h0
    by_contra hn0
    obtain ⟨e, hne', he⟩ :=
      hdn 0
        (lt_of_le_of_ne (FFL.FirstOrder.Arithmetic.zero_le n₀)
          (Ne.symm hn0))
    exact hne' (by rw [dropCore_zero H₀ e he, hnil])
  · -- the successor step adds exactly one entry
    have hpred : m₀ - 1 + 1 = m₀ :=
      sub_add_self_of_le
        (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hpos)
    obtain ⟨H', hH', hstep⟩ :=
      eval_codePrec_succ _ _ (m₀ - 1) H₀ ![]
        (by rw [codeEvaluatorHistory] at hH₀; rw [hpred]; simpa using hH₀)
    rw [← codeEvaluatorHistory] at hH'
    rw [codeEvaluatorTableStep_eq, eval_codeBind_iff] at hstep
    obtain ⟨n', hlen', hsnoc⟩ := hstep
    have hproj : Semiformula.Evalb (H' :> ![m₀ - 1, H']) (code (Code.proj (1 : Fin 2))) :=
      (eval_proj_iff _ _ _).mpr rfl
    obtain ⟨hd0', hdn'⟩ := drops_of_length _ H' n' ![m₀ - 1, H'] hproj hlen'
    have hlen'' :
      Semiformula.Evalb (n' :> ![H']) (code (codeListLength (Code.proj (0 : Fin 1)))) :=
      length_of_drops _ H' n' ![H'] ((eval_proj_iff _ _ _).mpr rfl) hd0' hdn'
    have hn'm : n' = m₀ - 1 := by
      by_contra hcon
      exact hleast (m₀ - 1) (by rw [← hpred]; simp) ⟨H', n', by simpa using hH', hlen'', hcon⟩
    rw [hn'm] at hsnoc
    refine hne₀ ?_
    rw [← hpred]
    exact length_step (m₀ - 1) H' H₀ n₀ (by simpa using hsnoc) hd0 hdn

/-!
### The program index read from the history -/

private theorem posL [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {x y : M} (h : 0 < x * y) : 0 < x :=
  by
  rcases eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le x) with h0 | hp
  · rw [← h0, zero_mul] at h; exact absurd h (_root_.lt_irrefl 0)
  · exact hp

private theorem posR [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {x y : M} (h : 0 < x * y) : 0 < y :=
  by
  rcases eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le y) with h0 | hp
  · rw [← h0, mul_zero] at h; exact absurd h (_root_.lt_irrefl 0)
  · exact hp

/-- Both arguments of a successfully evaluated truncated difference have
values. -/
private theorem eval_sub_args [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n : ℕ} (A B : Code n) (z : M) (v : Fin n → M)
    (h : Semiformula.Evalb (z :> v) (code (codeSub A B))) :
    ∃ a b : M,
      Semiformula.Evalb (a :> v) (code A) ∧
        Semiformula.Evalb (b :> v) (code B) ∧ (z + b = a ∨ z = 0) :=
  by
  rw [codeSub, eval_codeRfindPos_iff] at h
  obtain ⟨⟨y, hy, hbody⟩, -⟩ := h
  rw [eval_codeOr_iff] at hbody
  obtain ⟨p, q, hp, hq, hcase⟩ := hbody
  rw [eval_codeEq_iff] at hp
  obtain ⟨e₁, e₂, he₁, he₂, hdec⟩ := hp
  rw [eval_codeAdd_iff] at he₁
  obtain ⟨zz, b, hzz, hb, hsum⟩ := he₁
  rw [eval_codeHead_iff] at hzz
  simp only [Matrix.cons_val_zero] at hzz
  subst hzz
  rw [eval_codeLift_iff] at hb he₂
  refine ⟨e₂, b, he₂, hb, ?_⟩
  rcases hdec with ⟨heq, -⟩ | ⟨-, hp0⟩
  · left; rw [← heq, hsum]
  · right
    rw [eval_codeAnd_iff] at hq
    obtain ⟨c₁, c₂, -, hc₂, hdec₂⟩ := hq
    have hqpos : 0 < q := by
      rcases hcase with ⟨hpos, -⟩ | ⟨-, h0⟩
      · rw [hp0, zero_add] at hpos; exact hpos
      · exact absurd h0 (ne_of_gt hy)
    have hc₂pos : 0 < c₂ := by
      rcases hdec₂ with ⟨hpos, -⟩ | ⟨-, h0⟩
      · exact posR hpos
      · exact absurd h0 (ne_of_gt hqpos)
    rw [eval_codeEq_iff] at hc₂
    obtain ⟨d₁, d₂, hd₁, hd₂, hdec₃⟩ := hc₂
    rw [eval_codeHead_iff] at hd₁
    simp only [Matrix.cons_val_zero] at hd₁
    rw [eval_zero_iff] at hd₂
    rcases hdec₃ with ⟨heq, -⟩ | ⟨-, h0⟩
    · rw [hd₁] at heq; rw [heq, hd₂]
    · exact absurd h0 (ne_of_gt hc₂pos)

/-- Two codes with a common value have the same graph, at whatever arities and
assignments they are written. -/
private theorem graph_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k l : ℕ} (A : Code k) (A' : Code l) (t : M)
    (v : Fin k → M) (v' : Fin l → M) (h : Semiformula.Evalb (t :> v) (code A))
    (h' : Semiformula.Evalb (t :> v') (code A')) :
    ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v') (code A') := by
  intro x
  constructor
  · intro hx; rw [eval_unique hx h]; exact h'
  · intro hx; rw [eval_unique hx h']; exact h

-- The history-evaluator code contains the whole evaluator-cell code.

/-- A successful history-evaluator lookup one step past the pair of `s` and
`qCode` exhibits `qCode` as the second Cantor component of the length of the
history one step earlier. -/
theorem eval_codeHistoryEvaluator_succ_extract_index [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s qCode u y : M)
    (h : Semiformula.Evalb ![y + 1, s, qCode, u] (code codeHistoryEvaluator)) :
    Semiformula.Evalb ![qCode, s, qCode, u]
      (code (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  rw [codeHistoryEvaluator, codeTableLookup_eq] at h
  obtain ⟨a, -, ha, -, -⟩ := eval_sub_args _ _ _ _ h
  rw [codeListGetOptional] at ha
  obtain ⟨row, hrow, -⟩ := eval_codeIfPos_cases _ _ _ _ _ ha
  rw [codeListDrop_eq_dropCore, eval_comp_iff] at hrow
  obtain ⟨w, -, hwi⟩ := hrow
  have hY := hwi 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hY
  obtain ⟨a₁, -, ha₁, -, -⟩ := eval_sub_args _ _ _ _ hY
  rw [codeListGetOptional] at ha₁
  obtain ⟨tbl, htbl, -⟩ := eval_codeIfPos_cases _ _ _ _ _ ha₁
  rw [codeListDrop_eq_dropCore, eval_comp_iff] at htbl
  obtain ⟨w', -, hw'i⟩ := htbl
  have hDT := hw'i 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hDT
  rw [eval_comp_iff] at hDT
  obtain ⟨w'', hhist, hw''i⟩ := hDT
  have hsucc := hw''i 0
  simp only [Matrix.cons_val_zero] at hsucc
  rw [eval_codeSucc_iff] at hsucc
  obtain ⟨m, hm, hw''0⟩ := hsucc
  have hshape : w'' = (m + 1) :> ![] := by
    funext j
    refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
    exact hw''0
  rw [hshape, codeEvaluatorHistory] at hhist
  obtain ⟨H₀, hH₀, hstep⟩ := eval_codePrec_succ _ _ m _ ![] hhist
  rw [← codeEvaluatorHistory] at hH₀
  rw [codeEvaluatorTableStep_eq, eval_codeBind_iff] at hstep
  obtain ⟨n', hlen', -⟩ := hstep
  obtain ⟨hd0, hdn⟩ :=
    drops_of_length _ H₀ n' ![m, H₀] ((eval_proj_iff (1 : Fin 2) H₀ ![m, H₀]).mpr rfl) hlen'
  have hn'm : n' = m :=
    eval_codeEvaluatorHistory_length_unique m H₀ n' (by simpa using hH₀)
      (length_of_drops _ H₀ n' ![H₀] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  rw [hn'm] at hd0 hdn
  have hbefore :
    Semiformula.Evalb (H₀ :> ![s, qCode, u]) (code codeEvaluatorHistoryBeforeCell) :=
    by
    rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff]
    refine ⟨![m], by simpa using hH₀, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simpa using hm
  have hlen :
    Semiformula.Evalb (m :> ![s, qCode, u])
      (code (codeListLength codeEvaluatorHistoryBeforeCell)) :=
    length_of_drops _ H₀ m ![s, qCode, u] hbefore hd0 hdn
  have hmpair : m = FFL.FirstOrder.Arithmetic.pair s qCode :=
    eval_unique hm
      (eval_codePair _ _ s qCode ![s, qCode, u] ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_proj_iff _ _ _).mpr rfl))
  have hu :=
    eval_codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell) m ![s, qCode, u] hlen
  rw [hmpair, FFL.FirstOrder.Arithmetic.pi₂_pair] at hu
  exact hu

/-!
### The evaluator cell read from the history -/

-- The history-evaluator code contains the whole evaluator-cell code.

/-- A successful history-evaluator lookup one step past the pair of `s` and
`qCode` has its input `u` strictly below `s`, and exhibits its own value as the
evaluator cell of the history one step earlier at index `u`.

The bound is strict.  The entry at `u` is nonempty, so the position of the row
recursion that holds it is positive, position zero being the empty list; that
position plus `u` is `s`. -/
private theorem pair_assignment {α : Type*} (w : Fin 2 → α) (a : α) (h : w 0 = a) :
    w = a :> ![w 1] := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa using h
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl

private theorem singleton_assignment {α : Type*} (w : Fin 1 → α) (a : α) (h : w 0 = a) :
    w = a :> ![] := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa using h

private theorem positive_recursion_entry [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (cell : Code 4)
    (w₀ w₁ bound row input value : M)
    (hrec :
      Semiformula.Evalb ![row, bound, w₀, w₁]
        (code (codePrec (codeListNil (n := 2)) (codeListCons cell (Code.proj (1 : Fin 4))))))
    (hdrops : ∀ t : M, t ≤ input → ∃ z : M, Semiformula.Evalb ![z, t, row] (code dropCore))
    (hentry : Semiformula.Evalb ![value, input, row] (code dropCore)) (hpositive : 0 < value) :
    ∃ a previous head tail : M,
      a + input = bound ∧
        0 < a ∧
          Semiformula.Evalb ![head, a - 1, previous, w₀, w₁] (code cell) ∧
            Semiformula.Evalb ![tail, a - 1, previous, w₀, w₁] (code (Code.proj (1 : Fin 4))) ∧
              value = FFL.FirstOrder.Arithmetic.pair head tail + 1 :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (U := 𝐈Σ₁) inferInstance
  have hbound : input ≤ bound := by
    by_contra hcon
    have hlt : bound < input := not_le.mp hcon
    obtain ⟨a, result, ha, heval, hdrop⟩ :=
      chain_match _ _ w₀ w₁ bound row input hrec hdrops bound le_rfl (le_of_lt hlt)
    have ha0 : a = 0 :=
      by
      have heq : a + bound = 0 + bound := by simpa using ha
      exact add_right_cancel heq
    rw [ha0] at heval
    have hbase := eval_codePrec_zero _ _ result ![w₀, w₁] heval
    have hzero : result = 0 := by
      simpa [codeListNil] using (eval_zero_iff (M := M) result ![w₀, w₁]).mp hbase
    rw [hzero] at hdrop
    have hnil := drops_zero_from row bound input hdrop hdrops input (le_of_lt hlt) le_rfl
    exact absurd (eval_unique hentry hnil) (ne_of_gt hpositive)
  obtain ⟨a, result, ha, heval, hdrop⟩ :=
    chain_match _ _ w₀ w₁ bound row input hrec hdrops input hbound le_rfl
  have hresult : result = value := eval_unique hdrop hentry
  have hapos : 0 < a :=
    by
    rcases eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le a) with hzero | hpos
    · rw [← hzero] at heval
      have hbase := eval_codePrec_zero _ _ result ![w₀, w₁] heval
      have hz : result = 0 := by
        simpa [codeListNil] using (eval_zero_iff (M := M) result ![w₀, w₁]).mp hbase
      exact absurd (hz ▸ hresult) (ne_of_gt hpositive).symm
    · exact hpos
  have hpredecessor : a - 1 + 1 = a :=
    sub_add_self_of_le (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hapos)
  obtain ⟨previous, _, hstep⟩ :=
    eval_codePrec_succ _ _ (a - 1) result ![w₀, w₁] (by rw [hpredecessor]; exact heval)
  obtain ⟨head, tail, hhead, htail, hvalue⟩ := codeListCons_args _ _ result _ hstep
  exact ⟨a, previous, head, tail, ha, hapos, hhead, htail, by rw [← hresult]; exact hvalue⟩

private theorem eval_codeHistoryEvaluator_succ_extract_cell_core [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    (s qCode u y : M)
    (h : Semiformula.Evalb ![y + 1, s, qCode, u] (code codeHistoryEvaluator)) :
    u < s ∧
      Semiformula.Evalb ![y + 1, s, qCode, u]
        (code (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)))) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  have hone : ∀ w : Fin 3 → M, Semiformula.Evalb ((1 : M) :> w) (code (codeConst (n := 3) 1)) :=
    by intro w; rw [eval_codeConst_iff]; simp
  rw [codeHistoryEvaluator, codeTableLookup_eq] at h
  obtain ⟨a, b₀, ha, hb₀, hcase₀⟩ := eval_sub_args _ _ _ _ h
  have hb₀v : b₀ = 1 := eval_unique hb₀ (hone _)
  have hay : a = y + 1 + 1 := by
    rcases hcase₀ with heq | h0
    · rw [← heq, hb₀v]
    · exact absurd h0.symm (zero_ne_add_one y)
  rw [codeListGetOptional] at ha
  obtain ⟨f, hf, hbr⟩ := eval_codeIfPos_cases _ _ _ _ _ ha
  have hanz : ¬Semiformula.Evalb (a :> ![s, qCode, u]) (code (Code.zero 3)) :=
    by
    intro hR
    rw [eval_zero_iff, hay] at hR
    exact (zero_ne_add_one (y + 1)) hR.symm
  obtain ⟨hfpos, hsucc⟩ := hbr.resolve_right (fun hp => hanz hp.2)
  rw [eval_codeSucc_iff] at hsucc
  obtain ⟨c, hc, hac⟩ := hsucc
  have hcy : c = y + 1 :=
    by
    have : c + 1 = y + 1 + 1 := by rw [← hac, hay]
    exact add_right_cancel this
  have hfdrop := hf
  rw [codeListDrop_eq_dropCore, eval_comp_iff] at hf
  obtain ⟨w, hfw, hwi⟩ := hf
  have hw0 : w 0 = u := by
    have h0 := hwi 0
    simp only [Matrix.cons_val_zero] at h0
    simpa using eval_unique h0 ((eval_proj_iff (2 : Fin 3) u ![s, qCode, u]).mpr rfl)
  have hYv := hwi 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hYv
  have hinner : Semiformula.Evalb ![f, u, w 1] (code dropCore) :=
    by
    have hshape := pair_assignment w u hw0
    rw [hshape] at hfw
    simpa using hfw
  have hdropRow := drop_prefix (w 1) u f hinner
  obtain ⟨a₁, b₁, ha₁, hb₁, hcase₁⟩ := eval_sub_args _ _ _ _ hYv
  have hb₁v : b₁ = 1 := eval_unique hb₁ (hone _)
  have hYpos : w 1 + 1 = a₁ := by
    rcases hcase₁ with heq | h0
    · rw [← heq, hb₁v]
    · exfalso
      have hz0 : Semiformula.Evalb ![(0 : M), 0, w 1] (code dropCore) :=
        by
        obtain ⟨z, hz⟩ :=
          hdropRow 0 (FFL.FirstOrder.Arithmetic.zero_le u)
        have hzw : z = w 1 := dropCore_zero (w 1) z hz
        have hz0' : z = 0 := by rw [hzw, h0]
        rw [hz0'] at hz
        exact hz
      have :=
        drops_zero_from (w 1) 0 u hz0 hdropRow u
          (FFL.FirstOrder.Arithmetic.zero_le u) le_rfl
      exact
        absurd (eval_unique hinner this)
          (ne_of_gt hfpos)
            -- the outer lookup selects the row of the predecessor history
  rw [codeListGetOptional] at ha₁
  obtain ⟨g, hg, hbr₁⟩ := eval_codeIfPos_cases _ _ _ _ _ ha₁
  have ha₁nz : ¬Semiformula.Evalb (a₁ :> ![s, qCode, u]) (code (Code.zero 3)) :=
    by
    intro hR
    rw [eval_zero_iff, ← hYpos] at hR
    exact (zero_ne_add_one (w 1)) hR.symm
  obtain ⟨hgpos, hsucc₁⟩ := hbr₁.resolve_right (fun hp => ha₁nz hp.2)
  rw [eval_codeSucc_iff] at hsucc₁
  obtain ⟨c₁, hc₁, ha₁c⟩ := hsucc₁
  have hc₁Y : c₁ = w 1 :=
    by
    have : c₁ + 1 = w 1 + 1 := by rw [← ha₁c, hYpos]
    exact add_right_cancel this
  have hgsub := eval_codeSub _ (codeConst 1) g 1 ![s, qCode, u] hg (hone _)
  have hgu := eval_codeUnpair₁ _ (g - 1) ![s, qCode, u] hgsub
  have hc₁pi : c₁ = FFL.FirstOrder.Arithmetic.pi₁ (g - 1) :=
    eval_unique hc₁ hgu
  rw [codeListDrop_eq_dropCore, eval_comp_iff] at hg
  obtain ⟨w', hgw, hw'i⟩ := hg
  have hm := hw'i 0
  simp only [Matrix.cons_val_zero] at hm
  have hDT := hw'i 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hDT
  rw [eval_comp_iff] at hDT
  obtain ⟨w'', hhist, hw''i⟩ := hDT
  have hsuccP := hw''i 0
  simp only [Matrix.cons_val_zero] at hsuccP
  rw [eval_codeSucc_iff] at hsuccP
  obtain ⟨m, hmP, hw''0⟩ := hsuccP
  have hmw : w' 0 = m := eval_unique hm hmP
  have hshape'' := singleton_assignment w'' (m + 1) hw''0
  rw [hshape'', codeEvaluatorHistory] at hhist
  obtain ⟨H₀, hH₀, hstep⟩ := eval_codePrec_succ _ _ m _ ![] hhist
  rw [← codeEvaluatorHistory] at hH₀
  rw [codeEvaluatorTableStep_eq, eval_codeBind_iff] at hstep
  obtain ⟨n', hlen', hsnoc⟩ := hstep
  obtain ⟨hd0, hdn⟩ :=
    drops_of_length _ H₀ n' ![m, H₀] ((eval_proj_iff (1 : Fin 2) H₀ ![m, H₀]).mpr rfl) hlen'
  have hn'm : n' = m :=
    eval_codeEvaluatorHistory_length_unique m H₀ n' (by simpa using hH₀)
      (length_of_drops _ H₀ n' ![H₀] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  rw [hn'm] at hd0 hdn hsnoc hlen'
  have hgT : Semiformula.Evalb ![g, m, w' 1] (code dropCore) :=
    by
    have hshape' := pair_assignment w' m hmw
    rw [hshape'] at hgw
    simpa using hgw
  have hdropT := drop_prefix (w' 1) m g hgT
  rw [historySnocCore_eq] at hsnoc
  obtain ⟨aT, pT, haT, hsaT, hdT⟩ :=
    chain_match _ _ m H₀ m (w' 1) m hsnoc hdropT m le_rfl le_rfl
  have haT0 : aT = 0 := by
    have : aT + m = 0 + m := by rw [haT, zero_add]
    exact add_right_cancel this
  rw [haT0] at hsaT
  have hbase := eval_codePrec_zero _ _ pT ![m, H₀] hsaT
  obtain ⟨rowv, nilv, hrow, hnil, hpTv⟩ := codeListCons_args _ _ pT _ hbase
  have hnil0 : nilv = 0 := by
    simpa [codeListNil] using (eval_zero_iff (M := M) nilv ![m, H₀]).mp hnil
  have hgp : g = pT := eval_unique hgT hdT
  have hrowv : w 1 = rowv := by
    rw [hc₁Y] at hc₁pi
    rw [hc₁pi, hgp, hpTv, hnil0, add_sub_self,
      FFL.FirstOrder.Arithmetic.pi₁_pair]
      -- the row recursion, whose bound is `s`
  rw [hrowv] at hinner hdropRow
  rw [codeEvaluatorRow_eq_bind, eval_codeBind_iff] at hrow
  obtain ⟨bnd, hbnd, hrowcore⟩ := hrow
  have hmpair : m = FFL.FirstOrder.Arithmetic.pair s qCode :=
    eval_unique hmP
      (eval_codePair _ _ s qCode ![s, qCode, u] ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_proj_iff _ _ _).mpr rfl))
  have hbnds : bnd = s :=
    by
    have :=
      eval_unique hbnd
        (eval_codeUnpair₁ (codeListLength (Code.proj (1 : Fin 2))) m ![m, H₀] hlen')
    rw [this, hmpair, FFL.FirstOrder.Arithmetic.pi₁_pair]
  rw [hbnds] at hrowcore
  obtain ⟨aR, q, cellv, l, haR, haRpos, hcell, hl, hpRv⟩ :=
    positive_recursion_entry _ m H₀ s rowv u f hrowcore hdropRow hinner hfpos
  have hpredR : aR - 1 + 1 = aR :=
    sub_add_self_of_le (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp haRpos)
  have hfsub := eval_codeSub _ (codeConst 1) f 1 ![s, qCode, u] hfdrop (hone _)
  have hcpi : c = FFL.FirstOrder.Arithmetic.pi₁ (f - 1) :=
    eval_unique hc (eval_codeUnpair₁ _ (f - 1) ![s, qCode, u] hfsub)
  have hpif : FFL.FirstOrder.Arithmetic.pi₁ (f - 1) = cellv := by
    rw [hpRv, add_sub_self,
      FFL.FirstOrder.Arithmetic.pi₁_pair]
  have hcelly : cellv = y + 1 := by rw [← hpif, ← hcpi]; exact hcy
  have hTsrc :
    Semiformula.Evalb (H₀ :> ![aR - 1, q, m, H₀])
      (code (codeLift (codeLift (Code.proj (1 : Fin 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr
      ((eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl))
  have hTtgt : Semiformula.Evalb (H₀ :> ![s, qCode, u]) (code codeEvaluatorHistoryBeforeCell) :=
    by
    rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff]
    refine ⟨![m], by simpa using hH₀, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simpa using hmP
  have hlenlift :
    Semiformula.Evalb (m :> ![aR - 1, q, m, H₀])
      (code (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))) :=
    length_of_drops _ H₀ m ![aR - 1, q, m, H₀] hTsrc hd0 hdn
  have hfuel :
    Semiformula.Evalb (s :> ![aR - 1, q, m, H₀])
      (code (codeUnpair₁ (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2))))))) :=
    by
    have hpi : FFL.FirstOrder.Arithmetic.pi₁ m = s := by
      rw [hmpair, FFL.FirstOrder.Arithmetic.pi₁_pair]
    have hlift := eval_codeUnpair₁ _ m ![aR - 1, q, m, H₀] hlenlift
    rwa [hpi] at hlift
  have hstepv :
    Semiformula.Evalb (aR :> ![aR - 1, q, m, H₀]) (code (codeSucc (Code.proj (0 : Fin 4)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨aR - 1, (eval_proj_iff _ _ _).mpr rfl, hpredR.symm⟩
  have hNsrc :
    Semiformula.Evalb (u :> ![aR - 1, q, m, H₀])
      (code
        (codeSub (codeUnpair₁ (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2))))))
          (codeSucc (Code.proj (0 : Fin 4))))) :=
    by
    have hsu : s - aR = u := sub_remove_left (by rw [← haR, add_comm])
    have := eval_codeSub _ _ s aR ![aR - 1, q, m, H₀] hfuel hstepv
    rwa [hsu] at this
  have hNtgt : Semiformula.Evalb (u :> ![s, qCode, u]) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hfin :=
    (eval_codeEvaluatorCell_congr_at _ _ _ _ cellv ![aR - 1, q, m, H₀] ![s, qCode, u]
          (graph_iff _ _ H₀ _ _ hTsrc hTtgt) (graph_iff _ _ u _ _ hNsrc hNtgt)).mp
      hcell
  rw [hcelly] at hfin
  refine ⟨?_, hfin⟩
  rw [← haR]
  exact lt_add_of_pos_left u haRpos

/-- A successful history-evaluator lookup one step past the pair of `s` and
`qCode` exhibits `qCode` as the second Cantor component of the length of the
history one step earlier, and exhibits its own value as the evaluator cell of
that history at index `u`. -/
theorem eval_codeHistoryEvaluator_succ_extract_cell [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s qCode u y : M)
    (h : Semiformula.Evalb ![y + 1, s, qCode, u] (code codeHistoryEvaluator)) :
    Semiformula.Evalb ![qCode, s, qCode, u]
        (code (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))) ∧
      Semiformula.Evalb ![y + 1, s, qCode, u]
        (code (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)))) :=
  ⟨eval_codeHistoryEvaluator_succ_extract_index s qCode u y h,
    (eval_codeHistoryEvaluator_succ_extract_cell_core s qCode u y h).2⟩

/-!
### Entries of an encoded list, independently of how the list is written -/

/-- The encoded list `l` has the nonzero entry `z` at index `i`: the drop of `l`
at `i` is a nonempty cons whose head is `z - 1`.

Stating this at values rather than at codes lets an entry be moved between
different presentations of the same list. -/
private abbrev GetAt (l i z : M) : Prop :=
  ∃ d hd : M,
    Semiformula.Evalb ![d, i, l] (code dropCore) ∧
      Semiformula.Evalb ![hd, d]
          (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
        0 < d ∧ z = hd + 1

/-- The head of a nonempty encoded list, read at one fixed presentation. -/
private theorem head_of_drop [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ} (D : Code r) (d : M) (v : Fin r → M)
    (hd : Semiformula.Evalb (d :> v) (code D)) :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pi₁ (d - 1) :> v)
      (code (codeUnpair₁ (codeSub D (codeConst 1)))) :=
  by
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (codeConst (n := r) 1)) := by
    rw [eval_codeConst_iff]; simp
  exact eval_codeUnpair₁ _ (d - 1) v (eval_codeSub _ (codeConst 1) d 1 v hd hone)

/-- A positive `codeListGet?` evaluation exhibits its list, its index and the
entry relation between them. -/
private theorem getAt_of_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ} (A B : Code r) (z : M) (v : Fin r → M)
    (hz : Semiformula.Evalb (z :> v) (code (codeListGetOptional A B))) (hpos : 0 < z) :
    ∃ l i : M,
      Semiformula.Evalb (l :> v) (code A) ∧ Semiformula.Evalb (i :> v) (code B) ∧ GetAt l i z :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  rw [codeListGetOptional] at hz
  obtain ⟨d, hd, hbr⟩ := eval_codeIfPos_cases _ _ _ _ _ hz
  have hnz : ¬Semiformula.Evalb (z :> v) (code (Code.zero r)) :=
    by
    intro hR
    rw [eval_zero_iff] at hR
    rw [hR] at hpos
    exact absurd hpos (_root_.lt_irrefl 0)
  obtain ⟨hdpos, hsucc⟩ := hbr.resolve_right (fun hp => hnz hp.2)
  rw [eval_codeSucc_iff] at hsucc
  obtain ⟨e, he, hze⟩ := hsucc
  have hev : e = FFL.FirstOrder.Arithmetic.pi₁ (d - 1) := eval_unique he (head_of_drop _ d v hd)
  have hdcopy := hd
  rw [codeListDrop_eq_dropCore, eval_comp_iff] at hd
  obtain ⟨w, hdw, hwi⟩ := hd
  have hB := hwi 0
  simp only [Matrix.cons_val_zero] at hB
  have hA := hwi 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hA
  have hshape : w = (w 0 :> ![w 1]) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro j'
      refine Fin.cases ?_ (fun j'' => Fin.elim0 j'') j'
      rfl
  rw [hshape] at hdw
  refine
    ⟨w 1, w 0, hA, hB, d, FFL.FirstOrder.Arithmetic.pi₁ (d - 1), by simpa using hdw,
      head_of_drop (Code.proj (0 : Fin 1)) d ![d] ((eval_proj_iff _ _ _).mpr rfl), hdpos, ?_⟩
  rw [← hev, hze]

/-- Conversely, an entry relation gives a `codeListGet?` evaluation at any pair
of codes taking the list and the index as values. -/
private theorem eval_of_getAt [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ} (A B : Code r) (l i z : M) (v : Fin r → M)
    (hA : Semiformula.Evalb (l :> v) (code A)) (hB : Semiformula.Evalb (i :> v) (code B))
    (hg : GetAt l i z) : Semiformula.Evalb (z :> v) (code (codeListGetOptional A B)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  obtain ⟨d, hh, hd, hhead, hdpos, hz⟩ := hg
  have hdrop : Semiformula.Evalb (d :> v) (code (codeListDrop A B)) :=
    by
    rw [codeListDrop_eq_dropCore, eval_comp_iff]
    refine ⟨![i, l], by simpa using hd, ?_⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa using hB
    · intro j'
      refine Fin.cases ?_ (fun j'' => Fin.elim0 j'') j'
      simpa using hA
  have hhv : hh = FFL.FirstOrder.Arithmetic.pi₁ (d - 1) :=
    eval_unique hhead
      (head_of_drop (Code.proj (0 : Fin 1)) d ![d] ((eval_proj_iff _ _ _).mpr rfl))
  rw [codeListGetOptional]
  exact
    eval_codeIfPos_of _ _ _ d (FFL.FirstOrder.Arithmetic.pi₁ (d - 1) + 1) 0 z v hdrop
      ((eval_codeSucc_iff _ _ _).mpr ⟨_, head_of_drop _ d v hdrop, rfl⟩)
      ((eval_zero_iff _ _).mpr rfl) (Or.inl ⟨hdpos, by rw [hz, hhv]⟩)

/-!
### An entry older than the last row survives one step back -/

-- The history code contains the whole evaluator-cell code, so unifying it
-- against the recursion eliminators exceeds the default heartbeat limit.

/-- An entry of the history at `j + 1` whose index is below `j` is already an
entry of the history at `j`, with the same value.

Every evaluation used is supplied: the recursion values come from the successful
table step, and the drop values from the supplied entry. -/
private theorem getAt_step_down [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (j i z Hj1 : M)
    (hHj1 : Semiformula.Evalb ![Hj1, j + 1] (code codeEvaluatorHistory)) (hij : i < j)
    (hget : GetAt Hj1 i z) (hz : 1 < z) :
    ∃ Hj : M, Semiformula.Evalb ![Hj, j] (code codeEvaluatorHistory) ∧ GetAt Hj i z :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  obtain ⟨d, hh, hd, hhead, hdpos, hzv⟩ := hget
  rw [codeEvaluatorHistory] at hHj1
  obtain ⟨Hj, hHj, hstep⟩ := eval_codePrec_succ _ _ j Hj1 ![] hHj1
  rw [← codeEvaluatorHistory] at hHj
  rw [codeEvaluatorTableStep_eq, eval_codeBind_iff] at hstep
  obtain ⟨n', hlen', hsnoc⟩ := hstep
  obtain ⟨hd0, hdn⟩ :=
    drops_of_length _ Hj n' ![j, Hj] ((eval_proj_iff (1 : Fin 2) Hj ![j, Hj]).mpr rfl) hlen'
  have hn'j : n' = j :=
    eval_codeEvaluatorHistory_length_unique j Hj n' (by simpa using hHj)
      (length_of_drops _ Hj n' ![Hj] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  rw [hn'j] at hd0 hdn hsnoc hlen'
  have hdropJ1 := drop_prefix Hj1 i d hd
  rw [historySnocCore_eq] at hsnoc
  obtain ⟨a, p, hai, hsa, hdi⟩ :=
    chain_match _ _ j Hj j Hj1 i hsnoc hdropJ1 i (le_of_lt hij) le_rfl
  have hpd : p = d := eval_unique hdi hd
  have hapos : 0 < a :=
    by
    rcases eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le a) with h0 | hpos
    · exfalso
      rw [← h0, zero_add] at hai
      rw [hai] at hij
      exact absurd hij (_root_.lt_irrefl j)
    · exact hpos
  have hpred : a - 1 + 1 = a :=
    sub_add_self_of_le (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hapos)
  obtain ⟨q, -, hcons⟩ := eval_codePrec_succ _ _ (a - 1) p ![j, Hj] (by rw [hpred]; exact hsa)
  obtain ⟨x, l, hx, hl, hpv⟩ := codeListCons_args _ _ p _ hcons
  have hxh : x = hh :=
    by
    have h1 := head_of_drop (Code.proj (0 : Fin 1)) d ![d] ((eval_proj_iff _ _ _).mpr rfl)
    have h2 : FFL.FirstOrder.Arithmetic.pi₁ (d - 1) = x := by
      rw [← hpd, hpv, add_sub_self, FFL.FirstOrder.Arithmetic.pi₁_pair]
    rw [h2] at h1
    exact (eval_unique hhead h1).symm
  have hxpos : 0 < x := by
    rw [hxh]
    rcases eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le hh) with h0 | hpos
    · exfalso
      rw [← h0, zero_add] at hzv
      rw [hzv] at hz
      exact absurd hz (_root_.lt_irrefl 1)
    · exact hpos
  have hTsrc :
    Semiformula.Evalb (Hj :> ![a - 1, q, j, Hj])
      (code (codeLift (codeLift (Code.proj (1 : Fin 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr
      ((eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl))
  have hlenlift :
    Semiformula.Evalb (j :> ![a - 1, q, j, Hj])
      (code (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))) :=
    length_of_drops _ Hj j ![a - 1, q, j, Hj] hTsrc hd0 hdn
  have hstepv :
    Semiformula.Evalb (a :> ![a - 1, q, j, Hj]) (code (codeSucc (Code.proj (0 : Fin 4)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨a - 1, (eval_proj_iff _ _ _).mpr rfl, hpred.symm⟩
  have hidx :
    Semiformula.Evalb (i :> ![a - 1, q, j, Hj])
      (code
        (codeSub (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))
          (codeSucc (Code.proj (0 : Fin 4))))) :=
    by
    have hji : j - a = i := sub_remove_left (by rw [← hai, add_comm])
    have := eval_codeSub _ _ j a ![a - 1, q, j, Hj] hlenlift hstepv
    rwa [hji] at this
  obtain ⟨gv, b₂, hgv, hb₂, hcase⟩ := eval_sub_args _ _ _ _ hx
  have hb₂v : b₂ = 1 :=
    by
    have : Semiformula.Evalb ((1 : M) :> ![a - 1, q, j, Hj]) (code (codeConst (n := 4) 1)) := by
      rw [eval_codeConst_iff]; simp
    exact eval_unique hb₂ this
  have hgvz : gv = z := by
    rcases hcase with heq | h0
    · rw [← heq, hb₂v, hxh, hzv]
    · exfalso
      rw [h0] at hxpos
      exact absurd hxpos (_root_.lt_irrefl 0)
  rw [hgvz] at hgv
  obtain ⟨l', i', hl', hi', hgetJ⟩ :=
    getAt_of_eval _ _ z ![a - 1, q, j, Hj] hgv (lt_trans (by simp) hz)
  have hl'v : l' = Hj := eval_unique hl' hTsrc
  have hi'v : i' = i := eval_unique hi' hidx
  rw [hl'v, hi'v] at hgetJ
  exact ⟨Hj, hHj, hgetJ⟩

/-!
### An entry below the last row survives one step forward -/

-- The history code contains the whole evaluator-cell code, so unifying it
-- against the recursion eliminators exceeds the default heartbeat limit.

/-- An entry of the history at `j` whose index is below `j` is still an entry of
the history at `j + 1`, with the same value.

Both history evaluations are supplied.  The drops of the extended history up to
the index come from a value of its length, which
`eval_codeListLength_exists_of_value` supplies and
`eval_codeEvaluatorHistory_length_unique` identifies with `j + 1`. -/
private theorem getAt_step_up [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (j i z Hj Hj1 : M)
    (hHj : Semiformula.Evalb ![Hj, j] (code codeEvaluatorHistory))
    (hHj1 : Semiformula.Evalb ![Hj1, j + 1] (code codeEvaluatorHistory)) (hij : i < j)
    (hget : GetAt Hj i z) : GetAt Hj1 i z := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
        -- the drops of the extended history up to index `i`
  have hself : Semiformula.Evalb (Hj1 :> ![Hj1]) (code (Code.proj (0 : Fin 1))) :=
    (eval_proj_iff _ _ _).mpr rfl
  obtain ⟨len1, hlen1⟩ :=
    eval_codeListLength_exists_of_value (Code.proj (0 : Fin 1)) Hj1 ![Hj1] hself
  have hlen1v : len1 = j + 1 :=
    eval_codeEvaluatorHistory_length_unique (j + 1) Hj1 len1 hHj1 hlen1
  obtain ⟨-, hdn1⟩ := drops_of_length _ Hj1 len1 ![Hj1] hself hlen1
  obtain ⟨e, -, he⟩ := hdn1 i (by rw [hlen1v]; exact lt_trans hij (lt_add_one j))
  have hdropJ1 := drop_prefix Hj1 i e he
  rw [codeEvaluatorHistory] at hHj1
  obtain ⟨H', hH', hstep⟩ := eval_codePrec_succ _ _ j Hj1 ![] hHj1
  rw [← codeEvaluatorHistory] at hH'
  have hH'j : H' = Hj :=
    eval_unique (show Semiformula.Evalb ![H', j] (code codeEvaluatorHistory) by simpa using hH')
      hHj
  rw [hH'j] at hstep
  rw [codeEvaluatorTableStep_eq, eval_codeBind_iff] at hstep
  obtain ⟨n', hlen', hsnoc⟩ := hstep
  obtain ⟨hd0, hdn⟩ :=
    drops_of_length _ Hj n' ![j, Hj] ((eval_proj_iff (1 : Fin 2) Hj ![j, Hj]).mpr rfl) hlen'
  have hn'j : n' = j :=
    eval_codeEvaluatorHistory_length_unique j Hj n' hHj
      (length_of_drops _ Hj n' ![Hj] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  rw [hn'j] at hd0 hdn hsnoc
  rw [historySnocCore_eq] at hsnoc
  obtain ⟨a, p, hai, hsa, hdi⟩ :=
    chain_match _ _ j Hj j Hj1 i hsnoc hdropJ1 i (le_of_lt hij) le_rfl
  have hapos : 0 < a :=
    by
    rcases
      eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le a) with
      h0 | hpos
    · exfalso
      rw [← h0, zero_add] at hai
      rw [hai] at hij
      exact absurd hij (_root_.lt_irrefl j)
    · exact hpos
  have hpred : a - 1 + 1 = a :=
    sub_add_self_of_le
      (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hapos)
  obtain ⟨q, -, hcons⟩ := eval_codePrec_succ _ _ (a - 1) p ![j, Hj] (by rw [hpred]; exact hsa)
  obtain ⟨x, l, hx, -, hpv⟩ := codeListCons_args _ _ p _ hcons
  have hTsrc :
    Semiformula.Evalb (Hj :> ![a - 1, q, j, Hj])
      (code (codeLift (codeLift (Code.proj (1 : Fin 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr
      ((eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl))
  have hlenlift :
    Semiformula.Evalb (j :> ![a - 1, q, j, Hj])
      (code (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))) :=
    length_of_drops _ Hj j ![a - 1, q, j, Hj] hTsrc hd0 hdn
  have hstepv :
    Semiformula.Evalb (a :> ![a - 1, q, j, Hj]) (code (codeSucc (Code.proj (0 : Fin 4)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨a - 1, (eval_proj_iff _ _ _).mpr rfl, hpred.symm⟩
  have hidx :
    Semiformula.Evalb (i :> ![a - 1, q, j, Hj])
      (code
        (codeSub (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))
          (codeSucc (Code.proj (0 : Fin 4))))) :=
    by
    have hji : j - a = i := sub_remove_left (by rw [← hai, add_comm])
    have := eval_codeSub _ _ j a ![a - 1, q, j, Hj] hlenlift hstepv
    rwa [hji] at this
  have hone : Semiformula.Evalb ((1 : M) :> ![a - 1, q, j, Hj]) (code (codeConst (n := 4) 1)) :=
    by rw [eval_codeConst_iff]; simp
  have hxz : x = z - 1 :=
    eval_unique hx
      (eval_codeSub _ (codeConst 1) z 1 ![a - 1, q, j, Hj]
        (eval_of_getAt _ _ Hj i z ![a - 1, q, j, Hj] hTsrc hidx hget) hone)
        -- the drop of the extended history at `i` is that cons
  obtain ⟨-, hh, -, -, -, hzv⟩ := hget
  refine
    ⟨p, FFL.FirstOrder.Arithmetic.pi₁ (p - 1), hdi,
      head_of_drop (Code.proj (0 : Fin 1)) p ![p] ((eval_proj_iff _ _ _).mpr rfl), ?_, ?_⟩
  · rw [hpv]
    exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
  · rw [hpv, add_sub_self, FFL.FirstOrder.Arithmetic.pi₁_pair,
      hxz, hzv, add_sub_self]

/-!
### Descending to the stage that first records the row -/

-- The history code contains the whole evaluator-cell code.

/-- An entry recorded at a later stage was already recorded at the first stage
past its index. -/
private theorem getAt_descend [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (m i z Hm : M)
    (hHm : Semiformula.Evalb ![Hm, m] (code codeEvaluatorHistory)) (hget : GetAt Hm i z)
    (hz : 1 < z) (hle : i + 1 ≤ m) :
    ∃ H : M, Semiformula.Evalb ![H, i + 1] (code codeEvaluatorHistory) ∧ GetAt H i z :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  have hHist :
    Σ-[1].Definable
      (fun w : Fin 5 → M => Semiformula.Evalb ![w 2, w 3] (code codeEvaluatorHistory)) :=
    by
    refine
      ((definable_code_graph (M := M) codeEvaluatorHistory).retractiont (f :=
            ![(#2 : ArithmeticSemiterm M 5), #3])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#2 : ArithmeticSemiterm M 5), #3] j)) = ![w 2, w 3] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
        simp
    rw [he]
  have hDrop :
    Σ-[1].Definable (fun w : Fin 5 → M => Semiformula.Evalb ![w 1, i, w 2] (code dropCore)) :=
    by
    refine
      ((definable_code_graph (M := M) dropCore).retractiont (f :=
            ![(#1 : ArithmeticSemiterm M 5), &i, #2])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#1 : ArithmeticSemiterm M 5), &i, #2] j)) =
        ![w 1, i, w 2] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ ?_ j1
        · simp
        · intro j2
          refine Fin.cases ?_ (fun j3 => Fin.elim0 j3) j2
          simp
    rw [he]
  have hHead :
    Σ-[1].Definable
      (fun w : Fin 5 → M =>
        Semiformula.Evalb ![w 0, w 1]
          (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1))))) :=
    by
    refine
      ((definable_code_graph (M := M)
                (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))).retractiont
            (f := ![(#0 : ArithmeticSemiterm M 5), #1])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#0 : ArithmeticSemiterm M 5), #1] j)) = ![w 0, w 1] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
        simp
    rw [he]
  have hdef :
    Σ-[1].DefinablePred
      (fun t : M =>
        i + 1 + t ≤ m →
          ∃ j H d hd : M,
            j + t = m ∧
              Semiformula.Evalb ![H, j] (code codeEvaluatorHistory) ∧
                Semiformula.Evalb ![d, i, H] (code dropCore) ∧
                  Semiformula.Evalb ![hd, d]
                      (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                    0 < d ∧ z = hd + 1) :=
    by
    have hbody :
      Σ-[1].Definable
        (fun w : Fin 5 → M =>
          w 3 + w 4 = m ∧
            Semiformula.Evalb ![w 2, w 3] (code codeEvaluatorHistory) ∧
              Semiformula.Evalb ![w 1, i, w 2] (code dropCore) ∧
                Semiformula.Evalb ![w 0, w 1]
                    (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                  0 < w 1 ∧ z = w 0 + 1) :=
      (by definability : Σ-[1].Definable (fun w : Fin 5 → M => w 3 + w 4 = m)).and
        (hHist.and (hDrop.and (hHead.and (by definability))))
    exact
      HierarchySymbol.Definable.imp (by definability)
        (HierarchySymbol.Definable.exs
          (HierarchySymbol.Definable.exs
            (HierarchySymbol.Definable.exs (HierarchySymbol.Definable.exs hbody))))
  have hall :
    ∀ t : M,
      i + 1 + t ≤ m →
        ∃ j H d hd : M,
          j + t = m ∧
            Semiformula.Evalb ![H, j] (code codeEvaluatorHistory) ∧
              Semiformula.Evalb ![d, i, H] (code dropCore) ∧
                Semiformula.Evalb ![hd, d]
                    (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                  0 < d ∧ z = hd + 1 :=
    by
    refine InductionOnHierarchy.succ_induction Σ 1 hdef ?_ ?_
    · intro _
      obtain ⟨d, hd, h1, h2, h3, h4⟩ := hget
      exact ⟨m, Hm, d, hd, add_zero m, hHm, h1, h2, h3, h4⟩
    · intro t IH ht
      have ht' : i + 1 + t ≤ m := le_trans (by rw [← add_assoc]; exact le_self_add) ht
      obtain ⟨j, H, d, hd, hjt, hH, h1, h2, h3, h4⟩ := IH ht'
      have hij2 : i + 1 + 1 ≤ j :=
        by
        have hh : i + 1 + (t + 1) ≤ j + t := by rw [hjt]; exact ht
        rw [← add_assoc, add_right_comm (i + 1) t 1] at hh
        exact le_of_add_le_add_right hh
      have hjpos : 0 < j := lt_of_lt_of_le (by simp) hij2
      have hpred : j - 1 + 1 = j :=
        sub_add_self_of_le (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hjpos)
      have hij : i < j - 1 :=
        by
        have : i + 1 ≤ j - 1 := by
          have h := hij2
          rw [← hpred] at h
          exact le_of_add_le_add_right h
        exact lt_of_lt_of_le (by simp) this
      obtain ⟨H', hH', hget'⟩ :=
        getAt_step_down (j - 1) i z H (by rw [hpred]; exact hH) hij ⟨d, hd, h1, h2, h3, h4⟩ hz
      obtain ⟨d', hd', g1, g2, g3, g4⟩ := hget'
      refine ⟨j - 1, H', d', hd', ?_, hH', g1, g2, g3, g4⟩
      calc
        j - 1 + (t + 1) = (j - 1 + 1) + t := by rw [add_comm t 1, ← add_assoc]
        _ = j + t := by rw [hpred]
        _ = m := hjt
  obtain ⟨j, H, d, hd, hjt, hH, h1, h2, h3, h4⟩ :=
    hall (m - (i + 1)) (by rw [add_tsub_self_of_le hle])
  have hjeq : j = i + 1 :=
    by
    have hb : i + 1 + (m - (i + 1)) = m := add_tsub_self_of_le hle
    exact add_right_cancel (hjt.trans hb.symm)
  rw [hjeq] at hH
  exact ⟨H, hH, d, hd, h1, h2, h3, h4⟩

/-!
### A positive lookup at an earlier stage -/

/-- The argument of a successfully evaluated first Cantor component has a
value. -/
private theorem unpair₁_arg [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (X : Code r) (z : M) (v : Fin r → M)
    (h : Semiformula.Evalb (z :> v) (code (codeUnpair₁ X))) :
    ∃ a : M, Semiformula.Evalb (a :> v) (code X) :=
  by
  rw [codeUnpair₁] at h
  obtain ⟨t, ht, -⟩ := eval_codeIfPos_cases _ _ _ _ _ h
  rw [eval_codeLt_iff] at ht
  obtain ⟨u, -, hu, -, -⟩ := ht
  obtain ⟨a, -, ha, -, -⟩ := eval_sub_args _ _ _ _ hu
  exact ⟨a, ha⟩

/-- An entry of the empty list is impossible. -/
private theorem getAt_nil_absurd [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (n z : M) (hg : GetAt 0 n z) : False := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  obtain ⟨d, -, hd, -, hdpos, -⟩ := hg
  have hdrop := drop_prefix 0 n d hd
  obtain ⟨z₀, hz₀⟩ :=
    hdrop 0 (FFL.FirstOrder.Arithmetic.zero_le n)
  have hz₀0 : z₀ = 0 := dropCore_zero 0 z₀ hz₀
  rw [hz₀0] at hz₀
  have :=
    drops_zero_from 0 0 n hz₀ hdrop n
      (FFL.FirstOrder.Arithmetic.zero_le n) le_rfl
  rw [eval_unique hd this] at hdpos
  exact absurd hdpos (_root_.lt_irrefl 0)

-- The history-evaluator code contains the whole evaluator-cell code.

/-- A successful lookup of an earlier row in the history at a later stage is
already a successful `codeHistoryEvaluator` evaluation at that earlier stage.

`𝐈𝐎𝐩𝐞𝐧` is listed only so that Foundation's `pair` elaborates in the
statement; it is implied by `𝐏𝐀`. -/
theorem eval_codeHistoryEvaluator_succ_of_prefix_lookup [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (s qCode n y : M) (q : ℕ)
    (hprefix :
      FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) <
        FFL.FirstOrder.Arithmetic.pair s qCode)
    (h :
      Semiformula.Evalb ((y + 1) :> ![s, qCode, n])
        (code
          (codeTableLookup codeEvaluatorHistoryBeforeCell
            (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)) (codeConst (n := 3) q)
            (Code.proj (2 : Fin 3))))) :
    Semiformula.Evalb ![y + 1, s, ((q : ℕ) : M), n] (code codeHistoryEvaluator) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hone : ∀ w : Fin 3 → M, Semiformula.Evalb ((1 : M) :> w) (code (codeConst (n := 3) 1)) :=
    by intro w; rw [eval_codeConst_iff]; simp
  rw [codeTableLookup_eq] at h
  obtain ⟨G2, b₀, hG2, hb₀, hcase₀⟩ := eval_sub_args _ _ _ _ h
  have hG2v : G2 = y + 1 + 1 := by
    rcases hcase₀ with heq | h0
    · rw [← heq, eval_unique hb₀ (hone _)]
    · exact absurd h0.symm (zero_ne_add_one y)
  rw [hG2v] at hG2
  obtain ⟨rowv, n₀, hrow, hn₀, hgetRow⟩ := getAt_of_eval _ _ _ _ hG2 (by simp)
  have hn₀v : n₀ = n := by
    simpa using eval_unique hn₀ ((eval_proj_iff (2 : Fin 3) n ![s, qCode, n]).mpr rfl)
  rw [hn₀v] at hgetRow
  obtain ⟨G1, b₁, hG1, hb₁, hcase₁⟩ := eval_sub_args _ _ _ _ hrow
  have hrowpos : 0 < rowv :=
    by
    rcases
      eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le rowv) with
      h0 | hp
    · exact
        absurd (getAt_nil_absurd n (y + 1 + 1) (by rw [← h0] at hgetRow; exact hgetRow))
          not_false
    · exact hp
  have hG1v : G1 = rowv + 1 := by
    rcases hcase₁ with heq | h0
    · rw [← heq, eval_unique hb₁ (hone _)]
    · exfalso
      rw [h0] at hrowpos
      exact absurd hrowpos (_root_.lt_irrefl 0)
  rw [hG1v] at hG1
  obtain ⟨Hm, i₀, hHm, hi₀, hgetHm⟩ :=
    getAt_of_eval _ _ _ _ hG1
      (by simp)
        -- the history is the one at the pair of `s` and `qCode`
  have hbefore := hHm
  rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff] at hbefore
  obtain ⟨w, hhist, hwi⟩ := hbefore
  have hpv := hwi 0
  simp only [Matrix.cons_val_zero] at hpv
  have hmv : w 0 = FFL.FirstOrder.Arithmetic.pair s qCode :=
    eval_unique hpv
      (eval_codePair _ _ s qCode ![s, qCode, n] ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_proj_iff _ _ _).mpr rfl))
  have hshape : w = (w 0) :> ![] := by
    funext j
    refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
    rfl
  rw [hshape, hmv] at hhist
  obtain ⟨fu, cqv, hfu, hcq⟩ := codePair_args _ _ _ _ hi₀
  obtain ⟨lenv, hlenv⟩ :=
    unpair₁_arg (codeListLength codeEvaluatorHistoryBeforeCell) fu ![s, qCode, n] hfu
  obtain ⟨hd0, hdn⟩ := drops_of_length _ Hm lenv ![s, qCode, n] hHm hlenv
  have hlenm : lenv = FFL.FirstOrder.Arithmetic.pair s qCode :=
    eval_codeEvaluatorHistory_length_unique _ Hm lenv hhist
      (length_of_drops _ Hm lenv ![Hm] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  have hi₀v :
    i₀ = FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    by
    have hfuv : fu = s :=
      by
      have hu := eval_unique hfu (eval_codeUnpair₁ _ lenv ![s, qCode, n] hlenv)
      rw [hu, hlenm, FFL.FirstOrder.Arithmetic.pi₁_pair]
    have hcqv : cqv = ((q : ℕ) : M) := by rw [eval_codeConst_iff] at hcq; exact hcq
    rw [eval_unique hi₀ (eval_codePair _ _ fu cqv ![s, qCode, n] hfu hcq), hfuv, hcqv]
  rw [hi₀v] at hgetHm
  obtain ⟨H, hH, hgetH⟩ :=
    getAt_descend _ _ _ Hm hhist hgetHm (by simpa using hrowpos)
      (FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hprefix)
        -- reassemble the history-evaluator evaluation at the earlier stage
  rw [codeHistoryEvaluator, codeTableLookup_eq]
  have hpair :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :>
        ![s, ((q : ℕ) : M), n])
      (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    eval_codePair _ _ s _ ![s, ((q : ℕ) : M), n] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  have htab :
    Semiformula.Evalb (H :> ![s, ((q : ℕ) : M), n])
      (code
        (codeEvaluatorHistory.comp
          ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])) :=
    by
    rw [eval_comp_iff]
    refine
      ⟨![FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) + 1], by
        simpa using hH, ?_⟩
    intro j
    refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
    simpa using (eval_codeSucc_iff _ _ _).mpr ⟨_, hpair, rfl⟩
  have hget1 := eval_of_getAt _ _ H _ (rowv + 1) ![s, ((q : ℕ) : M), n] htab hpair hgetH
  have hsub1 :=
    eval_codeSub _ (codeConst 1) (rowv + 1) 1 ![s, ((q : ℕ) : M), n] hget1
      (by rw [eval_codeConst_iff]; simp)
  rw [add_sub_self] at hsub1
  have hget2 :=
    eval_of_getAt _ (Code.proj (2 : Fin 3)) rowv n (y + 1 + 1) ![s, ((q : ℕ) : M), n] hsub1
      ((eval_proj_iff _ _ _).mpr rfl) hgetRow
  have hsub2 :=
    eval_codeSub _ (codeConst 1) (y + 1 + 1) 1 ![s, ((q : ℕ) : M), n] hget2
      (by rw [eval_codeConst_iff]; simp)
  rw [add_sub_self] at hsub2
  simpa using hsub2

/-!
### Totality of one evaluation row -/

/-- The row of a table has a value at any value of the table.

The row is primitive recursion on the fuel read from the table length, so
`eval_codePrec_exists_of_total` applies: the base is the empty list and the step
conses one evaluator cell onto the row built so far.  The step is constructed at
every recursion index and every predecessor row, the terminal index included,
because the bounded search inside `codePrec` evaluates its step there as well.

Only existence is asserted.  Nothing here decodes the row, and `table` is not
assumed to encode a well-formed table. -/
theorem eval_codeEvaluatorRow_exists_of_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ} (dtable : Code r)
    (table : M) (v : Fin r → M) (htable : Semiformula.Evalb (table :> v) (code dtable)) :
    ∃ row : M, Semiformula.Evalb (row :> v) (code (codeEvaluatorRow dtable)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨p, hp⟩ := eval_codeListLength_exists_of_value dtable table v htable
  have hbound := eval_codeUnpair₁ (codeListLength dtable) p v hp
  have hbase : ∃ z : M, Semiformula.Evalb (z :> v) (code (codeListNil (n := r))) :=
    ⟨0, (eval_zero_iff _ _).mpr rfl⟩
  have hstep :
    ∀ i : M,
      i ≤ FFL.FirstOrder.Arithmetic.pi₁ p →
        ∀ row : M,
          ∃ w : M,
            Semiformula.Evalb (w :> i :> row :> v)
              (code
                (codeListCons
                  (codeEvaluatorCell (codeLift (codeLift dtable))
                    (codeSub (codeUnpair₁ (codeListLength (codeLift (codeLift dtable))))
                      (codeSucc (Code.proj (0 : Fin (r + 2))))))
                  (Code.proj (1 : Fin (r + 2))))) :=
    by
    intro i _ row
    have htable₁ : Semiformula.Evalb (table :> row :> v) (code (codeLift dtable)) :=
      (eval_codeLift_iff dtable table row v).mpr htable
    have htable₂ :
      Semiformula.Evalb (table :> i :> row :> v) (code (codeLift (codeLift dtable))) :=
      (eval_codeLift_iff (codeLift dtable) table i (row :> v)).mpr htable₁
    obtain ⟨pi, hpi⟩ :=
      eval_codeListLength_exists_of_value (codeLift (codeLift dtable)) table (i :> row :> v)
        htable₂
    have hbi :=
      eval_codeUnpair₁ (codeListLength (codeLift (codeLift dtable))) pi (i :> row :> v) hpi
    have hidx : Semiformula.Evalb (i :> i :> row :> v) (code (Code.proj (0 : Fin (r + 2)))) :=
      (eval_proj_iff _ _ _).mpr rfl
    have hsucc :
      Semiformula.Evalb ((i + 1) :> i :> row :> v)
        (code (codeSucc (Code.proj (0 : Fin (r + 2))))) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨i, hidx, rfl⟩
    have hrev := eval_codeSub _ _ _ (i + 1) (i :> row :> v) hbi hsucc
    obtain ⟨c, hc⟩ :=
      eval_codeEvaluatorCell_exists_of_values (codeLift (codeLift dtable)) _ table _
        (i :> row :> v) htable₂ hrev
    have hrow : Semiformula.Evalb (row :> i :> row :> v) (code (Code.proj (1 : Fin (r + 2)))) :=
      (eval_proj_iff _ _ _).mpr (by simp)
    exact eval_codeListCons_exists_of_values _ _ c row (i :> row :> v) hc hrow
  obtain ⟨w, hw⟩ := eval_codePrec_exists_of_total _ _ _ v hbase hstep
  refine ⟨w, ?_⟩
  rw [codeEvaluatorRow_eq_bind, eval_codeBind_iff]
  exact ⟨_, hbound, hw⟩

/-- Extending a table by one row has a value at any value of the table.

The row has a value by `eval_codeEvaluatorRow_exists_of_value`, and appending it
has a value by `eval_codeListSnoc_exists_of_values`.  Only existence is
asserted: neither the table nor the row is decoded. -/
theorem eval_codeEvaluatorTableStep_exists_of_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ} (dtable : Code r)
    (table : M) (v : Fin r → M) (htable : Semiformula.Evalb (table :> v) (code dtable)) :
    ∃ table' : M, Semiformula.Evalb (table' :> v) (code (codeEvaluatorTableStep dtable)) :=
  by
  obtain ⟨row, hrow⟩ := eval_codeEvaluatorRow_exists_of_value dtable table v htable
  exact
    eval_codeListSnoc_exists_of_values dtable (codeEvaluatorRow dtable) table row v htable hrow

/-- The history has a value at every stage.

The history is `codePrec` with base `codeListNil` and step
`codeEvaluatorTableStep` applied to the projection onto the predecessor table,
so `eval_codePrec_exists_of_total` applies: the base has value `0`, and the step
has a value by `eval_codeEvaluatorTableStep_exists_of_value`.  The step is
constructed at every recursion index and every predecessor table, the terminal
index included, because the bounded search inside `codePrec` evaluates its step
there as well.

Only existence is asserted.  Nothing here decodes the history or any table in
it. -/
theorem eval_codeEvaluatorHistory_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (m : M) :
    ∃ H : M, Semiformula.Evalb ![H, m] (code codeEvaluatorHistory) :=
  by
  have hbase : ∃ z : M, Semiformula.Evalb (z :> ![]) (code (codeListNil (n := 0))) :=
    ⟨0, (eval_zero_iff _ _).mpr rfl⟩
  have hstep :
    ∀ i : M,
      i ≤ m →
        ∀ table : M,
          ∃ w : M,
            Semiformula.Evalb (w :> i :> table :> ![])
              (code (codeEvaluatorTableStep (Code.proj (1 : Fin 2)))) :=
    by
    intro i _ table
    exact
      eval_codeEvaluatorTableStep_exists_of_value (Code.proj (1 : Fin 2)) table
        (i :> table :> ![]) ((eval_proj_iff _ _ _).mpr (by simp))
  exact eval_codePrec_exists_of_total _ _ m ![] hbase hstep

/-!
### The history and cell arguments read before the cell -/

/-- The history one step before the cell has a value at every argument triple,
and that value is the history at the pair of the first two arguments.

`codeEvaluatorHistoryBeforeCell` is `codeEvaluatorHistory` composed with the
pair of the first two projections.  History totality,
`eval_codeEvaluatorHistory_exists`, gives the history a value `H` at the stage
`pair s qCode`, and `eval_codePair` gives the composed argument that value. -/
theorem eval_codeEvaluatorHistoryBeforeCell_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (s qCode u : M) :
    ∃ H : M,
      Semiformula.Evalb (H :> ![s, qCode, u]) (code codeEvaluatorHistoryBeforeCell) ∧
        Semiformula.Evalb ![H, FFL.FirstOrder.Arithmetic.pair s qCode]
          (code codeEvaluatorHistory) :=
  by
  obtain ⟨H, hH⟩ := eval_codeEvaluatorHistory_exists (FFL.FirstOrder.Arithmetic.pair s qCode)
  refine ⟨H, ?_, hH⟩
  have hpair :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, u])
      (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    eval_codePair _ _ s qCode ![s, qCode, u] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff]
  refine ⟨![FFL.FirstOrder.Arithmetic.pair s qCode], by simpa using hH, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  simpa using hpair

/-- The length of the history read before the cell is the pair of the first
two arguments.

The history has a value by `eval_codeEvaluatorHistoryBeforeCell_exists`, its
length has a value by `eval_codeListLength_exists_of_value`, and
`eval_codeEvaluatorHistory_length_unique` identifies that value with the stage
`pair s qCode`. -/
theorem eval_codeEvaluatorHistoryBeforeCell_length [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (s qCode u : M) :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, u])
      (code (codeListLength codeEvaluatorHistoryBeforeCell)) :=
  by
  obtain ⟨H, hbefore, hH⟩ := eval_codeEvaluatorHistoryBeforeCell_exists s qCode u
  obtain ⟨lenv, hlenv⟩ :=
    eval_codeListLength_exists_of_value codeEvaluatorHistoryBeforeCell H ![s, qCode, u] hbefore
  have hcongr :
    Semiformula.Evalb (lenv :> ![s, qCode, u])
        (code (codeListLength codeEvaluatorHistoryBeforeCell)) ↔
      Semiformula.Evalb (lenv :> ![H]) (code (codeListLength (Code.proj (0 : Fin 1)))) :=
    by
    refine eval_codeListLength_congr_at _ _ lenv ![s, qCode, u] ![H] ?_
    intro x
    constructor
    · intro hx
      have hxH : x = H := eval_unique hx hbefore
      rw [hxH]
      exact (eval_proj_iff _ _ _).mpr rfl
    · intro hx
      have hxH : x = H := by
        simpa using eval_unique hx ((eval_proj_iff (0 : Fin 1) H ![H]).mpr rfl)
      rw [hxH]
      exact hbefore
  have hlen1 : Semiformula.Evalb ![lenv, H] (code (codeListLength (Code.proj (0 : Fin 1)))) :=
    by simpa using hcongr.mp hlenv
  have hval : lenv = FFL.FirstOrder.Arithmetic.pair s qCode :=
    eval_codeEvaluatorHistory_length_unique _ H lenv hH hlen1
  rw [← hval]
  exact hlenv

/-- The fuel that the evaluator cell reads, the first component of the history
length, is the first argument. -/
theorem eval_codeEvaluatorCell_fuel [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u : M) :
    Semiformula.Evalb (s :> ![s, qCode, u])
      (code (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))) :=
  by
  have h :=
    eval_codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)
      (FFL.FirstOrder.Arithmetic.pair s qCode) ![s, qCode, u]
      (eval_codeEvaluatorHistoryBeforeCell_length s qCode u)
  rwa [FFL.FirstOrder.Arithmetic.pi₁_pair] at h

/-- The program index that the evaluator cell reads, the second component of
the history length, is the second argument. -/
theorem eval_codeEvaluatorCell_index [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u : M) :
    Semiformula.Evalb (qCode :> ![s, qCode, u])
      (code (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))) :=
  by
  have h :=
    eval_codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)
      (FFL.FirstOrder.Arithmetic.pair s qCode) ![s, qCode, u]
      (eval_codeEvaluatorHistoryBeforeCell_length s qCode u)
  rwa [FFL.FirstOrder.Arithmetic.pi₂_pair] at h

/-- The history evaluator has a value at every argument triple.

At `s, qCode, u` the three projections have values `s`, `qCode` and `u`, the
pair of the first two has value `pair s qCode` by `eval_codePair`, and its
successor has value `pair s qCode + 1`.  The history has a value `H` at that
stage by `eval_codeEvaluatorHistory_exists`, so the composed table argument of
`codeTableLookup` has value `H`, and the lookup has a value by
`eval_codeTableLookup_exists_of_values`.  `𝐈𝐎𝐩𝐞𝐧` is installed inside the proof
for `eval_codePair` and is derived from `𝐏𝐀` through `𝐈Σ 1`.

Only existence is asserted.  Nothing here decodes the history, the table, or
the program index. -/
theorem eval_codeHistoryEvaluator_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s qCode u : M) :
    ∃ z : M, Semiformula.Evalb ![z, s, qCode, u] (code codeHistoryEvaluator) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 :=
    models_of_subtheory (U := 𝐈Σ1) (models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance))
  have hs : Semiformula.Evalb (s :> ![s, qCode, u]) (code (Code.proj (0 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hq : Semiformula.Evalb (qCode :> ![s, qCode, u]) (code (Code.proj (1 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hu : Semiformula.Evalb (u :> ![s, qCode, u]) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hpair := eval_codePair _ _ s qCode ![s, qCode, u] hs hq
  have hsucc :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pair s qCode + 1) :> ![s, qCode, u])
      (code (codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3))))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨_, hpair, rfl⟩
  obtain ⟨H, hH⟩ :=
    eval_codeEvaluatorHistory_exists (FFL.FirstOrder.Arithmetic.pair s qCode + 1)
  have htab :
    Semiformula.Evalb (H :> ![s, qCode, u])
      (code
        (codeEvaluatorHistory.comp
          ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])) :=
    (eval_comp_iff _ _ _ _).mpr
      ⟨![FFL.FirstOrder.Arithmetic.pair s qCode + 1], hH, Fin.forall_fin_one.mpr hsucc⟩
  exact eval_codeTableLookup_exists_of_values _ _ _ _ H s qCode u ![s, qCode, u] htab hs hq hu

/-!
### The same lookup at a later stage -/

-- The history-evaluator code contains the whole evaluator-cell code.

/-- A successful `codeHistoryEvaluator` evaluation at `s, q, n` is a successful
lookup of the same row, with the fixed query `q`, in the history before the cell
at `s, qCode, n`, whenever the pair of `s` and `q` is below the pair of `s` and
`qCode`.

This is the converse of `eval_codeHistoryEvaluator_succ_of_prefix_lookup`.  The
row is an entry of the history one step past the pair of `s` and `q`.  An
induction on the stage, `InductionOnHierarchy.succ_induction` on a Sigma-one
condition, shows that it is an entry of the history at every later stage up to
the pair of `s` and `qCode`: `eval_codeEvaluatorHistory_exists` gives each next
history a value, and `getAt_step_up` preserves the entry.

`𝐈𝐎𝐩𝐞𝐧` is listed only so that Foundation's `pair` elaborates in the
statement; it is implied by `𝐏𝐀`. -/
private theorem history_ascent_definable :
    ∀ P C z : M,
      Σ-[1].DefinablePred
        (fun t : M =>
          P + 1 + t ≤ C →
            ∃ j H' d hd : M,
              P + 1 + t = j ∧
                Semiformula.Evalb ![H', j] (code codeEvaluatorHistory) ∧
                  Semiformula.Evalb ![d, P, H'] (code dropCore) ∧
                    Semiformula.Evalb ![hd, d]
                        (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                      0 < d ∧ z = hd + 1) :=
  by
  intro P C z
  have hHist :
    Σ-[1].Definable
      (fun w : Fin 5 → M => Semiformula.Evalb ![w 2, w 3] (code codeEvaluatorHistory)) :=
    by
    refine
      ((definable_code_graph (M := M) codeEvaluatorHistory).retractiont (f :=
            ![(#2 : ArithmeticSemiterm M 5), #3])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#2 : ArithmeticSemiterm M 5), #3] j)) = ![w 2, w 3] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
        simp
    rw [he]
  have hDrop :
    Σ-[1].Definable (fun w : Fin 5 → M => Semiformula.Evalb ![w 1, P, w 2] (code dropCore)) :=
    by
    refine
      ((definable_code_graph (M := M) dropCore).retractiont (f :=
            ![(#1 : ArithmeticSemiterm M 5), &P, #2])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#1 : ArithmeticSemiterm M 5), &P, #2] j)) =
        ![w 1, P, w 2] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ ?_ j1
        · simp
        · intro j2
          refine Fin.cases ?_ (fun j3 => Fin.elim0 j3) j2
          simp
    rw [he]
  have hHead :
    Σ-[1].Definable
      (fun w : Fin 5 → M =>
        Semiformula.Evalb ![w 0, w 1]
          (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1))))) :=
    by
    refine
      ((definable_code_graph (M := M)
                (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))).retractiont
            (f := ![(#0 : ArithmeticSemiterm M 5), #1])).of_iff
        ?_
    intro w
    have he :
      (fun j => Semiterm.val w id (![(#0 : ArithmeticSemiterm M 5), #1] j)) = ![w 0, w 1] :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j1
        refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
        simp
    rw [he]
  have hbody :
    Σ-[1].Definable
      (fun w : Fin 5 → M =>
        P + 1 + w 4 = w 3 ∧
          Semiformula.Evalb ![w 2, w 3] (code codeEvaluatorHistory) ∧
            Semiformula.Evalb ![w 1, P, w 2] (code dropCore) ∧
              Semiformula.Evalb ![w 0, w 1]
                  (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                0 < w 1 ∧ z = w 0 + 1) :=
    (by definability : Σ-[1].Definable (fun w : Fin 5 → M => P + 1 + w 4 = w 3)).and
      (hHist.and (hDrop.and (hHead.and (by definability))))
  exact
    HierarchySymbol.Definable.imp (by definability)
      (HierarchySymbol.Definable.exs
        (HierarchySymbol.Definable.exs
          (HierarchySymbol.Definable.exs (HierarchySymbol.Definable.exs hbody))))

theorem eval_prefix_lookup_succ_of_codeHistoryEvaluator [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (s qCode n y : M) (q : ℕ)
    (hprefix :
      FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) <
        FFL.FirstOrder.Arithmetic.pair s qCode)
    (h : Semiformula.Evalb ![y + 1, s, ((q : ℕ) : M), n] (code codeHistoryEvaluator)) :
    Semiformula.Evalb ((y + 1) :> ![s, qCode, n])
      (code
        (codeTableLookup codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)) (codeConst (n := 3) q)
          (Code.proj (2 : Fin 3)))) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- the Sigma-one condition of the ascent
  have hdef := history_ascent_definable (M := M)
  have hone : ∀ w : Fin 3 → M, Semiformula.Evalb ((1 : M) :> w) (code (codeConst (n := 3) 1)) :=
    by intro w; rw [eval_codeConst_iff]; simp
  have hpairQ :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :>
        ![s, ((q : ℕ) : M), n])
      (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    eval_codePair _ _ s _ ![s, ((q : ℕ) : M), n] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  rw [codeHistoryEvaluator, codeTableLookup_eq] at h
  obtain ⟨G2, b₀, hG2, hb₀, hcase₀⟩ := eval_sub_args _ _ _ _ h
  have hG2v : G2 = y + 1 + 1 := by
    rcases hcase₀ with heq | h0
    · rw [← heq, eval_unique hb₀ (hone _)]
    · exact absurd h0.symm (zero_ne_add_one y)
  rw [hG2v] at hG2
  obtain ⟨rowv, n₀, hrow, hn₀, hgetRow⟩ := getAt_of_eval _ _ _ _ hG2 (by simp)
  have hn₀v : n₀ = n := by
    simpa using eval_unique hn₀ ((eval_proj_iff (2 : Fin 3) n ![s, ((q : ℕ) : M), n]).mpr rfl)
  rw [hn₀v] at hgetRow
  obtain ⟨G1, b₁, hG1, hb₁, hcase₁⟩ := eval_sub_args _ _ _ _ hrow
  have hrowpos : 0 < rowv :=
    by
    rcases
      eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le rowv) with
      h0 | hp
    · exact
        absurd (getAt_nil_absurd n (y + 1 + 1) (by rw [← h0] at hgetRow; exact hgetRow))
          not_false
    · exact hp
  have hG1v : G1 = rowv + 1 := by
    rcases hcase₁ with heq | h0
    · rw [← heq, eval_unique hb₁ (hone _)]
    · exfalso
      rw [h0] at hrowpos
      exact absurd hrowpos (_root_.lt_irrefl 0)
  rw [hG1v] at hG1
  obtain ⟨H, i₀, hH, hi₀, hgetH⟩ := getAt_of_eval _ _ _ _ hG1 (by simp)
  have hi₀v :
    i₀ = FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    eval_unique hi₀ hpairQ
  rw [hi₀v] at hgetH
  rw [eval_comp_iff] at hH
  obtain ⟨w, hhist, hwi⟩ := hH
  have hsv := hwi 0
  simp only [Matrix.cons_val_zero] at hsv
  have hw0 :
    w 0 = FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) + 1 :=
    eval_unique hsv ((eval_codeSucc_iff _ _ _).mpr ⟨_, hpairQ, rfl⟩)
  have hshape : w = (w 0) :> ![] := by
    funext j
    refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
    rfl
  rw [hshape, hw0] at hhist
  generalize hPdef :
    FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) =
    P at hgetH hhist hprefix
  generalize hCdef : FFL.FirstOrder.Arithmetic.pair s qCode =
    C at hprefix
  have hall :
    ∀ t : M,
      P + 1 + t ≤ C →
        ∃ j H' d hd : M,
          P + 1 + t = j ∧
            Semiformula.Evalb ![H', j] (code codeEvaluatorHistory) ∧
              Semiformula.Evalb ![d, P, H'] (code dropCore) ∧
                Semiformula.Evalb ![hd, d]
                    (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                  0 < d ∧ rowv + 1 = hd + 1 :=
    by
    refine InductionOnHierarchy.succ_induction Σ 1 (hdef P C (rowv + 1)) ?_ ?_
    · intro _
      obtain ⟨d, hd, h1, h2, h3, h4⟩ := hgetH
      exact ⟨P + 1, H, d, hd, add_zero _, hhist, h1, h2, h3, h4⟩
    · intro t IH ht
      have ht' : P + 1 + t ≤ C := le_trans (by rw [← add_assoc]; exact le_self_add) ht
      obtain ⟨j, H', d, hd, hjt, hH', h1, h2, h3, h4⟩ := IH ht'
      obtain ⟨H'', hH''⟩ := eval_codeEvaluatorHistory_exists (j + 1)
      have hPj : P < j := by
        rw [← hjt]
        exact lt_of_lt_of_le (lt_add_one P) le_self_add
      obtain ⟨d', hd', g1, g2, g3, g4⟩ :=
        getAt_step_up j P (rowv + 1) H' H'' hH' hH'' hPj ⟨d, hd, h1, h2, h3, h4⟩
      refine ⟨j + 1, H'', d', hd', ?_, hH'', g1, g2, g3, g4⟩
      rw [← hjt]
      exact (add_assoc (P + 1) t 1).symm
  have hle : P + 1 ≤ C :=
    FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hprefix
  obtain ⟨j, Hm, d, hd, hjt, hHm, h1, h2, h3, h4⟩ :=
    hall (C - (P + 1)) (by rw [add_tsub_self_of_le hle])
  have hjC : j = C := by rw [← hjt, add_tsub_self_of_le hle]
  rw [hjC] at hHm
  have hgetHm : GetAt Hm P (rowv + 1) := ⟨d, hd, h1, h2, h3, h4⟩
  subst hPdef hCdef
  have hpairC :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, n])
      (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    eval_codePair _ _ s qCode ![s, qCode, n] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  have hbefore :
    Semiformula.Evalb (Hm :> ![s, qCode, n]) (code codeEvaluatorHistoryBeforeCell) :=
    by
    rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff]
    refine
      ⟨![FFL.FirstOrder.Arithmetic.pair s qCode], by
        simpa using hHm, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simpa using hpairC
  obtain ⟨lenv, hlenv⟩ :=
    eval_codeListLength_exists_of_value codeEvaluatorHistoryBeforeCell Hm ![s, qCode, n] hbefore
  obtain ⟨hd0, hdn⟩ := drops_of_length _ Hm lenv ![s, qCode, n] hbefore hlenv
  have hlenm : lenv = FFL.FirstOrder.Arithmetic.pair s qCode :=
    eval_codeEvaluatorHistory_length_unique _ Hm lenv hHm
      (length_of_drops _ Hm lenv ![Hm] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  have hfuel := eval_codeUnpair₁ _ lenv ![s, qCode, n] hlenv
  rw [hlenm, FFL.FirstOrder.Arithmetic.pi₁_pair] at hfuel
  have hkey :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :>
        ![s, qCode, n])
      (code
        (codePair (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst (n := 3) q))) :=
    eval_codePair _ _ s _ ![s, qCode, n] hfuel ((eval_codeConst_iff _ _ _).mpr rfl)
  have hget1 := eval_of_getAt _ _ Hm _ (rowv + 1) ![s, qCode, n] hbefore hkey hgetHm
  have hsub1 := eval_codeSub _ (codeConst 1) (rowv + 1) 1 ![s, qCode, n] hget1 (hone _)
  rw [add_sub_self] at hsub1
  have hget2 :=
    eval_of_getAt _ (Code.proj (2 : Fin 3)) rowv n (y + 1 + 1) ![s, qCode, n] hsub1
      ((eval_proj_iff _ _ _).mpr rfl) hgetRow
  have hsub2 := eval_codeSub _ (codeConst 1) (y + 1 + 1) 1 ![s, qCode, n] hget2 (hone _)
  rw [add_sub_self] at hsub2
  rw [codeTableLookup_eq]
  exact hsub2

/-!
### A successful lookup and a successful cell -/

-- The history-evaluator code contains the whole evaluator-cell code.

/-- A successful history lookup is exactly a successful evaluator cell in the
preceding history at an input strictly below the stage bound. -/
private theorem eval_codeHistoryEvaluator_succ_of_cell [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    (s qCode u y : M) (hus : u < s)
    (hcell : Semiformula.Evalb ![y + 1, s, qCode, u]
      (code (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))))) :
    Semiformula.Evalb ![y + 1, s, qCode, u] (code codeHistoryEvaluator) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐈Σ1 from inferInstance)
  have hone : ∀ w : Fin 3 → M, Semiformula.Evalb ((1 : M) :> w) (code (codeConst (n := 3) 1)) :=
    by
    intro w
    rw [eval_codeConst_iff]
    simp
      -- the stage `m`, the pair of `s` and `qCode`
  have hmP :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, u])
      (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    eval_codePair _ _ s qCode ![s, qCode, u] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  generalize hmdef : FFL.FirstOrder.Arithmetic.pair s qCode =
    m at hmP
  obtain ⟨H₀, hH₀⟩ := eval_codeEvaluatorHistory_exists m
  obtain ⟨H₁, hH₁⟩ :=
    eval_codeEvaluatorHistory_exists
      (m + 1)
        -- the drops of `H₁` up to index `m`
  have hself₁ : Semiformula.Evalb (H₁ :> ![H₁]) (code (Code.proj (0 : Fin 1))) :=
    (eval_proj_iff _ _ _).mpr rfl
  obtain ⟨len₁, hlen₁⟩ :=
    eval_codeListLength_exists_of_value (Code.proj (0 : Fin 1)) H₁ ![H₁] hself₁
  have hlen₁v : len₁ = m + 1 :=
    eval_codeEvaluatorHistory_length_unique (m + 1) H₁ len₁ hH₁ hlen₁
  obtain ⟨-, hdn₁⟩ := drops_of_length _ H₁ len₁ ![H₁] hself₁ hlen₁
  obtain ⟨e₁, -, he₁⟩ := hdn₁ m (by rw [hlen₁v]; exact lt_add_one m)
  have hdropT := drop_prefix H₁ m e₁ he₁
  have hH₁c := hH₁
  rw [codeEvaluatorHistory] at hH₁c
  obtain ⟨H', hH', hstep⟩ := eval_codePrec_succ _ _ m H₁ ![] hH₁c
  rw [← codeEvaluatorHistory] at hH'
  have hH'0 : H' = H₀ :=
    eval_unique (show Semiformula.Evalb ![H', m] (code codeEvaluatorHistory) by simpa using hH')
      hH₀
  rw [hH'0] at hstep
  rw [codeEvaluatorTableStep_eq, eval_codeBind_iff] at hstep
  obtain ⟨n', hlen', hsnoc⟩ := hstep
  obtain ⟨hd0, hdn⟩ :=
    drops_of_length _ H₀ n' ![m, H₀] ((eval_proj_iff (1 : Fin 2) H₀ ![m, H₀]).mpr rfl) hlen'
  have hn'm : n' = m :=
    eval_codeEvaluatorHistory_length_unique m H₀ n' hH₀
      (length_of_drops _ H₀ n' ![H₀] ((eval_proj_iff _ _ _).mpr rfl) hd0 hdn)
  rw [hn'm] at hd0 hdn hsnoc hlen'
  rw [historySnocCore_eq] at hsnoc
  obtain ⟨aT, pT, haT, hsaT, hdT⟩ := chain_match _ _ m H₀ m H₁ m hsnoc hdropT m le_rfl le_rfl
  have haT0 : aT = 0 := by
    have : aT + m = 0 + m := by rw [haT, zero_add]
    exact add_right_cancel this
  rw [haT0] at hsaT
  have hbase := eval_codePrec_zero _ _ pT ![m, H₀] hsaT
  obtain ⟨rowv, nilv, hrow, -, hpTv⟩ := codeListCons_args _ _ pT _ hbase
  have hgetH : GetAt H₁ m (rowv + 1) :=
    by
    refine
      ⟨pT, FFL.FirstOrder.Arithmetic.pi₁ (pT - 1), hdT,
        head_of_drop (Code.proj (0 : Fin 1)) pT ![pT] ((eval_proj_iff _ _ _).mpr rfl), ?_, ?_⟩
    · rw [hpTv]
      exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
    · rw [hpTv, add_sub_self, FFL.FirstOrder.Arithmetic.pi₁_pair]
        -- the row recursion, whose bound is `s`
  rw [codeEvaluatorRow_eq_bind, eval_codeBind_iff] at hrow
  obtain ⟨bnd, hbnd, hrowcore⟩ := hrow
  have hbnds : bnd = s :=
    by
    have :=
      eval_unique hbnd
        (eval_codeUnpair₁ (codeListLength (Code.proj (1 : Fin 2))) m ![m, H₀] hlen')
    rw [this, ← hmdef, FFL.FirstOrder.Arithmetic.pi₁_pair]
  rw [hbnds] at hrowcore
  have hselfR : Semiformula.Evalb (rowv :> ![rowv]) (code (Code.proj (0 : Fin 1))) :=
    (eval_proj_iff _ _ _).mpr rfl
  obtain ⟨lenR, hlenR⟩ :=
    eval_codeListLength_exists_of_value (Code.proj (0 : Fin 1)) rowv ![rowv] hselfR
  obtain ⟨hd0R, hdnR⟩ := drops_of_length _ rowv lenR ![rowv] hselfR hlenR
  have hulen : u < lenR := by
    by_contra hcon
    have hle : lenR ≤ u := not_lt.mp hcon
    have hdropR :
      ∀ t : M, t ≤ lenR → ∃ z : M, Semiformula.Evalb ![z, t, rowv] (code dropCore) :=
      by
      intro t ht
      rcases lt_or_eq_of_le ht with hlt | rfl
      · obtain ⟨e, -, he⟩ := hdnR t hlt
        exact ⟨e, he⟩
      · exact ⟨0, hd0R⟩
    have hls : lenR < s := lt_of_le_of_lt hle hus
    obtain ⟨a, p, ha, hsa, hdp⟩ :=
      chain_match _ _ m H₀ s rowv lenR hrowcore hdropR lenR (le_of_lt hls) le_rfl
    have hp0 : p = 0 := eval_unique hdp hd0R
    have hapos : 0 < a :=
      by
      rcases
        eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le a) with
        h0 | hpos
      · exfalso
        rw [← h0, zero_add] at ha
        rw [ha] at hls
        exact absurd hls (_root_.lt_irrefl s)
      · exact hpos
    have hpred : a - 1 + 1 = a :=
      sub_add_self_of_le
        (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp hapos)
    obtain ⟨q', -, hstep'⟩ :=
      eval_codePrec_succ _ _ (a - 1) p ![m, H₀] (by rw [hpred]; exact hsa)
    exact codeListCons_ne_zero _ _ p _ hstep' hp0
  obtain ⟨eR, -, heR⟩ := hdnR u hulen
  have hdropRow := drop_prefix rowv u eR heR
  obtain ⟨aR, pR, haR, hsaR, hdR⟩ :=
    chain_match _ _ m H₀ s rowv u hrowcore hdropRow u (le_of_lt hus) le_rfl
  have haRpos : 0 < aR :=
    by
    rcases
      eq_or_lt_of_le (FFL.FirstOrder.Arithmetic.zero_le aR) with
      h0 | hpos
    · exfalso
      rw [← h0, zero_add] at haR
      rw [haR] at hus
      exact absurd hus (_root_.lt_irrefl s)
    · exact hpos
  have hpredR : aR - 1 + 1 = aR :=
    sub_add_self_of_le
      (FFL.FirstOrder.Arithmetic.pos_iff_one_le.mp haRpos)
  obtain ⟨q, -, hstepR⟩ :=
    eval_codePrec_succ _ _ (aR - 1) pR ![m, H₀] (by rw [hpredR]; exact hsaR)
  obtain ⟨cellv, l, hcellv, -, hpRv⟩ := codeListCons_args _ _ pR _ hstepR
  have hTsrc :
    Semiformula.Evalb (H₀ :> ![aR - 1, q, m, H₀])
      (code (codeLift (codeLift (Code.proj (1 : Fin 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr
      ((eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl))
  have hTtgt : Semiformula.Evalb (H₀ :> ![s, qCode, u]) (code codeEvaluatorHistoryBeforeCell) :=
    by
    rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff]
    refine ⟨![m], by simpa using hH₀, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simpa using hmP
  have hlenlift :
    Semiformula.Evalb (m :> ![aR - 1, q, m, H₀])
      (code (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2)))))) :=
    length_of_drops _ H₀ m ![aR - 1, q, m, H₀] hTsrc hd0 hdn
  have hfuel :
    Semiformula.Evalb (s :> ![aR - 1, q, m, H₀])
      (code (codeUnpair₁ (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2))))))) :=
    by
    have hpi : FFL.FirstOrder.Arithmetic.pi₁ m = s := by
      rw [← hmdef, FFL.FirstOrder.Arithmetic.pi₁_pair]
    have hlift := eval_codeUnpair₁ _ m ![aR - 1, q, m, H₀] hlenlift
    rwa [hpi] at hlift
  have hstepv :
    Semiformula.Evalb (aR :> ![aR - 1, q, m, H₀]) (code (codeSucc (Code.proj (0 : Fin 4)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨aR - 1, (eval_proj_iff _ _ _).mpr rfl, hpredR.symm⟩
  have hNsrc :
    Semiformula.Evalb (u :> ![aR - 1, q, m, H₀])
      (code
        (codeSub (codeUnpair₁ (codeListLength (codeLift (codeLift (Code.proj (1 : Fin 2))))))
          (codeSucc (Code.proj (0 : Fin 4))))) :=
    by
    have hsu : s - aR = u := sub_remove_left (by rw [← haR, add_comm])
    have := eval_codeSub _ _ s aR ![aR - 1, q, m, H₀] hfuel hstepv
    rwa [hsu] at this
  have hNtgt : Semiformula.Evalb (u :> ![s, qCode, u]) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hcellsrc :=
    (eval_codeEvaluatorCell_congr_at _ _ _ _ (y + 1) ![aR - 1, q, m, H₀] ![s, qCode, u]
          (graph_iff _ _ H₀ _ _ hTsrc hTtgt) (graph_iff _ _ u _ _ hNsrc hNtgt)).mpr
      hcell
  have hcellvy : cellv = y + 1 := eval_unique hcellv hcellsrc
  have hgetRow : GetAt rowv u (y + 1 + 1) :=
    by
    refine
      ⟨pR, FFL.FirstOrder.Arithmetic.pi₁ (pR - 1), hdR,
        head_of_drop (Code.proj (0 : Fin 1)) pR ![pR] ((eval_proj_iff _ _ _).mpr rfl), ?_, ?_⟩
    · rw [hpRv]
      exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
    · rw [hpRv, add_sub_self, FFL.FirstOrder.Arithmetic.pi₁_pair,
        hcellvy]
        -- reassemble the two lookups in the history one step past `m`
  have htab :
    Semiformula.Evalb (H₁ :> ![s, qCode, u])
      (code
        (codeEvaluatorHistory.comp
          ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])) :=
    by
    rw [eval_comp_iff]
    refine ⟨![m + 1], by simpa using hH₁, ?_⟩
    intro j
    refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
    simpa using (eval_codeSucc_iff _ _ _).mpr ⟨_, hmP, rfl⟩
  have hget1 := eval_of_getAt _ _ H₁ m (rowv + 1) ![s, qCode, u] htab hmP hgetH
  have hsub1 := eval_codeSub _ (codeConst 1) (rowv + 1) 1 ![s, qCode, u] hget1 (hone _)
  rw [add_sub_self] at hsub1
  have hget2 :=
    eval_of_getAt _ (Code.proj (2 : Fin 3)) rowv u (y + 1 + 1) ![s, qCode, u] hsub1
      ((eval_proj_iff _ _ _).mpr rfl) hgetRow
  have hsub2 := eval_codeSub _ (codeConst 1) (y + 1 + 1) 1 ![s, qCode, u] hget2 (hone _)
  rw [add_sub_self] at hsub2
  rw [codeHistoryEvaluator, codeTableLookup_eq]
  exact hsub2

/-!
### A successful lookup in a history at an earlier row -/

-- The history-evaluator code contains the whole evaluator-cell code.

theorem eval_codeHistoryEvaluator_succ_iff_cell [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (s qCode u y : M) :
    Semiformula.Evalb ![y + 1, s, qCode, u]
        (FFL.FirstOrder.Arithmetic.code codeHistoryEvaluator) ↔
      u < s ∧
        Semiformula.Evalb ![y + 1, s, qCode, u]
          (FFL.FirstOrder.Arithmetic.code
            (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)))) :=
  by
  exact
    ⟨eval_codeHistoryEvaluator_succ_extract_cell_core s qCode u y, fun h =>
      eval_codeHistoryEvaluator_succ_of_cell s qCode u y h.1 h.2⟩

/-- **Earlier-row bridge.**  Let `H` be the value of `codeEvaluatorHistory` at a
row count `N`, and let the row `pair k q` of the standard index `q` lie below
`N`.  For codes `dtable`, `dk`, `dq`, `dn` whose values at `v` are `H`, `k`, the
numeral `q` and `u`, the table lookup succeeds with output `y + 1` exactly when
`codeHistoryEvaluator` succeeds with output `y + 1` at stage `k`, index `q`,
input `u`.

The stage `k` is arbitrary below the row bound; it need not be the stage that
produced `H`.  No certificate persistence is used: the forward direction
descends from `N` to `pair k q + 1` with `getAt_step_down`, and the reverse
direction ascends from `pair k q + 1` to `N` with `getAt_step_up`. -/
theorem eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ} (dtable dk dq dn : Code r) (v : Fin r → M) (N H k u y : M)
    (q : ℕ) (hH : Semiformula.Evalb ![H, N] (code codeEvaluatorHistory))
    (hrow : FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) < N)
    (htable : Semiformula.Evalb (H :> v) (code dtable))
    (hk : Semiformula.Evalb (k :> v) (code dk))
    (hq : Semiformula.Evalb (((q : ℕ) : M) :> v) (code dq))
    (hn : Semiformula.Evalb (u :> v) (code dn)) :
    Semiformula.Evalb ((y + 1) :> v) (code (codeTableLookup dtable dk dq dn)) ↔
      Semiformula.Evalb ![y + 1, k, ((q : ℕ) : M), u] (code codeHistoryEvaluator) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hone :
    ∀ {s : ℕ} (w : Fin s → M), Semiformula.Evalb ((1 : M) :> w) (code (codeConst (n := s) 1)) :=
    by intro s w; rw [eval_codeConst_iff]; simp
  have hkey :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) :> v)
      (code (codePair dk dq)) :=
    eval_codePair _ _ k _ v hk hq
  have hpairQ :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) :>
        ![k, ((q : ℕ) : M), u])
      (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    eval_codePair _ _ k _ ![k, ((q : ℕ) : M), u] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  constructor
  · -- the lookup in `H` gives the history evaluator at the earlier stage
    intro h
    rw [codeTableLookup_eq] at h
    obtain ⟨G2, b₀, hG2, hb₀, hcase₀⟩ := eval_sub_args _ _ _ _ h
    have hG2v : G2 = y + 1 + 1 := by
      rcases hcase₀ with heq | h0
      · rw [← heq, eval_unique hb₀ (hone _)]
      · exact absurd h0.symm (zero_ne_add_one y)
    rw [hG2v] at hG2
    obtain ⟨rowv, n₀, hrowc, hn₀, hgetRow⟩ := getAt_of_eval _ _ _ _ hG2 (by simp)
    have hn₀v : n₀ = u := eval_unique hn₀ hn
    rw [hn₀v] at hgetRow
    obtain ⟨G1, b₁, hG1, hb₁, hcase₁⟩ := eval_sub_args _ _ _ _ hrowc
    have hrowpos : 0 < rowv :=
      by
      rcases
        eq_or_lt_of_le
          (FFL.FirstOrder.Arithmetic.zero_le rowv) with
        h0 | hp
      · exact
          absurd (getAt_nil_absurd u (y + 1 + 1) (by rw [← h0] at hgetRow; exact hgetRow))
            not_false
      · exact hp
    have hG1v : G1 = rowv + 1 := by
      rcases hcase₁ with heq | h0
      · rw [← heq, eval_unique hb₁ (hone _)]
      · exfalso
        rw [h0] at hrowpos
        exact absurd hrowpos (_root_.lt_irrefl 0)
    rw [hG1v] at hG1
    obtain ⟨Hm, i₀, hHm, hi₀, hgetHm⟩ := getAt_of_eval _ _ _ _ hG1 (by simp)
    have hHmv : Hm = H := eval_unique hHm htable
    have hi₀v :
      i₀ = FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) :=
      eval_unique hi₀ hkey
    rw [hHmv, hi₀v] at hgetHm
    obtain ⟨H', hH', hgetH'⟩ :=
      getAt_descend _ _ _ H hH hgetHm (by simpa using hrowpos)
        (FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hrow)
          -- reassemble the history-evaluator evaluation at the earlier stage
    rw [codeHistoryEvaluator, codeTableLookup_eq]
    have htab :
      Semiformula.Evalb (H' :> ![k, ((q : ℕ) : M), u])
        (code
          (codeEvaluatorHistory.comp
            ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])) :=
      by
      rw [eval_comp_iff]
      refine
        ⟨![FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) + 1], by
          simpa using hH', ?_⟩
      intro j
      refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
      simpa using (eval_codeSucc_iff _ _ _).mpr ⟨_, hpairQ, rfl⟩
    have hget1 := eval_of_getAt _ _ H' _ (rowv + 1) ![k, ((q : ℕ) : M), u] htab hpairQ hgetH'
    have hsub1 :=
      eval_codeSub _ (codeConst 1) (rowv + 1) 1 ![k, ((q : ℕ) : M), u] hget1 (hone _)
    rw [add_sub_self] at hsub1
    have hget2 :=
      eval_of_getAt _ (Code.proj (2 : Fin 3)) rowv u (y + 1 + 1) ![k, ((q : ℕ) : M), u] hsub1
        ((eval_proj_iff _ _ _).mpr rfl) hgetRow
    have hsub2 :=
      eval_codeSub _ (codeConst 1) (y + 1 + 1) 1 ![k, ((q : ℕ) : M), u] hget2 (hone _)
    rw [add_sub_self] at hsub2
    simpa using hsub2
  · -- the history evaluator at the earlier stage gives the lookup in `H`
    intro h
    have hdef := history_ascent_definable (M := M)
    rw [codeHistoryEvaluator, codeTableLookup_eq] at h
    obtain ⟨G2, b₀, hG2, hb₀, hcase₀⟩ := eval_sub_args _ _ _ _ h
    have hG2v : G2 = y + 1 + 1 := by
      rcases hcase₀ with heq | h0
      · rw [← heq, eval_unique hb₀ (hone _)]
      · exact absurd h0.symm (zero_ne_add_one y)
    rw [hG2v] at hG2
    obtain ⟨rowv, n₀, hrowc, hn₀, hgetRow⟩ := getAt_of_eval _ _ _ _ hG2 (by simp)
    have hn₀v : n₀ = u := by
      simpa using eval_unique hn₀ ((eval_proj_iff (2 : Fin 3) u ![k, ((q : ℕ) : M), u]).mpr rfl)
    rw [hn₀v] at hgetRow
    obtain ⟨G1, b₁, hG1, hb₁, hcase₁⟩ := eval_sub_args _ _ _ _ hrowc
    have hrowpos : 0 < rowv :=
      by
      rcases
        eq_or_lt_of_le
          (FFL.FirstOrder.Arithmetic.zero_le rowv) with
        h0 | hp
      · exact
          absurd (getAt_nil_absurd u (y + 1 + 1) (by rw [← h0] at hgetRow; exact hgetRow))
            not_false
      · exact hp
    have hG1v : G1 = rowv + 1 := by
      rcases hcase₁ with heq | h0
      · rw [← heq, eval_unique hb₁ (hone _)]
      · exfalso
        rw [h0] at hrowpos
        exact absurd hrowpos (_root_.lt_irrefl 0)
    rw [hG1v] at hG1
    obtain ⟨H₀, i₀, hH₀, hi₀, hgetH₀⟩ := getAt_of_eval _ _ _ _ hG1 (by simp)
    have hi₀v :
      i₀ = FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) :=
      eval_unique hi₀ hpairQ
    rw [hi₀v] at hgetH₀
    rw [eval_comp_iff] at hH₀
    obtain ⟨w, hhist, hwi⟩ := hH₀
    have hsv := hwi 0
    simp only [Matrix.cons_val_zero] at hsv
    have hw0 :
      w 0 = FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) + 1 :=
      eval_unique hsv ((eval_codeSucc_iff _ _ _).mpr ⟨_, hpairQ, rfl⟩)
    have hshape : w = (w 0) :> ![] := by
      funext j
      refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
      rfl
    rw [hshape, hw0] at hhist
    generalize hPdef :
      FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) =
      P at hgetH₀ hhist hrow
    have hall :
      ∀ t : M,
        P + 1 + t ≤ N →
          ∃ j H' d hd : M,
            P + 1 + t = j ∧
              Semiformula.Evalb ![H', j] (code codeEvaluatorHistory) ∧
                Semiformula.Evalb ![d, P, H'] (code dropCore) ∧
                  Semiformula.Evalb ![hd, d]
                      (code (codeUnpair₁ (codeSub (Code.proj (0 : Fin 1)) (codeConst 1)))) ∧
                    0 < d ∧ rowv + 1 = hd + 1 :=
      by
      refine InductionOnHierarchy.succ_induction Σ 1 (hdef P N (rowv + 1)) ?_ ?_
      · intro _
        obtain ⟨d, hd, h1, h2, h3, h4⟩ := hgetH₀
        exact ⟨P + 1, H₀, d, hd, add_zero _, hhist, h1, h2, h3, h4⟩
      · intro t IH ht
        have ht' : P + 1 + t ≤ N := le_trans (by rw [← add_assoc]; exact le_self_add) ht
        obtain ⟨j, H', d, hd, hjt, hH', h1, h2, h3, h4⟩ := IH ht'
        obtain ⟨H'', hH''⟩ := eval_codeEvaluatorHistory_exists (j + 1)
        have hPj : P < j := by
          rw [← hjt]
          exact lt_of_lt_of_le (lt_add_one P) le_self_add
        obtain ⟨d', hd', g1, g2, g3, g4⟩ :=
          getAt_step_up j P (rowv + 1) H' H'' hH' hH'' hPj ⟨d, hd, h1, h2, h3, h4⟩
        refine ⟨j + 1, H'', d', hd', ?_, hH'', g1, g2, g3, g4⟩
        rw [← hjt]
        exact (add_assoc (P + 1) t 1).symm
    have hle : P + 1 ≤ N :=
      FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hrow
    obtain ⟨j, Hm, d, hd, hjt, hHm, h1, h2, h3, h4⟩ :=
      hall (N - (P + 1)) (by rw [add_tsub_self_of_le hle])
    have hjN : j = N := by rw [← hjt, add_tsub_self_of_le hle]
    rw [hjN] at hHm
    have hHmv : Hm = H := eval_unique hHm hH
    have hgetH : GetAt H P (rowv + 1) := by rw [← hHmv]; exact ⟨d, hd, h1, h2, h3, h4⟩
    subst hPdef
    have hget1 := eval_of_getAt _ _ H _ (rowv + 1) v htable hkey hgetH
    have hsub1 := eval_codeSub _ (codeConst 1) (rowv + 1) 1 v hget1 (hone _)
    rw [add_sub_self] at hsub1
    have hget2 := eval_of_getAt _ dn rowv u (y + 1 + 1) v hsub1 hn hgetRow
    have hsub2 := eval_codeSub _ (codeConst 1) (y + 1 + 1) 1 v hget2 (hone _)
    rw [add_sub_self] at hsub2
    rw [codeTableLookup_eq]
    exact hsub2

/-- **Input bound.**  Under the hypotheses of the earlier-row bridge, a
successful lookup forces the input below the earlier stage. -/
theorem input_lt_of_codeTableLookup_succ_of_history [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ}
    (dtable dk dq dn : Code r) (v : Fin r → M) (N H k u y : M) (q : ℕ)
    (hH : Semiformula.Evalb ![H, N] (code codeEvaluatorHistory))
    (hrow : FFL.FirstOrder.Arithmetic.pair k ((q : ℕ) : M) < N)
    (htable : Semiformula.Evalb (H :> v) (code dtable))
    (hk : Semiformula.Evalb (k :> v) (code dk))
    (hq : Semiformula.Evalb (((q : ℕ) : M) :> v) (code dq))
    (hn : Semiformula.Evalb (u :> v) (code dn))
    (h : Semiformula.Evalb ((y + 1) :> v) (code (codeTableLookup dtable dk dq dn))) : u < k :=
  ((eval_codeHistoryEvaluator_succ_iff_cell k ((q : ℕ) : M) u y).mp
      ((eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history dtable dk dq dn v N H k u
            y q hH hrow htable hk hq hn).mp
        h)).1

-- The history code contains the whole evaluator-cell code.

/-- **Predecessor-stage specialization.**  In the history before the cell at
`k + 1, q, w` (which holds the rows below `pair (k + 1) q`), the lookup at the
decremented stage read by the dispatcher, the program index read by the
dispatcher, and an input code `dn` with value `u` succeeds with output `y + 1`
exactly when `codeHistoryEvaluator` succeeds at `y + 1, k, q, u`. -/
theorem eval_predecessor_lookup_succ_iff_codeHistoryEvaluator [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (k w u y : M) (q : ℕ) (dn : Code 3)
    (hn : Semiformula.Evalb (u :> ![k + 1, ((q : ℕ) : M), w]) (code dn)) :
    Semiformula.Evalb ((y + 1) :> ![k + 1, ((q : ℕ) : M), w])
        (code
          (codeTableLookup codeEvaluatorHistoryBeforeCell
            (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
              (codeConst 1))
            (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) dn)) ↔
      Semiformula.Evalb ![y + 1, k, ((q : ℕ) : M), u] (code codeHistoryEvaluator) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨H, hbefore, hH⟩ := eval_codeEvaluatorHistoryBeforeCell_exists (k + 1) ((q : ℕ) : M) w
  have hone :
    Semiformula.Evalb ((1 : M) :> ![k + 1, ((q : ℕ) : M), w]) (code (codeConst (n := 3) 1)) :=
    by rw [eval_codeConst_iff]; simp
  have hk :
    Semiformula.Evalb (k :> ![k + 1, ((q : ℕ) : M), w])
      (code
        (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst 1))) :=
    by
    have h :=
      eval_codeSub _ (codeConst 1) (k + 1) 1 ![k + 1, ((q : ℕ) : M), w]
        (eval_codeEvaluatorCell_fuel (k + 1) ((q : ℕ) : M) w) hone
    rwa [add_sub_self] at h
  exact
    eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history _ _ _ dn
      ![k + 1, ((q : ℕ) : M), w] (FFL.FirstOrder.Arithmetic.pair (k + 1) ((q : ℕ) : M)) H k u y
      q hH (FFL.FirstOrder.Arithmetic.pair_lt_pair_left (lt_add_one k) _) hbefore hk
      (eval_codeEvaluatorCell_index (k + 1) ((q : ℕ) : M) w) hn

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
