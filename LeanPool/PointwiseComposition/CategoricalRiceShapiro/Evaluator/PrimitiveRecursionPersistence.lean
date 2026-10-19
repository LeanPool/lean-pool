/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Certificate
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.PersistenceInduction
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.PrimitiveRecursionStructuralBridges

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Tag-6 certificate persistence

Constructor number `6` is primitive recursion.  This file proves conditional
certificate persistence at a standard index `q` with `partrecCodeTag q = 6`:
for arbitrary model stages `s ≤ t`, an arbitrary input and an arbitrary output,
a certificate for `q` at stage `s` persists to stage `t`, conditional on the
same persistence at every standard index `p < q`.  The theory assumptions
throughout are `𝐏𝐀` and `𝐈𝐎𝐩𝐞𝐧`; the proofs obtain `𝐏𝐀⁻` from `𝐏𝐀` with
`models_of_subtheory`.

The full theorem is assembled from two subcases distinguished by the recursion
argument of the input, and from the internal stage induction of
`Evaluator.PersistenceInduction`.

Write `P_q(s)` for the fixed-stage predicate of `q` at a model stage `s`: every
certificate for `q` at stage `s`, on every input and every output, persists to
every stage `t ≥ s`.

`evalnCertificateFormula_natCode_persist_of_tag_six_zero` concerns an input of
the form `pair z 0`, whose recursion argument is zero.  It proves that the
certificate for `q` on that input persists from a stage `s` to every stage
`t ≥ s`, conditional on the same persistence for every standard index `p < q`,
whatever the constructor number of `p`.

`evalnCertificateFormula_natCode_persist_of_tag_six_succ_step` concerns an input
of the form `pair z (a + 1)`, whose recursion argument is a successor.  It
proves one step: a certificate at a stage `k + 1` persists to every stage
`t ≥ k + 1`, conditional on both `P_q(k)` and persistence for every standard
index `p < q`.  The two hypotheses govern disjoint lookups.  The predecessor
lookup has index `q`, and only `P_q(k)` governs it; the step-payload lookup has
index `partrecCodePayload₂ q < q`, and only the smaller-index hypothesis governs
it.  The theorem performs no induction on a model element.

The zero-argument proof derives the source history from the source certificate
and the source cell from the source history; the fuel `s` of that cell is
positive.  It re-encodes `q` as the canonical primitive-recursion index of its
decoded payloads, reads the constructor number `6` and the two payloads inside
the model, and proves that the cell value is the value of the primitive-
recursion branch.  By `eval_codePrecEvaluatorCell_succ_iff_of_zero`, at the
source stage the branch value is the value of the lookup of the base payload,
from which `eval_codeHistoryEvaluator_succ_of_prefix_lookup` derives a source
history of the base payload on `z`.  The induction hypothesis is applied once,
at `partrecCodePayload₁ q`.  At the target stage the reverse direction of the
same equivalence gives the branch its value; the target history value and
`eval_codeEvaluatorCell_exists_of_values` give the whole target cell a value,
and `eval_unique` identifies it with the branch value.  The target cell then
gives the target history and the target certificate.

The successor-argument proof follows the same outline through the cell and the
branch, but uses `eval_codePrecEvaluatorCell_succ_iff_of_succ`, whose forward
direction produces an intermediate value `x` together with the predecessor
lookup and the step-payload lookup.  The predecessor lookup at the source stage
becomes a history of `q` on `pair z a` at stage `k`, to which `P_q(k)` applies,
with `k ≤ t - 1` derived from `k + 1 ≤ t`; the general earlier-row bridge
`eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history` returns the
result to a lookup at the arbitrary target stage `t`, whose first environment
component is not a literal successor.  The same general bridge, instantiated on
the lifted four-place environment of the step branch, relates both step-payload
lookups to histories of `partrecCodePayload₂ q` on `pair z (pair a x)`, to which
the smaller-index hypothesis applies.  The reverse direction of the successor
equivalence, at the same `x`, gives the target branch its value, and the
remaining steps are those of the zero-argument proof.  No new public structural
bridge is required.

`evalnCertificateFormula_natCode_persist_of_tag_six_succ` assembles the complete
successor premise `P_q(k) → P_q(k + 1)` from the two subcases.  An arbitrary
input `u` is `pair (π₁ u) (π₂ u)` by `pair_unpair`, and its recursion argument
`π₂ u` is split into the zero and positive cases by the dichotomy
`0 < π₂ u ∨ 0 = π₂ u`; the zero case is the zero-argument theorem at source
stage `k + 1`, and the positive case is the one-step successor theorem at
`π₂ u - 1`, the only case that uses `P_q(k)`.

`evalnCertificateFormula_natCode_persist_of_tag_six` applies
`certificate_persistence_of_stage_induction` to that successor premise and to
the stage-zero premise `evalnCertificateFormula_natCode_persist_of_stage_zero`
of `Evaluator.PersistenceInduction`.  The induction on the stage is internal to
the model and belongs to that interface; no induction on a model element occurs
in this file.

The generic readings of the history, the fuel and the program index are the
public theorems of `Evaluator.HistoryEvaluation`; the fourteen private helpers
below are local to this file.

Scope:

* this file proves tag-6 certificate persistence for a standard index of
  constructor number `6`, at arbitrary model stages, inputs and outputs,
  conditional on persistence at every smaller standard index;
* that hypothesis is discharged only by the external induction on the standard
  index, which is not proved in the library;
* it proves no persistence case at constructor numbers `0`–`3` or `7`;
* it proves no persistence theorem for every standard index;
* it proves no theorem of Appendix B.
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

/-!
### Re-encoding and readings at a standard tag-6 index -/

/-- A standard tag-6 index, cast into the model, is the canonical
primitive-recursion index of its decoded payloads. -/
theorem tagSix_canonical_cast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (q : ℕ) (hq : partrecCodeTag q = 6) :
    ((q : ℕ) : M) =
      ((canonicalPartrecPrecIndex (partrecCodePayload₁ q) (partrecCodePayload₂ q) : ℕ) : M) :=
  by conv_lhs => rw [partrecCode_eq_canonicalPartrecPrecIndex_of_tag_six q hq]

/-- The constructor number `6`, read at a standard tag-6 index. -/
theorem tagSix_read_tag [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (hq : partrecCodeTag q = 6) (v : Fin r → M)
    (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb ((6 : M) :> v) (code (codePartrecTag d)) :=
  by
  rw [tagSix_canonical_cast (M := M) q hq] at hd
  exact
    eval_codePartrecTag_canonicalPartrecPrecIndex d (partrecCodePayload₁ q)
      (partrecCodePayload₂ q) v hd

/-- The base payload, read at a standard tag-6 index. -/
theorem tagSix_read_payload₁ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (hq : partrecCodeTag q = 6) (v : Fin r → M)
    (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₁ q : ℕ) : M) :> v) (code (codePartrecPayload₁ d)) :=
  by
  rw [tagSix_canonical_cast (M := M) q hq] at hd
  exact
    eval_codePartrecPayload₁_canonicalPartrecPrecIndex d (partrecCodePayload₁ q)
      (partrecCodePayload₂ q) v hd

/-- The step payload, read at a standard tag-6 index. -/
theorem tagSix_read_payload₂ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (hq : partrecCodeTag q = 6) (v : Fin r → M)
    (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₂ q : ℕ) : M) :> v) (code (codePartrecPayload₂ d)) :=
  by
  rw [tagSix_canonical_cast (M := M) q hq] at hd
  exact
    eval_codePartrecPayload₂_canonicalPartrecPrecIndex d (partrecCodePayload₁ q)
      (partrecCodePayload₂ q) v hd

/-!
### The constructor-6 branch of the eager dispatcher -/

/-- With positive fuel and a tag reading of `6`, the cell value is the value of
the primitive-recursion branch.  The first comparison of the dispatcher, with
`4`, and the second, with `5`, both fail, and the third, with `6`, succeeds. -/
theorem tagSix_prec_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r) (v : Fin r → M)
    (z k : M) (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hkpos : 0 < k)
    (htag :
      Semiformula.Evalb ((6 : M) :> v)
        (code (codePartrecTag (codeUnpair₂ (codeListLength dtable)))))
    (hcell : Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn))) :
    Semiformula.Evalb (z :> v)
      (code
        (codePrecEvaluatorCell dtable
          (codeSub (codeUnpair₁ (codeListLength dtable)) (codeConst 1))
          (codeUnpair₂ (codeListLength dtable))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) :=
  by
  have hconst :
    ∀ (m : ℕ) (x : M),
      Semiformula.Evalb (x :> v) (code (codeConst (n := r) m)) → x = ((m : ℕ) : M) :=
    fun m x hx => eval_unique hx (eval_codeConst m v)
  have hcast4 : ((4 : ℕ) : M) = (4 : M) := by simp
  have hcast5 : ((5 : ℕ) : M) = (5 : M) := by simp
  have hcast6 : ((6 : ℕ) : M) = (6 : M) := by simp
  have hne64 : ¬((6 : M) = ((4 : ℕ) : M)) :=
    by
    rw [hcast4]
    exact fun hc =>
      absurd hc.symm
        (_root_.ne_of_lt
          (by
            simpa [FFL.FirstOrder.Arithmetic.numeral_eq_natCast] using
              (FFL.FirstOrder.Arithmetic.numeral_lt_of_lt (M := M) (by omega : 4 < 6))))
  have hne65 : ¬((6 : M) = ((5 : ℕ) : M)) :=
    by
    rw [hcast5]
    exact fun hc =>
      absurd hc.symm
        (_root_.ne_of_lt
          (by
            simpa [FFL.FirstOrder.Arithmetic.numeral_eq_natCast] using
              (FFL.FirstOrder.Arithmetic.numeral_lt_of_lt (M := M) (by omega : 5 < 6))))
  simp only [codeEvaluatorCell] at hcell
  obtain ⟨kf, hkf, hkcase⟩ := eval_codeIfPos_cases _ _ _ z v hcell
  have hkfk : kf = k := eval_unique hkf hk
  rcases hkcase with ⟨-, hafterFuel⟩ | ⟨h0, -⟩
  swap
  · exact absurd (hkfk ▸ h0 : k = 0) (ne_of_gt hkpos)
  obtain ⟨e4, he4, h4case⟩ := eval_codeIfPos_cases _ _ _ z v hafterFuel
  rw [eval_codeEq_iff] at he4
  obtain ⟨a4, b4, ha4, hb4, hc4⟩ := he4
  have ha46 : a4 = (6 : M) := eval_unique ha4 htag
  have hb44 : b4 = ((4 : ℕ) : M) := hconst 4 b4 hb4
  have he40 : e4 = 0 := by
    rcases hc4 with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact absurd (by rw [← ha46, ← hb44]; exact heq) hne64
    · exact h0
  rcases h4case with ⟨hpos, -⟩ | ⟨-, hafterFour⟩
  · exact absurd (he40 ▸ hpos) (_root_.lt_irrefl 0)
  obtain ⟨e5, he5, h5case⟩ := eval_codeIfPos_cases _ _ _ z v hafterFour
  rw [eval_codeEq_iff] at he5
  obtain ⟨a5, b5, ha5, hb5, hc5⟩ := he5
  have ha56 : a5 = (6 : M) := eval_unique ha5 htag
  have hb55 : b5 = ((5 : ℕ) : M) := hconst 5 b5 hb5
  have he50 : e5 = 0 := by
    rcases hc5 with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact absurd (by rw [← ha56, ← hb55]; exact heq) hne65
    · exact h0
  rcases h5case with ⟨hpos, -⟩ | ⟨-, hafterFive⟩
  · exact absurd (he50 ▸ hpos) (_root_.lt_irrefl 0)
  obtain ⟨e6, he6, h6case⟩ := eval_codeIfPos_cases _ _ _ z v hafterFive
  rw [eval_codeEq_iff] at he6
  obtain ⟨a6, b6, ha6, hb6, hc6⟩ := he6
  have ha66 : a6 = (6 : M) := eval_unique ha6 htag
  have hb66 : b6 = ((6 : ℕ) : M) := hconst 6 b6 hb6
  have he61 : e6 = 1 := by
    rcases hc6 with ⟨-, h1⟩ | ⟨hne, -⟩
    · exact h1
    · exact absurd (by rw [ha66, hb66, hcast6]) hne
  rcases h6case with ⟨-, hprec⟩ | ⟨h0, -⟩
  · exact hprec
  · exact absurd (he61 ▸ h0 : (1 : M) = 0) _root_.one_ne_zero

/-!
### Fuel arithmetic and the readings the branch uses -/

/-- The dispatcher evaluates the branch at the decremented fuel `k - 1`; for
positive `k`, its successor, the key of the base lookup, is `k`. -/
theorem tagSix_succ_pred [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : M} (hk : 0 < k) : k - 1 + 1 = k :=
  FFL.FirstOrder.Arithmetic.sub_add_self_of_le
    (FFL.FirstOrder.Arithmetic.one_le_of_zero_lt k hk)

/-- The decremented fuel, as the dispatcher computes it. -/
theorem tagSix_decremented_fuel [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
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
theorem tagSix_base_key [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u : M) (hs : 0 < s) :
    Semiformula.Evalb (s :> ![s, qCode, u])
      (code
        (codeSucc
          (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst 1)))) :=
  by
  refine (eval_codeSucc_iff _ _ _).mpr ⟨s - 1, tagSix_decremented_fuel s qCode u, ?_⟩
  exact (tagSix_succ_pred hs).symm

/-!
### Relating the base lookup of the branch to the history bridges

The branch reads its table, key, query and argument through decoded codes; the
history bridges use the fuel key, a constant query and the argument itself.  The
four congruences below prove that the two forms have the same values. -/

/-- The branch table readings agree when the caller argument changes. -/
theorem tagSix_table_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode u z x : M) :
    Semiformula.Evalb (x :> ![s, qCode, u]) (code codeEvaluatorHistoryBeforeCell) ↔
      Semiformula.Evalb (x :> ![s, qCode, z]) (code codeEvaluatorHistoryBeforeCell) :=
  by
  have hpair :
    ∀ c : M,
      Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, c])
        (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    fun c =>
    eval_codePair _ _ s qCode ![s, qCode, c] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff, eval_comp_iff]
  constructor
  · rintro ⟨w, hw, hcomp⟩
    refine ⟨w, hw, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    have h0 := hcomp 0
    have : w 0 = FFL.FirstOrder.Arithmetic.pair s qCode := eval_unique h0 (hpair u)
    simpa [this] using hpair z
  · rintro ⟨w, hw, hcomp⟩
    refine ⟨w, hw, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    have h0 := hcomp 0
    have : w 0 = FFL.FirstOrder.Arithmetic.pair s qCode := eval_unique h0 (hpair z)
    simpa [this] using hpair u

/-- The branch key reading agrees with the source-stage constant. -/
theorem tagSix_key_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u z : M) (hs : 0 < s) (x : M) :
    Semiformula.Evalb (x :> ![s, qCode, u])
        (code
          (codeSucc
            (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
              (codeConst 1)))) ↔
      Semiformula.Evalb (x :> ![s, qCode, z])
        (code (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))) :=
  by
  constructor
  · intro hx
    have hxs : x = s := eval_unique hx (tagSix_base_key s qCode u hs)
    rw [hxs]
    exact eval_codeEvaluatorCell_fuel s qCode z
  · intro hx
    have hxs : x = s := eval_unique hx (eval_codeEvaluatorCell_fuel s qCode z)
    rw [hxs]
    exact tagSix_base_key s qCode u hs

/-- The decoded base-program query agrees with its constant index. -/
theorem tagSix_query_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s u z : M) (q : ℕ) (hq : partrecCodeTag q = 6) (x : M) :
    Semiformula.Evalb (x :> ![s, ((q : ℕ) : M), u])
        (code
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) ↔
      Semiformula.Evalb (x :> ![s, ((q : ℕ) : M), z])
        (code (codeConst (n := 3) (partrecCodePayload₁ q))) :=
  by
  have hleft := tagSix_read_payload₁ _ q hq _ (eval_codeEvaluatorCell_index s ((q : ℕ) : M) u)
  have hright :
    Semiformula.Evalb (((partrecCodePayload₁ q : ℕ) : M) :> ![s, ((q : ℕ) : M), z])
      (code (codeConst (n := 3) (partrecCodePayload₁ q))) :=
    eval_codeConst _ ![s, ((q : ℕ) : M), z]
  constructor
  · intro hx
    have hxv : x = ((partrecCodePayload₁ q : ℕ) : M) := eval_unique hx hleft
    rw [hxv]
    exact hright
  · intro hx
    have hxv : x = ((partrecCodePayload₁ q : ℕ) : M) := eval_unique hx hright
    rw [hxv]
    exact hleft

/-- The base-program argument agrees with the caller pair first component. -/
theorem tagSix_argument_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode z x : M) :
    Semiformula.Evalb (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeUnpair₁ (Code.proj (2 : Fin 3)))) ↔
      Semiformula.Evalb (x :> ![s, qCode, z]) (code (Code.proj (2 : Fin 3))) :=
  by
  have hleft :
    Semiformula.Evalb (z :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z 0])
      (code (codeUnpair₁ (Code.proj (2 : Fin 3)))) :=
    by
    have h :=
      eval_codeUnpair₁ (Code.proj (2 : Fin 3)) (FFL.FirstOrder.Arithmetic.pair z 0)
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z 0] ((eval_proj_iff _ _ _).mpr rfl)
    rwa [FFL.FirstOrder.Arithmetic.pi₁_pair] at h
  have hright : Semiformula.Evalb (z :> ![s, qCode, z]) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  constructor
  · intro hx
    have hxz : x = z := eval_unique hx hleft
    rw [hxz]
    exact hright
  · intro hx
    have hxz : x = z := eval_unique hx hright
    rw [hxz]
    exact hleft

/-!
### The zero-argument case -/

/-- **Tag-6 certificate persistence on a zero recursion argument.**  For a
standard index `q` of constructor number `6`, a certificate on an input
`pair z 0` persists from a stage `s` to any later stage `t`, given persistence
for every strictly smaller standard index.  This is the zero-argument
induction subcase only; the successor argument is not treated here. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_six_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (hq : partrecCodeTag q = 6)
    (ih :
      ∀ p : ℕ,
        p < q →
          ∀ s t u y : M,
            s ≤ t →
              Semiformula.Evalb ![s, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4) →
                Semiformula.Evalb ![t, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∀ s t z y : M,
      s ≤ t →
        Semiformula.Evalb
            ![s, ((q : ℕ) : M),
              FFL.FirstOrder.Arithmetic.pair z 0, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb
            ![t, ((q : ℕ) : M),
              FFL.FirstOrder.Arithmetic.pair z 0, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  intro s t z y hst source_certificate
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
  have source_history :=
    (evalnCertificateFormula_eval_history_iff s ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
      source_certificate
  obtain ⟨hus, source_cell⟩ :=
    (eval_codeHistoryEvaluator_succ_iff_cell s ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
      source_history
  have hs : (0 : M) < s :=
    lt_of_le_of_lt
      (FFL.FirstOrder.Arithmetic.zero_le
        (FFL.FirstOrder.Arithmetic.pair z 0))
      hus
  have ht : (0 : M) < t := lt_of_lt_of_le hs hst
  obtain ⟨Hs, hHs, -⟩ :=
    eval_codeEvaluatorHistoryBeforeCell_exists s ((q : ℕ) : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have hidx_s :=
    eval_codeEvaluatorCell_index s ((q : ℕ) : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have htag_s := tagSix_read_tag _ q hq _ hidx_s
  have hn_s :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z 0 :>
        ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have source_branch :=
    tagSix_prec_branch codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))
      ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0]
      (y + 1) s
      (eval_codeEvaluatorCell_fuel s ((q : ℕ) : M)
        (FFL.FirstOrder.Arithmetic.pair z 0))
      hs htag_s source_cell
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
  have source_base_lookup := source_equivalence.mp source_branch
  have source_lookup_fuelled :=
    (eval_codeTableLookup_congr_at codeEvaluatorHistoryBeforeCell
          (codeSucc
            (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
              (codeConst 1)))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeUnpair₁ (Code.proj (2 : Fin 3))) codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst (n := 3) (partrecCodePayload₁ q)) (Code.proj (2 : Fin 3)) (y + 1)
          ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0]
          ![s, ((q : ℕ) : M), z]
          (tagSix_table_congr s ((q : ℕ) : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) z)
          (tagSix_key_congr s ((q : ℕ) : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) z hs)
          (tagSix_query_congr s
            (FFL.FirstOrder.Arithmetic.pair z 0) z q hq)
          (tagSix_argument_congr s ((q : ℕ) : M) z)).mp
      source_base_lookup
  have payload₁_lt : partrecCodePayload₁ q < q := (partrecCodePayloads_lt_of_tag_six q hq).1
  have prefix_s :
    FFL.FirstOrder.Arithmetic.pair s
        ((partrecCodePayload₁ q : ℕ) : M) <
      FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast payload₁_lt)
        -- (8, continued) the source lookup gives a source history for the base payload on `z`
  have payload₁_history_at_s :=
    eval_codeHistoryEvaluator_succ_of_prefix_lookup s ((q : ℕ) : M) z y (partrecCodePayload₁ q)
      prefix_s source_lookup_fuelled
  have payload₁_certificate_at_s :=
    (evalnCertificateFormula_eval_history_iff s ((partrecCodePayload₁ q : ℕ) : M) z y).mpr
      payload₁_history_at_s
  have payload₁_certificate_at_t :=
    ih (partrecCodePayload₁ q) payload₁_lt s t z y hst payload₁_certificate_at_s
  have payload₁_history_at_t :=
    (evalnCertificateFormula_eval_history_iff t ((partrecCodePayload₁ q : ℕ) : M) z y).mp
      payload₁_certificate_at_t
  have prefix_t :
    FFL.FirstOrder.Arithmetic.pair t
        ((partrecCodePayload₁ q : ℕ) : M) <
      FFL.FirstOrder.Arithmetic.pair t ((q : ℕ) : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right t
      (by exact_mod_cast payload₁_lt)
  have target_lookup :=
    eval_prefix_lookup_succ_of_codeHistoryEvaluator t ((q : ℕ) : M) z y (partrecCodePayload₁ q)
      prefix_t payload₁_history_at_t
  obtain ⟨Ht, hHt, -⟩ :=
    eval_codeEvaluatorHistoryBeforeCell_exists t ((q : ℕ) : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have hidx_t :=
    eval_codeEvaluatorCell_index t ((q : ℕ) : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have htag_t := tagSix_read_tag _ q hq _ hidx_t
  have hn_t :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z 0 :>
        ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have target_lookup_decoded :=
    (eval_codeTableLookup_congr_at codeEvaluatorHistoryBeforeCell
          (codeSucc
            (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
              (codeConst 1)))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeUnpair₁ (Code.proj (2 : Fin 3))) codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst (n := 3) (partrecCodePayload₁ q)) (Code.proj (2 : Fin 3)) (y + 1)
          ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0]
          ![t, ((q : ℕ) : M), z]
          (tagSix_table_congr t ((q : ℕ) : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) z)
          (tagSix_key_congr t ((q : ℕ) : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) z ht)
          (tagSix_query_congr t
            (FFL.FirstOrder.Arithmetic.pair z 0) z q hq)
          (tagSix_argument_congr t ((q : ℕ) : M) z)).mpr
      target_lookup
  have target_equivalence :
    Semiformula.Evalb
        ((y + 1) :>
          ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      Semiformula.Evalb
        ((y + 1) :>
          ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeTableLookup dtable (codeSucc dk') dcf (codeUnpair₁ dn))) :=
    eval_codePrecEvaluatorCell_succ_iff_of_zero dtable dk' dq dcf dcg dn Ht (t - 1)
      ((q : ℕ) : M) ((partrecCodePayload₁ q : ℕ) : M) ((partrecCodePayload₂ q : ℕ) : M) z y
      ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0] hHt
      (tagSix_decremented_fuel t ((q : ℕ) : M)
        (FFL.FirstOrder.Arithmetic.pair z 0))
      hidx_t (tagSix_read_payload₁ _ q hq _ hidx_t) (tagSix_read_payload₂ _ q hq _ hidx_t) hn_t
  have target_branch := target_equivalence.mpr target_lookup_decoded
  obtain ⟨w, hw⟩ :=
    eval_codeEvaluatorCell_exists_of_values dtable dn Ht
      (FFL.FirstOrder.Arithmetic.pair z 0)
      ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0] hHt
      hn_t
  have target_cell :
    Semiformula.Evalb
      ((y + 1) :>
        ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
      (code (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)))) :=
    by
    have hbranch :=
      tagSix_prec_branch codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))
        ![t, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0] w
        t
        (eval_codeEvaluatorCell_fuel t ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z 0))
        ht htag_t hw
    have hwy : w = y + 1 := eval_unique hbranch target_branch
    rwa [hwy] at hw
  have target_history :=
    (eval_codeHistoryEvaluator_succ_iff_cell t ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z 0) y).mpr
      ⟨lt_of_lt_of_le hus hst, target_cell⟩
  exact
    (evalnCertificateFormula_eval_history_iff t ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z 0) y).mpr
      target_history

/-!
### The step argument of the successor branch -/

/-- The step lookup reads the argument `pair z (pair a x)` in the lifted
environment, where the intermediate value `x` is the new head. -/
theorem tagSix_step_argument [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode z a x : M) :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pair z (FFL.FirstOrder.Arithmetic.pair a x)) :>
        (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code
        (codePair (codeLift (codeUnpair₁ (Code.proj (2 : Fin 3))))
          (codePair (codeLift (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1)))
            (codeHead (n := 3))))) :=
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
  have hz :
    Semiformula.Evalb (z :> (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code (codeLift (codeUnpair₁ (Code.proj (2 : Fin 3))))) :=
    (eval_codeLift_iff _ _ _ _).mpr h1
  have ha :
    Semiformula.Evalb (a :> (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code (codeLift (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1)))) :=
    (eval_codeLift_iff _ _ _ _).mpr h3
  have hx :
    Semiformula.Evalb (x :> (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code (codeHead (n := 3))) :=
    (eval_codeHead_iff _ _).mpr rfl
  exact eval_codePair _ _ z _ _ hz (eval_codePair _ _ a x _ ha hx)

/-!
### The successor-argument one-step persistence theorem -/

-- The history code contains the whole evaluator-cell code.

/-- **Tag-6 certificate persistence on a successor recursion argument, one
step.**  For a standard index `q` of constructor number `6`, assume persistence
for every smaller standard index (`ih`) and the whole fixed-stage predicate at a
model stage `k` (`hpred`).  Then a certificate at stage `k + 1` on an input
`pair z (a + 1)` persists to every stage `t ≥ k + 1`.

The predecessor lookup has index `q`, so it is governed by `hpred`; the
step-payload lookup has index `partrecCodePayload₂ q < q`, so it is governed by
`ih`.  This theorem performs no induction and does not use
`certificate_persistence_of_stage_induction`. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_six_succ_step [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (hq : partrecCodeTag q = 6)
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
    ∀ t z a y : M,
      k + 1 ≤ t →
        Semiformula.Evalb
            ![k + 1, ((q : ℕ) : M),
              FFL.FirstOrder.Arithmetic.pair z (a + 1), y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb
            ![t, ((q : ℕ) : M),
              FFL.FirstOrder.Arithmetic.pair z (a + 1), y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  intro t z a y hkt source_certificate
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
  have source_history :=
    (evalnCertificateFormula_eval_history_iff (k + 1) ((q : ℕ) : M) u y).mp source_certificate
  obtain ⟨hus, source_cell⟩ :=
    (eval_codeHistoryEvaluator_succ_iff_cell (k + 1) ((q : ℕ) : M) u y).mp source_history
  have hs : (0 : M) < k + 1 :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le k)
      (lt_add_one k)
  have ht : (0 : M) < t := lt_of_lt_of_le hs hkt
  have hpredt : t - 1 + 1 = t := tagSix_succ_pred ht
  have htpred_lt : t - 1 < t :=
    by
    have h : t - 1 < t - 1 + 1 := lt_add_one (t - 1)
    rwa [hpredt] at h
  obtain ⟨Hs, hHs, hHistS⟩ := eval_codeEvaluatorHistoryBeforeCell_exists (k + 1) ((q : ℕ) : M) u
  have hidx_s := eval_codeEvaluatorCell_index (k + 1) ((q : ℕ) : M) u
  have htag_s := tagSix_read_tag _ q hq _ hidx_s
  have hn_s : Semiformula.Evalb (u :> ![k + 1, ((q : ℕ) : M), u]) (code dn) :=
    (eval_proj_iff _ _ _).mpr rfl
  have source_branch :=
    tagSix_prec_branch codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))
      ![k + 1, ((q : ℕ) : M), u] (y + 1) (k + 1)
      (eval_codeEvaluatorCell_fuel (k + 1) ((q : ℕ) : M) u) hs htag_s source_cell
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
  obtain ⟨x, source_pred_lookup, source_step_lookup⟩ := source_equivalence.mp source_branch
  obtain ⟨Ht, hHt, hHistT⟩ := eval_codeEvaluatorHistoryBeforeCell_exists t ((q : ℕ) : M) u
  have hidx_t := eval_codeEvaluatorCell_index t ((q : ℕ) : M) u
  have htag_t := tagSix_read_tag _ q hq _ hidx_t
  have hn_t : Semiformula.Evalb (u :> ![t, ((q : ℕ) : M), u]) (code dn) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hist_pred_src :
    Semiformula.Evalb
      ![x + 1, k, ((q : ℕ) : M),
        FFL.FirstOrder.Arithmetic.pair z a]
      (code codeHistoryEvaluator) :=
    (eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator k z a x q).mp source_pred_lookup
  have cert_pred_src :=
    (evalnCertificateFormula_eval_history_iff k ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z a) x).mpr
      hist_pred_src
  have hk_le : k ≤ t - 1 :=
    by
    have h : k + 1 ≤ t - 1 + 1 := by rw [hpredt]; exact hkt
    exact le_of_add_le_add_right h
  have cert_pred_tgt :=
    hpred (t - 1) (FFL.FirstOrder.Arithmetic.pair z a) x hk_le
      cert_pred_src
  have hist_pred_tgt :=
    (evalnCertificateFormula_eval_history_iff (t - 1) ((q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z a) x).mp
      cert_pred_tgt
  have target_pred_lookup :
    Semiformula.Evalb ((x + 1) :> ![t, ((q : ℕ) : M), u])
      (code
        (codeTableLookup dtable dk' dq
          (codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1))))) :=
    (eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history dtable dk' dq _
          ![t, ((q : ℕ) : M), u]
          (FFL.FirstOrder.Arithmetic.pair t ((q : ℕ) : M)) Ht
          (t - 1) (FFL.FirstOrder.Arithmetic.pair z a) x q hHistT
          (FFL.FirstOrder.Arithmetic.pair_lt_pair_left htpred_lt
            _)
          hHt (tagSix_decremented_fuel t ((q : ℕ) : M) u) hidx_t
          (eval_prec_predecessor_argument t ((q : ℕ) : M) z a)).mpr
      hist_pred_tgt
  have hpayload₂_lt : partrecCodePayload₂ q < q := (partrecCodePayloads_lt_of_tag_six q hq).2
  have hrow_step :
    ∀ s : M,
      FFL.FirstOrder.Arithmetic.pair s
          ((partrecCodePayload₂ q : ℕ) : M) <
        FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    fun s =>
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast hpayload₂_lt)
  have hstep_bridge :
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
  have hist_step_src := (hstep_bridge (k + 1) hs Hs hHs hHistS).mp source_step_lookup
  have cert_step_src :=
    (evalnCertificateFormula_eval_history_iff (k + 1) ((partrecCodePayload₂ q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z
            (FFL.FirstOrder.Arithmetic.pair a x))
          y).mpr
      hist_step_src
  have cert_step_tgt :=
    ih (partrecCodePayload₂ q) hpayload₂_lt (k + 1) t
      (FFL.FirstOrder.Arithmetic.pair z
        (FFL.FirstOrder.Arithmetic.pair a x))
      y hkt cert_step_src
  have hist_step_tgt :=
    (evalnCertificateFormula_eval_history_iff t ((partrecCodePayload₂ q : ℕ) : M)
          (FFL.FirstOrder.Arithmetic.pair z
            (FFL.FirstOrder.Arithmetic.pair a x))
          y).mp
      cert_step_tgt
  have target_step_lookup := (hstep_bridge t ht Ht hHt hHistT).mpr hist_step_tgt
  have target_equivalence :
    Semiformula.Evalb ((y + 1) :> ![t, ((q : ℕ) : M), u])
        (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      ∃ x' : M,
        Semiformula.Evalb ((x' + 1) :> ![t, ((q : ℕ) : M), u])
            (code
              (codeTableLookup dtable dk' dq
                (codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1))))) ∧
          Semiformula.Evalb ((y + 1) :> x' :> ![t, ((q : ℕ) : M), u])
            (code
              (codeTableLookup (codeLift dtable) (codeLift (codeSucc dk')) (codeLift dcg)
                (codePair (codeLift (codeUnpair₁ dn))
                  (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1)))
                    (codeHead (n := 3)))))) :=
    eval_codePrecEvaluatorCell_succ_iff_of_succ dtable dk' dq dcf dcg dn Ht (t - 1)
      ((q : ℕ) : M) ((partrecCodePayload₁ q : ℕ) : M) ((partrecCodePayload₂ q : ℕ) : M) z a y
      ![t, ((q : ℕ) : M), u] hHt (tagSix_decremented_fuel t ((q : ℕ) : M) u) hidx_t
      (tagSix_read_payload₁ _ q hq _ hidx_t) (tagSix_read_payload₂ _ q hq _ hidx_t) hn_t
  have target_branch :=
    target_equivalence.mpr
      ⟨x, target_pred_lookup, target_step_lookup⟩
        -- (8) the whole target cell has a value, and it is the branch value
  obtain ⟨w, hw⟩ :=
    eval_codeEvaluatorCell_exists_of_values dtable dn Ht u ![t, ((q : ℕ) : M), u] hHt hn_t
  have target_cell :
    Semiformula.Evalb ((y + 1) :> ![t, ((q : ℕ) : M), u])
      (code (codeEvaluatorCell codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3)))) :=
    by
    have hbranch :=
      tagSix_prec_branch codeEvaluatorHistoryBeforeCell (Code.proj (2 : Fin 3))
        ![t, ((q : ℕ) : M), u] w t (eval_codeEvaluatorCell_fuel t ((q : ℕ) : M) u) ht htag_t hw
    have hwy : w = y + 1 := eval_unique hbranch target_branch
    rwa [hwy] at hw
  have target_history :=
    (eval_codeHistoryEvaluator_succ_iff_cell t ((q : ℕ) : M) u y).mpr
      ⟨lt_of_lt_of_le hus hkt, target_cell⟩
  exact (evalnCertificateFormula_eval_history_iff t ((q : ℕ) : M) u y).mpr target_history

/-!
### The complete successor premise over arbitrary inputs -/

/-- **The complete successor premise at constructor number `6`.**  Assume
persistence at every standard index `p < q` and the whole fixed-stage predicate
of `q` at a model stage `k`.  Then the fixed-stage predicate of `q` holds at
`k + 1`, over arbitrary inputs.

The arbitrary input `u` is decomposed by `pair_unpair` into
`pair (π₁ u) (π₂ u)`, and the recursion argument `π₂ u` is split into its zero
and positive cases by the ordered-semiring dichotomy `0 < π₂ u ∨ 0 = π₂ u`.  The
zero case is the zero-argument theorem above, at source stage `k + 1`; the
positive case is the one-step successor theorem above, at `π₂ u - 1`, and is the
only case that uses the supplied predicate at `k`.  The proof performs no
induction; that dichotomy is its only split. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_six_succ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (hq : partrecCodeTag q = 6)
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
            (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  intro t u y hkt source_certificate
  obtain ⟨z, b, rfl⟩ :
    ∃ z b : M, u = FFL.FirstOrder.Arithmetic.pair z b :=
    ⟨FFL.FirstOrder.Arithmetic.pi₁ u,
      FFL.FirstOrder.Arithmetic.pi₂ u,
      (FFL.FirstOrder.Arithmetic.pair_unpair u).symm⟩
      -- the recursion argument is zero or positive
  rcases (FFL.FirstOrder.Arithmetic.zero_le b).lt_or_eq with hb |
    hb
  · -- positive: `b = (b - 1) + 1`, and the one-step successor theorem applies
    obtain ⟨a, rfl⟩ : ∃ a : M, b = a + 1 := ⟨b - 1, (tagSix_succ_pred hb).symm⟩
    exact
      evalnCertificateFormula_natCode_persist_of_tag_six_succ_step q hq ih k hpred t z a y hkt
        source_certificate
  · -- zero: the zero-argument theorem applies, from source stage `k + 1`
    subst hb
    exact
      evalnCertificateFormula_natCode_persist_of_tag_six_zero q hq ih (k + 1) t z y hkt
        source_certificate

/-!
### Full conditional tag-6 persistence -/

/-- **Tag-6 certificate persistence.**  For a standard index `q` of constructor
number `6`, a certificate persists from every stage `s` to every stage `t ≥ s`,
on arbitrary input and output, conditional on persistence at every standard
index `p < q`.  The internal induction on the stage is
`certificate_persistence_of_stage_induction`; this theorem supplies its two
premises, the stage-zero premise of `Evaluator.PersistenceInduction` and the
complete successor premise above, and does not reproduce the induction. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_six [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (q : ℕ) (hq : partrecCodeTag q = 6)
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
    (fun k hpred => evalnCertificateFormula_natCode_persist_of_tag_six_succ q hq ih k hpred)

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
