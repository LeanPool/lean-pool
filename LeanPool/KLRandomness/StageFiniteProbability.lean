/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineCodePrefix
public import LeanPool.KLRandomness.PoolAdviceComputable
public import LeanPool.KLRandomness.PoolAdviceMeasure
public import Mathlib.Probability.ConditionalProbability

/-!
# Exact rational integration under finitely many affine constraints

The old stage is represented by a finite list of ordinary affine codes. At any
prefix depth covering their widths, conditioning is an exact ratio of two
finite rational sums. The same algorithm works when the codes themselves vary;
in particular it can be used to compare all syndromes of a proposed new block.

The identities include inconsistent constraints (both the conditional measure
and the rational quotient then vanish). Positivity is needed only when the law
is subsequently used as a probability measure.
-/

@[expose] public section

namespace Klr.StageFiniteProbability

open MeasureTheory ProbabilityTheory SparseSearch RationalComputability

/-- The actual simultaneous event represented by a finite list of codes. -/
def event (cs : List AffineCode.Data) : Set Cantor :=
  {X | ∀ c ∈ cs, X ∈ AffineCode.event c}

@[simp] theorem event_nil : event [] = Set.univ := by ext X; simp [event]

@[simp] theorem event_cons (c : AffineCode.Data) (cs : List AffineCode.Data) :
    event (c :: cs) = AffineCode.event c ∩ event cs := by
  ext X
  simp [event]

theorem measurableSet_event (cs : List AffineCode.Data) : MeasurableSet (event cs) := by
  induction cs with
  | nil => simp
  | cons c cs ih => simpa only [event_cons] using (AffineCode.measurableSet_event c).inter ih

/-- The finite-stage law, with all previous affine equations in the header. -/
noncomputable def law (cs : List AffineCode.Data) : Measure Cantor :=
  cond fairCoin (event cs)

/-- Check all old equations on one input prefix. -/
def accepts (cs : List AffineCode.Data) (s : List Bool) : Bool :=
  cs.all (fun c => AffineCode.accepts c s)

theorem computable_accepts : Computable₂ accepts := by
  exact computable_list_all Computable.fst
    (AffineCode.computable_accepts.comp Computable.snd
      (Computable.snd.comp Computable.fst))

/-- Covering a code's width is enough; extra input bits do not affect its event. -/
theorem accepts_code_inputPrefix (c : AffineCode.Data) (n : ℕ)
    (hn : AffineCode.width c ≤ n) (X : Cantor) :
    AffineCode.accepts c (ScanRule.inputPrefix X n) = true ↔ X ∈ AffineCode.event c := by
  constructor
  · intro h
    exact AffineCode.cylinder_subset_event h (ScanRule.mem_cylinder_inputPrefix X n)
  · intro h
    apply (AffineCode.accepts_eq_true _ _).mpr
    refine ⟨by simpa using hn, ?_⟩
    intro i hi
    rw [← (AffineCode.mem_event_iff c X).mp h i hi]
    apply AffineCode.parity_congr
    intro k hk
    dsimp only
    rw [ScanRule.getD_inputPrefix X (hk.trans_le hn)]

theorem accepts_inputPrefix (cs : List AffineCode.Data) (n : ℕ)
    (hn : ∀ c ∈ cs, AffineCode.width c ≤ n) (X : Cantor) :
    accepts cs (ScanRule.inputPrefix X n) = true ↔ X ∈ event cs := by
  simp only [accepts, List.all_eq_true, event, Set.mem_ofPred_eq]
  exact forall₂_congr fun c hc => accepts_code_inputPrefix c n (hn c hc) X

/-- Finite conditional expectation, computed with exact rational arithmetic. -/
def expectation (cs : List AffineCode.Data) (n : ℕ) (f : List Bool → ℚ) : ℚ :=
  PoolAdvice.average n (fun s => if accepts cs s then f s else 0) /
    PoolAdvice.average n (fun s => if accepts cs s then 1 else 0)

/-- The finite ratio is uniformly computable in the old constraints, depth,
and every additional parameter of a computable rational integrand. -/
theorem computable_expectation {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {n : α → ℕ} {f : α → List Bool → ℚ}
    (hcs : Computable cs) (hn : Computable n) (hf : Computable₂ f) :
    Computable (fun a => expectation (cs a) (n a) (f a)) := by
  have ha := computable_accepts.comp (hcs.comp Computable.fst) Computable.snd
  have hnum := PoolAdvice.computable_average (f := fun a s =>
    _root_.cond (accepts (cs a) s) (f a s) (0 : ℚ)) hn
    (Computable.cond ha hf (Computable.const (0 : ℚ)))
  have hden := PoolAdvice.computable_average (f := fun a s =>
    _root_.cond (accepts (cs a) s) (1 : ℚ) 0) hn
    (Computable.cond ha (Computable.const (1 : ℚ)) (Computable.const 0))
  exact (primrec_rat_div.to_comp.comp hnum hden).of_eq fun _ => by
    simp only [expectation, Bool.cond_eq_ite]

theorem denominator_eq_measureReal (cs : List AffineCode.Data) (n : ℕ)
    (hn : ∀ c ∈ cs, AffineCode.width c ≤ n) :
    (PoolAdvice.average n (fun s => if accepts cs s then (1 : ℚ) else 0) : ℝ) =
      fairCoin.real (event cs) := by
  rw [PoolAdvice.average_eq_integral, ← integral_indicator_one (measurableSet_event cs)]
  apply integral_congr_ae
  filter_upwards [] with X
  by_cases hX : X ∈ event cs
  · simp [Set.indicator_of_mem hX, (accepts_inputPrefix cs n hn X).mpr hX]
  · simp [Set.indicator_of_notMem hX, mt (accepts_inputPrefix cs n hn X).mp hX]

/-- The executable finite sum is the integral under the actual conditional law. -/
theorem expectation_eq_integral (cs : List AffineCode.Data) (n : ℕ)
    (hn : ∀ c ∈ cs, AffineCode.width c ≤ n) (f : List Bool → ℚ) :
    (expectation cs n f : ℝ) =
      ∫ X, (f (ScanRule.inputPrefix X n) : ℝ) ∂law cs := by
  have hnum :
      (PoolAdvice.average n (fun s => if accepts cs s then f s else 0) : ℝ) =
        ∫ X in event cs, (f (ScanRule.inputPrefix X n) : ℝ) ∂fairCoin := by
    rw [PoolAdvice.average_eq_integral, ← integral_indicator (measurableSet_event cs)]
    apply integral_congr_ae
    filter_upwards [] with X
    by_cases hX : X ∈ event cs
    · simp [Set.indicator_of_mem hX, (accepts_inputPrefix cs n hn X).mpr hX]
    · simp [Set.indicator_of_notMem hX, mt (accepts_inputPrefix cs n hn X).mp hX]
  rw [expectation, Rat.cast_div, hnum, denominator_eq_measureReal cs n hn]
  simp [law, ProbabilityTheory.cond, integral_smul_measure, measureReal_def, ENNReal.toReal_inv,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- A Boolean prefix event has an exact rational finite-stage probability. -/
def probability (cs : List AffineCode.Data) (n : ℕ) (p : List Bool → Bool) : ℚ :=
  expectation cs n (fun s => if p s then 1 else 0)

theorem computable_probability {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {n : α → ℕ} {p : α → List Bool → Bool}
    (hcs : Computable cs) (hn : Computable n) (hp : Computable₂ p) :
    Computable (fun a => probability (cs a) (n a) (p a)) := by
  exact (computable_expectation (f := fun a s => _root_.cond (p a s) (1 : ℚ) 0) hcs hn
    (Computable.cond hp (Computable.const (1 : ℚ)) (Computable.const 0))).of_eq
      fun _ => by simp only [probability, Bool.cond_eq_ite]

theorem probability_eq_measureReal (cs : List AffineCode.Data) (n : ℕ)
    (hn : ∀ c ∈ cs, AffineCode.width c ≤ n) (p : List Bool → Bool) :
    (probability cs n p : ℝ) =
      (law cs).real {X | p (ScanRule.inputPrefix X n) = true} := by
  have hm : Measurable (fun X : Cantor => p (ScanRule.inputPrefix X n)) := by
    simpa only [ScanRule.monotone_transcript] using
      DropEvents.measurable_transcript_eval ScanRule.monotone n p
  have hs : MeasurableSet {X | p (ScanRule.inputPrefix X n) = true} :=
    hm (measurableSet_singleton true)
  rw [probability, expectation_eq_integral cs n hn, ← integral_indicator_one hs]
  apply integral_congr_ae
  filter_upwards [] with X
  by_cases h : p (ScanRule.inputPrefix X n) = true <;> simp [h, Set.indicator]

end Klr.StageFiniteProbability
