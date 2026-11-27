/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PairRespecting
public import LeanPool.KLRandomness.ComputableRational
public import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Base-four betting and paired binary betting

The four symbols are represented explicitly by pairs of bits. A base-four
strategy reads one whole digit at a time; its fair capital averages over all
four possible answers. Both simulation directions preserve uniform computable
real capital and success.
-/

@[expose] public section

namespace Klr.BaseFour

/-- A four-symbol digit represented by its high and low bits. -/
abbrev Digit := Bool × Bool
/-- An infinite sequence of four-symbol digits. -/
abbrev Stream := ℕ → Digit

/-- The base-four digits obtained by grouping adjacent binary coordinates. -/
def pairDigits (X : Cantor) : Stream := fun n => (X (2 * n), X (2 * n + 1))

/-- Flatten a finite digit transcript to its consecutive binary answers. -/
def unpack : List Digit → List Bool
  | [] => []
  | d :: v => d.1 :: d.2 :: unpack v

/-- Group consecutive answers; an unfinished last digit is omitted. -/
def pack : List Bool → List Digit
  | a :: b :: v => (a, b) :: pack v
  | _ => []

@[simp] theorem unpack_nil : unpack [] = [] := rfl
@[simp] theorem unpack_cons (d : Digit) (v : List Digit) :
    unpack (d :: v) = d.1 :: d.2 :: unpack v := rfl
@[simp] theorem pack_nil : pack [] = [] := rfl
@[simp] theorem pack_singleton (b : Bool) : pack [b] = [] := rfl
@[simp] theorem pack_cons_cons (a b : Bool) (v : List Bool) :
    pack (a :: b :: v) = (a, b) :: pack v := rfl

@[simp] theorem length_unpack (v : List Digit) : (unpack v).length = 2 * v.length := by
  induction v with
  | nil => rfl
  | cons d v ih => simp only [unpack_cons, List.length_cons, ih]; omega

@[simp] theorem length_pack (v : List Bool) : (pack v).length = v.length / 2 := by
  match v with
  | [] => rfl
  | [a] => simp
  | a :: b :: v =>
    have ih := length_pack v
    simp only [pack_cons_cons, List.length_cons, ih]
    omega

theorem unpack_append (v w : List Digit) : unpack (v ++ w) = unpack v ++ unpack w := by
  induction v with
  | nil => rfl
  | cons d v ih => simp [ih]

@[simp] theorem unpack_snoc (v : List Digit) (d : Digit) :
    unpack (v ++ [d]) = unpack v ++ [d.1, d.2] := by
  rw [unpack_append]
  rfl

@[simp] theorem pack_unpack (v : List Digit) : pack (unpack v) = v := by
  induction v with
  | nil => rfl
  | cons d v ih => cases d; simp only [unpack_cons, pack_cons_cons, ih]

@[simp] theorem pack_unpack_snoc (v : List Digit) (b : Bool) :
    pack (unpack v ++ [b]) = v := by
  induction v with
  | nil => rfl
  | cons d v ih =>
    rcases d with ⟨a, c⟩
    simpa using congrArg (List.cons (a, c)) ih

@[simp] theorem pack_unpack_two (v : List Digit) (a b : Bool) :
    pack (unpack v ++ [a, b]) = v ++ [(a, b)] := by
  rw [← unpack_snoc v (a, b), pack_unpack]

theorem take_unpack (v : List Digit) (n : ℕ) :
    (unpack v).take (2 * n) = unpack (v.take n) := by
  induction v generalizing n with
  | nil => simp
  | cons d v ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      simp [ih]

theorem pack_take (v : List Bool) (n : ℕ) :
    pack (v.take n) = (pack v).take (n / 2) := by
  match v with
  | [] => simp
  | [a] =>
    cases n <;> simp
  | a :: b :: v =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        have ih := pack_take v n
        rw [show (n + 1 + 1) / 2 = n / 2 + 1 by omega]
        simpa using congrArg (List.cons (a, b)) ih

/-- Every binary transcript consists of complete digits and at most one
additional answer. -/
theorem unpack_cases (v : List Bool) :
    (∃ w, v = unpack w) ∨ (∃ w b, v = unpack w ++ [b]) := by
  match v with
  | [] => exact Or.inl ⟨[], rfl⟩
  | [a] => exact Or.inr ⟨[], a, rfl⟩
  | a :: b :: v =>
    rcases unpack_cases v with ⟨w, rfl⟩ | ⟨w, c, rfl⟩
    · exact Or.inl ⟨(a, b) :: w, rfl⟩
    · exact Or.inr ⟨(a, b) :: w, c, rfl⟩

private def packState : List Bool → List Digit × List Digit
  | [] => ([], [])
  | a :: v =>
    (cond (decide (v.length = 0)) [] ((a, v.getD 0 false) :: (packState v).2),
      (packState v).1)

private theorem packState_eq (v : List Bool) :
    packState v = (pack v, pack v.tail) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [packState, ih]
    cases v <;> simp [pack]

private theorem primrec_packState : Primrec packState := by
  let α := List Bool × (Bool × List Bool × (List Digit × List Digit))
  have ha : Primrec (fun p : α => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : α => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun p : α => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec (fun p : α => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have he := Primrec.eq.decide.comp (Primrec.list_length.comp hv) (Primrec.const 0)
  have hb := (Primrec.list_getD false).comp hv (Primrec.const 0)
  have hd := Primrec.list_cons.comp (ha.pair hb) hr
  have hh := ((Primrec.cond he (Primrec.const []) hd).pair hl).to₂
  apply (Primrec.list_rec Primrec.id (Primrec.const ([], [])) hh).of_eq
  intro v
  induction v with
  | nil => rfl
  | cons a v ih =>
    dsimp only [id_eq, List.recOn] at ih
    simp only [id_eq, packState, ih]

theorem computable_pack : Computable pack :=
  (Primrec.fst.comp primrec_packState).to_comp.of_eq
    (fun v => by rw [packState_eq])

theorem computable_unpack : Computable unpack := by
  have h₁ : Primrec (fun p : List Digit × (Digit × List Bool) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have h₂ : Primrec (fun p : List Digit × (Digit × List Bool) => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun p : List Digit × (Digit × List Bool) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hh := (Primrec.list_cons.comp h₁ (Primrec.list_cons.comp h₂ ht)).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const []) hh).to_comp.of_eq
  intro v
  induction v with
  | nil => rfl
  | cons d v ih =>
    dsimp only [id_eq] at ih
    simp only [id_eq, List.foldr_cons, ih, unpack_cons]

/-- Last answer of a binary transcript, with zero for the empty transcript. -/
def lastBit (v : List Bool) : Bool := v.getD (v.length - 1) false

theorem computable_lastBit : Computable lastBit :=
  (Primrec.list_getD false).to_comp.comp Computable.id
    (Primrec.nat_sub.to_comp.comp Computable.list_length (Computable.const 1))

@[simp] theorem lastBit_snoc (v : List Bool) (b : Bool) :
    lastBit (v ++ [b]) = b := by
  simp only [lastBit, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

/-- Uniform real computability on finite four-symbol transcripts. -/
def ComputableRealCapital (d : List Digit → ℝ) : Prop :=
  ∃ q : List Digit → ℕ → ℚ,
    Computable (fun p : List Digit × ℕ => ((q p.1 p.2).num, (q p.1 p.2).den)) ∧
    ∀ v n, |(q v n : ℝ) - d v| ≤ (1 / 2 : ℝ) ^ n

/-- A computable adaptive query rule that never repeats a digit position along a branch. -/
structure ScanRule where
  /-- Position of the next digit to read after a finite transcript. -/
  query : List Digit → ℕ
  computable_query : Computable query
  fresh : ∀ (v : List Digit) (n : ℕ), n < v.length → query (v.take n) ≠ query v

namespace ScanRule

/-- Digit answers observed through the given number of queries. -/
def transcript (π : ScanRule) (X : Stream) : ℕ → List Digit
  | 0 => []
  | n + 1 =>
    let v := transcript π X n
    v ++ [X (π.query v)]

@[simp] theorem transcript_zero (π : ScanRule) (X : Stream) :
    π.transcript X 0 = [] := rfl

@[simp] theorem transcript_succ (π : ScanRule) (X : Stream) (n : ℕ) :
    π.transcript X (n + 1) =
      π.transcript X n ++ [X (π.query (π.transcript X n))] := rfl

@[simp] theorem length_transcript (π : ScanRule) (X : Stream) (n : ℕ) :
    (π.transcript X n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- Read each digit query as two consecutive bit queries. -/
def toBinary (π : ScanRule) : Klr.ScanRule where
  query v := 2 * π.query (pack v) + v.length % 2
  computable_query :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2)
        (π.computable_query.comp computable_pack))
      (Primrec.nat_mod.to_comp.comp Computable.list_length (Computable.const 2))
  fresh := by
    intro v n hn he
    simp only [List.length_take, Nat.min_eq_left hn.le, pack_take] at he
    have hq : π.query ((pack v).take (n / 2)) = π.query (pack v) := by omega
    have hl : n / 2 < (pack v).length := by rw [length_pack]; omega
    exact π.fresh (pack v) (n / 2) hl hq

@[simp] theorem toBinary_query_unpack (π : ScanRule) (v : List Digit) :
    π.toBinary.query (unpack v) = 2 * π.query v := by
  simp [toBinary]

@[simp] theorem toBinary_query_unpack_snoc (π : ScanRule) (v : List Digit) (b : Bool) :
    π.toBinary.query (unpack v ++ [b]) = 2 * π.query v + 1 := by
  simp [toBinary, Nat.add_mod]

theorem toBinary_pairRespecting (π : ScanRule) : π.toBinary.PairRespecting := by
  intro v hv
  rcases unpack_cases v with ⟨w, rfl⟩ | ⟨w, b, rfl⟩
  · simp
  · simp [Nat.add_mod] at hv

theorem toBinary_transcript (π : ScanRule) (X : Cantor) (n : ℕ) :
    π.toBinary.transcript X (2 * n) = unpack (π.transcript (pairDigits X) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [Klr.ScanRule.transcript_succ, Klr.ScanRule.transcript_succ, ih]
    simp [transcript_succ, pairDigits, List.append_assoc]

end ScanRule

/-- A pair-respecting binary scan induces a fresh scan of the digit positions. -/
def ofBinaryScan (π : Klr.ScanRule) (hπ : π.PairRespecting) : ScanRule where
  query v := π.query (unpack v) / 2
  computable_query := Primrec.nat_div.to_comp.comp
    (π.computable_query.comp computable_unpack) (Computable.const 2)
  fresh := by
    intro v n hn he
    have h₁ := (hπ (unpack (v.take n)) (by simp)).1
    have h₂ := (hπ (unpack v) (by simp)).1
    have hq : π.query (unpack (v.take n)) = π.query (unpack v) := by omega
    have hl : 2 * n < (unpack v).length := by simp; omega
    apply π.fresh (unpack v) (2 * n) hl
    simpa only [take_unpack] using hq

theorem ofBinaryScan_transcript (π : Klr.ScanRule) (hπ : π.PairRespecting)
    (X : Cantor) (n : ℕ) :
    π.transcript X (2 * n) = unpack ((ofBinaryScan π hπ).transcript (pairDigits X) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let v := (ofBinaryScan π hπ).transcript (pairDigits X) n
    have he := (hπ (unpack v) (by simp)).1
    have hq : 2 * (π.query (unpack v) / 2) = π.query (unpack v) := by omega
    have hp := (hπ (unpack v) (by simp)).2 (X (π.query (unpack v)))
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [Klr.ScanRule.transcript_succ, Klr.ScanRule.transcript_succ, ih]
    change unpack v ++ [X (π.query (unpack v))] ++
      [X (π.query (unpack v ++ [X (π.query (unpack v))]))] = _
    rw [hp]
    simp only [ScanRule.transcript_succ, unpack_snoc, pairDigits, ofBinaryScan]
    change unpack v ++ [X (π.query (unpack v))] ++ [X (π.query (unpack v) + 1)] =
      unpack v ++ [X (2 * (π.query (unpack v) / 2)),
        X (2 * (π.query (unpack v) / 2) + 1)]
    rw [hq]
    simp [List.append_assoc]

/-- A nonnegative fair capital process on four-symbol transcripts, starting at one. -/
structure CapitalProcess where
  /-- Capital after observing a finite digit transcript. -/
  value : List Digit → ℝ
  initial : value [] = 1
  nonneg : ∀ v, 0 ≤ value v
  fair : ∀ v,
    value (v ++ [(false, false)]) + value (v ++ [(false, true)]) +
      value (v ++ [(true, false)]) + value (v ++ [(true, true)]) = 4 * value v

/-- Conditional expectation after seeing the first bit of a digit. -/
def splitValue {α : Type*} [DivisionRing α] (d : List Digit → α) (v : List Bool) : α :=
  if v.length % 2 = 0 then d (pack v)
  else (d (pack v ++ [(lastBit v, false)]) + d (pack v ++ [(lastBit v, true)])) / 2

@[simp] theorem splitValue_unpack {α : Type*} [DivisionRing α]
    (d : List Digit → α) (v : List Digit) : splitValue d (unpack v) = d v := by
  simp [splitValue]

@[simp] theorem splitValue_unpack_snoc {α : Type*} [DivisionRing α]
    (d : List Digit → α) (v : List Digit) (b : Bool) :
    splitValue d (unpack v ++ [b]) =
      (d (v ++ [(b, false)]) + d (v ++ [(b, true)])) / 2 := by
  simp [splitValue, Nat.add_mod]

@[simp] theorem splitValue_unpack_two {α : Type*} [DivisionRing α]
    (d : List Digit → α) (v : List Digit) (a b : Bool) :
    splitValue d (unpack v ++ [a, b]) = d (v ++ [(a, b)]) := by
  rw [← unpack_snoc v (a, b), splitValue_unpack]

private theorem computable_splitValue {q : List Digit → ℕ → ℚ}
    (hq : Computable (fun p : List Digit × ℕ => q p.1 p.2)) :
    Computable (fun p : List Bool × ℕ => splitValue (fun v => q v p.2) p.1) := by
  have hfst := Computable.fst (α := List Bool) (β := ℕ)
  have hsnd := Computable.snd (α := List Bool) (β := ℕ)
  have hp := computable_pack.comp hfst
  have hb := computable_lastBit.comp hfst
  have h₀ := hq.comp ((Computable.list_concat.comp hp
    (hb.pair (Computable.const false))).pair hsnd)
  have h₁ := hq.comp ((Computable.list_concat.comp hp
    (hb.pair (Computable.const true))).pair hsnd)
  have hh := RationalComputability.primrec_rat_div.to_comp.comp
    (RationalComputability.primrec_rat_add.to_comp.comp h₀ h₁) (Computable.const 2)
  have he := Primrec.eq.decide.to_comp.comp
    (Primrec.nat_mod.to_comp.comp (Computable.list_length.comp hfst)
      (Computable.const 2)) (Computable.const 0)
  have h := Computable.cond he (hq.comp (hp.pair hsnd)) hh
  exact h.of_eq (fun p => by simp [splitValue, Bool.cond_eq_ite])

theorem ComputableRealCapital.toBinary {d : List Digit → ℝ}
    (hd : ComputableRealCapital d) : Klr.ComputableRealCapital (splitValue d) := by
  obtain ⟨q, hq, herr⟩ := hd
  refine ⟨fun v n => splitValue (fun w => q w n) v, ?_, ?_⟩
  · exact RationalComputability.primrec_rat_numDen.to_comp.comp
      (computable_splitValue (RationalComputability.computable_rat_of_numDen hq))
  · intro v n
    by_cases hv : v.length % 2 = 0
    · simpa only [splitValue, ite_eq_left hv] using herr (pack v) n
    · have h₀ := abs_le.mp (herr (pack v ++ [(lastBit v, false)]) n)
      have h₁ := abs_le.mp (herr (pack v ++ [(lastBit v, true)]) n)
      simp only [splitValue, ite_eq_right hv]
      push_cast
      rw [abs_le]
      constructor <;> linarith

namespace CapitalProcess

/-- Splitting a four-way fair bet into its two binary conditional bets. -/
noncomputable def toBinary (d : CapitalProcess) : Klr.CapitalProcess where
  value := splitValue d.value
  initial := by simpa [splitValue] using d.initial
  nonneg := by
    intro v
    unfold splitValue
    split_ifs
    · exact d.nonneg _
    · exact div_nonneg (add_nonneg (d.nonneg _) (d.nonneg _)) (by norm_num)
  fair := by
    intro v
    rcases unpack_cases v with ⟨w, rfl⟩ | ⟨w, b, rfl⟩
    · simp only [splitValue_unpack_snoc, splitValue_unpack]
      linarith [d.fair w]
    · simp only [List.append_assoc, List.cons_append, List.nil_append,
        splitValue_unpack_two, splitValue_unpack_snoc]
      ring

@[simp] theorem toBinary_value_unpack (d : CapitalProcess) (v : List Digit) :
    d.toBinary.value (unpack v) = d.value v := splitValue_unpack _ _

end CapitalProcess

/-- Restrict a binary capital process to complete digit transcripts. -/
noncomputable def ofBinaryCapital (d : Klr.CapitalProcess) : CapitalProcess where
  value v := d.value (unpack v)
  initial := d.initial
  nonneg v := d.nonneg _
  fair := by
    intro v
    have h := d.fair (unpack v)
    have h₀ := d.fair (unpack v ++ [false])
    have h₁ := d.fair (unpack v ++ [true])
    simp only [unpack_snoc]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h₀ h₁
    linarith

theorem computableRealCapital_ofBinary {d : List Bool → ℝ}
    (hd : Klr.ComputableRealCapital d) :
    ComputableRealCapital (fun v => d (unpack v)) := by
  obtain ⟨q, hq, herr⟩ := hd
  refine ⟨fun v n => q (unpack v) n, ?_, fun v n => herr (unpack v) n⟩
  have hp := (computable_unpack.comp (Computable.fst (α := List Digit) (β := ℕ))).pair
    (Computable.snd (α := List Digit) (β := ℕ))
  have h := hq.comp hp
  exact h

/-- A total adaptive four-symbol scan with uniformly computable fair capital. -/
structure BettingStrategy where
  /-- The rule choosing which digit position to inspect next. -/
  scan : ScanRule
  /-- The capital process on digit transcripts. -/
  capital : CapitalProcess
  computable_capital : ComputableRealCapital capital.value

/-- Success means capital is unbounded along the observed digit transcript. -/
def BettingStrategy.Succeeds (s : BettingStrategy) (X : Stream) : Prop :=
  ∀ bound : ℝ, ∃ n, bound < s.capital.value (s.scan.transcript X n)

/-- A stream on which every total computable-real four-symbol strategy has bounded capital. -/
def KolmogorovLovelandRandom (X : Stream) : Prop :=
  ∀ s : BettingStrategy, ¬ s.Succeeds X

namespace BettingStrategy

/-- Simulate a four-way bet by two successive binary bets on an adjacent pair. -/
noncomputable def toBinary (s : BettingStrategy) : Klr.BettingStrategy where
  scan := s.scan.toBinary
  capital := s.capital.toBinary
  computable_capital := s.computable_capital.toBinary

theorem toBinary_pairRespecting (s : BettingStrategy) : s.toBinary.PairRespecting :=
  s.scan.toBinary_pairRespecting

theorem toBinary_preserves_success (s : BettingStrategy) {X : Cantor}
    (hs : s.Succeeds (pairDigits X)) : s.toBinary.Succeeds X := by
  intro bound
  obtain ⟨n, hn⟩ := hs bound
  refine ⟨2 * n, ?_⟩
  change bound < s.capital.toBinary.value (s.scan.toBinary.transcript X (2 * n))
  simpa only [ScanRule.toBinary_transcript, CapitalProcess.toBinary_value_unpack] using hn

end BettingStrategy

/-- Restrict a pair-respecting binary strategy to times when whole pairs have been read. -/
noncomputable def ofBinary (s : Klr.BettingStrategy) (hs : s.PairRespecting) : BettingStrategy where
  scan := ofBinaryScan s.scan hs
  capital := ofBinaryCapital s.capital
  computable_capital := computableRealCapital_ofBinary s.computable_capital

/-- A binary capital process can grow by at most a factor of two between
successive complete digits. -/
theorem binary_succeeds_iff_even (s : Klr.BettingStrategy) (X : Cantor) :
    s.Succeeds X ↔ ∀ bound : ℝ, ∃ n,
      bound < s.capital.value (s.scan.transcript X (2 * n)) := by
  constructor
  · intro hs bound
    obtain ⟨t, ht⟩ := hs (2 * max bound 0)
    refine ⟨t / 2, ?_⟩
    have hmax := le_max_left bound (0 : ℝ)
    have hnonneg := le_max_right bound (0 : ℝ)
    by_cases he : t % 2 = 0
    · have ht' : t = 2 * (t / 2) := by omega
      rw [ht'] at ht
      linarith
    · have ht' : t = 2 * (t / 2) + 1 := by omega
      rw [ht', Klr.ScanRule.transcript_succ] at ht
      have hc := s.capital.successor_le (s.scan.transcript X (2 * (t / 2)))
        (X (s.scan.query (s.scan.transcript X (2 * (t / 2)))))
      linarith
  · intro hs bound
    obtain ⟨n, hn⟩ := hs bound
    exact ⟨2 * n, hn⟩

theorem ofBinary_succeeds_iff (s : Klr.BettingStrategy) (hs : s.PairRespecting) (X : Cantor) :
    (ofBinary s hs).Succeeds (pairDigits X) ↔ s.Succeeds X := by
  rw [binary_succeeds_iff_even]
  change (∀ bound : ℝ, ∃ n,
    bound < s.capital.value (unpack ((ofBinaryScan s.scan hs).transcript (pairDigits X) n))) ↔ _
  simp only [ofBinaryScan_transcript s.scan hs X]

/-- Four-symbol KL randomness is exactly resistance to pair-respecting binary
strategies. Both sides use total fresh scans and uniformly computable real capital. -/
theorem kolmogorovLovelandRandom_pairDigits_iff (X : Cantor) :
    KolmogorovLovelandRandom (pairDigits X) ↔ Klr.PairRespectingRandom X := by
  constructor
  · intro hX s hs hsucc
    exact hX (ofBinary s hs) ((ofBinary_succeeds_iff s hs X).mpr hsucc)
  · intro hX s hsucc
    exact hX s.toBinary s.toBinary_pairRespecting (s.toBinary_preserves_success hsucc)

/-- Grouping binary digits into pairs preserves KL randomness. -/
theorem of_binary_kolmogorovLovelandRandom {X : Cantor}
    (hX : Klr.KolmogorovLovelandRandom X) : KolmogorovLovelandRandom (pairDigits X) :=
  (kolmogorovLovelandRandom_pairDigits_iff X).mpr hX.pairRespectingRandom

end Klr.BaseFour
