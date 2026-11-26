/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import Mathlib.Data.Fin.VecNotation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.VectorSort
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Install.Products
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Seats

/-!
# Bit-addressed memory tapes

A row specifies an address, the bit before the access and the bit
after it. Initial contents are zero. Reads can write back the same
bit, and initialization by advice can be implemented by writes.
-/

@[expose] public section

section

namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Coloring

/-- Computes the row by the application `Format.pair (.addr w) (.pair .bit .bit)`. -/
abbrev Row (w : ℕ) := Format.pair (.addr w) (.pair .bit .bit)

/-- Computes the tape by the application `Format.vec j (Row w)`. -/
abbrev Tape (j w : ℕ) := Format.vec j (Row w)

variable {j w : ℕ}

/-- In the case `0 => fun _`, this construction gives `false`. -/
def cells (x : (Tape j w).obj) : ℕ → B w → Bool
  | 0 => fun _ => false
  | n + 1 => if h : n < 2 ^ j then
      Function.update (cells x n) (x ⟨n, h⟩).1 (x ⟨n, h⟩).2.2
    else cells x n

/-- The condition `∀ i, (x i).2.1 = cells x i.val (x i).1` on the specified data. -/
def Valid (x : (Tape j w).obj) : Prop :=
  ∀ i, (x i).2.1 = cells x i.val (x i).1

instance (x : (Tape j w).obj) : Decidable (Valid x) := by unfold Valid; infer_instance

theorem written (x : (Tape j w).obj) (i : B j) :
    cells x (i.val + 1) (x i).1 = (x i).2.2 := by
  rw [cells, dite_eq_left i.isLt, Function.update_self]

theorem unchanged (x : (Tape j w).obj) (a : B w) {start stop : ℕ} (h : start ≤ stop)
    (hn : ∀ i : B j, start ≤ i.val → i.val < stop → (x i).1 ≠ a) :
    cells x stop a = cells x start a := by
  induction stop, h using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
    have hh := ih (fun i h₁ h₂ => hn i h₁ (by omega))
    rw [cells]
    split
    · rename_i hi
      rw [Function.update_of_ne (hn ⟨n, hi⟩ h (Nat.lt_succ_self n)).symm]
      exact hh
    · exact hh

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end

section
/- # Adjacent accesses in stable address order -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Coloring

variable {j w : ℕ} (x : (Tape j w).obj)

/-- The indexed operation `permutation (fun i => (x i).1) (fun _ => true)`. -/
def order : Equiv.Perm (B j) := permutation (fun i => (x i).1) (fun _ => true)

/-- The value specified by `x ∘ order x`. -/
def sorted : (Tape j w).obj := x ∘ order x

private theorem earlier (i k : B j) :
    i < k ↔ (sorted x i).1 < (sorted x k).1 ∨
      (sorted x i).1 = (sorted x k).1 ∧ order x i < order x k := by
  let f := fun i : B j => toLex (false, toLex ((x i).1, i))
  have hi : Function.Injective f := fun _ _ h => congrArg (fun t => t.2.2) h
  have hm : StrictMono (f ∘ order x) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hi.comp (order x).injective)
  rw [← hm.lt_iff_lt]
  simp [f, sorted, Prod.Lex.toLex_lt_toLex]

/-- The quantity computed by `⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩`. -/
def prev (i : B j) : B j := ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

/-- Any earlier access to this address lies no later than the previous
row in sorted order, which then has the same address. -/
private theorem previous (i k : B j) (hk : k < order x i) (he : (x k).1 = (sorted x i).1) :
    0 < i.val ∧ (sorted x (prev i)).1 = (sorted x i).1 ∧ k ≤ order x (prev i) := by
  let t := (order x).symm k
  have ht : order x t = k := (order x).apply_symm_apply k
  have he' : (sorted x t).1 = (sorted x i).1 := by rw [sorted, Function.comp_apply, ht]; exact he
  have hi : t < i := (earlier x t i).mpr (.inr ⟨he', ht.trans_lt hk⟩)
  change t.val < i.val at hi
  have hpos : 0 < i.val := by omega
  have hpred : t ≤ prev i := by change t.val ≤ i.val - 1; omega
  have hpred' : prev i < i := by change i.val - 1 < i.val; omega
  have hu : (sorted x (prev i)).1 ≤ (sorted x i).1 := by
    rcases (earlier x _ _).mp hpred' with h | h
    · exact h.le
    · exact h.1.le
  refine ⟨hpos, ?_⟩
  rcases hpred.eq_or_lt with heq | hl
  · rw [← heq, ht]; exact ⟨he', le_rfl⟩
  rcases (earlier x _ _).mp hl with h | h
  · exact (hu.not_gt (he' ▸ h)).elim
  · exact ⟨h.1.symm.trans he', ht.symm.le.trans h.2.le⟩

/-- Returns `(x (prev i)).2.2` when `0 < i.val ∧ (x (prev i)).1 = (x i).1` holds, and `false`
otherwise. -/
def expected (i : B j) : Bool :=
  if 0 < i.val ∧ (x (prev i)).1 = (x i).1 then (x (prev i)).2.2 else false

private theorem before (i : B j) :
    cells x (order x i).val (sorted x i).1 = expected (sorted x) i := by
  unfold expected
  split
  · rename_i h
    have hp : prev i < i := by change i.val - 1 < i.val; omega
    have htime := ((earlier x _ _).mp hp).resolve_left (not_lt_of_ge h.2.ge)
    rw [unchanged x _ (Nat.succ_le_of_lt htime.2) (by
      intro k hk hk' he
      have ht : k.val ≤ (order x (prev i)).val := (previous x i k hk' he).2.2
      omega), ← h.2]
    exact written x _
  · rename_i h
    rw [unchanged x _ (Nat.zero_le _) (by
      intro k _ hk he
      obtain ⟨h₁, h₂, _⟩ := previous x i k hk he
      exact h ⟨h₁, h₂⟩)]
    rfl

theorem valid_iff : Valid x ↔ ∀ i, (sorted x i).2.1 = expected (sorted x) i := by
  simp_rw [← before]
  constructor
  · exact fun h i => h (order x i)
  · intro h i
    obtain ⟨k, rfl⟩ := (order x).surjective i
    exact h k

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end

section
/- # Computing all the local checks in stable address order -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Coloring

variable (F : Type) [Field F] (j w : ℕ)

private theorem tape_width : (Tape j w).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 1 := by
  simp only [Tape, Row, Format.width_vec, Format.width_pair, Format.width_addr, pow_one]
  rw [Format.width_bit]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem cheap_sorted : Cheap F j (j + w + 2) (Tape j w) (Tape j w) sorted 43 := by
  have ha : (Format.vec j (.addr w)).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 1 := by
    simp only [Format.width_vec, Format.width_addr, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have hb : (Format.vec j .bit).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 1 := by
    rw [Format.width_vec, Format.width_bit, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have pick : Cheap F j (j + w + 2) (Tape j w) (.vec j (.addr w)) (fun x i => (x i).1) 2 :=
    Cheap.project F (tape_width _ _) ha (fun i => (i.1, .inl i.2)) (fun _ _ => rfl)
  have mark := Cheap.const F (tape_width j w) hb (fun _ => true)
  have perm := (pick.pair mark).comp ((cheap_permutation F j w).widen (l := j + w + 2) (by omega))
  have read := Cheap.lookup F j (j + w + 2) (Row w) (by omega) (by simp [Row])
  have H := ((Cheap.id F (tape_width j w)).pair perm).comp read
  simp only [Function.comp_def, id_eq] at H
  exact H

private abbrev Test := Format.pair (.pair (.addr w) (.addr w)) (.pair .bit .bit)

private def neighbors (x : (Tape j w).obj) (i : B j) : (Test w).obj :=
  (((x (prev i)).1, (x i).1), ((x i).2.1, (x (prev i)).2.2))

private theorem test_width : (Test w).width ≤ (100 + (j + w + 2)) ^ 2 := by
  simp only [Test, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]
  ring_nf
  omega

private theorem cheap_neighbors : Cheap F j (j + w + 2) (Tape j w) (.vec j (Test w))
    (neighbors j w) 3 := by
  have ha : (Tape j w).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 2 :=
    (tape_width _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide)))
  have hb : (Format.vec j (Test w)).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 2 := by
    rw [Format.width_vec]
    exact Nat.mul_le_mul_left _ (test_width j w)
  let e : (Format.vec j (Test w)).pins → (Tape j w).pins
    | (i, .inl (.inl a)) => (prev i, .inl a)
    | (i, .inl (.inr a)) => (i, .inl a)
    | (i, .inr (.inl a)) => (i, .inr (.inl a))
    | (i, .inr (.inr a)) => (prev i, .inr (.inr a))
  apply Cheap.project F ha hb e
  rintro x ⟨i, (a | a) | (a | a)⟩ <;> rfl

private def test (i : B j) (x : (Test w).obj) : Bool :=
  decide (x.2.1 = if 0 < i.val ∧ x.1.1 = x.1.2 then x.2.2 else false)

private theorem cheap_test (i : B j) : Cheap F 0 (j + w + 2) (Test w) .bit (test j w i) 2 := by
  let g := fun x : Bool × Bool × Bool => decide (x.2.1 = if 0 < i.val ∧ x.1 then x.2.2 else false)
  have hc := (numeric_eq F w).par (Circuit.id F (.pair .bit .bit))
  have ho := hc.comp (small (F := F) (A := .pair .bit (.pair .bit .bit)) (by simp) g)
  have he : Circuit F (Test w) .bit (test j w i) (2 * w + 1 + 2 + 200) := by
    rw [Format.width_pair .bit .bit, Format.width_bit] at ho
    convert ho using 1
    funext x
    simp only [test, g, Function.comp_apply, Prod.map, id_eq, decide_eq_true_eq]
  refine ⟨_, he, ?_⟩
  simp only [Test, Format.width_pair, Format.width_addr, pow_zero, one_mul]
  rw [Format.width_bit]
  ring_nf
  omega

/-- Tests whether `(sorted x i).2.1 = expected (sorted x) i` holds. -/
def checks (x : (Tape j w).obj) (i : B j) : Bool :=
  decide ((sorted x i).2.1 = expected (sorted x) i)

theorem cheap_checks : Cheap F j (j + w + 2) (Tape j w) (.vec j .bit) (checks j w) 45 :=
  ((cheap_sorted F j w).comp (cheap_neighbors F j w)).comp (Cheap.map _ (cheap_test F j w))

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end

section
/- # Trivalent verification of a named memory tape -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Coloring Install

private theorem estimate (j w : ℕ) :
    2 ^ j * (100 + (j + w + 2)) ^ 45 + 2 ^ j * 16 ≤ 2 ^ j * (100 + j + w) ^ 100 := by
  rw [← mul_add]
  apply Nat.mul_le_mul_left
  let k := 100 + j + w
  have hk : 100 ≤ k := by unfold k; omega
  have hh : 100 + (j + w + 2) ≤ k ^ 2 := by unfold k; ring_nf; omega
  calc
    _ ≤ (k ^ 2) ^ 45 + 16 := Nat.add_le_add_right (Nat.pow_le_pow_left hh _) _
    _ = k ^ 90 + 16 := by rw [← pow_mul]
    _ ≤ k ^ 90 * k := by
      have h : 0 < k ^ 90 := pow_pos (by omega) _
      generalize k ^ 90 = v at h ⊢
      nlinarith
    _ ≤ k ^ 100 := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by decide)

/-- One zero-one weight verifies every read against the most recent
write to the same address, with no multiplicity in any characteristic. -/
theorem weight (F : Type) [Field F] (j w : ℕ) :
    Weight F (fun b => if Valid ((Tape j w).code.symm b) then 1 else 0)
      (2 ^ j * (100 + j + w) ^ 100) := by
  let pin : (Unit → Bool) → F := fun x => if x () then 1 else 0
  have hp : Weight F pin 16 := Weight.dense F Unit pin
  obtain ⟨m, hm, hb⟩ := cheap_checks F j w
  have hn : m + 2 ^ j * 16 ≤ 2 ^ j * (100 + j + w) ^ 100 :=
    (Nat.add_le_add_right ((Nat.le_add_left _ _).trans hb) _).trans (estimate j w)
  have h := (BNet.weight hm (hp.prod j)).mono hn
  convert h using 1
  funext b
  let x := (Tape j w).code.symm b
  change (if Valid x then (1 : F) else 0) = ∏ i : B j, if checks j w x i then 1 else 0
  by_cases hx : Valid x
  · have hc (i : B j) : checks j w x i = true := decide_eq_true ((valid_iff x).mp hx i)
    simp only [hx, hc, ite_true, Finset.prod_const_one]
  · obtain ⟨i, hi⟩ := not_forall.mp (mt (valid_iff x).mpr hx)
    rw [ite_eq_right hx]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [checks, hi])

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end

/-
# Dyadic dictionary seats

The active bit distinguishes an empty call from an unused seat.
Lengths are explicit and each width uses one common table label.
Uniformity is in the choice of the dictionary as well as the slot.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Coloring Install

open scoped Classical in
/-- The quantity computed by `Format.pair .bit (.pair (.addr (b + 1)) (.vec b .bit))`. -/
abbrev token (b : ℕ) := Format.pair .bit (.pair (.addr (b + 1)) (.vec b .bit))

open scoped Classical in
/-- The token value of type `(token b).obj → F` for the given inputs. -/
def tokenValue {F : Type} [Field F] (U : ℕ) (W : List Bool → F) (b : ℕ) :
    (token b).obj → F :=
  fun (active, n, x) => if !active then 1 else
    if n.val ≤ U ∧ n.val ≤ 2 ^ b then W ((List.ofFn x).take n.val) else 0

open scoped Classical in
private theorem token_width (b : ℕ) : (token b).width ≤ 4 * 2 ^ b := by
  simp only [token, Format.width_pair, Format.width_vec]
  rw [Format.width_bit, Format.width_addr]
  have := Nat.lt_two_pow_self (n := b)
  omega

open scoped Classical in
/-- The least binary width whose power of two reaches the stated size. -/
def ceiling (U : ℕ) := Nat.clog 2 (U + 1)
open scoped Classical in
/-- Computes the calls by the application `Slot t t (ceiling U)`. -/
abbrev Calls (t U : ℕ) := Slot t t (ceiling U)

variable {F : Type} [Field F] (U : ℕ) (W : List Bool → F)

open scoped Classical in
/-- Reindexes two finite types using equality of cardinalities. -/
def sites (b : ℕ) : (token b).pins ≃ slots (word (token b).width) :=
  Fintype.equivOfCardEq (by simp [Format.width])

open scoped Classical in
/-- The indexed operation `⟨word (token b).width, .unit, fun x _ => tokenValue U W b ((token
b).code.symm (bits (word (token b).width) x ∘ sites b))⟩`. -/
def label (b : ℕ) : Table F :=
  ⟨word (token b).width, .unit,
    fun x _ => tokenValue U W b ((token b).code.symm (bits (word (token b).width) x ∘ sites b))⟩

open scoped Classical in
/-- Computes the labels by the application `label U W '' Set.Iic (ceiling U)`. -/
def labels : Set (Table F) := label U W '' Set.Iic (ceiling U)

open scoped Classical in
theorem label_cost {b : ℕ} (hb : b ≤ ceiling U) :
    WideWeight F (8 * (U + 1)) (labels U W) (tokenValue U W b ∘ (token b).code.symm) (5 * 2 ^ b)
      := by
  have h₁ : 2 ^ b ≤ 2 * (U + 1) :=
    (Nat.pow_le_pow_right (by decide) hb).trans (pow_clog_le_twice (by omega))
  have hw := token_width b
  let a := word (token b).width
  let f := fun (x : Val a) (_ : Val .unit) =>
    tokenValue U W b ((token b).code.symm (bits a x ∘ sites b))
  have hn : Wide F (8 * (U + 1)) (labels U W) a .unit f (1 + wd a) := by
    apply Wide.table
    · simp only [a, wd_word, wd, add_zero]
      omega
    · exact .inr ⟨b, hb, rfl⟩
  intro c e
  refine ⟨1 + wd a, ?_, ?_⟩
  · show 1 + wd a ≤ 5 * 2 ^ b
    rw [show wd a = (token b).width from wd_word _]
    have := Nat.two_pow_pos b
    omega
  · simpa [f, Function.comp_def] using hn.pre (rewire_reindex ((sites b).symm.trans e))

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end

/-
# Packing variable-length calls

Every call costs at least one bit of charge. Within each dyadic bucket
we use an initial segment of the installed seats, in issuance order.
Unused seats contribute one.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

variable {F : Type} [Field F] {n t U : ℕ}

open scoped Classical in
/-- The maximum of the quantities in `1 x.length`. -/
def callCharge (x : List Bool) := max 1 x.length

open scoped Classical in
/-- The indexed operation `(false, 0, fun _ => false)`. -/
def emptyToken (b : ℕ) : (token b).obj := (false, 0, fun _ => false)

open scoped Classical in
/-- Returns `(true, ⟨x.length, h⟩, fun i => x[i.val]?.getD false)` when `h : x.length < 2 ^ (b +
1)` holds, and `emptyToken b` otherwise. -/
def encodeToken (b : ℕ) (x : List Bool) : (token b).obj :=
  if h : x.length < 2 ^ (b + 1) then
    (true, ⟨x.length, h⟩, fun i => x[i.val]?.getD false)
  else emptyToken b

open scoped Classical in
theorem tokenValue_encode (W : List Bool → F) (b : ℕ) (x : List Bool)
    (hx : x.length ≤ U) (hb : x.length ≤ 2 ^ b) :
    tokenValue U W b (encodeToken b x) = W x := by
  have hn : x.length < 2 ^ (b + 1) := lt_of_le_of_lt hb (by
    rw [pow_succ]
    have : 0 < 2 ^ b := Nat.two_pow_pos b
    omega)
  simp only [encodeToken, dite_eq_left hn, tokenValue, Bool.not_true, Bool.false_eq_true, ite_false,
    hx, hb, and_self, ite_true]
  congr 1
  apply List.ext_getElem
  · simp [hb]
  · intro i h₁ h₂
    simp [h₂]

open scoped Classical in
/-- A slot stores the ordinal of its call, or a sentinel for an unused seat. -/
def Issuance (x : Fin n → List Bool) (p : Calls t U → Fin (n + 1)) : Prop :=
  ∀ b : Fin (ceiling U + 1), OrderedSeats (bucket (fun i => callCharge (x i)) b)
    (fun s => p ⟨b, s⟩)

open scoped Classical in
theorem unique_issuance (x : Fin n → List Bool) (h : ∑ i, callCharge (x i) ≤ t) :
    ∃! p : Calls t U → Fin (n + 1), Issuance x p := by
  have hp (i : Fin n) : 1 ≤ callCharge (x i) := le_max_left _ _
  have hn : n ≤ t := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)).trans h
  have hh (b : Fin (ceiling U + 1)) := unique_seats (n := seats t t b)
    (bucket (fun i => callCharge (x i)) b.val)
    ((bucket_capacity hp h b.val).trans (min_le_min_right _ hn))
  let p := fun s : Calls t U => (hh s.1).choose s.2
  refine ⟨p, fun b => (hh b).choose_spec.1, ?_⟩
  intro q hq
  funext ⟨b, i⟩
  exact congrFun ((hh b).choose_spec.2 _ (hq b)) i

variable {x : Fin n → List Bool} {p : Calls t U → Fin (n + 1)}

open scoped Classical in
private theorem Issuance.index (h : Issuance x p) {i s} (he : p s = i.castSucc) :
    Nat.clog 2 (callCharge (x i)) = s.1.val := by
  have hh := ((h s.1).2.1 i).mp ⟨s.2, he⟩
  simpa [bucket] using hh

open scoped Classical in
theorem Issuance.covers (h : Issuance x p) (hu : ∀ i, (x i).length ≤ U) (i : Fin n) :
    ∃! s, p s = i.castSucc := by
  have hb : Nat.clog 2 (callCharge (x i)) ≤ ceiling U := by
    apply Nat.clog_mono_right
    exact max_le (by omega) ((hu i).trans (Nat.le_succ _))
  let b : Fin (ceiling U + 1) := ⟨_, Nat.lt_succ_of_le hb⟩
  obtain ⟨s, hs⟩ := ((h b).2.1 i).mpr (by simp [bucket, b])
  refine ⟨⟨b, s⟩, hs, ?_⟩
  rintro ⟨d, z⟩ hz
  have hd : d = b := Fin.ext (h.index hz).symm
  subst d
  have he : z = s := (h b).2.2 _ _ (hz.trans hs.symm) (hz.trans_ne (Fin.castSucc_ne_last i))
  rw [he]

open scoped Classical in
/-- The indexed operation `Fin.lastCases (emptyToken _) (fun i => encodeToken _ (x i)) (p s)`. -/
def tokens (x : Fin n → List Bool) (p : Calls t U → Fin (n + 1)) (s : Calls t U) :
    (token s.1.val).obj :=
  Fin.lastCases (emptyToken _) (fun i => encodeToken _ (x i)) (p s)

open scoped Classical in
theorem Issuance.product (h : Issuance x p) (hu : ∀ i, (x i).length ≤ U) (W : List Bool → F) :
    (∏ s, tokenValue U W s.1.val (tokens x p s)) = ∏ i, W (x i) := by
  have he (s : Calls t U) : tokenValue U W s.1.val (tokens x p s) =
      ∏ i : Fin n, if p s = i.castSucc then W (x i) else 1 := by
    by_cases hn : p s = Fin.last n
    · simp [tokens, hn, emptyToken, tokenValue, Ne.symm (Fin.castSucc_ne_last _)]
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hn
    have hb : (x i).length ≤ 2 ^ s.1.val := by
      rw [← h.index hi.symm]
      exact (le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)
    simp [tokens, ← hi, tokenValue_encode W _ _ (hu i) hb]
  simp_rw [he]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨s, hs, hu⟩ := h.covers hu i
  rw [Finset.prod_eq_single s]
  · exact ite_eq_left hs
  · intro z _ hz
    exact ite_eq_right (mt (hu z) hz)
  · simp

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end
