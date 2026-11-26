/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Weights

/-!
# A faster weighted population count

`RACert.wtot b E = ∑ⱼ 2^j · popcount Eⱼ` runs the fast population count once per table, which
costs 16 big-number operations per table. This file provides `RACert.wtotF`, which computes the
same number (`wtotF_eq`) but shares the SWAR rounds between the tables: neighbouring tables are
merged *inside* each round, with the weight of the second one, so that the number of big numbers
halves with every round.

## Merged rounds

Let `u` and `v` have `2^j`-bit fields, let `m = maskLo b j` select the even fields and write
`u = uₑ + 2^(2^j) uₒ` for the numbers made of the even and of the odd fields. A plain round
computes `uₑ + uₒ`. For the merged round the second number comes multiplied by its weight
`c = 2^t`, as `v' = c * v`, and

* `Xe = (u &&& m) + (v' &&& (m <<< t)) = uₑ + c vₑ` (masking is done on the two summands
  separately, where the fields are still intact),
* `X = u + v' = Xe + 2^(2^j) (uₒ + c vₒ)` as a natural number (its fields overflow, which does
  not matter since it is never masked),
* `swarMerge = Xe + ((X - Xe) >>> 2^j) = (uₑ + uₒ) + c (vₑ + vₒ)` (7 operations), or
* `swarMergeW = X + (2^(2^j) - 1) * Xe = 2^(2^j) * ((uₑ + uₒ) + c (vₑ + vₒ))` (6 operations).

The second form is used when the result is itself the second partner in the next round, whose
weight is exactly `2^(2^j)`; so the weights never cost an operation of their own. In the same
way `swarStep0W b x = x + (x &&& m₀) = 2 * swarStep0 b x` (2 operations) and
`swarStepW = u + (2^(2^j) - 1) * (u &&& m)` (3 operations) for an unpaired number.

## The pipeline

* tables to 2-bit fields: `swarStep0` (3 operations) or `swarStep0W` (2 operations), alternating;
* pairs of tables to 4-bit fields `≤ 12`, pairs of pairs to 8-bit fields `≤ 120` (`stage`);
* pairs of those to 16-bit fields `≤ 4080` (`swarMerge`), then one unmasked round to 32-bit
  fields `≤ 8160` and a reduction modulo `2^32 - 1`, which adds up the fields (`octSum`).

`wtotFast` does this for lists of any length (`pairFold` is the traversal of a list two elements
at a time; groups of eight tables are combined by Horner's rule), and `wtotFast_eq` is its
specification. For kernel evaluation `wtotF` uses the explicit formulas `wtot2`, …, `wtot8` for
lists of two to eight tables, which are what `wtotFast` unfolds to (`wtot2_eq`, …, by `rfl`), and
`popFast` for a single table.

For `1, 2, …, 8` tables this takes `16, 23, 32, 37, 51, 56, 65, 70` big operations (one of them a
reduction modulo a one-limb constant), instead of `16` per table. All bounds hold for arbitrary
tables below `2^(2^b)` with `5 ≤ b ≤ 24`; outside this range `wtotF` falls back to `wtot`.
-/

@[expose] public section

namespace RACert

/-! ### Digit strings with a digit bound and a digit sum -/

/-- `x` is a string of `n` digits in base `2 ^ w`, all at most `B`, with digit sum `S`. -/
def IsDig (w n B S x : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, x = digitVal w n f ∧ (∀ k, f k ≤ B) ∧ (∀ k, n ≤ k → f k = 0) ∧
    ∑ k ∈ Finset.range n, f k = S

theorem IsDig.mono {w n B B' S x : ℕ} (h : IsDig w n B S x) (hB : B ≤ B') : IsDig w n B' S x := by
  obtain ⟨f, hx, hf, h0, hS⟩ := h
  exact ⟨f, hx, fun k => Nat.le_trans (hf k) hB, h0, hS⟩

theorem IsDig.add_mul {w n B B' S S' x y : ℕ} (c : ℕ) (hx : IsDig w n B S x)
    (hy : IsDig w n B' S' y) : IsDig w n (B + c * B') (S + c * S') (x + c * y) := by
  obtain ⟨f, rfl, hf, hf0, hfS⟩ := hx
  obtain ⟨g, rfl, hg, hg0, hgS⟩ := hy
  refine ⟨fun k => f k + c * g k, ?_,
    fun k => Nat.add_le_add (hf k) (Nat.mul_le_mul_left c (hg k)), fun k hk => ?_, ?_⟩
  · rw [← digitVal_const_mul, digitVal_add]
  · simp only [hf0 k hk, hg0 k hk, Nat.mul_zero, Nat.add_zero]
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfS, hgS]

/-- A truth table is a string of bits. -/
theorem isDig_table {b e : ℕ} (he : e < 2 ^ 2 ^ b) :
    IsDig 1 (2 ^ b) 1 (∑ β ∈ Finset.range (2 ^ b), (e.testBit β).toNat) e := by
  refine ⟨fun k => (e.testBit k).toNat, ?_, fun k => Bool.toNat_le _, fun k hk => ?_, rfl⟩
  · rw [← mod_two_pow_eq_digitVal, Nat.mod_eq_of_lt he]
  · simp only [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) hk)),
      Bool.toNat_false]

theorem sum_range_le_mul {n B : ℕ} {f : ℕ → ℕ} (hf : ∀ k, f k ≤ B) :
    ∑ k ∈ Finset.range n, f k ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hf n
    rw [Finset.sum_range_succ, Nat.succ_mul]
    omega

theorem isDig_pairSum {w m B S : ℕ} {f : ℕ → ℕ} (hf : ∀ k, f k ≤ B)
    (h0 : ∀ k, 2 * m ≤ k → f k = 0) (hS : ∑ k ∈ Finset.range (2 * m), f k = S) :
    IsDig w m (2 * B) S (digitVal w m (pairSum f)) :=
  ⟨pairSum f, rfl, pairSum_le hf, pairSum_eq_zero h0, by rw [sum_pairSum, hS]⟩

theorem IsDig.swarStep0 {b m n S x : ℕ} (hn : n = 2 * m) (hb : 2 * m = 2 ^ b) (hpos : 0 < b)
    (h : IsDig 1 n 1 S x) : IsDig (2 ^ 1) m 2 S (swarStep0 b x) := by
  subst hn
  obtain ⟨f, rfl, hf, h0, hS⟩ := h
  rw [swarStep0_digitVal hb hpos (fun k => Nat.lt_succ_of_le (hf k))]
  exact isDig_pairSum hf h0 hS

theorem IsDig.swarStepC {b j m n B S x : ℕ} (hn : n = 2 * m) (hb : 2 ^ (j + 1) * m = 2 ^ b)
    (hj : j < b) (hB : 2 * B < 2 ^ 2 ^ j) (h : IsDig (2 ^ j) n B S x) :
    IsDig (2 ^ (j + 1)) m (2 * B) S (swarStepC b j x) := by
  subst hn
  obtain ⟨f, rfl, hf, h0, hS⟩ := h
  rw [swarStepC_digitVal hb hj (fun k => Nat.lt_of_le_of_lt
    (by have h1 := hf k; have h2 := hf (k + 1); omega) hB) h0]
  exact isDig_pairSum hf h0 hS

/-! ### Even and odd fields -/

/-- Splitting a digit string into its digits at even and at odd positions. -/
theorem digitVal_split (w m : ℕ) (h : ℕ → ℕ) :
    digitVal w (2 * m) h = digitVal (2 * w) m (fun k => h (2 * k)) +
      2 ^ w * digitVal (2 * w) m (fun k => h (2 * k + 1)) := by
  rw [digitVal_two_mul, ← digitVal_const_mul, digitVal_add]

/-- The even fields `E` and the odd fields `O` of a string of `2^j`-bit fields: the string is
`E + 2^(2^j) O`, masking gives `E`, and a SWAR round gives `E + O`. -/
theorem digitVal_parts {b j m : ℕ} (hb : 2 ^ (j + 1) * m = 2 ^ b) (hj : j < b) {f : ℕ → ℕ}
    (hf : ∀ k, f k < 2 ^ 2 ^ j) :
    ∃ E O, digitVal (2 ^ j) (2 * m) f = E + 2 ^ 2 ^ j * O ∧
      digitVal (2 ^ j) (2 * m) f &&& maskLo b j = E ∧
      digitVal (2 ^ (j + 1)) m (pairSum f) = E + O := by
  have hm := digitVal_shiftRight_and_maskLo hb hj (e := 0) (Nat.zero_le 1) hf
  simp only [Nat.mul_zero, Nat.shiftRight_zero, Nat.add_zero] at hm
  refine ⟨digitVal (2 ^ (j + 1)) m (fun k => f (2 * k)),
    digitVal (2 ^ (j + 1)) m (fun k => f (2 * k + 1)), ?_, hm, ?_⟩
  · rw [pow_succ' 2 j]
    exact digitVal_split (2 ^ j) m f
  · rw [digitVal_add]
    rfl

theorem mul_and_shiftLeft {t c : ℕ} (hc : c = 2 ^ t) (v M : ℕ) :
    (c * v) &&& (M <<< t) = c * (v &&& M) := by
  subst hc
  rw [Nat.mul_comm (2 ^ t) v, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_and_distrib, Nat.shiftLeft_eq,
    Nat.mul_comm]

/-! ### Merged SWAR rounds -/

/-- The first SWAR round with doubled result, `x + (x &&& 0x5555…) = 2 * swarStep0 b x`, in two
operations. -/
def swarStep0W (b x : ℕ) : ℕ := Nat.add x (Nat.land x (maskLo b 0))

/-- A SWAR round with result multiplied by `k + 1 = 2^(2^j)`, in three operations:
`u + k * (u &&& maskLo b j) = 2^(2^j) * swarStep b j u`. -/
def swarStepW (b j k u : ℕ) : ℕ := Nat.add u (Nat.mul k (Nat.land u (maskLo b j)))

/-- A merged SWAR round in seven operations: for `v = 2^t * v₀`,
`swarMerge b j t u v = swarStep b j u + 2^t * swarStep b j v₀`. -/
def swarMerge (b j t u v : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.land u (maskLo b j)) (Nat.land v (Nat.shiftLeft (maskLo b j) t)))
    (Nat.shiftRight
      (Nat.sub (Nat.add u v)
        (Nat.add (Nat.land u (maskLo b j)) (Nat.land v (Nat.shiftLeft (maskLo b j) t))))
      (Nat.pow 2 j))

/-- A merged SWAR round with result multiplied by `k + 1 = 2^(2^j)`, in six operations: for
`v = 2^t * v₀`, `swarMergeW b j t k u v = 2^(2^j) * (swarStep b j u + 2^t * swarStep b j v₀)`. -/
def swarMergeW (b j t k u v : ℕ) : ℕ :=
  Nat.add (Nat.add u v)
    (Nat.mul k (Nat.add (Nat.land u (maskLo b j)) (Nat.land v (Nat.shiftLeft (maskLo b j) t))))

section parts

variable {b j t c k u v E O E' O' : ℕ}

theorem swarStep0W_parts (hu : u = E + 2 * O) (hue : u &&& maskLo b 0 = E) :
    swarStep0W b u = 2 * (E + O) := by
  change u + (u &&& maskLo b 0) = _
  rw [hue, hu]
  omega

theorem swarStepW_parts (hk : k + 1 = 2 ^ 2 ^ j) (hu : u = E + 2 ^ 2 ^ j * O)
    (hue : u &&& maskLo b j = E) : swarStepW b j k u = 2 ^ 2 ^ j * (E + O) := by
  change u + k * (u &&& maskLo b j) = _
  rw [hue, hu, ← hk]
  ring

theorem swarMerge_parts (hc : c = 2 ^ t) (hu : u = E + 2 ^ 2 ^ j * O)
    (hue : u &&& maskLo b j = E) (hv : v = E' + 2 ^ 2 ^ j * O') (hve : v &&& maskLo b j = E') :
    swarMerge b j t u (c * v) = (E + O) + c * (E' + O') := by
  have hX : u + c * v = (E + c * E') + 2 ^ 2 ^ j * (O + c * O') := by
    rw [hu, hv]
    ring
  change ((u &&& maskLo b j) + ((c * v) &&& (maskLo b j <<< t))) +
    ((u + c * v - ((u &&& maskLo b j) + ((c * v) &&& (maskLo b j <<< t)))) >>> 2 ^ j) = _
  rw [mul_and_shiftLeft hc, hue, hve, hX, Nat.add_sub_cancel_left, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  ring

theorem swarMergeW_parts (hc : c = 2 ^ t) (hk : k + 1 = 2 ^ 2 ^ j) (hu : u = E + 2 ^ 2 ^ j * O)
    (hue : u &&& maskLo b j = E) (hv : v = E' + 2 ^ 2 ^ j * O') (hve : v &&& maskLo b j = E') :
    swarMergeW b j t k u (c * v) = 2 ^ 2 ^ j * ((E + O) + c * (E' + O')) := by
  change (u + c * v) + k * ((u &&& maskLo b j) + ((c * v) &&& (maskLo b j <<< t))) = _
  rw [mul_and_shiftLeft hc, hue, hve, hu, hv, ← hk]
  ring

end parts

/-- The doubled first round, for a string of bits. -/
theorem IsDig.swarStep0W {b m n S x : ℕ} (hn : n = 2 * m) (hb : 2 * m = 2 ^ b) (hpos : 0 < b)
    (h : IsDig 1 n 1 S x) : ∃ y, IsDig (2 ^ 1) m 2 S y ∧ swarStep0W b x = 2 * y := by
  subst hn
  obtain ⟨f, rfl, hf, h0, hS⟩ := h
  obtain ⟨E, O, hu, hue, hEO⟩ := digitVal_parts (b := b) (j := 0) (m := m) (f := f)
    (by rw [Nat.zero_add, pow_one]; exact hb) hpos
    (fun k => by rw [pow_zero, pow_one]; exact Nat.lt_succ_of_le (hf k))
  simp only [pow_zero, pow_one] at hu hue
  have hI : IsDig (2 ^ 1) m 2 S (digitVal (2 ^ (0 + 1)) m (pairSum f)) := isDig_pairSum hf h0 hS
  refine ⟨_, hI, ?_⟩
  rw [hEO]
  exact swarStep0W_parts hu hue

/-- An unpaired number in a round: the plain result and its multiple. -/
theorem single_spec {b j m n k B S u : ℕ} (hn : n = 2 * m) (hb : 2 ^ (j + 1) * m = 2 ^ b)
    (hj : j < b) (hk : k + 1 = 2 ^ 2 ^ j) (hB : B < 2 ^ 2 ^ j) (hu : IsDig (2 ^ j) n B S u) :
    ∃ r, IsDig (2 ^ (j + 1)) m (2 * B) S r ∧ swarStep b j u = r ∧
      swarStepW b j k u = 2 ^ 2 ^ j * r := by
  subst hn
  obtain ⟨f, rfl, hf, hf0, hfS⟩ := hu
  have hf' : ∀ k, f k < 2 ^ 2 ^ j := fun k => Nat.lt_of_le_of_lt (hf k) hB
  obtain ⟨E, O, hu, hue, hEO⟩ := digitVal_parts hb hj hf'
  refine ⟨digitVal (2 ^ (j + 1)) m (pairSum f), isDig_pairSum hf hf0 hfS,
    swarStep_digitVal hb hj hf', ?_⟩
  rw [hEO]
  exact swarStepW_parts hk hu hue

/-- A pair of numbers in a merged round (the second one multiplied by its weight `c = 2^t`):
the plain result and its multiple. -/
theorem merge_spec {b j m n t c k B S S' u y : ℕ} (hn : n = 2 * m)
    (hb : 2 ^ (j + 1) * m = 2 ^ b) (hj : j < b) (hc : c = 2 ^ t) (hk : k + 1 = 2 ^ 2 ^ j)
    (hB : B < 2 ^ 2 ^ j) (hu : IsDig (2 ^ j) n B S u) (hy : IsDig (2 ^ j) n B S' y) :
    ∃ r, IsDig (2 ^ (j + 1)) m (2 * B + c * (2 * B)) (S + c * S') r ∧
      swarMerge b j t u (c * y) = r ∧ swarMergeW b j t k u (c * y) = 2 ^ 2 ^ j * r := by
  subst hn
  obtain ⟨f, rfl, hf, hf0, hfS⟩ := hu
  obtain ⟨g, rfl, hg, hg0, hgS⟩ := hy
  obtain ⟨E, O, hu, hue, hEO⟩ := digitVal_parts hb hj (fun k => Nat.lt_of_le_of_lt (hf k) hB)
  obtain ⟨E', O', hv, hve, hEO'⟩ := digitVal_parts hb hj (fun k => Nat.lt_of_le_of_lt (hg k) hB)
  refine ⟨(E + O) + c * (E' + O'), ?_, swarMerge_parts hc hu hue hv hve,
    swarMergeW_parts hc hk hu hue hv hve⟩
  rw [← hEO, ← hEO']
  exact (isDig_pairSum hf hf0 hfS).add_mul c (isDig_pairSum hg hg0 hgS)

/-! ### Folding a list two elements at a time -/

/-- Fold a list two elements at a time, from the left: `f2 p a rest` (or `f2' p a rest`) for a
pair `p, a` and `f1 p` (or `f1' p`) for an unpaired last element `p`; the primed functions are
used for the results at odd positions. The state consists of `pend`, whether an element `p` is
waiting for its partner, and `odd`, the parity of the position of the next result. -/
noncomputable def pairFold {α : Type} (f2 f2' : ℕ → ℕ → α → α) (f1 f1' : ℕ → α) (z : α)
    (L : List ℕ) : Bool → ℕ → Bool → α :=
  List.rec (motive := fun _ => Bool → ℕ → Bool → α)
    (fun pend p odd =>
      Bool.rec (motive := fun _ => α) z (Bool.rec (motive := fun _ => α) (f1 p) (f1' p) odd) pend)
    (fun a _ ih pend p odd =>
      Bool.rec (motive := fun _ => α) (ih true a odd)
        (Bool.rec (motive := fun _ => α) (f2 p a (ih false 0 true)) (f2' p a (ih false 0 false))
          odd) pend) L

/-- `WRep R c q L T`: the elements `x` of `L` have values `S` in the sense of `R · S x` (which may
depend on the parity of the position; `q` is the parity of the first position), and
`T = ∑ᵢ c^i Sᵢ`. -/
inductive WRep (R : Bool → ℕ → ℕ → Prop) (c : ℕ) : Bool → List ℕ → ℕ → Prop
  | nil (q : Bool) : WRep R c q [] 0
  | cons {q : Bool} {x S : ℕ} {l : List ℕ} {T : ℕ} (hx : R q S x) (hl : WRep R c (!q) l T) :
      WRep R c q (x :: l) (S + c * T)

theorem WRep.nil_inv {R : Bool → ℕ → ℕ → Prop} {c : ℕ} {q : Bool} {T : ℕ}
    (h : WRep R c q [] T) : T = 0 := by
  cases h
  rfl

theorem WRep.cons_inv {R : Bool → ℕ → ℕ → Prop} {c : ℕ} {q : Bool} {x : ℕ} {l : List ℕ} {T : ℕ}
    (h : WRep R c q (x :: l) T) : ∃ S T', R q S x ∧ WRep R c (!q) l T' ∧ T = S + c * T' := by
  cases h with
  | cons hx hl => exact ⟨_, _, hx, hl, rfl⟩

theorem WRep.single {R : Bool → ℕ → ℕ → Prop} {c : ℕ} {q : Bool} {x S : ℕ} (hx : R q S x) :
    WRep R c q [x] S := by
  have h := WRep.cons (c := c) hx (WRep.nil (!q))
  rwa [Nat.mul_zero, Nat.add_zero] at h

/-- The specification of `pairFold`: merging neighbours with weight `c` turns a weighted sum with
weights `c^i` into one with weights `(c^2)^i`. -/
theorem pairFold_sem {α : Type} {f2 f2' : ℕ → ℕ → α → α} {f1 f1' : ℕ → α} {z : α}
    {R : Bool → ℕ → ℕ → Prop} {c c2 : ℕ} {Sem : Bool → α → ℕ → Prop} (hc : c2 = c * c)
    (hz : ∀ q, Sem q z 0)
    (h2 : ∀ p a r S S' T, R false S p → R true S' a → Sem true r T →
      Sem false (f2 p a r) (S + c * S' + c2 * T))
    (h2' : ∀ p a r S S' T, R false S p → R true S' a → Sem false r T →
      Sem true (f2' p a r) (S + c * S' + c2 * T))
    (h1 : ∀ p S, R false S p → Sem false (f1 p) S)
    (h1' : ∀ p S, R false S p → Sem true (f1' p) S) (L : List ℕ) :
    (∀ T q p, WRep R c false L T → Sem q (pairFold f2 f2' f1 f1' z L false p q) T) ∧
      (∀ T q p S, WRep R c true L T → R false S p →
        Sem q (pairFold f2 f2' f1 f1' z L true p q) (S + c * T)) := by
  subst hc
  induction L with
  | nil =>
    refine ⟨fun T q p h => ?_, fun T q p S h hp => ?_⟩
    · rw [h.nil_inv]
      exact hz q
    · rw [h.nil_inv, Nat.mul_zero, Nat.add_zero]
      cases q
      · exact h1 p S hp
      · exact h1' p S hp
  | cons a l ih =>
    refine ⟨fun T q p h => ?_, fun T q p S h hp => ?_⟩
    · obtain ⟨S', T', ha, hl, rfl⟩ := h.cons_inv
      exact ih.2 T' q a S' hl ha
    · obtain ⟨S', T', ha, hl, rfl⟩ := h.cons_inv
      rw [show S + c * (S' + c * T') = S + c * S' + c * c * T' by ring]
      cases q
      · exact h2 p a _ S S' T' hp ha (ih.1 T' true 0 hl)
      · exact h2' p a _ S S' T' hp ha (ih.1 T' false 0 hl)

/-! ### The rounds on lists -/

/-- The numbers between two rounds: digit strings at even positions and `K` times a digit string
at odd positions. -/
def Fld (w n B K : ℕ) (q : Bool) (S x : ℕ) : Prop :=
  ∃ y, IsDig w n B S y ∧ x = bif q then K * y else y

/-- One round on a list: neighbours `p, a` are merged (`a` comes multiplied by its weight `2^t`),
and the results at odd positions are multiplied by `k + 1 = 2^(2^j)`, their weight in the next
round. The functions `pre` and `preW` are applied to the list elements first. -/
noncomputable def stage (b j t k : ℕ) (pre preW : ℕ → ℕ) (L : List ℕ) : List ℕ :=
  pairFold (fun p a r => List.cons (swarMerge b j t (pre p) (preW a)) r)
    (fun p a r => List.cons (swarMergeW b j t k (pre p) (preW a)) r)
    (fun p => List.cons (swarStep b j (pre p)) List.nil)
    (fun p => List.cons (swarStepW b j k (pre p)) List.nil) List.nil L false 0 false

theorem stage_rep {b j m n t c c2 k B Bout : ℕ} {pre preW : ℕ → ℕ} {R : Bool → ℕ → ℕ → Prop}
    (hn : n = 2 * m) (hb : 2 ^ (j + 1) * m = 2 ^ b) (hj : j < b) (hc : c = 2 ^ t)
    (hc2 : c2 = c * c) (hk : k + 1 = 2 ^ 2 ^ j) (hB : B < 2 ^ 2 ^ j)
    (hBout : 2 * B + c * (2 * B) ≤ Bout)
    (hpre : ∀ S p, R false S p → IsDig (2 ^ j) n B S (pre p))
    (hpreW : ∀ S a, R true S a → ∃ y, IsDig (2 ^ j) n B S y ∧ preW a = c * y)
    {L : List ℕ} {T : ℕ} (h : WRep R c false L T) :
    WRep (Fld (2 ^ (j + 1)) m Bout (2 ^ 2 ^ j)) c2 false (stage b j t k pre preW L) T := by
  refine (pairFold_sem (Sem := WRep (Fld (2 ^ (j + 1)) m Bout (2 ^ 2 ^ j)) c2) hc2
    (fun q => WRep.nil q) ?_ ?_ ?_ ?_ L).1 T false 0 h
  · intro p a r S S' T hp ha hr
    obtain ⟨y, hy, hay⟩ := hpreW S' a ha
    obtain ⟨x, hx, h1, -⟩ := merge_spec (k := k) hn hb hj hc hk hB (hpre S p hp) hy
    exact WRep.cons (q := false) ⟨x, hx.mono hBout, by rw [hay]; exact h1⟩ hr
  · intro p a r S S' T hp ha hr
    obtain ⟨y, hy, hay⟩ := hpreW S' a ha
    obtain ⟨x, hx, -, h2⟩ := merge_spec (k := k) hn hb hj hc hk hB (hpre S p hp) hy
    exact WRep.cons (q := true) ⟨x, hx.mono hBout, by rw [hay]; exact h2⟩ hr
  · intro p S hp
    obtain ⟨x, hx, h1, -⟩ := single_spec (k := k) hn hb hj hk hB (hpre S p hp)
    exact WRep.single ⟨x, hx.mono (Nat.le_trans (Nat.le_add_right _ _) hBout), h1⟩
  · intro p S hp
    obtain ⟨x, hx, -, h2⟩ := single_spec (k := k) hn hb hj hk hB (hpre S p hp)
    exact WRep.single ⟨x, hx.mono (Nat.le_trans (Nat.le_add_right _ _) hBout), h2⟩

/-! ### The weighted population count -/

/-- Two numbers with 8-bit fields (the second multiplied by `16`), to their weighted digit sum:
a merged round, an unmasked round and a reduction modulo `2^32 - 1`. -/
def octSum (b p a : ℕ) : ℕ := Nat.mod (swarStepC b 4 (swarMerge b 3 4 p a)) 4294967295

/-- `octSum`, plus `256` times the result `r` for the rest of the list. -/
def octPair (b p a r : ℕ) : ℕ := Nat.add (octSum b p a) (Nat.mul 256 r)

/-- A number with 8-bit fields to its digit sum. -/
def octSingle (b p : ℕ) : ℕ := Nat.mod (swarStepC b 4 (swarStepC b 3 p)) 4294967295

/-- The weighted population count for `5 ≤ b ≤ 24`. -/
noncomputable def wtotFast (b : ℕ) (E : List ℕ) : ℕ :=
  pairFold (octPair b) (octPair b) (octSingle b) (octSingle b) 0
    (stage b 2 2 15 (fun x => x) (fun x => x) (stage b 1 1 3 (swarStep0 b) (swarStep0W b) E))
    false 0 false

/-- The list elements before the first round: truth tables. -/
def Tab (b : ℕ) (_ : Bool) (S e : ℕ) : Prop :=
  e < 2 ^ 2 ^ b ∧ S = ∑ β ∈ Finset.range (2 ^ b), (e.testBit β).toNat

theorem wrep_tables {b : ℕ} {E : List ℕ} (hE : ∀ e ∈ E, e < 2 ^ 2 ^ b) (q : Bool) :
    WRep (Tab b) 2 q E (∑ β ∈ Finset.range (2 ^ b), wsum β E) := by
  induction E generalizing q with
  | nil =>
    simp only [wsum_nil, Finset.sum_const_zero]
    exact WRep.nil q
  | cons e es ih =>
    have h := WRep.cons (c := 2) (q := q) (R := Tab b) ⟨hE e List.mem_cons_self, rfl⟩
      (ih (fun x hx => hE x (List.mem_cons_of_mem _ hx)) (!q))
    rw [show (∑ β ∈ Finset.range (2 ^ b), wsum β (e :: es)) =
        ∑ β ∈ Finset.range (2 ^ b), (e.testBit β).toNat +
          2 * ∑ β ∈ Finset.range (2 ^ b), wsum β es by
      simp only [wsum_cons, Finset.sum_add_distrib, Finset.mul_sum]]
    exact h

/-- The last two steps: an unmasked round to 32-bit fields and the reduction modulo
`2^32 - 1`. -/
theorem fin_spec {d S w : ℕ} (hd : d ≤ 19) (h : IsDig (2 ^ 4) (2 ^ (d + 1)) 4080 S w) :
    swarStepC (d + 5) 4 w % 4294967295 = S := by
  obtain ⟨f, hx, hf, -, hS⟩ := h.swarStepC (b := d + 5) (m := 2 ^ d) (by ring) (by ring)
    (by omega) (by norm_num)
  have hmod := digitVal_mod_two_pow_sub_one 32 (2 ^ d) f
  have hle : S ≤ 2 ^ d * (2 * 4080) := by
    rw [← hS]
    exact sum_range_le_mul hf
  have h19 : 2 ^ d ≤ 524288 := Nat.pow_le_pow_right (by omega) hd
  rw [hx]
  change digitVal 32 (2 ^ d) f % (2 ^ 32 - 1) = S
  rw [hmod, hS]
  exact Nat.mod_eq_of_lt (by omega)

theorem wtotFast_eq {d : ℕ} {E : List ℕ} (hd : d ≤ 19) (hE : ∀ e ∈ E, e < 2 ^ 2 ^ (d + 5)) :
    wtotFast (d + 5) E = ∑ β ∈ Finset.range (2 ^ (d + 5)), wsum β E := by
  -- tables to 4-bit fields
  have hB : WRep (Fld (2 ^ (1 + 1)) (2 ^ (d + 3)) 12 (2 ^ 2 ^ 1)) 4 false
      (stage (d + 5) 1 1 3 (swarStep0 (d + 5)) (swarStep0W (d + 5)) E)
      (∑ β ∈ Finset.range (2 ^ (d + 5)), wsum β E) := by
    refine stage_rep (n := 2 ^ (d + 4)) (B := 2) (c := 2) (R := Tab (d + 5)) (by ring) (by ring)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
      (wrep_tables hE false)
    · rintro S p ⟨hp, rfl⟩
      exact (isDig_table hp).swarStep0 (by ring) (by ring) (by omega)
    · rintro S a ⟨ha, rfl⟩
      exact (isDig_table ha).swarStep0W (by ring) (by ring) (by omega)
  -- 4-bit fields to 8-bit fields
  have hC : WRep (Fld (2 ^ (2 + 1)) (2 ^ (d + 2)) 120 (2 ^ 2 ^ 2)) 16 false
      (stage (d + 5) 2 2 15 (fun x => x) (fun x => x)
        (stage (d + 5) 1 1 3 (swarStep0 (d + 5)) (swarStep0W (d + 5)) E))
      (∑ β ∈ Finset.range (2 ^ (d + 5)), wsum β E) := by
    refine stage_rep (n := 2 ^ (d + 3)) (B := 12) (c := 4) (by ring) (by ring)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ hB
    · rintro S p ⟨y, hy, hp⟩
      have hp' : p = y := hp
      rw [hp']
      exact hy
    · rintro S a ⟨y, hy, ha⟩
      exact ⟨y, hy, ha⟩
  -- 8-bit fields to the result
  have hpair : ∀ p a r S S' T, Fld (2 ^ (2 + 1)) (2 ^ (d + 2)) 120 (2 ^ 2 ^ 2) false S p →
      Fld (2 ^ (2 + 1)) (2 ^ (d + 2)) 120 (2 ^ 2 ^ 2) true S' a → r = T →
      octPair (d + 5) p a r = S + 16 * S' + 256 * T := by
    rintro p a r S S' T ⟨u, hu, hp⟩ ⟨y, hy, ha⟩ rfl
    have hp' : p = u := hp
    have ha' : a = 16 * y := ha
    rw [hp', ha']
    obtain ⟨x, hx, h1, -⟩ := merge_spec (b := d + 5) (j := 3) (t := 4) (c := 16) (k := 255)
      (m := 2 ^ (d + 1)) (by ring) (by ring) (by omega) (by norm_num) (by norm_num)
      (by norm_num) hu hy
    change swarStepC (d + 5) 4 (swarMerge (d + 5) 3 4 u (16 * y)) % 4294967295 + 256 * r = _
    rw [h1, fin_spec hd (hx.mono (by norm_num))]
  have hsingle : ∀ p S, Fld (2 ^ (2 + 1)) (2 ^ (d + 2)) 120 (2 ^ 2 ^ 2) false S p →
      octSingle (d + 5) p = S := by
    rintro p S ⟨u, hu, hp⟩
    have hp' : p = u := hp
    rw [hp']
    exact fin_spec hd ((hu.swarStepC (by ring) (by ring) (by omega) (by norm_num)).mono
      (by norm_num))
  exact (pairFold_sem (c := 16) (c2 := 256) (Sem := fun _ r T => r = T) (by norm_num)
    (fun _ => rfl) hpair hpair hsingle hsingle _).1 _ false 0 hC

/-! ### Explicit formulas for up to eight tables

The kernel evaluates `wtotFast` with some overhead for the list traversals, which is noticeable
for small tables. For lists of at most eight tables `wtotF` therefore uses the following explicit
formulas; they are what `wtotFast` unfolds to. -/

/-- `wtotFast b [a0, a1]`. -/
def wtot2 (b a0 a1 : ℕ) : ℕ :=
  octSingle b (swarStep b 2 (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1)))

/-- `wtotFast b [a0, a1, a2]`. -/
def wtot3 (b a0 a1 a2 : ℕ) : ℕ :=
  octSingle b
    (swarMerge b 2 2
      (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1))
      (swarStepW b 1 3 (swarStep0 b a2)))

/-- `wtotFast b [a0, a1, a2, a3]`. -/
def wtot4 (b a0 a1 a2 a3 : ℕ) : ℕ :=
  octSingle b
    (swarMerge b 2 2
      (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1))
      (swarMergeW b 1 1 3 (swarStep0 b a2) (swarStep0W b a3)))

/-- `wtotFast b [a0, a1, a2, a3, a4]`. -/
def wtot5 (b a0 a1 a2 a3 a4 : ℕ) : ℕ :=
  octSum b
    (swarMerge b 2 2
      (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1))
      (swarMergeW b 1 1 3 (swarStep0 b a2) (swarStep0W b a3)))
    (swarStepW b 2 15 (swarStep b 1 (swarStep0 b a4)))

/-- `wtotFast b [a0, a1, a2, a3, a4, a5]`. -/
def wtot6 (b a0 a1 a2 a3 a4 a5 : ℕ) : ℕ :=
  octSum b
    (swarMerge b 2 2
      (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1))
      (swarMergeW b 1 1 3 (swarStep0 b a2) (swarStep0W b a3)))
    (swarStepW b 2 15 (swarMerge b 1 1 (swarStep0 b a4) (swarStep0W b a5)))

/-- `wtotFast b [a0, a1, a2, a3, a4, a5, a6]`. -/
def wtot7 (b a0 a1 a2 a3 a4 a5 a6 : ℕ) : ℕ :=
  octSum b
    (swarMerge b 2 2
      (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1))
      (swarMergeW b 1 1 3 (swarStep0 b a2) (swarStep0W b a3)))
    (swarMergeW b 2 2 15
      (swarMerge b 1 1 (swarStep0 b a4) (swarStep0W b a5))
      (swarStepW b 1 3 (swarStep0 b a6)))

/-- `wtotFast b [a0, a1, a2, a3, a4, a5, a6, a7]`. -/
def wtot8 (b a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) : ℕ :=
  octSum b
    (swarMerge b 2 2
      (swarMerge b 1 1 (swarStep0 b a0) (swarStep0W b a1))
      (swarMergeW b 1 1 3 (swarStep0 b a2) (swarStep0W b a3)))
    (swarMergeW b 2 2 15
      (swarMerge b 1 1 (swarStep0 b a4) (swarStep0W b a5))
      (swarMergeW b 1 1 3 (swarStep0 b a6) (swarStep0W b a7)))

theorem wtot2_eq (b a0 a1 : ℕ) :
    wtot2 b a0 a1 = wtotFast b [a0, a1] := rfl

theorem wtot3_eq (b a0 a1 a2 : ℕ) :
    wtot3 b a0 a1 a2 = wtotFast b [a0, a1, a2] := rfl

theorem wtot4_eq (b a0 a1 a2 a3 : ℕ) :
    wtot4 b a0 a1 a2 a3 = wtotFast b [a0, a1, a2, a3] := rfl

theorem wtot5_eq (b a0 a1 a2 a3 a4 : ℕ) :
    wtot5 b a0 a1 a2 a3 a4 = wtotFast b [a0, a1, a2, a3, a4] := rfl

theorem wtot6_eq (b a0 a1 a2 a3 a4 a5 : ℕ) :
    wtot6 b a0 a1 a2 a3 a4 a5 = wtotFast b [a0, a1, a2, a3, a4, a5] := rfl

theorem wtot7_eq (b a0 a1 a2 a3 a4 a5 a6 : ℕ) :
    wtot7 b a0 a1 a2 a3 a4 a5 a6 = wtotFast b [a0, a1, a2, a3, a4, a5, a6] := rfl

theorem wtot8_eq (b a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) :
    wtot8 b a0 a1 a2 a3 a4 a5 a6 a7 = wtotFast b [a0, a1, a2, a3, a4, a5, a6, a7] := rfl

/-- `∑ j, 2 ^ j * popcount (E j)` with few big-number operations. -/
noncomputable def wtotF (b : ℕ) (E : List ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (wtot b E)
    (Bool.rec (motive := fun _ => ℕ) (wtot b E)
      (List.rec (motive := fun _ => ℕ) 0 (fun a0 l0 _ =>
        List.rec (motive := fun _ => ℕ) (popFast b a0) (fun a1 l1 _ =>
          List.rec (motive := fun _ => ℕ) (wtot2 b a0 a1) (fun a2 l2 _ =>
            List.rec (motive := fun _ => ℕ) (wtot3 b a0 a1 a2) (fun a3 l3 _ =>
              List.rec (motive := fun _ => ℕ) (wtot4 b a0 a1 a2 a3) (fun a4 l4 _ =>
                List.rec (motive := fun _ => ℕ) (wtot5 b a0 a1 a2 a3 a4) (fun a5 l5 _ =>
                  List.rec (motive := fun _ => ℕ) (wtot6 b a0 a1 a2 a3 a4 a5) (fun a6 l6 _ =>
                    List.rec (motive := fun _ => ℕ) (wtot7 b a0 a1 a2 a3 a4 a5 a6) (fun a7 l7 _ =>
                      List.rec (motive := fun _ => ℕ) (wtot8 b a0 a1 a2 a3 a4 a5 a6 a7)
                        (fun _ _ _ => wtotFast b E)
                        l7) l6) l5) l4) l3) l2) l1) l0) E)
      (Nat.ble b 24)) (Nat.ble 5 b)

theorem wtotF_eq {b : ℕ} {E : List ℕ} (hE : ∀ e ∈ E, e < 2 ^ 2 ^ b) :
    wtotF b E = ∑ β ∈ Finset.range (2 ^ b), wsum β E := by
  rw [wtotF]
  cases h5 : Nat.ble 5 b
  · exact wtot_eq hE
  cases h24 : Nat.ble b 24
  · exact wtot_eq hE
  rw [Nat.ble_eq] at h5 h24
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 5 := ⟨b - 5, by omega⟩
  have hd : d ≤ 19 := by omega
  rcases E with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
    ⟨a8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · change (0 : ℕ) = _
    simp only [wsum_nil, Finset.sum_const_zero]
  · have he := hE a0 List.mem_cons_self
    change popFast (d + 5) a0 = _
    rw [← wtot_eq hE, wtot_cons, wtot_nil, popcountF_eq he, popFast_eq (by omega) he]
    omega
  · exact (wtot2_eq _ _ _).trans (wtotFast_eq hd hE)
  · exact (wtot3_eq _ _ _ _).trans (wtotFast_eq hd hE)
  · exact (wtot4_eq _ _ _ _ _).trans (wtotFast_eq hd hE)
  · exact (wtot5_eq _ _ _ _ _ _).trans (wtotFast_eq hd hE)
  · exact (wtot6_eq _ _ _ _ _ _ _).trans (wtotFast_eq hd hE)
  · exact (wtot7_eq _ _ _ _ _ _ _ _).trans (wtotFast_eq hd hE)
  · exact (wtot8_eq _ _ _ _ _ _ _ _ _).trans (wtotFast_eq hd hE)
  · exact wtotFast_eq hd hE

end RACert
