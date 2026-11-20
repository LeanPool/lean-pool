/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Words.Periods
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Infinite words and ultimately periodic infinite words

Infinite words are functions `ℕ → α`, with finite prefixes `streamPrefix ξ n`, periods
(`StreamPeriod`) and least periods (`LeastStreamPeriod`); the positive periods of an infinite
word are the multiples of its least period. A `Ray` is an ultimately periodic infinite word
`stem · loop^ω`, given by a finite stem and a nonempty loop. In the bound on rejected tails,
rays describe live periodic continuations of runs of a reader, and the comparisons between
suffixes of rays are the comparisons that a channel records.

The onset of a ray is the least position from which it is purely periodic, and its period is
its least period. Fine–Wilf for purely periodic infinite words (`streamEq_of_agree`) shows that
two suffixes of rays, from positions `a` and `b`, that agree on a prefix of length
`max(A - a, A' - b, 0) + ν + ν'` agree everywhere, where `A`, `A'` are the onsets and `ν`, `ν'`
the periods (`stream_suffix_eq_of_prefix_eq`); so equality of suffixes is decidable. Equal
suffixes start at the same distance before the onsets, or both at or after them
(`suffix_eq_cases`).

## Main declarations

- `streamPrefix`, `prepend`: finite prefixes of infinite words and prefixing by a finite word.
- `StreamPeriod`, `LeastStreamPeriod`, `leastPeriod_dvd_iff`: periods of infinite words.
- `PeriodicFrom`: an infinite word is purely periodic from a position on.
- `streamEq_of_agree`: Fine–Wilf for purely periodic infinite words.
- `Ray`, `Ray.stream`, `Ray.onset`, `Ray.period`: rays, their infinite words, onsets and
  periods.
- `Ray.leastStreamPeriod_shift`: every suffix from the onset on has least period `period`.
- `Ray.stream_suffix_eq_of_prefix_eq`, `Ray.suffix_eq_cases`: comparison of suffixes of two rays.
- `Ray.streamPrefix_stream`: the finite prefixes of a ray.
- `Ray.prefixBeforeOnset`, `Ray.suffixBeforeOnset`: the text of a ray before its onset, and its
  part after a cut.
-/

@[expose] public section


namespace DeciSigma1.Words

open DeciSigma1.Words (pow)

/-! ## Finite prefixes and periods of infinite words -/

section Streams

variable {α : Type*}

/-- The finite prefix of length `n` of an infinite word. -/
def streamPrefix (ξ : ℕ → α) (n : ℕ) : List α := List.ofFn (fun i : Fin n => ξ i)

theorem streamPrefix_succ (ξ : ℕ → α) (n : ℕ) :
    streamPrefix ξ (n + 1) = streamPrefix ξ n ++ [ξ n] := by
  simpa [streamPrefix, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n + 1) => ξ i))

@[simp] theorem length_streamPrefix (ξ : ℕ → α) (n : ℕ) :
    (streamPrefix ξ n).length = n := by simp [streamPrefix]

@[simp] theorem getElem_streamPrefix (ξ : ℕ → α) (n i : ℕ) (h : i < n) :
    (streamPrefix ξ n)[i]'(by simpa using h) = ξ i := by simp [streamPrefix]

@[simp] theorem take_streamPrefix (ξ : ℕ → α) (n k : ℕ) :
    (streamPrefix ξ n).take k = streamPrefix ξ (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [streamPrefix]

/-- Prefixing an infinite word by a finite word. -/
def prepend (w : List α) (ξ : ℕ → α) (i : ℕ) : α :=
  if h : i < w.length then w[i] else ξ (i - w.length)

theorem prepend_prefix (w : List α) (ξ : ℕ → α) :
    streamPrefix (prepend w ξ) w.length = w := by
  apply List.ext_getElem <;> simp [streamPrefix, prepend]

theorem prepend_prefix_add (w : List α) (ξ : ℕ → α) (n : ℕ) :
    streamPrefix (prepend w ξ) (w.length + n) = w ++ streamPrefix ξ n := by
  induction n with
  | zero => simpa only [Nat.add_zero, show streamPrefix ξ 0 = [] from rfl,
      List.append_nil] using prepend_prefix w ξ
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih]
    simp [prepend, List.append_assoc, streamPrefix_succ]

/-- The infinite word `ξ` has period `p`: `ξ (i + p) = ξ i` for every `i`. -/
def StreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop := ∀ i, ξ (i + p) = ξ i

theorem streamPeriod_mod {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    ξ n = ξ (n % p) := by
  by_cases hp : p = 0
  · simp [hp]
  · induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n < p
      · simp [Nat.mod_eq_of_lt hn]
      · have hle : p ≤ n := by omega
        calc
          ξ n = ξ (n - p) := by simpa [Nat.sub_add_cancel hle] using h (n - p)
          _ = ξ ((n - p) % p) := ih _ (by omega)
          _ = ξ (n % p) := by rw [← Nat.mod_eq_sub_mod hle]

theorem streamPeriod_prefix {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    List.HasPeriod (streamPrefix ξ n) p := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hi' : i <
      n := by simpa only [length_streamPrefix] using (by omega : i < (streamPrefix ξ n).length)
  have hip : i + p < n := by simp only [length_streamPrefix] at hi; omega
  simp only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi', dite_eq_left hip, h i]

theorem streamPeriod_gcd {ξ : ℕ → α} {p q : ℕ}
    (hp : StreamPeriod ξ p) (hq : StreamPeriod ξ q) : StreamPeriod ξ (Nat.gcd p q) := by
  intro i
  let n := i + p + q + Nat.gcd p q + 1
  have hg := (streamPeriod_prefix hp n).gcd (streamPeriod_prefix hq n) (by simp [n]; omega)
  have hh := (List.hasPeriod_iff_getElem?.mp hg) i (by simp [n]; omega)
  have hi : i < n := by dsimp [n]; omega
  have hj : i + Nat.gcd p q < n := by dsimp [n]; omega
  simpa only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi, dite_eq_left hj,
    Option.some.injEq] using hh.symm

theorem streamPrefix_add (ξ : ℕ → α) (k n : ℕ) :
    streamPrefix ξ (k + n) = streamPrefix ξ k ++ streamPrefix (fun i => ξ (k + i)) n := by
  induction n with
  | zero => simp [streamPrefix]
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih, streamPrefix_succ, List.append_assoc]

theorem streamPeriod_shift {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (k : ℕ) :
    StreamPeriod (fun i => ξ (k + i)) p := by
  intro i; simpa [Nat.add_assoc] using h (k + i)

/-- The least positive period of an infinite word. -/
def LeastStreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop :=
  0 < p ∧ StreamPeriod ξ p ∧ ∀ q, 0 < q → StreamPeriod ξ q → p ≤ q

/-- If an infinite word with a positive period has a suffix with period `q`, the word itself has
period `q`. -/
theorem period_of_suffix {ξ : ℕ → α} {p q k : ℕ} (hp : 0 < p)
    (hξ : StreamPeriod ξ p) (hq : StreamPeriod (fun i => ξ (k + i)) q) :
    StreamPeriod ξ q := by
  intro i
  have hlarge : k ≤ i + k * p := by nlinarith
  have hh := hq (i + k * p - k)
  change ξ (k + (i + k * p - k + q)) = ξ (k + (i + k * p - k)) at hh
  have he₁ : k + (i + k * p - k + q) = i + q + k * p := by omega
  have he₂ : k + (i + k * p - k) = i + k * p := by omega
  rw [he₁, he₂, streamPeriod_mod hξ (i + q + k * p),
    streamPeriod_mod hξ (i + k * p)] at hh
  simpa only [Nat.add_mul_mod_self_right, ← streamPeriod_mod hξ] using hh

/-- Every suffix of an infinite word has the same least period. -/
theorem leastPeriod_suffix {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p) (k : ℕ) :
    LeastStreamPeriod (fun i => ξ (k + i)) p := by
  refine ⟨hp.1, streamPeriod_shift hp.2.1 k, ?_⟩
  intro q hq hper
  exact hp.2.2 q hq (period_of_suffix hp.1 hp.2.1 hper)

/-- The periods of an infinite word are the multiples of its least positive period. -/
theorem leastPeriod_dvd_iff {ξ : ℕ → α} {p q : ℕ} (hp : LeastStreamPeriod ξ p) :
    StreamPeriod ξ q ↔ p ∣ q := by
  constructor
  · intro hper
    have hg := streamPeriod_gcd hp.2.1 hper
    have hgp := Nat.gcd_pos_of_pos_left q hp.1
    have hmin := hp.2.2 (Nat.gcd p q) hgp hg
    have hle := Nat.gcd_le_left q hp.1
    have he : Nat.gcd p q = p := by omega
    rw [← he]; exact Nat.gcd_dvd_right p q
  · intro hd i
    rw [streamPeriod_mod hp.2.1 (i + q), streamPeriod_mod hp.2.1 i]
    congr 1
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]

end Streams

variable {α : Type}

/-! ## Pure periodicity from a position -/

/-- `ξ` is purely periodic with period `p` from position `A` on. -/
def PeriodicFrom (ξ : ℕ → α) (A p : ℕ) : Prop := StreamPeriod (fun t => ξ (A + t)) p

theorem PeriodicFrom.mono {ξ : ℕ → α} {A A' p : ℕ} (h : PeriodicFrom ξ A p) (hA : A ≤ A') :
    PeriodicFrom ξ A' p := by
  intro t
  have := h (A' - A + t)
  simp only at this ⊢
  rwa [show A + (A' - A + t + p) = A' + (t + p) by omega,
    show A + (A' - A + t) = A' + t by omega] at this

theorem PeriodicFrom.add_mul {ξ : ℕ → α} {A p : ℕ} (h : PeriodicFrom ξ A p) (s m : ℕ) :
    ξ (A + s + m * p) = ξ (A + s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ξ (A + (s + m * p + p)) = ξ (A + (s + m * p)) := h (s + m * p)
    calc ξ (A + s + (m + 1) * p) = ξ (A + (s + m * p + p)) := by congr 1; ring
      _ = ξ (A + (s + m * p)) := h1
      _ = ξ (A + s + m * p) := by congr 1; ring
      _ = ξ (A + s) := ih

/-- **Fine–Wilf for infinite periodic words.** Two purely periodic infinite words with least
periods `p` and `q` that agree on their first `p + q` letters are equal. -/
theorem streamEq_of_agree {ξ η : ℕ → α} {p q : ℕ} (hξ : LeastStreamPeriod ξ p)
    (hη : LeastStreamPeriod η q) (h : ∀ t < p + q, ξ t = η t) : ∀ t, ξ t = η t := by
  set n := p + q
  have hw : streamPrefix ξ n = streamPrefix η n := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [streamPrefix, List.getElem_ofFn]
    exact h i (by simpa using hi)
  have hwp : (streamPrefix ξ n).HasPeriod p := streamPeriod_prefix hξ.2.1 n
  have hwq : (streamPrefix ξ n).HasPeriod q := hw ▸ streamPeriod_prefix hη.2.1 n
  have hg := hwp.gcd hwq (by simp only [length_streamPrefix, n]; omega)
  set g := Nat.gcd p q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left q hξ.1
  have hper : PeriodicOn (streamPrefix ξ n) g 0 n := by
    rw [periodicOn_iff_hasPeriod (Nat.zero_le _) (by simp)]
    simpa using hg
  -- positions below `n` congruent modulo `g` carry equal letters
  have hmod : ∀ x y, x < n → y < n → x % g = y % g → ξ x = ξ y := by
    intro x y hx hy hxy
    have := hper.eq_of_mod (Nat.zero_le x) (Nat.zero_le y) hx hy hxy
    rw [List.getElem?_eq_getElem (by simpa using hx), List.getElem?_eq_getElem (by simpa using hy),
      Option.some_inj] at this
    simpa [hx, hy] using this
  -- `g` is a period of `ξ`, hence `g = p`
  have hgp : g = p := by
    have hgξ : StreamPeriod ξ g := by
      intro i
      rw [streamPeriod_mod hξ.2.1 (i + g), streamPeriod_mod hξ.2.1 i]
      apply hmod _ _ (by have := Nat.mod_lt (i + g) hξ.1; omega)
        (by have := Nat.mod_lt i hξ.1; omega)
      rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left p q), Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left p q),
        Nat.add_mod_right]
    exact le_antisymm (Nat.le_of_dvd hξ.1 (Nat.gcd_dvd_left p q)) (hξ.2.2 g hgpos hgξ)
  -- likewise `g = q`
  have hmodη : ∀ x y, x < n → y < n → x % g = y % g → η x = η y := by
    intro x y hx hy hxy
    rw [← h x hx, ← h y hy]; exact hmod x y hx hy hxy
  have hgq : g = q := by
    have hgη : StreamPeriod η g := by
      intro i
      rw [streamPeriod_mod hη.2.1 (i + g), streamPeriod_mod hη.2.1 i]
      apply hmodη _ _ (by have := Nat.mod_lt (i + g) hη.1; omega)
        (by have := Nat.mod_lt i hη.1; omega)
      rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right p q),
        Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right p q), Nat.add_mod_right]
    exact le_antisymm (Nat.le_of_dvd hη.1 (Nat.gcd_dvd_right p q)) (hη.2.2 g hgpos hgη)
  intro t
  rw [streamPeriod_mod hξ.2.1 t, streamPeriod_mod hη.2.1 t, ← hgp, ← hgq]
  exact h _ (by have := Nat.mod_lt t hgpos; omega)

/-! ## Comparisons between prefixes of infinite words -/

theorem drop_streamPrefix (ξ : ℕ → α) {a n : ℕ} (ha : a ≤ n) :
    (streamPrefix ξ n).drop a = streamPrefix (fun t => ξ (a + t)) (n - a) := by
  conv_lhs => rw [show n = a + (n - a) by omega, streamPrefix_add]
  exact List.drop_left' (by simp)

theorem streamPrefix_prefix_iff (ξ η : ℕ → α) (m m' : ℕ) :
    streamPrefix η m <+: streamPrefix ξ m' ↔ m ≤ m' ∧ ∀ t < m, η t = ξ t := by
  constructor
  · intro h
    have hlen := h.length_le
    simp only [length_streamPrefix] at hlen
    refine ⟨hlen, fun t ht => ?_⟩
    have := h.getElem (by simpa using ht)
    simpa [streamPrefix] using this
  · rintro ⟨hle, heq⟩
    rw [List.prefix_iff_eq_take, length_streamPrefix, take_streamPrefix, min_eq_left hle]
    apply List.ext_getElem (by simp)
    intro t ht _
    simp only [streamPrefix, List.getElem_ofFn]
    exact heq t (by simpa using ht)

/-- A suffix of a prefix of `η` is a prefix of a suffix of a prefix of `ξ` if and only if it is
not longer and the two infinite words agree on its length. This is the form in which channels
compare prefixes of rays. -/
theorem drop_streamPrefix_prefix_iff (ξ η : ℕ → α) {L L' a b : ℕ} (hb : b ≤ L) (ha : a ≤ L') :
    (streamPrefix η L).drop b <+: (streamPrefix ξ L').drop a ↔
      L - b ≤ L' - a ∧ ∀ t < L - b, η (b + t) = ξ (a + t) := by
  rw [drop_streamPrefix η hb, drop_streamPrefix ξ ha, streamPrefix_prefix_iff]

/-! ## Suffixes of prefixes of infinite words -/

theorem streamPrefix_suffix_iff (ξ η : ℕ → α) (m n : ℕ) :
    streamPrefix η m <:+ streamPrefix ξ n ↔ m ≤ n ∧ ∀ t < m, η t = ξ (n - m + t) := by
  constructor
  · intro h
    have hlen := h.length_le
    simp only [length_streamPrefix] at hlen
    refine ⟨hlen, fun t ht => ?_⟩
    rw [List.suffix_iff_eq_drop] at h
    simp only [length_streamPrefix] at h
    rw [drop_streamPrefix ξ (by omega)] at h
    have := congrArg (fun l => l[t]?) h
    rw [List.getElem?_eq_getElem (by simpa using ht), List.getElem?_eq_getElem (by simp; omega),
      getElem_streamPrefix _ _ _ ht, getElem_streamPrefix _ _ _ (by omega)] at this
    exact Option.some.inj this
  · rintro ⟨hle, heq⟩
    rw [List.suffix_iff_eq_drop, length_streamPrefix, length_streamPrefix,
      drop_streamPrefix ξ (by omega)]
    apply List.ext_getElem (by simp; omega)
    intro t h1 h2
    simp only [length_streamPrefix] at h1
    rw [getElem_streamPrefix _ _ _ h1, getElem_streamPrefix _ _ _ (by omega)]
    exact heq t h1

/-! ## Rays -/

/-- A ray: the ultimately periodic infinite word `stem · loop^ω`. -/
structure Ray (α : Type) where
  /-- The finite word before the periodic part. -/
  stem : List α
  /-- The repeated word. -/
  loop : List α
  loop_ne_nil : loop ≠ []

namespace Ray

variable (Ω : Ray α)

theorem loop_length_pos : 0 < Ω.loop.length := List.length_pos_iff.mpr Ω.loop_ne_nil

/-- The periodic part `loop^ω`. -/
def periodicTail (n : ℕ) : α := Ω.loop[n % Ω.loop.length]'(Nat.mod_lt _ Ω.loop_length_pos)

/-- The infinite word `stem · loop^ω`. -/
def stream : ℕ → α := prepend Ω.stem Ω.periodicTail

variable {Ω}

theorem periodicTail_period_length : StreamPeriod Ω.periodicTail Ω.loop.length := by
  intro t; simp only [periodicTail, Nat.add_mod_right]

theorem stream_of_ge {n : ℕ} (h : Ω.stem.length ≤ n) :
    Ω.stream n = Ω.periodicTail (n - Ω.stem.length) := by
  simp only [stream, prepend, dite_eq_right (not_lt.mpr h)]

theorem stream_add_stem (t : ℕ) : Ω.stream (Ω.stem.length + t) = Ω.periodicTail t := by
  rw [stream_of_ge (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The ray is purely periodic with period `|loop|` from position `A` on; a finite check. -/
def OnsetAt (A : ℕ) : Prop :=
  ∀ t < Ω.stem.length - A, Ω.stream (A + t + Ω.loop.length) = Ω.stream (A + t)

instance [DecidableEq α] (A : ℕ) : Decidable (Ω.OnsetAt A) :=
  inferInstanceAs (Decidable (∀ t < _, _))

theorem onsetAt_iff {A : ℕ} : Ω.OnsetAt A ↔ PeriodicFrom Ω.stream A Ω.loop.length := by
  constructor
  · intro h t
    change Ω.stream (A + (t + Ω.loop.length)) = Ω.stream (A + t)
    by_cases ht : A + t < Ω.stem.length
    · rw [← Nat.add_assoc]; exact h t (by omega)
    · rw [stream_of_ge (by omega), stream_of_ge (by omega),
        show A + (t + Ω.loop.length) - Ω.stem.length = A + t - Ω.stem.length +
            Ω.loop.length by omega,
        periodicTail_period_length]
  · intro h t _
    have : Ω.stream (A + (t + Ω.loop.length)) = Ω.stream (A + t) := h t
    rwa [← Nat.add_assoc] at this

theorem exists_onsetAt (Ω : Ray α) : ∃ A, Ω.OnsetAt A := ⟨Ω.stem.length, fun t ht => by omega⟩

theorem exists_period (Ω : Ray α) :
    ∃ p, 0 < p ∧ ∀ t < Ω.loop.length, Ω.periodicTail (t + p) = Ω.periodicTail t :=
  ⟨Ω.loop.length, Ω.loop_length_pos, fun t _ => periodicTail_period_length t⟩

variable [DecidableEq α]

/-- The onset: the least position from which the ray is purely periodic. -/
def onset (Ω : Ray α) : ℕ := Nat.find Ω.exists_onsetAt

/-- The period: the least period of `loop^ω`. -/
def period (Ω : Ray α) : ℕ := Nat.find Ω.exists_period

theorem onset_le_stem : Ω.onset ≤ Ω.stem.length :=
  Nat.find_min' Ω.exists_onsetAt (fun t ht => by omega)

theorem periodicFrom_onset : PeriodicFrom Ω.stream Ω.onset Ω.loop.length :=
  onsetAt_iff.mp (Nat.find_spec Ω.exists_onsetAt)

theorem periodicFrom_of_onset_le {A : ℕ} (h : Ω.onset ≤ A) :
    PeriodicFrom Ω.stream A Ω.loop.length :=
  periodicFrom_onset.mono h

/-- A suffix that is purely periodic with any positive period starts at or after the onset. -/
theorem onset_le_of_periodicFrom {A p : ℕ} (hp : 0 < p) (h : PeriodicFrom Ω.stream A p) :
    Ω.onset ≤ A := by
  by_cases hA : Ω.stem.length ≤ A
  · exact onset_le_stem.trans hA
  · apply Nat.find_min' Ω.exists_onsetAt
    rw [onsetAt_iff]
    apply period_of_suffix (k := Ω.stem.length - A) hp h
    intro i
    simp only
    rw [show A + (Ω.stem.length - A + (i + Ω.loop.length)) = Ω.stem.length + (i + Ω.loop.length) by
        omega, show A + (Ω.stem.length - A + i) = Ω.stem.length + i by omega,
      stream_add_stem, stream_add_stem, periodicTail_period_length]

/-- `onset ≤ A` if and only if the suffix from `A` is purely periodic. -/
theorem onset_le_iff {A : ℕ} : Ω.onset ≤ A ↔ ∃ p, 0 < p ∧ PeriodicFrom Ω.stream A p :=
  ⟨fun h => ⟨_, Ω.loop_length_pos, periodicFrom_of_onset_le h⟩,
    fun ⟨_, hp, h⟩ => onset_le_of_periodicFrom hp h⟩

theorem period_pos : 0 < Ω.period := (Nat.find_spec Ω.exists_period).1

theorem periodicTail_leastPeriod : StreamPeriod Ω.periodicTail Ω.period := by
  intro t
  have hs : ∀ t < Ω.loop.length, Ω.periodicTail (t + Ω.period) = Ω.periodicTail t :=
      (Nat.find_spec Ω.exists_period).2
  have hn := Ω.loop_length_pos
  calc Ω.periodicTail (t + Ω.period) = Ω.periodicTail ((t + Ω.period) % Ω.loop.length) :=
      streamPeriod_mod periodicTail_period_length _
    _ = Ω.periodicTail ((t % Ω.loop.length + Ω.period) % Ω.loop.length) := by rw [Nat.mod_add_mod]
    _ = Ω.periodicTail (t % Ω.loop.length + Ω.period) :=
        (streamPeriod_mod periodicTail_period_length _).symm
    _ = Ω.periodicTail (t % Ω.loop.length) := hs _ (Nat.mod_lt _ hn)
    _ = Ω.periodicTail t := (streamPeriod_mod periodicTail_period_length _).symm

theorem leastStreamPeriod_periodicTail : LeastStreamPeriod Ω.periodicTail Ω.period :=
  ⟨period_pos, periodicTail_leastPeriod, fun _ hq hqp => Nat.find_min' Ω.exists_period ⟨hq,
      fun t _ => hqp t⟩⟩

theorem period_dvd : Ω.period ∣ Ω.loop.length :=
  (leastPeriod_dvd_iff leastStreamPeriod_periodicTail).mp periodicTail_period_length

/-- Every suffix from the onset on has least period `period`. -/
theorem leastStreamPeriod_shift {A : ℕ} (h : Ω.onset ≤ A) :
    LeastStreamPeriod (fun t => Ω.stream (A + t)) Ω.period := by
  set m := max A Ω.stem.length
  have hsuf : (fun i => (fun t => Ω.stream (A + t)) (m - A + i)) =
      fun i => Ω.periodicTail (m - Ω.stem.length + i) := by
    funext i
    simp only
    rw [stream_of_ge (by omega)]
    congr 1; omega
  have hleast : LeastStreamPeriod (fun i => (fun t => Ω.stream (A + t)) (m - A + i)) Ω.period := by
    rw [hsuf]; exact leastPeriod_suffix leastStreamPeriod_periodicTail _
  refine ⟨period_pos, ?_, fun q hq hqp => hleast.2.2 q hq (streamPeriod_shift hqp _)⟩
  exact period_of_suffix Ω.loop_length_pos (periodicFrom_of_onset_le h) hleast.2.1

/-! ## Comparing suffixes of rays -/

/-- Two suffixes of rays, from positions `a` and `b`, that agree on their first
`max(A - a, A' - b, 0) + ν + ν'` letters agree everywhere; here `A`, `A'` are the onsets and
`ν`, `ν'` the periods. -/
theorem stream_suffix_eq_of_prefix_eq (Ω Ω' : Ray α) (a b : ℕ)
    (h : ∀ t < max (Ω.onset - a) (max (Ω'.onset - b) 0) + Ω.period + Ω'.period,
      Ω.stream (a + t) = Ω'.stream (b + t)) : ∀ t, Ω.stream (a + t) = Ω'.stream (b + t) := by
  set m := max (Ω.onset - a) (max (Ω'.onset - b) 0)
  have h1 := leastStreamPeriod_shift (Ω := Ω) (A := a + m) (by omega)
  have h2 := leastStreamPeriod_shift (Ω := Ω') (A := b + m) (by omega)
  have heq := streamEq_of_agree h1 h2 (fun t ht => by
    show Ω.stream (a + m + t) = Ω'.stream (b + m + t)
    rw [show a + m + t = a + (m + t) by ring, show b + m + t = b + (m + t) by ring]
    exact h _ (by omega))
  intro t
  by_cases ht : t < m
  · exact h t (by omega)
  · have : Ω.stream (a + m + (t - m)) = Ω'.stream (b + m + (t - m)) := heq (t - m)
    rwa [show a + m + (t - m) = a + t by omega, show b + m + (t - m) = b + t by omega] at this

/-- Equality of two suffixes of rays is decidable: by `stream_suffix_eq_of_prefix_eq` it is a
finite check. -/
instance decSuffixEq (Ω Ω' : Ray α) (a b : ℕ) :
    Decidable (∀ t, Ω.stream (a + t) = Ω'.stream (b + t)) :=
  decidable_of_iff (∀ t < max (Ω.onset - a) (max (Ω'.onset - b) 0) + Ω.period + Ω'.period,
      Ω.stream (a + t) = Ω'.stream (b + t))
    ⟨stream_suffix_eq_of_prefix_eq Ω Ω' a b, fun h t _ => h t⟩

/-- If two suffixes of rays are equal, either both start at or after the onsets, or both start
before them at the same distance. -/
theorem suffix_eq_cases {Ω' : Ray α} {a b : ℕ} (h : ∀ t, Ω.stream (a + t) = Ω'.stream (b + t)) :
    (Ω.onset ≤ a ∧ Ω'.onset ≤ b) ∨ (a < Ω.onset ∧ Ω.onset - a = Ω'.onset - b) := by
  have hper : ∀ m p, PeriodicFrom Ω.stream (a + m) p ↔ PeriodicFrom Ω'.stream (b + m) p := by
    intro m p
    unfold PeriodicFrom StreamPeriod
    simp only
    constructor
    · intro hp i
      rw [show b + m + (i + p) = b + (m + i + p) by ring, show b + m + i = b + (m + i) by ring,
        ← h, ← h]
      have := hp i
      rwa [show a + m + (i + p) = a + (m + i + p) by ring,
        show a + m + i = a + (m + i) by ring] at this
    · intro hp i
      rw [show a + m + (i + p) = a + (m + i + p) by ring, show a + m + i = a + (m + i) by ring,
        h, h]
      have := hp i
      rwa [show b + m + (i + p) = b + (m + i + p) by ring,
        show b + m + i = b + (m + i) by ring] at this
  have key : ∀ m, Ω.onset ≤ a + m ↔ Ω'.onset ≤ b + m := by
    intro m
    rw [onset_le_iff, onset_le_iff]
    exact exists_congr fun p => and_congr_right fun _ => hper m p
  have e1 := (key (Ω.onset - a)).mp (by omega)
  have e2 := (key (Ω'.onset - b)).mpr (by omega)
  by_cases ha : Ω.onset ≤ a
  · left; exact ⟨ha, by omega⟩
  · right; exact ⟨by omega, by omega⟩

/-- Rays with the same infinite word have the same onset. -/
theorem onset_eq_of_stream_eq {Ω Ω' : Ray α} (h : ∀ t, Ω.stream t = Ω'.stream t) :
    Ω.onset = Ω'.onset := by
  have hf : Ω.stream = Ω'.stream := funext h
  have key : ∀ A, Ω.onset ≤ A ↔ Ω'.onset ≤ A := by
    intro A; rw [onset_le_iff, onset_le_iff, hf]
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

/-- The period of a ray is at most any positive period of any of its suffixes. -/
theorem period_le_of_periodicFrom {Ω : Ray α} {A p : ℕ} (hp : 0 < p)
    (h : PeriodicFrom Ω.stream A p) :
    Ω.period ≤ p := by
  have h1 := leastStreamPeriod_shift (Ω := Ω) (A := max A Ω.onset) (le_max_right _ _)
  exact h1.2.2 p hp (h.mono (le_max_left _ _))

theorem periodicFrom_period (Ω : Ray α) : PeriodicFrom Ω.stream Ω.onset Ω.period :=
  (leastStreamPeriod_shift (Ω := Ω) le_rfl).2.1

/-- The text of a ray before its onset. -/
def prefixBeforeOnset (Ω : Ray α) : List α := streamPrefix Ω.stream Ω.onset

/-- The text of a ray from the cut `J` to its onset (empty if the onset is at most `J`). -/
def suffixBeforeOnset (Ω : Ray α) (J : ℕ) :
    List α := streamPrefix (fun t => Ω.stream (J + t)) (Ω.onset - J)

@[simp] theorem length_suffixBeforeOnset (Ω : Ray α) (J : ℕ) :
    (Ω.suffixBeforeOnset J).length = Ω.onset - J := by simp [suffixBeforeOnset]

theorem suffixBeforeOnset_suffix_prefixBeforeOnset (Ω : Ray α) (J : ℕ) :
    Ω.suffixBeforeOnset J <:+ Ω.prefixBeforeOnset := by
  rw [suffixBeforeOnset, prefixBeforeOnset, streamPrefix_suffix_iff]
  exact ⟨by omega, fun t ht => by congr 1; omega⟩

/-! ## Finite prefixes of rays -/

omit [DecidableEq α] in
theorem streamPrefix_periodicTail (L : ℕ) :
    streamPrefix Ω.periodicTail L = (pow Ω.loop (L + 1)).take L := by
  have hn := Ω.loop_length_pos
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L
  · rw [List.getElem?_take_of_lt hi, getElem?_pow Ω.loop_ne_nil
      (by rw [length_pow]; nlinarith),
      List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem (Nat.mod_lt _ hn)]
    simp [hi, periodicTail]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

omit [DecidableEq α] in
/-- The prefix of length `|stem| + L` of a ray is `stem ++ (loop^(L+1)).take L`. -/
theorem streamPrefix_stream (L : ℕ) :
    streamPrefix Ω.stream (Ω.stem.length + L) = Ω.stem ++ (pow Ω.loop (L + 1)).take L := by
  rw [stream, prepend_prefix_add, streamPrefix_periodicTail]

end Ray

end DeciSigma1.Words
