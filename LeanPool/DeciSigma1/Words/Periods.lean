/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Periods, primitive words and conjugacy

Combinatorics on finite words for the shortening of periodic factors: powers of a word, the
least period of a word (with periods in the sense of Mathlib's `List.HasPeriod`), periodicity
on an interval of positions, the periodicity lemma of Fine and Wilf on a common interval,
primitive words and their rotation classes.

## Main declarations

- `pow`: the power `μ^n` of a word.
- `leastPeriod`: the least positive period of a word.
- `leastPeriod_dvd`: the least period divides every period `g` of a word of length at least
  `2g`.
- `PeriodicOn`: a word has period `d` on the interval of positions `[s, e)`.
- `period_extend_gcd`: Fine–Wilf on a common interval.
- `IsPrimitive`, `primitive_take_leastPeriod`: primitive words; the prefix of a word of length
  its least period is primitive when the word is at least twice as long.
- `IsConjugate`: two words are rotations of each other.
-/

@[expose] public section


namespace DeciSigma1.Words

variable {α : Type*}

section Powers

variable {μ π u w : List α} {p q n : ℕ}

/-- The power `μ^n`: `n` copies of `μ`. -/
def pow (μ : List α) : ℕ → List α
  | 0 => []
  | n + 1 => μ ++ pow μ n

@[simp] theorem pow_zero (μ : List α) : pow μ 0 = [] := rfl

@[simp] theorem pow_succ (μ : List α) (n : ℕ) : pow μ (n + 1) = μ ++ pow μ n := rfl

theorem pow_add (μ : List α) (m n : ℕ) : pow μ (m + n) = pow μ m ++ pow μ n := by
  induction m with
  | zero => simp
  | succ m ih => simpa [Nat.succ_add, List.append_assoc] using congrArg (μ ++ ·) ih

@[simp] theorem length_pow (μ : List α) (n : ℕ) : (pow μ n).length = n * μ.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem pow_nil (n : ℕ) : pow ([] : List α) n = [] := by
  induction n <;> simp_all

theorem prefix_append_of_prefix_pow (n : ℕ) (h : π <+: pow μ n) : π <+: μ ++ π := by
  induction n generalizing π with
  | zero => simp only [pow_zero, List.prefix_nil] at h; simp [h]
  | succ n ih =>
    rw [pow_succ] at h
    by_cases hlen : π.length ≤ μ.length
    · exact ((List.isPrefix_append_of_length hlen).mp h).trans (List.prefix_append _ _)
    · have hμ : μ <+: π :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) h (by omega)
      obtain ⟨τ, rfl⟩ := hμ
      rw [List.prefix_append_right_inj] at h
      simpa only [List.append_assoc, List.prefix_append_right_inj] using ih h

theorem hasPeriod_pow (u : List α) (n : ℕ) : (pow u n).HasPeriod u.length := by
  cases n with
  | zero => simp
  | succ n =>
    change pow u (n + 1) <+: (pow u (n + 1)).take u.length ++ pow u (n + 1)
    rw [pow_succ, List.take_left]
    exact prefix_append_of_prefix_pow (n + 1) List.prefix_rfl

theorem getElem?_pow (hu : u ≠ []) (hi : n < (pow u q).length) :
    (pow u q)[n]? = u[n % u.length]? := by
  rw [← (hasPeriod_pow u q).getElem?_mod u.length n (pow u q) hi]
  cases q with
  | zero => simp at hi
  | succ q =>
    exact List.getElem?_append_left (Nat.mod_lt _ (List.length_pos_iff.mpr hu))

end Powers

/-! ## Least periods -/

instance hasPeriodDecidable [DecidableEq α] (w : List α) (p : ℕ) : Decidable (w.HasPeriod p) :=
  inferInstanceAs (Decidable (w <+: _))

theorem exists_pos_period (w : List α) : ∃ p, 0 < p ∧ w.HasPeriod p :=
  ⟨w.length + 1, Nat.succ_pos _, List.hasPeriod_of_length_le w _ (Nat.le_succ _)⟩

/-- The least positive period of `w` (`1` for the empty word). -/
def leastPeriod [DecidableEq α] (w : List α) : ℕ := Nat.find (exists_pos_period w)

section LeastPeriod

variable [DecidableEq α] {w : List α} {p g : ℕ}

theorem leastPeriod_pos (w : List α) : 0 < leastPeriod w :=
  (Nat.find_spec (exists_pos_period w)).1

theorem hasPeriod_leastPeriod (w : List α) : w.HasPeriod (leastPeriod w) :=
  (Nat.find_spec (exists_pos_period w)).2

theorem leastPeriod_le (hp : 0 < p) (h : w.HasPeriod p) : leastPeriod w ≤ p :=
  Nat.find_min' (exists_pos_period w) ⟨hp, h⟩

/-- The least period of a word of length at least `2g` with period `g` divides `g`. -/
theorem leastPeriod_dvd (h : w.HasPeriod g) (h2 : 2 * g ≤ w.length) : leastPeriod w ∣ g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact dvd_zero _
  have hle : leastPeriod w ≤ g := leastPeriod_le hg h
  have hpos := leastPeriod_pos w
  have hgcd := (hasPeriod_leastPeriod w).gcd h (by
    have := Nat.gcd_pos_of_pos_left g hpos
    omega)
  have h1 : leastPeriod w ≤ (leastPeriod w).gcd g :=
    leastPeriod_le (Nat.gcd_pos_of_pos_left g hpos) hgcd
  have h2 : (leastPeriod w).gcd g ≤ leastPeriod w := Nat.gcd_le_left g hpos
  have heq : (leastPeriod w).gcd g = leastPeriod w := le_antisymm h2 h1
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

end LeastPeriod

/-! ## Periods on an interval of positions -/

/-- `w` has period `d` on the interval of positions `[s, e)`: `w[p]? = w[p + d]?` whenever
`s ≤ p` and `p + d < e`. -/
def PeriodicOn (w : List α) (d s e : ℕ) : Prop := ∀ p, s ≤ p → p + d < e → w[p]? = w[p + d]?

namespace PeriodicOn

variable {w : List α} {d s e : ℕ}

theorem mono {s' e' : ℕ} (h : PeriodicOn w d s e) (hs : s ≤ s') (he : e' ≤ e) :
    PeriodicOn w d s' e' :=
  fun p hp hpe => h p (hs.trans hp) (by omega)

/-- In a periodic interval, positions that differ by a multiple of the period carry equal
letters. -/
theorem eq_of_le_add (h : PeriodicOn w d s e) {p : ℕ} (hp : s ≤ p) :
    ∀ j, p + j * d < e → w[p]? = w[p + j * d]? := by
  intro j
  induction j with
  | zero => intro; simp
  | succ j ih =>
    intro hj
    rw [ih (by nlinarith), h (p + j * d) (by omega) (by nlinarith)]
    congr 1
    ring

theorem eq_of_mod (h : PeriodicOn w d s e) {p q : ℕ} (hp : s ≤ p) (hq : s ≤ q) (hpe : p < e)
    (hqe : q < e) (hpq : p % d = q % d) : w[p]? = w[q]? := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.mod_zero] at hpq; rw [hpq]
  rcases le_total p q with hle | hle
  · obtain ⟨j, hj⟩ : d ∣ q - p := (Nat.modEq_iff_dvd' hle).mp hpq
    have : q = p + j * d := by rw [mul_comm]; omega
    rw [this]; exact h.eq_of_le_add hp j (by omega)
  · obtain ⟨j, hj⟩ : d ∣ p - q := (Nat.modEq_iff_dvd' hle).mp hpq.symm
    have : p = q + j * d := by rw [mul_comm]; omega
    rw [this]; exact (h.eq_of_le_add hq j (by omega)).symm

/-- Two intervals with period `d` that overlap in at least `d` positions form one interval with
period `d`. -/
theorem union {s₂ e₂ : ℕ} (h₁ : PeriodicOn w d s e) (h₂ : PeriodicOn w d s₂ e₂)
    (hov : s₂ + d ≤ e) : PeriodicOn w d s (max e e₂) := by
  intro p hp hpe
  by_cases hp1 : p + d < e
  · exact h₁ p hp hp1
  · exact h₂ p (by omega) (by omega)

/-- In an interval with period `d`, the factor of length `d` at `z` is a rotation of the factor
of length `d` at the start of the interval. -/
theorem window_rotate (h : PeriodicOn w d s e) (he : e ≤ w.length) {z : ℕ} (hsz : s ≤ z)
    (hz : z + d ≤ e) : (w.drop z).take d = ((w.drop s).take d).rotate ((z - s) % d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  apply List.ext_getElem?
  intro i
  by_cases hi : i < d
  · have hlen : ((w.drop s).take d).length = d := by simp; omega
    rw [List.getElem?_rotate (by omega), hlen, List.getElem?_take_of_lt hi, List.getElem?_drop,
      List.getElem?_take_of_lt (Nat.mod_lt _ hd), List.getElem?_drop]
    apply h.eq_of_mod (by omega) (by omega) (by omega)
      (by have := Nat.mod_lt (i + (z - s) % d) hd; omega)
    have h1 : (i + (z - s) % d) % d ≡ i + (z - s) [MOD d] :=
      (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ (Nat.mod_modEq _ _))
    have h2 := Nat.ModEq.add_left s h1
    rw [show s + (i + (z - s)) = z + i by omega] at h2
    exact h2.symm
  · have h1 : ((w.drop z).take d).length ≤ i := by simp only [List.length_take]; omega
    have h2 : (((w.drop s).take d).rotate ((z - s) % d)).length ≤ i := by
      simp only [List.length_rotate, List.length_take]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

end PeriodicOn

theorem periodicOn_iff_hasPeriod {w : List α} {d s e : ℕ} (hse : s ≤ e) (he : e ≤ w.length) :
    PeriodicOn w d s e ↔ ((w.drop s).take (e - s)).HasPeriod d := by
  rw [List.hasPeriod_iff_getElem?]
  simp only [List.length_take, List.length_drop, List.getElem?_take, List.getElem?_drop]
  constructor
  · intro h i hi
    have h1 : i < e - s := by omega
    have h2 : i + d < e - s := by omega
    simp only [h1, h2, ite_true]
    exact h (s + i) (by omega) (by omega) |>.trans (by congr 1; omega)
  · intro h p hp hpe
    have := h (p - s) (by omega)
    have h1 : p - s < e - s := by omega
    have h2 : p - s + d < e - s := by omega
    simp only [h1, h2, ite_true] at this
    convert this using 2 <;> omega

/-- A period on an interval transfers to every word with the same letters below its end. -/
theorem PeriodicOn.transfer {w w' : List α} {p s e : ℕ}
    (h : PeriodicOn w p s e)
    (hw : ∀ q < e, w'[q]? = w[q]?) : PeriodicOn w' p s e := by
  intro q hq hqe
  rw [hw q (by omega), hw (q + p) hqe]
  exact h q hq hqe

/-- Fine–Wilf on a common interval: an interval of length at least `p + q - gcd p q` with
periods `p` and `q` has period `gcd p q`. -/
theorem period_extend_gcd {w : List α} {p q s e : ℕ} (hse : s ≤ e) (he : e ≤ w.length)
    (hp : PeriodicOn w p s e) (hq : PeriodicOn w q s e) (hlen : p + q - p.gcd q ≤ e - s) :
    PeriodicOn w (p.gcd q) s e := by
  rw [periodicOn_iff_hasPeriod hse he] at hp hq ⊢
  have hl : ((w.drop s).take (e - s)).length = e - s := by simp; omega
  exact hp.gcd hq (by rw [hl]; exact hlen)

/-! ## Primitive words -/

/-- A word is primitive if it is nonempty and not a proper power. -/
def IsPrimitive (ρ : List α) : Prop := ρ ≠ [] ∧ ∀ (u : List α) (m : ℕ), ρ = pow u m → m = 1

/-- A period that divides the length is a period of the cyclic word. -/
theorem hasPeriod_iff_cyclic {ρ : List α} {p : ℕ} (hn : 0 < ρ.length) (hp : p ∣ ρ.length) :
    ρ.HasPeriod p ↔ ∀ i, ρ[i % ρ.length]? = ρ[(i + p) % ρ.length]? := by
  constructor
  · intro h i
    rw [List.hasPeriod_iff_forall_getElem?_mod] at h
    rw [h _ (Nat.mod_lt _ hn), h _ (Nat.mod_lt _ hn)]
    congr 1
    obtain ⟨c, hc⟩ := hp
    rw [hc, Nat.mod_mul_right_mod, Nat.mod_mul_right_mod, Nat.add_mod_right]
  · intro h
    rw [List.hasPeriod_iff_getElem?]
    intro i hi
    have := h i
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem isPrimitive_iff_period {ρ : List α} : IsPrimitive ρ ↔
    ρ ≠ [] ∧ ∀ p, 0 < p → p < ρ.length → p ∣ ρ.length → ¬ ρ.HasPeriod p := by
  constructor
  · rintro ⟨hne, hpow⟩
    refine ⟨hne, fun p hp hpn hdvd hper => ?_⟩
    obtain ⟨m, hm⟩ := hdvd
    have hu : ρ.take p ≠ [] := by
      intro h; rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · exact hne h
    have hlen' : (pow (ρ.take p) m).length = ρ.length := by
      rw [length_pow, List.length_take, min_eq_left hpn.le,
        hm, mul_comm]
    have hρ : ρ = pow (ρ.take p) m := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < ρ.length
      · rw [getElem?_pow hu (by omega),
          List.length_take, min_eq_left hpn.le, List.getElem?_take_of_lt (Nat.mod_lt _ hp)]
        exact ((hper.getElem?_mod p i ρ hi)).symm
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have := hpow _ _ hρ
    subst this
    omega
  · rintro ⟨hne, hper⟩
    refine ⟨hne, fun u m hρ => ?_⟩
    have hlen : ρ.length = m * u.length := by
      rw [hρ, length_pow]
    rcases m with _ | _ | m
    · exfalso; apply hne; rw [hρ]; rfl
    · rfl
    · exfalso
      have hu : 0 < u.length := by
        rcases Nat.eq_zero_or_pos u.length with h | h
        · exfalso; apply hne; rw [List.length_eq_zero_iff.mp h] at hρ
          rw [hρ, pow_nil]
        · exact h
      apply hper u.length hu (by rw [hlen]; nlinarith) ⟨m + 2, by rw [hlen, mul_comm]⟩
      rw [hρ]
      exact hasPeriod_pow u _

instance isPrimitiveDecidable [DecidableEq α] : DecidablePred (IsPrimitive (α := α)) :=
  fun ρ => decidable_of_iff (ρ ≠ [] ∧ ∀ p < ρ.length, 0 < p → p ∣ ρ.length → ¬ ρ.HasPeriod p)
    (by rw [isPrimitive_iff_period]
        exact and_congr_right fun _ =>
          ⟨fun h p hp hpn => h p hpn hp, fun h p hpn hp => h p hp hpn⟩)

theorem IsPrimitive.ne_nil {ρ : List α} (h : IsPrimitive ρ) : ρ ≠ [] := h.1

theorem rotate_back_mod (n r x : ℕ) (hn : 0 < n) : ((x + (n - r % n)) % n + r) % n = x % n := by
  have h1 : (x + (n - r % n)) % n + r ≡ x + (n - r % n) + r [MOD n] :=
    Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
  have h2 : x + (n - r % n) + r ≡ x + (n - r % n) + r % n [MOD n] :=
    Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
  have h3 : x + (n - r % n) + r % n = x + n := by have := Nat.mod_lt r hn; omega
  rw [h3] at h2
  exact h1.trans (h2.trans Nat.add_modEq_right)

/-- Rotations of primitive words are primitive. -/
theorem IsPrimitive.rotate {ρ : List α} (h : IsPrimitive ρ) (r : ℕ) : IsPrimitive (ρ.rotate r) := by
  rw [isPrimitive_iff_period] at h ⊢
  obtain ⟨hne, hper⟩ := h
  have hn : 0 < ρ.length := List.length_pos_iff.mpr hne
  refine ⟨by rw [Ne, List.rotate_eq_nil_iff]; exact hne, fun p hp hpn hdvd hrot => ?_⟩
  rw [List.length_rotate] at hpn hdvd
  apply hper p hp hpn hdvd
  rw [hasPeriod_iff_cyclic (by simpa using hn) (by simpa using hdvd)] at hrot
  rw [hasPeriod_iff_cyclic hn hdvd]
  intro i
  simp only [List.length_rotate] at hrot
  have := hrot (i + (ρ.length - r % ρ.length))
  rw [List.getElem?_rotate (Nat.mod_lt _ hn), List.getElem?_rotate (Nat.mod_lt _ hn),
    Nat.add_right_comm i _ p, rotate_back_mod _ _ _ hn, rotate_back_mod _ _ _ hn] at this
  exact this

/-- The prefix of length `leastPeriod w` of a word of length at least twice its least period is
primitive. -/
theorem primitive_take_leastPeriod [DecidableEq α] {w : List α}
    (h2 : 2 * leastPeriod w ≤ w.length) : IsPrimitive (w.take (leastPeriod w)) := by
  set p := leastPeriod w with hp_def
  have hpos : 0 < p := leastPeriod_pos w
  have hlen : (w.take p).length = p := by simp; omega
  rw [isPrimitive_iff_period]
  refine
      ⟨by intro h; rw [← List.length_eq_zero_iff, hlen] at h; omega, fun q hq hqp hdvd hper => ?_⟩
  rw [hlen] at hqp hdvd
  -- `w` would have the smaller period `q`
  have hw : w.HasPeriod q := by
    rw [List.hasPeriod_iff_forall_getElem?_mod]
    intro i hi
    have hwp := hasPeriod_leastPeriod w
    rw [List.hasPeriod_iff_forall_getElem?_mod] at hwp hper
    rw [hlen] at hper
    rw [hwp i hi, ← List.getElem?_take_of_lt (Nat.mod_lt i hpos),
      hper _ (Nat.mod_lt i hpos), List.getElem?_take_of_lt (lt_trans (Nat.mod_lt _ hq) hqp),
      Nat.mod_mod_of_dvd _ hdvd]
  exact absurd (leastPeriod_le hq hw) (by omega)

/-! ## Rotation classes -/

/-- Two words are conjugate if one is a rotation of the other. -/
def IsConjugate (ρ ρ' : List α) : Prop := ∃ r, ρ' = ρ.rotate r

theorem isConjugate_iff_isRotated {ρ ρ' : List α} : IsConjugate ρ ρ' ↔ ρ ~r ρ' :=
  ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

instance sameClassDecidable [DecidableEq α] (ρ ρ' : List α) : Decidable (IsConjugate ρ ρ') :=
  decidable_of_iff _ isConjugate_iff_isRotated.symm

namespace IsConjugate

variable {ρ ρ' ρ'' : List α}

theorem refl (ρ : List α) : IsConjugate ρ ρ := ⟨0, by simp⟩

theorem symm (h : IsConjugate ρ ρ') : IsConjugate ρ' ρ :=
  isConjugate_iff_isRotated.mpr (isConjugate_iff_isRotated.mp h).symm

theorem trans (h₁ : IsConjugate ρ ρ') (h₂ : IsConjugate ρ' ρ'') : IsConjugate ρ ρ'' :=
  isConjugate_iff_isRotated.mpr ((isConjugate_iff_isRotated.mp h₁).trans
    (isConjugate_iff_isRotated.mp h₂))

theorem length_eq (h : IsConjugate ρ ρ') : ρ'.length = ρ.length := by
  obtain ⟨r, rfl⟩ := h; simp

theorem isPrimitive (h : IsConjugate ρ ρ') (hρ : IsPrimitive ρ) : IsPrimitive ρ' := by
  obtain ⟨r, rfl⟩ := h; exact hρ.rotate r

end IsConjugate

end DeciSigma1.Words
