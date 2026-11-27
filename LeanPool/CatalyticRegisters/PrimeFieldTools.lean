/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

/-!
# Zero-Mathlib Prime-Field Arithmetic, Lucas's Theorem, and Finite Differences

Self-contained number-theoretic and combinatorial toolkit supporting Theorem T1
(`Catalytic.DigitSumDichotomy`) with zero Mathlib dependencies:
  * Primality (`IsPrime`), Bézout identity (`bezout`), Euclid's lemma (`prime_dvd_mul`),
    and modular inverses (`exists_mod_inv`),
  * Binomial coefficients (`choose`), Fermat's Little Theorem (`fermat_little`),
    and Lucas's Theorem (`lucas_theorem`),
  * Base-`p` digit sum (`digitSum`), `pow_mod_eq_pow_digitSum`, and bidirectional Lucas digit lemmas,
  * Forward finite difference operator (`iterDiff`) giving exact weights on `{0..s}`,
  * Monic annihilator polynomial (`prodLinear`) for any finite set `A ⊆ 𝔽_p`.
-/

namespace Catalytic

@[expose] public section

/-! ## 0. Zero-Mathlib Strong Induction & Bézout Identity -/

/-- Strong induction on `Nat` (zero Mathlib). -/
theorem nat_strong_ind {P : Nat → Prop} (step : ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  have h : ∀ k m, m < k → P m := by
    intro k
    induction k with
    | zero => intro m hm; omega
    | succ k ih =>
      intro m hm
      by_cases hlt : m < k
      · exact ih m hlt
      · have hmk : m = k := by omega
        subst hmk
        exact step m ih
  intro n
  exact h (n + 1) n (Nat.lt_succ_self n)

/-- Extended Euclidean algorithm returning `(x, y)` such that `a * x + b * y = gcd a b`. -/
def bezout (a b : Nat) : Int × Int :=
  if _hb : b = 0 then
    (1, 0)
  else
    let res := bezout b (a % b)
    (res.2, res.1 - (a / b : Int) * res.2)
termination_by b
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero _hb)

theorem bezout_spec (a b : Nat) :
    (a : Int) * (bezout a b).1 + (b : Int) * (bezout a b).2 = (Nat.gcd a b : Int) := by
  induction b using nat_strong_ind generalizing a with
  | _ b ih =>
    unfold bezout
    by_cases hb : b = 0
    · subst hb
      simp [Nat.gcd_zero_right]
    · simp only [hb, ↓reduceDIte]
      have hlt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
      have hrec := ih (a % b) hlt b
      have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
        rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
      rw [hgcd, ← hrec]
      have hdiv : (a : Int) = (b : Int) * (a / b : Int) + (a % b : Int) := by
        have h := Nat.div_add_mod a b
        have h1 : (a : Int) = ((b * (a / b) + a % b : Nat) : Int) := by rw [h]
        rw [Int.natCast_add, Int.natCast_mul] at h1
        exact h1
      let x := (bezout b (a % b)).1
      let y := (bezout b (a % b)).2
      change (a : Int) * y + (b : Int) * (x - (a / b : Int) * y) = (b : Int) * x + (a % b : Int) * y
      have hmul : (a : Int) * y = (b : Int) * ((a / b : Int) * y) + (a % b : Int) * y := by
        calc
          (a : Int) * y = ((b : Int) * (a / b : Int) + (a % b : Int)) * y := congrArg (· * y) hdiv
          _ = (b : Int) * (a / b : Int) * y + (a % b : Int) * y := Int.add_mul _ _ _
          _ = (b : Int) * ((a / b : Int) * y) + (a % b : Int) * y := by rw [Int.mul_assoc]
      rw [hmul, Int.mul_sub]
      omega

/-! ## 1. Primality, Euclid's Lemma, and Modular Inverses -/

/-- Elementary primality predicate (zero Mathlib). -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := by
  have := hp.1; omega

theorem IsPrime.gt_one {p : Nat} (hp : IsPrime p) : 1 < p := by
  have := hp.1; omega

theorem IsPrime.two : IsPrime 2 := by
  refine ⟨Nat.le_refl 2, ?_⟩
  intro d hd
  have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
  omega

/-- Euclid's lemma via `bezout_spec`. -/
theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · right
    have hgdvd : Nat.gcd a p ∣ p := Nat.gcd_dvd_right a p
    have hg1 : Nat.gcd a p = 1 := by
      rcases hp.2 (Nat.gcd a p) hgdvd with h1 | hp'
      · exact h1
      · exfalso
        have : p ∣ a := hp' ▸ Nat.gcd_dvd_left a p
        exact ha this
    let x := (bezout a p).1
    let y := (bezout a p).2
    have hbez : (a : Int) * x + (p : Int) * y = 1 := by
      have h0 := bezout_spec a p
      rw [hg1] at h0
      exact h0
    obtain ⟨k, hk⟩ := h
    have hab : (b : Int) * (a : Int) = (p : Int) * (k : Int) := by
      have : b * a = p * k := by rw [Nat.mul_comm, hk]
      exact_mod_cast this
    have hmul : (b : Int) = (p : Int) * ((k : Int) * x + (b : Int) * y) := by
      calc
        (b : Int) = (b : Int) * ((a : Int) * x + (p : Int) * y) := by rw [hbez, Int.mul_one]
        _ = (b : Int) * ((a : Int) * x) + (b : Int) * ((p : Int) * y) := Int.mul_add _ _ _
        _ = ((b : Int) * (a : Int)) * x + (p : Int) * ((b : Int) * y) := by
          rw [← Int.mul_assoc (b : Int) (a : Int) x, ← Int.mul_assoc (b : Int) (p : Int) y,
              Int.mul_comm (b : Int) (p : Int), Int.mul_assoc (p : Int) (b : Int) y]
        _ = (p : Int) * ((k : Int) * x) + (p : Int) * ((b : Int) * y) := by
          rw [hab, Int.mul_assoc]
        _ = (p : Int) * ((k : Int) * x + (b : Int) * y) := (Int.mul_add _ _ _).symm
    have hdvdI : (p : Int) ∣ (b : Int) := ⟨(k : Int) * x + (b : Int) * y, hmul⟩
    exact Int.ofNat_dvd.mp hdvdI

theorem prime_mul_mod_ne_zero {p a b : Nat} (hp : IsPrime p)
    (ha : a % p ≠ 0) (hb : b % p ≠ 0) : (a * b) % p ≠ 0 := by
  intro h
  have hd : p ∣ a * b := Nat.dvd_of_mod_eq_zero h
  rcases prime_dvd_mul hp hd with h1 | h2
  · exact ha (Nat.mod_eq_zero_of_dvd h1)
  · exact hb (Nat.mod_eq_zero_of_dvd h2)

/-- Existence of multiplicative inverse modulo any prime `p`. -/
theorem exists_mod_inv {p a : Nat} (hp : IsPrime p) (ha : a % p ≠ 0) :
    ∃ u : Nat, u < p ∧ (u * a) % p = 1 := by
  have hndvd : ¬ (p ∣ a) := fun h => ha (Nat.mod_eq_zero_of_dvd h)
  have hg1 : Nat.gcd a p = 1 := by
    rcases hp.2 (Nat.gcd a p) (Nat.gcd_dvd_right a p) with h1 | hp'
    · exact h1
    · exfalso; exact hndvd (hp' ▸ Nat.gcd_dvd_left a p)
  let x := (bezout a p).1
  let y := (bezout a p).2
  have hbez : (a : Int) * x + (p : Int) * y = 1 := by
    have h0 := bezout_spec a p; rw [hg1] at h0; exact h0
  let uInt : Int := x % (p : Int)
  have hp_pos : (0 : Int) < (p : Int) := by have := hp.pos; omega
  have hu_nn : 0 ≤ uInt := Int.emod_nonneg _ (by omega)
  have hu_lt : uInt < (p : Int) := Int.emod_lt_of_pos _ hp_pos
  let u : Nat := uInt.toNat
  have hu_eq : (u : Int) = uInt := Int.toNat_of_nonneg hu_nn
  refine ⟨u, by omega, ?_⟩
  have hmodI : ((u * a : Nat) : Int) % (p : Int) = 1 := by
    have hcast : ((u * a : Nat) : Int) = uInt * (a : Int) := by
      rw [Int.natCast_mul, hu_eq]
    rw [hcast]
    have h1 : (uInt * (a : Int)) % (p : Int) = (x * (a : Int)) % (p : Int) := by
      simp only [uInt, Int.mul_emod, Int.emod_emod]
    rw [h1, Int.mul_comm x (a : Int)]
    have h2 : (a : Int) * x = 1 + (p : Int) * (-y) := by
      rw [Int.mul_neg]; omega
    rw [h2, Int.add_mul_emod_self_left]
    have hp1 : 1 < (p : Int) := by have := hp.gt_one; omega
    exact Int.emod_eq_of_lt (by omega) hp1
  have hmodN : (((u * a) % p : Nat) : Int) = (1 : Int) := by
    rw [Int.natCast_emod]; exact hmodI
  omega

/-! ## 2. Factorial, Binomial Coefficients, Fermat's Little Theorem, and Lucas's Theorem -/

/-- The factorial of a natural number. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

theorem prime_not_dvd_fact {p : Nat} (hp : IsPrime p) :
    ∀ n : Nat, n < p → ¬ (p ∣ fact n)
  | 0, _ => by
    intro h
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide) h
    have := hp.1; omega
  | n + 1, hn => by
    intro h
    rcases prime_dvd_mul hp h with h1 | h2
    · have := Nat.le_of_dvd (Nat.succ_pos n) h1; omega
    · exact prime_not_dvd_fact hp n (by omega) h2

/-- Standard binomial coefficient `C(n, k)` via Pascal's recurrence. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl

theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k' => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k' =>
      rw [choose, ih (k := k') (by omega), ih (k := k' + 1) (by omega)]

@[simp] theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [choose, ih, choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.add_zero]

theorem choose_mul_fact (n k : Nat) (hk : k ≤ n) :
    choose n k * fact k * fact (n - k) = fact n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ n ih =>
    cases k with
    | zero => simp [choose, fact]
    | succ k' =>
      by_cases hlt : k' + 1 = n + 1
      · have hkn : k' = n := by omega
        subst hkn
        simp [choose_self, fact]
      · have hk1 : k' ≤ n := by omega
        have hk2 : k' + 1 ≤ n := by omega
        have ih1 := ih k' hk1
        have ih2 := ih (k' + 1) hk2
        have hsub : n + 1 - (k' + 1) = n - k' := by omega
        have hsub2 : n - k' = (n - (k' + 1)) + 1 := by omega
        rw [choose, hsub]
        have hf1 : fact (k' + 1) = (k' + 1) * fact k' := rfl
        have hf2 : fact (n - k') = (n - k') * fact (n - (k' + 1)) := by
          conv => lhs; rw [hsub2]
          simp only [fact]
          rw [← hsub2]
        have hL1 : choose n k' * fact (k' + 1) * fact (n - k') = (k' + 1) * fact n := by
          rw [hf1]
          calc
            choose n k' * ((k' + 1) * fact k') * fact (n - k')
                = (k' + 1) * (choose n k' * fact k' * fact (n - k')) := by
                  rw [Nat.mul_comm (choose n k'), ← Nat.mul_assoc, Nat.mul_assoc (k' + 1),
                      Nat.mul_comm (fact k') (choose n k'), Nat.mul_assoc (k' + 1)]
            _   = (k' + 1) * fact n := by rw [ih1]
        have hL2 : choose n (k' + 1) * fact (k' + 1) * fact (n - k') = (n - k') * fact n := by
          rw [hf2]
          calc
            choose n (k' + 1) * fact (k' + 1) * ((n - k') * fact (n - (k' + 1)))
                = (n - k') * (choose n (k' + 1) * fact (k' + 1) * fact (n - (k' + 1))) := by
                  rw [← Nat.mul_assoc, Nat.mul_comm (choose n (k' + 1) * fact (k' + 1)) (n - k'),
                      Nat.mul_assoc, Nat.mul_assoc]
            _   = (n - k') * fact n := by rw [ih2]
        calc
          (choose n k' + choose n (k' + 1)) * fact (k' + 1) * fact (n - k')
              = choose n k' * fact (k' + 1) * fact (n - k') +
                choose n (k' + 1) * fact (k' + 1) * fact (n - k') := by
                  rw [Nat.add_mul, Nat.add_mul]
          _   = (k' + 1) * fact n + (n - k') * fact n := by rw [hL1, hL2]
          _   = (k' + 1 + (n - k')) * fact n := (Nat.add_mul _ _ _).symm
          _   = (n + 1) * fact n := by congr 1; omega
          _   = fact (n + 1) := rfl

theorem prime_dvd_choose {p k : Nat} (hp : IsPrime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ choose p k := by
  have h1 := choose_mul_fact p k (by omega)
  have hfp : p ∣ fact p := by
    cases p with
    | zero => have := hp.pos; omega
    | succ m => exact ⟨fact m, rfl⟩
  rw [← h1, Nat.mul_assoc] at hfp
  rcases prime_dvd_mul hp hfp with hch | hrest
  · exact hch
  · exfalso
    rcases prime_dvd_mul hp hrest with hf1 | hf2
    · exact prime_not_dvd_fact hp k hkp hf1
    · exact prime_not_dvd_fact hp (p - k) (by omega) hf2

theorem prime_not_dvd_choose_of_lt {p n k : Nat} (hp : IsPrime p) (hk : k ≤ n) (hn : n < p) :
    choose n k % p ≠ 0 := by
  intro h
  have hd : p ∣ choose n k := Nat.dvd_of_mod_eq_zero h
  have h1 := choose_mul_fact n k hk
  have hfn : p ∣ fact n := by
    rw [← h1]
    exact Nat.dvd_trans (Nat.dvd_trans hd (Nat.dvd_mul_right _ _)) (Nat.dvd_mul_right _ _)
  exact prime_not_dvd_fact hp n hn hfn

/-! ### Finite Sums over `Nat` -/

/-- Sum a natural-valued function on the indices strictly below the bound. -/
def sumNat (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => sumNat m f + f m

theorem sumNat_succ (n : Nat) (f : Nat → Nat) : sumNat (n + 1) f = sumNat n f + f n := rfl

theorem sumNat_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumNat_succ, sumNat_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]

theorem sumNat_congr_mod {p n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i % p = g i % p) :
    sumNat n f % p = sumNat n g % p := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumNat_succ, sumNat_succ, Nat.add_mod, ih (fun i hi => h i (by omega)),
        h m (Nat.lt_succ_self m), ← Nat.add_mod]

theorem sumNat_zero {n : Nat} {f : Nat → Nat} (h : ∀ i < n, f i = 0) : sumNat n f = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumNat_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]

theorem sumNat_mod_zero {p n : Nat} {f : Nat → Nat} (h : ∀ i < n, f i % p = 0) :
    sumNat n f % p = 0 := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih =>
    rw [sumNat_succ, Nat.add_mod, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]
    simp

theorem sumNat_add (n : Nat) (f g : Nat → Nat) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumNat_succ, sumNat_succ, sumNat_succ, ih]; omega

theorem sumNat_mul_left (n c : Nat) (f : Nat → Nat) :
    sumNat n (fun i => c * f i) = c * sumNat n f := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih => rw [sumNat_succ, sumNat_succ, ih, Nat.mul_add]

theorem sumNat_mul_right (n c : Nat) (f : Nat → Nat) :
    sumNat n (fun i => f i * c) = sumNat n f * c := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih => rw [sumNat_succ, sumNat_succ, ih, Nat.add_mul]

theorem sumNat_succ_shift (n : Nat) (f : Nat → Nat) :
    sumNat (n + 1) f = f 0 + sumNat n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih =>
    rw [sumNat_succ (m + 1), ih, sumNat_succ m (fun i => f (i + 1)), Nat.add_assoc]

theorem sumNat_single {n k : Nat} (hk : k < n) (f : Nat → Nat)
    (hzero : ∀ i < n, i ≠ k → f i = 0) :
    sumNat n f = f k := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [sumNat_succ]
    by_cases hkm : k = m
    · subst hkm
      rw [sumNat_zero (fun i hi => hzero i (by omega) (by omega)), Nat.zero_add]
    · rw [ih (by omega) (fun i hi hne => hzero i (by omega) hne),
          hzero m (Nat.lt_succ_self m) (Ne.symm hkm), Nat.add_zero]

/-- Standard `Nat` Binomial Theorem: `(a + b)^n = ∑_{k=0}^n choose n k * a^(n-k) * b^k`. -/
theorem nat_binomial (a b n : Nat) :
    (a + b) ^ n = sumNat (n + 1) (fun k => choose n k * a ^ (n - k) * b ^ k) := by
  induction n with
  | zero => simp [sumNat]
  | succ n ih =>
    rw [Nat.pow_succ, ih, Nat.mul_add, ← sumNat_mul_right, ← sumNat_mul_right]
    have hA :
        sumNat (n + 1) (fun k => choose n k * a ^ (n - k) * b ^ k * a) =
          a ^ (n + 1) + sumNat n (fun k => choose n (k + 1) * a ^ (n - k) * b ^ (k + 1)) := by
      rw [sumNat_succ_shift]
      congr 1
      · simp [Nat.pow_succ]
      · apply sumNat_congr
        intro k hk
        have hsub : n - (k + 1) + 1 = n - k := by omega
        calc
          choose n (k + 1) * a ^ (n - (k + 1)) * b ^ (k + 1) * a
              = choose n (k + 1) * a ^ (n - (k + 1)) * (b ^ (k + 1) * a) := Nat.mul_assoc _ _ _
          _   = choose n (k + 1) * a ^ (n - (k + 1)) * (a * b ^ (k + 1)) := by rw [Nat.mul_comm (b ^ (k + 1)) a]
          _   = choose n (k + 1) * (a ^ (n - (k + 1)) * a) * b ^ (k + 1) := by
                rw [← Nat.mul_assoc (choose n (k + 1) * a ^ (n - (k + 1))) a, Nat.mul_assoc (choose n (k + 1))]
          _   = choose n (k + 1) * a ^ (n - (k + 1) + 1) * b ^ (k + 1) := by rw [← Nat.pow_succ]
          _   = choose n (k + 1) * a ^ (n - k) * b ^ (k + 1) := by rw [hsub]
    have hB :
        sumNat (n + 1) (fun k => choose n k * a ^ (n - k) * b ^ k * b) =
          sumNat n (fun k => choose n k * a ^ (n - k) * b ^ (k + 1)) + b ^ (n + 1) := by
      rw [sumNat_succ]
      congr 1
      · apply sumNat_congr
        intro k _
        rw [Nat.mul_assoc, Nat.pow_succ]
      · simp [choose_self, Nat.pow_succ]
    rw [hA, hB]
    have hRHS :
        sumNat (n + 2) (fun k => choose (n + 1) k * a ^ (n + 1 - k) * b ^ k) =
          a ^ (n + 1) +
            sumNat n (fun k => (choose n k + choose n (k + 1)) * a ^ (n - k) * b ^ (k + 1)) +
            b ^ (n + 1) := by
      rw [sumNat_succ (n + 1), sumNat_succ_shift n]
      congr 1
      · congr 1
        · simp
        · apply sumNat_congr
          intro k _
          have hsub : n + 1 - (k + 1) = n - k := by omega
          rw [choose, hsub]
      · simp [choose_self]
    rw [hRHS]
    have hcomb :
        sumNat n (fun k => choose n (k + 1) * a ^ (n - k) * b ^ (k + 1)) +
          sumNat n (fun k => choose n k * a ^ (n - k) * b ^ (k + 1)) =
        sumNat n (fun k => (choose n k + choose n (k + 1)) * a ^ (n - k) * b ^ (k + 1)) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro k _
      rw [Nat.add_mul, Nat.add_mul, Nat.add_comm]
    omega

/-- **Fermat's Little Theorem:** `a ^ p % p = a % p` for every prime `p` and every `a : Nat`. -/
theorem fermat_little {p : Nat} (hp : IsPrime p) (a : Nat) : a ^ p % p = a % p := by
  induction a with
  | zero => rw [Nat.zero_pow hp.pos]
  | succ n ih =>
    have hbin := nat_binomial n 1 p
    have h1 : (n + 1) ^ p % p = (n ^ p + 1) % p := by
      rw [hbin]
      cases p with
      | zero => have := hp.pos; omega
      | succ m =>
        rw [sumNat_succ (m + 1), sumNat_succ_shift m]
        have hmid : sumNat m (fun k => choose (m + 1) (k + 1) * n ^ (m + 1 - (k + 1))) % (m + 1) = 0 := by
          apply sumNat_mod_zero
          intro k hk
          have hd : (m + 1) ∣ choose (m + 1) (k + 1) :=
            prime_dvd_choose hp (Nat.succ_pos k) (by omega)
          have hdm : (m + 1) ∣ choose (m + 1) (k + 1) * n ^ (m + 1 - (k + 1)) :=
            Nat.dvd_trans hd (Nat.dvd_mul_right _ _)
          exact Nat.mod_eq_zero_of_dvd hdm
        simp only [choose_zero_right, choose_self, Nat.sub_zero, Nat.sub_self, Nat.pow_zero,
          Nat.one_mul, Nat.mul_one, Nat.one_pow]
        rw [Nat.add_mod, Nat.add_mod (n ^ (m + 1)), hmid, Nat.add_zero, Nat.mod_mod, ← Nat.add_mod]
    rw [h1, Nat.add_mod, ih, ← Nat.add_mod]

/-! ### Lucas's Theorem via Coefficient Convolution mod `p` -/

/-- The convolution coefficient of two natural-valued sequences at the specified index. -/
def conv (f g : Nat → Nat) (k : Nat) : Nat :=
  sumNat (k + 1) (fun i => f i * g (k - i))

/-- The specified coefficient of the convolution power of a sequence. -/
def convPow (f : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => conv (convPow f n) f

private theorem conv_congr_mod {p : Nat} {f1 f2 g1 g2 : Nat → Nat}
    (hf : ∀ k, f1 k % p = f2 k % p) (hg : ∀ k, g1 k % p = g2 k % p) (k : Nat) :
    conv f1 g1 k % p = conv f2 g2 k % p := by
  apply sumNat_congr_mod
  intro i _
  rw [Nat.mul_mod, hf i, hg (k - i), ← Nat.mul_mod]

private theorem sumNat_triangle_swap (n : Nat) (F : Nat → Nat → Nat) :
    sumNat (n + 1) (fun j => sumNat (j + 1) (fun i => F i j)) =
    sumNat (n + 1) (fun i => sumNat (n + 1 - i) (fun t => F i (i + t))) := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih =>
    rw [sumNat_succ (m + 1), ih, sumNat_succ (m + 1) (fun i => sumNat (m + 2 - i) (fun t => F i (i + t)))]
    rw [sumNat_succ (m + 1) (fun i => F i (m + 1))]
    have hstep :
        sumNat (m + 1) (fun i => sumNat (m + 1 - i) (fun t => F i (i + t))) +
          sumNat (m + 1) (fun i => F i (m + 1)) =
        sumNat (m + 1) (fun i => sumNat (m + 2 - i) (fun t => F i (i + t))) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro i hi
      have hsub : m + 2 - i = (m + 1 - i) + 1 := by omega
      rw [hsub, sumNat_succ]
      have hidx : i + (m + 1 - i) = m + 1 := by omega
      rw [hidx]
    have hlast : sumNat (m + 2 - (m + 1)) (fun t => F (m + 1) (m + 1 + t)) = F (m + 1) (m + 1) := by
      have : m + 2 - (m + 1) = 1 := by omega
      rw [this]; simp [sumNat]
    rw [hlast, ← Nat.add_assoc, hstep]

private theorem conv_assoc (f g h : Nat → Nat) (k : Nat) :
    conv (conv f g) h k = conv f (conv g h) k := by
  unfold conv
  have hL : sumNat (k + 1) (fun j => sumNat (j + 1) (fun i => f i * g (j - i)) * h (k - j)) =
      sumNat (k + 1) (fun j => sumNat (j + 1) (fun i => f i * g (j - i) * h (k - j))) := by
    apply sumNat_congr; intro j _; rw [← sumNat_mul_right]
  rw [hL, sumNat_triangle_swap k (fun i j => f i * g (j - i) * h (k - j))]
  apply sumNat_congr
  intro i hi
  have hsub : k + 1 - i = (k - i) + 1 := by omega
  rw [hsub, ← sumNat_mul_left]
  apply sumNat_congr
  intro t _
  have h1 : i + t - i = t := by omega
  have h2 : k - (i + t) = k - i - t := by omega
  rw [h1, h2, Nat.mul_assoc]

private theorem conv_one_right (f : Nat → Nat) (k : Nat) :
    conv f (fun j => if j = 0 then 1 else 0) k = f k := by
  unfold conv
  rw [sumNat_single (k := k) (Nat.lt_succ_self k)]
  · simp
  · intro i hi hne
    have hsub : k - i ≠ 0 := by omega
    simp [hsub]

private theorem convPow_add (f : Nat → Nat) (m n k : Nat) :
    convPow f (m + n) k = conv (convPow f m) (convPow f n) k := by
  induction n generalizing k with
  | zero => simp [convPow, conv_one_right]
  | succ n ih =>
    have h1 : m + (n + 1) = (m + n) + 1 := by omega
    rw [h1, convPow, convPow, ← conv_assoc]
    show sumNat (k + 1) (fun i => convPow f (m + n) i * f (k - i)) =
         sumNat (k + 1) (fun i => conv (convPow f m) (convPow f n) i * f (k - i))
    apply sumNat_congr
    intro i _
    rw [ih i]

private theorem convPow_mul (f : Nat → Nat) (m n k : Nat) :
    convPow f (m * n) k = convPow (convPow f m) n k := by
  induction n generalizing k with
  | zero => simp [convPow]
  | succ n ih =>
    rw [Nat.mul_succ, convPow_add, convPow]
    show sumNat (k + 1) (fun i => convPow f (m * n) i * convPow f m (k - i)) =
         sumNat (k + 1) (fun i => convPow (convPow f m) n i * convPow f m (k - i))
    apply sumNat_congr
    intro i _
    rw [ih i]

private theorem convPow_congr_mod {p : Nat} {f g : Nat → Nat}
    (h : ∀ k, f k % p = g k % p) (n k : Nat) :
    convPow f n k % p = convPow g n k % p := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [convPow]
    exact conv_congr_mod ih h k

private def onePlusX : Nat → Nat := fun k => if k ≤ 1 then 1 else 0

private theorem convPow_onePlusX (n k : Nat) : convPow onePlusX n k = choose n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [convPow, choose]
  | succ n ih =>
    simp only [convPow, conv]
    cases k with
    | zero => simp [sumNat, ih, onePlusX, choose]
    | succ k' =>
      have hterm : ∀ i < k' + 2,
          convPow onePlusX n i * onePlusX (k' + 1 - i) =
            if i = k' then choose n k' else if i = k' + 1 then choose n (k' + 1) else 0 := by
        intro i hi
        by_cases h1 : i = k'
        · subst h1; simp [ih, onePlusX]
        · by_cases h2 : i = k' + 1
          · subst h2; simp [ih, onePlusX]
          · have hgt : ¬ (k' + 1 - i ≤ 1) := by omega
            simp [onePlusX, h1, h2, hgt]
      rw [sumNat_congr hterm, sumNat_succ (k' + 1), sumNat_succ k']
      have hpre : sumNat k' (fun i => if i = k' then choose n k' else if i = k' + 1 then choose n (k' + 1) else 0) = 0 := by
        apply sumNat_zero
        intro i hi
        have h1 : i ≠ k' := by omega
        have h2 : i ≠ k' + 1 := by omega
        simp only [h1, h2, ↓reduceIte]
      rw [hpre, Nat.zero_add]
      simp [choose]

private def onePlusXp (p : Nat) : Nat → Nat := fun k => if k = 0 ∨ k = p then 1 else 0

private theorem convPow_onePlusXp {p : Nat} (hp : 0 < p) (q k : Nat) :
    convPow (onePlusXp p) q k = if p ∣ k then choose q (k / p) else 0 := by
  induction q generalizing k with
  | zero =>
    cases k with
    | zero => simp [convPow]
    | succ m =>
      have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
      simp only [convPow, hne, ↓reduceIte]
      by_cases hd : p ∣ m + 1
      · simp only [hd, ↓reduceIte]
        have hpos : 0 < (m + 1) / p := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos m) hd) hp
        cases hq : (m + 1) / p with
        | zero => omega
        | succ _ => rfl
      · simp [hd]
  | succ q ih =>
    simp only [convPow, conv]
    by_cases hk : k < p
    · have hsingle : sumNat (k + 1) (fun i => convPow (onePlusXp p) q i * onePlusXp p (k - i)) =
          convPow (onePlusXp p) q k := by
        rw [sumNat_single (k := k) (Nat.lt_succ_self k)]
        · simp [onePlusXp]
        · intro i hi hne
          have h1 : k - i ≠ 0 := by omega
          have h2 : k - i ≠ p := by omega
          simp [onePlusXp, h1, h2]
      rw [hsingle, ih]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · have hnd : ¬ (p ∣ k) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
        simp [hnd]
    · have hge : p ≤ k := by omega
      have hsplit : sumNat (k + 1) (fun i => convPow (onePlusXp p) q i * onePlusXp p (k - i)) =
          convPow (onePlusXp p) q (k - p) + convPow (onePlusXp p) q k := by
        have hfun : ∀ i < k + 1,
            convPow (onePlusXp p) q i * onePlusXp p (k - i) =
              (if i = k - p then convPow (onePlusXp p) q (k - p) else 0) +
              (if i = k then convPow (onePlusXp p) q k else 0) := by
          intro i hi
          have hneq : k - p ≠ k := by omega
          by_cases h1 : i = k - p
          · subst h1
            have hkp : k - (k - p) = p := by omega
            simp [onePlusXp, hkp, hneq]
          · by_cases h2 : i = k
            · subst h2; simp [onePlusXp, hneq.symm]
            · have ha : k - i ≠ 0 := by omega
              have hb : k - i ≠ p := by omega
              simp [onePlusXp, h1, h2, ha, hb]
        rw [sumNat_congr hfun, sumNat_add]
        have s1 : sumNat (k + 1) (fun i => if i = k - p then convPow (onePlusXp p) q (k - p) else 0) =
            convPow (onePlusXp p) q (k - p) := by
          rw [sumNat_single (k := k - p) (by omega)]
          · simp
          · intro i _ hne; simp [hne]
        have s2 : sumNat (k + 1) (fun i => if i = k then convPow (onePlusXp p) q k else 0) =
            convPow (onePlusXp p) q k := by
          rw [sumNat_single (k := k) (Nat.lt_succ_self k)]
          · simp
          · intro i _ hne; simp [hne]
        rw [s1, s2]
      rw [hsplit, ih, ih]
      by_cases hd : p ∣ k
      · obtain ⟨t, ht⟩ := hd
        have ht1 : 1 ≤ t := by
          cases t with
          | zero => simp at ht; omega
          | succ _ => omega
        have hdsub : p ∣ (k - p) := ⟨t - 1, by rw [ht, Nat.mul_sub_left_distrib, Nat.mul_one]⟩
        have hdiv1 : k / p = t := by rw [ht, Nat.mul_div_right t hp]
        have hdiv2 : (k - p) / p = t - 1 := by
          have : k - p = p * (t - 1) := by rw [ht, Nat.mul_sub_left_distrib, Nat.mul_one]
          rw [this, Nat.mul_div_right (t - 1) hp]
        have hdk : p ∣ k := ⟨t, ht⟩
        simp only [hdsub, hdk, ↓reduceIte, hdiv1, hdiv2]
        have ht_eq : t = (t - 1) + 1 := by omega
        conv => rhs; rw [ht_eq]
        rw [choose, ← ht_eq]
      · have hndsub : ¬ (p ∣ (k - p)) := by
          intro ⟨t, ht⟩
          apply hd
          refine ⟨t + 1, ?_⟩
          rw [Nat.mul_add, Nat.mul_one]; omega
        simp [hd, hndsub]

/-- **Lucas's Theorem:** For any prime `p` and any `n, k : Nat`,
`choose n k % p = (choose (n / p) (k / p) * choose (n % p) (k % p)) % p`. -/
theorem lucas_theorem {p : Nat} (hp : IsPrime p) (n k : Nat) :
    choose n k % p = (choose (n / p) (k / p) * choose (n % p) (k % p)) % p := by
  have h1 : choose n k = conv (convPow (convPow onePlusX p) (n / p)) (convPow onePlusX (n % p)) k := by
    rw [← convPow_onePlusX]
    have hdiv : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
    conv => lhs; rw [hdiv]
    rw [convPow_add]
    unfold conv
    apply sumNat_congr
    intro i _
    rw [convPow_mul]
  have hmodp : ∀ j, convPow onePlusX p j % p = onePlusXp p j % p := by
    intro j
    rw [convPow_onePlusX]
    by_cases hj0 : j = 0
    · subst hj0; simp [onePlusXp]
    · by_cases hjp : j = p
      · subst hjp; simp [onePlusXp, choose_self]
      · by_cases hjlt : j < p
        · have hd : p ∣ choose p j := prime_dvd_choose hp (by omega) hjlt
          simp [onePlusXp, hj0, hjp, Nat.mod_eq_zero_of_dvd hd]
        · have hgt : p < j := by omega
          simp [onePlusXp, hj0, hjp, choose_eq_zero_of_lt hgt]
  have h2 : choose n k % p =
      conv (convPow (onePlusXp p) (n / p)) (convPow onePlusX (n % p)) k % p := by
    rw [h1]
    exact conv_congr_mod (convPow_congr_mod hmodp (n / p)) (fun _ => rfl) k
  rw [h2]
  unfold conv
  have hsingle :
      sumNat (k + 1) (fun i => convPow (onePlusXp p) (n / p) i * convPow onePlusX (n % p) (k - i)) =
        choose (n / p) (k / p) * choose (n % p) (k % p) := by
    have hlt : p * (k / p) < k + 1 := by
      have := Nat.div_add_mod k p; omega
    rw [sumNat_single (k := p * (k / p)) hlt]
    · rw [convPow_onePlusXp hp.pos, convPow_onePlusX]
      have hdvd : p ∣ p * (k / p) := Nat.dvd_mul_right p (k / p)
      have hdivk : (p * (k / p)) / p = k / p := Nat.mul_div_right (k / p) hp.pos
      have hmodk : k - p * (k / p) = k % p := by have := Nat.div_add_mod k p; omega
      simp [hdvd, hdivk, hmodk]
    · intro i hi hne
      rw [convPow_onePlusXp hp.pos, convPow_onePlusX]
      by_cases hdi : p ∣ i
      · obtain ⟨t, rfl⟩ := hdi
        have htne : t ≠ k / p := fun h => hne (by rw [h])
        have hlt_t : t < k / p := by
          have h1 : p * t ≤ k := by omega
          have h2 : t ≤ k / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [Nat.mul_comm]; exact h1)
          omega
        have hsub_gt : n % p < k - p * t := by
          have hmod_lt : n % p < p := Nat.mod_lt n hp.pos
          have hdk : p * (k / p) ≤ k := by have := Nat.div_add_mod k p; omega
          have hstep : p * (t + 1) ≤ p * (k / p) := Nat.mul_le_mul_left p (by omega)
          rw [Nat.mul_add, Nat.mul_one] at hstep
          omega
        simp [choose_eq_zero_of_lt hsub_gt]
      · simp [hdi]
  rw [hsingle]

/-! ## 3. Base-`p` Digit Sum and Bidirectional Lucas/Fermat Lemmas -/

/-- The sum of the digits of a natural number in the given base. -/
def digitSum (p : Nat) (n : Nat) : Nat :=
  if _hp : 2 ≤ p then
    if _hn : n = 0 then 0
    else n % p + digitSum p (n / p)
  else n
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero _hn) (by omega)

theorem digitSum_zero (p : Nat) : digitSum p 0 = 0 := by
  unfold digitSum
  by_cases hp : 2 ≤ p <;> simp [hp]

theorem digitSum_eq {p : Nat} (hp : 2 ≤ p) (n : Nat) (hn : n ≠ 0) :
    digitSum p n = n % p + digitSum p (n / p) := by
  conv => lhs; unfold digitSum
  simp [hp, hn]

theorem digitSum_of_lt {p n : Nat} (hp : 2 ≤ p) (hn : n < p) : digitSum p n = n := by
  by_cases h0 : n = 0
  · subst h0; exact digitSum_zero p
  · rw [digitSum_eq hp n h0, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, digitSum_zero, Nat.add_zero]

theorem digitSum_mul_add {p q r : Nat} (hp : 2 ≤ p) (hr : r < p) :
    digitSum p (p * q + r) = r + digitSum p q := by
  by_cases h0 : p * q + r = 0
  · have hq0 : q = 0 := by
      cases q with
      | zero => rfl
      | succ m =>
        have hpos : p ≤ p * (m + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos m)
        omega
    have hr0 : r = 0 := by omega
    subst hq0; subst hr0; simp [digitSum_zero]
  · rw [digitSum_eq hp (p * q + r) h0]
    have hm : (p * q + r) % p = r := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hd : (p * q + r) / p = q := by
      rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    rw [hm, hd]

theorem digitSum_pow {p : Nat} (hp : 2 ≤ p) (m : Nat) : digitSum p (p ^ m) = 1 := by
  induction m with
  | zero =>
    rw [Nat.pow_zero]
    exact digitSum_of_lt hp (by omega)
  | succ k ih =>
    have h1 : p ^ (k + 1) = p * (p ^ k) + 0 := by rw [Nat.pow_succ, Nat.mul_comm, Nat.add_zero]
    rw [h1, digitSum_mul_add hp (by omega), ih, Nat.zero_add]

theorem digitSum_eq_zero_iff {p : Nat} (hp : 2 ≤ p) (n : Nat) : digitSum p n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · exfalso
      have hpos : ∀ m, m ≠ 0 → 0 < digitSum p m := by
        intro m
        induction m using nat_strong_ind with
        | _ m ihm =>
          intro hm
          rw [digitSum_eq hp m hm]
          by_cases hr : m % p = 0
          · have hq : m / p ≠ 0 := by
              have hdm := Nat.div_add_mod m p
              intro hdiv0; rw [hdiv0, hr] at hdm; simp at hdm; exact hm hdm.symm
            have hlt : m / p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by omega)
            have := ihm (m / p) hlt hq
            omega
          · omega
      have := hpos n hn; omega
  · intro h; subst h; exact digitSum_zero p

/-- **Fermat Digit-Sum Collapse:** For EVERY prime `p`, EVERY `a : Nat` (including `a = 0`),
and EVERY `n : Nat`, `a ^ n % p = a ^ (digitSum p n) % p`! -/
theorem pow_mod_eq_pow_digitSum {p : Nat} (hp : IsPrime p) (a n : Nat) :
    a ^ n % p = a ^ (digitSum p n) % p := by
  induction n using nat_strong_ind with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [digitSum_zero]
    · have hdiv : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
      have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.gt_one
      have hcomm : (a ^ p) ^ (n / p) = (a ^ (n / p)) ^ p := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
      rw [digitSum_eq hp.1 n hn]
      conv => lhs; rw [hdiv]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hcomm, fermat_little hp,
          ih (n / p) hlt, ← Nat.mul_mod, Nat.mul_comm, ← Nat.pow_add]

theorem exists_lucas_sub {p : Nat} (hp : IsPrime p) (d : Nat) :
    ∀ r ≤ digitSum p d,
      ∃ j ≤ d, digitSum p j = r ∧ choose d j % p ≠ 0 ∧ (r < digitSum p d → j < d) := by
  induction d using nat_strong_ind with
  | _ d ih =>
    intro r hr
    by_cases hd0 : d = 0
    · subst hd0
      rw [digitSum_zero] at hr
      have hr0 : r = 0 := by omega
      subst hr0
      refine ⟨0, Nat.le_refl 0, digitSum_zero p, ?_, fun h => by rw [digitSum_zero] at h; omega⟩
      have := hp.gt_one; simp [choose]; omega
    · rw [digitSum_eq hp.1 d hd0] at hr
      let rem := d % p
      let q := d / p
      have hrem_lt : rem < p := Nat.mod_lt d hp.pos
      have hq_lt : q < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.gt_one
      let jr := min r rem
      let rq := r - jr
      have hjr_le_rem : jr ≤ rem := Nat.min_le_right r rem
      have hrq_le : rq ≤ digitSum p q := by
        change r - min r rem ≤ digitSum p (d / p)
        omega
      obtain ⟨jq, hjq_le, hjq_sum, hjq_ch, hjq_lt⟩ := ih q hq_lt rq hrq_le
      let j := p * jq + jr
      have hj_le : j ≤ d := by
        have hdiv : d = p * q + rem := (Nat.div_add_mod d p).symm
        have hmul : p * jq ≤ p * q := Nat.mul_le_mul_left p hjq_le
        omega
      have hj_sum : digitSum p j = r := by
        rw [digitSum_mul_add hp.1 (by omega), hjq_sum]; omega
      have hj_ch : choose d j % p ≠ 0 := by
        rw [lucas_theorem hp]
        have hjdiv : j / p = jq := by
          show (p * jq + jr) / p = jq
          rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
        have hjmod : j % p = jr := by
          show (p * jq + jr) % p = jr
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hjdiv, hjmod]
        apply prime_mul_mod_ne_zero hp hjq_ch
        exact prime_not_dvd_choose_of_lt hp hjr_le_rem hrem_lt
      refine ⟨j, hj_le, hj_sum, hj_ch, ?_⟩
      intro hrlt
      rw [digitSum_eq hp.1 d hd0] at hrlt
      have hdiv : d = p * q + rem := (Nat.div_add_mod d p).symm
      by_cases hjr_lt : jr < rem
      · have hmul : p * jq ≤ p * q := Nat.mul_le_mul_left p hjq_le
        omega
      · have hrq_lt : rq < digitSum p q := by
          change r - min r rem < digitSum p (d / p)
          omega
        have hjq_strict : jq < q := hjq_lt hrq_lt
        have hmul : p * jq + p ≤ p * q := by
          have h1 : p * (jq + 1) ≤ p * q := Nat.mul_le_mul_left p hjq_strict
          rw [Nat.mul_add, Nat.mul_one] at h1; exact h1
        omega

theorem digitSum_le_of_choose_ne_zero {p : Nat} (hp : IsPrime p) (d : Nat) :
    ∀ j, choose d j % p ≠ 0 →
      digitSum p j ≤ digitSum p d ∧ (j < d → digitSum p j < digitSum p d) := by
  induction d using nat_strong_ind with
  | _ d ih =>
    intro j hch
    by_cases hd0 : d = 0
    · subst hd0
      cases j with
      | zero => simp [digitSum_zero]
      | succ j' => simp [choose] at hch
    · rw [lucas_theorem hp] at hch
      have hq_ne : choose (d / p) (j / p) % p ≠ 0 := by
        intro hz; rw [Nat.mul_mod, hz, Nat.zero_mul] at hch; exact hch rfl
      have hr_ne : choose (d % p) (j % p) % p ≠ 0 := by
        intro hz; rw [Nat.mul_mod, hz, Nat.mul_zero] at hch; exact hch rfl
      have hr_le : j % p ≤ d % p := by
        by_cases hle : j % p ≤ d % p
        · exact hle
        · exfalso
          have := choose_eq_zero_of_lt (n := d % p) (k := j % p) (by omega)
          simp [this] at hr_ne
      have hq_lt : d / p < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.gt_one
      obtain ⟨hq_sum_le, hq_sum_lt⟩ := ih (d / p) hq_lt (j / p) hq_ne
      by_cases hj0 : j = 0
      · subst hj0
        rw [digitSum_zero]
        have hd_pos : 0 < digitSum p d := by
          cases hdz : digitSum p d with
          | zero => exfalso; exact hd0 ((digitSum_eq_zero_iff hp.1 d).mp hdz)
          | succ _ => exact Nat.succ_pos _
        exact ⟨Nat.zero_le _, fun _ => hd_pos⟩
      · rw [digitSum_eq hp.1 d hd0, digitSum_eq hp.1 j hj0]
        refine ⟨by omega, ?_⟩
        intro hjlt
        have hdd : d = p * (d / p) + d % p := (Nat.div_add_mod d p).symm
        have hjj : j = p * (j / p) + j % p := (Nat.div_add_mod j p).symm
        by_cases hrl : j % p < d % p
        · omega
        · have hre : j % p = d % p := by omega
          have hqstrict : j / p < d / p := by
            cases Nat.lt_or_ge (j / p) (d / p) with
            | inl h => exact h
            | inr hge =>
              have hmul : p * (d / p) ≤ p * (j / p) := Nat.mul_le_mul_left p hge
              omega
          have := hq_sum_lt hqstrict
          omega

/-! ## 4. Forward Finite Differences over `Int` (For Sufficiency `⇐` of T1) -/

/-- Sum an integer-valued function on the indices strictly below the bound. -/
def sumInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | m + 1 => sumInt m f + f m

theorem sumInt_succ (n : Nat) (f : Nat → Int) : sumInt (n + 1) f = sumInt n f + f n := rfl

theorem sumInt_congr {n : Nat} {f g : Nat → Int} (h : ∀ i < n, f i = g i) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumInt_succ, sumInt_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]

theorem sumInt_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumInt_succ, sumInt_succ, sumInt_succ, ih]; omega

theorem sumInt_sub (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i - g i) = sumInt n f - sumInt n g := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumInt_succ, sumInt_succ, sumInt_succ, ih]; omega

theorem sumInt_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumInt n (fun i => c * f i) = c * sumInt n f := by
  induction n with
  | zero => simp [sumInt]
  | succ m ih => rw [sumInt_succ, sumInt_succ, ih, Int.mul_add]

theorem sumInt_zero {n : Nat} {f : Nat → Int} (h : ∀ i < n, f i = 0) : sumInt n f = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumInt_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]; omega

theorem sumInt_succ_shift (n : Nat) (f : Nat → Int) :
    sumInt (n + 1) f = f 0 + sumInt n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumInt]
  | succ m ih =>
    rw [sumInt_succ (m + 1), ih, sumInt_succ m (fun i => f (i + 1))]; omega

/-- Apply the forward-difference operator the specified number of times. -/
def iterDiff : Nat → (Nat → Int) → Nat → Int
  | 0, f, x => f x
  | s + 1, f, x => iterDiff s (fun y => f (y + 1) - f y) x

theorem iterDiff_add (s : Nat) (f g : Nat → Int) (x : Nat) :
    iterDiff s (fun y => f y + g y) x = iterDiff s f x + iterDiff s g x := by
  induction s generalizing f g x with
  | zero => rfl
  | succ s ih =>
    simp only [iterDiff]
    have hfun : (fun y => f (y + 1) + g (y + 1) - (f y + g y)) =
        (fun y => (f (y + 1) - f y) + (g (y + 1) - g y)) := by
      funext y; omega
    rw [hfun, ih]

theorem iterDiff_const_mul (s : Nat) (c : Int) (f : Nat → Int) (x : Nat) :
    iterDiff s (fun y => c * f y) x = c * iterDiff s f x := by
  induction s generalizing f x with
  | zero => rfl
  | succ s ih =>
    simp only [iterDiff]
    have hfun : (fun y => c * f (y + 1) - c * f y) = (fun y => c * (f (y + 1) - f y)) := by
      funext y; rw [← Int.mul_sub]
    rw [hfun, ih]

theorem iterDiff_sumInt (s n : Nat) (F : Nat → Nat → Int) (x : Nat) :
    iterDiff s (fun y => sumInt n (fun k => F k y)) x =
      sumInt n (fun k => iterDiff s (fun y => F k y) x) := by
  induction n with
  | zero =>
    simp only [sumInt]
    induction s generalizing x with
    | zero => rfl
    | succ s ih => exact ih x
  | succ m ih =>
    have hfun : (fun y => sumInt (m + 1) (fun k => F k y)) =
        (fun y => sumInt m (fun k => F k y) + F m y) := rfl
    rw [hfun, iterDiff_add, ih, sumInt_succ]

/-- The alternating sign with the given natural index, starting with plus one. -/
def altSign : Nat → Int
  | 0 => 1
  | k + 1 => -altSign k

theorem iterDiff_eq_sum (s : Nat) (f : Nat → Int) (x : Nat) :
    iterDiff s f x =
      sumInt (s + 1) (fun a => altSign (s - a) * (choose s a : Int) * f (x + a)) := by
  induction s generalizing f x with
  | zero => simp [iterDiff, sumInt, altSign, choose]
  | succ s ih =>
    simp only [iterDiff]
    rw [ih (fun y => f (y + 1) - f y) x]
    have hsplit :
        sumInt (s + 1) (fun a => altSign (s - a) * (choose s a : Int) * (f (x + a + 1) - f (x + a))) =
        sumInt (s + 1) (fun a => altSign (s - a) * (choose s a : Int) * f (x + (a + 1))) -
        sumInt (s + 1) (fun a => altSign (s - a) * (choose s a : Int) * f (x + a)) := by
      rw [← sumInt_sub]
      apply sumInt_congr
      intro a _
      have : x + a + 1 = x + (a + 1) := by omega
      rw [this, Int.mul_sub]
    rw [hsplit]
    have h1 :
        sumInt (s + 1) (fun a => altSign (s - a) * (choose s a : Int) * f (x + (a + 1))) =
        sumInt s (fun a => altSign (s - a) * (choose s a : Int) * f (x + (a + 1))) + f (x + (s + 1)) := by
      rw [sumInt_succ]
      simp only [Nat.sub_self, altSign, choose_self, Int.natCast_one, Int.one_mul]
    have h2 :
        sumInt (s + 1) (fun a => altSign (s - a) * (choose s a : Int) * f (x + a)) =
        altSign s * f x + sumInt s (fun a => altSign (s - (a + 1)) * (choose s (a + 1) : Int) * f (x + (a + 1))) := by
      rw [sumInt_succ_shift]
      simp only [Nat.sub_zero, choose_zero_right, Nat.add_zero, Int.natCast_one, Int.mul_one]
    rw [h1, h2]
    have hRHS :
        sumInt (s + 2) (fun a => altSign (s + 1 - a) * (choose (s + 1) a : Int) * f (x + a)) =
        altSign (s + 1) * f x +
        sumInt s (fun a => altSign (s - a) * ((choose s a : Int) + (choose s (a + 1) : Int)) * f (x + (a + 1))) +
        f (x + (s + 1)) := by
      rw [sumInt_succ (s + 1), sumInt_succ_shift s]
      congr 1
      · congr 1
        · simp only [Nat.sub_zero, choose_zero_right, Nat.add_zero, Int.natCast_one, Int.mul_one]
        · apply sumInt_congr
          intro a _
          have hsub : s + 1 - (a + 1) = s - a := by omega
          rw [hsub, choose, Int.natCast_add]
      · simp only [Nat.sub_self, altSign, choose_self, Int.natCast_one, Int.one_mul]
    rw [hRHS]
    have hmid :
        sumInt s (fun a => altSign (s - a) * (choose s a : Int) * f (x + (a + 1))) -
        sumInt s (fun a => altSign (s - (a + 1)) * (choose s (a + 1) : Int) * f (x + (a + 1))) =
        sumInt s (fun a => altSign (s - a) * ((choose s a : Int) + (choose s (a + 1) : Int)) * f (x + (a + 1))) := by
      rw [← sumInt_sub]
      apply sumInt_congr
      intro a ha
      have hsub : s - a = (s - (a + 1)) + 1 := by omega
      have hsign : -altSign (s - (a + 1)) = altSign (s - a) := by rw [hsub]; rfl
      calc
        altSign (s - a) * (choose s a : Int) * f (x + (a + 1)) -
          altSign (s - (a + 1)) * (choose s (a + 1) : Int) * f (x + (a + 1))
            = altSign (s - a) * (choose s a : Int) * f (x + (a + 1)) +
              (-altSign (s - (a + 1))) * (choose s (a + 1) : Int) * f (x + (a + 1)) := by
                rw [Int.neg_mul, Int.neg_mul, Int.sub_eq_add_neg]
        _   = altSign (s - a) * (choose s a : Int) * f (x + (a + 1)) +
              altSign (s - a) * (choose s (a + 1) : Int) * f (x + (a + 1)) := by rw [hsign]
        _   = altSign (s - a) * ((choose s a : Int) + (choose s (a + 1) : Int)) * f (x + (a + 1)) := by
                rw [← Int.add_mul, ← Int.mul_add]
    have hsign0 : -altSign s = altSign (s + 1) := rfl
    have hneg0 : -(altSign s * f x) = altSign (s + 1) * f x := by
      rw [← Int.neg_mul, hsign0]
    omega

theorem iterDiff_pow (r : Nat) :
    ∀ s x : Nat,
      (r < s → iterDiff s (fun y => ((y : Int) ^ r)) x = 0) ∧
      (r = s → iterDiff s (fun y => ((y : Int) ^ r)) x = (fact s : Int)) := by
  induction r using nat_strong_ind with
  | _ r ih =>
    intro s x
    cases s with
    | zero =>
      constructor
      · intro h; omega
      · intro hr; subst hr; simp [iterDiff, fact]
    | succ s' =>
      cases r with
      | zero =>
        constructor
        · intro _
          simp only [iterDiff, Int.pow_zero]
          have h0 : (fun _ : Nat => (1 : Int) - 1) = (fun _ => 0) := by funext _; rfl
          rw [h0]
          have hiter0 : ∀ (k y : Nat), iterDiff k (fun _ => (0 : Int)) y = 0 := by
            intro k
            induction k with
            | zero => intro _; rfl
            | succ m ihm => intro y; exact ihm y
          exact hiter0 s' x
        · intro h; omega
      | succ r' =>
        have hexp : ∀ y : Nat,
            ((y + 1 : Nat) : Int) ^ (r' + 1) - (y : Int) ^ (r' + 1) =
              sumInt (r' + 1) (fun k => (choose (r' + 1) k : Int) * (y : Int) ^ k) := by
          intro y
          have hnat := nat_binomial 1 y (r' + 1)
          rw [Nat.add_comm 1 y] at hnat
          have hcast : ((y + 1 : Nat) : Int) ^ (r' + 1) =
              sumInt (r' + 2) (fun k => (choose (r' + 1) k : Int) * (y : Int) ^ k) := by
            have h1 : (y + 1) ^ (r' + 1) = sumNat (r' + 2) (fun k => choose (r' + 1) k * y ^ k) := by
              rw [hnat]
              apply sumNat_congr
              intro k _; simp [Nat.one_pow]
            have hsum_cast : ∀ (m : Nat) (g : Nat → Nat),
                (sumNat m g : Int) = sumInt m (fun k => (g k : Int)) := by
              intro m g
              induction m with
              | zero => rfl
              | succ m' ihm' => rw [sumNat_succ, sumInt_succ, Int.natCast_add, ihm']
            rw [← Int.natCast_pow, h1, hsum_cast]
            apply sumInt_congr
            intro k _; rw [Int.natCast_mul, Int.natCast_pow]
          rw [hcast, sumInt_succ (r' + 1)]
          simp only [choose_self, Int.natCast_one, Int.one_mul]
          omega
        have hstep :
            iterDiff (s' + 1) (fun y => (y : Int) ^ (r' + 1)) x =
              sumInt (r' + 1) (fun k => (choose (r' + 1) k : Int) * iterDiff s' (fun y => (y : Int) ^ k) x) := by
          simp only [iterDiff]
          have hfun : (fun y : Nat => ((y + 1 : Nat) : Int) ^ (r' + 1) - (y : Int) ^ (r' + 1)) =
              (fun y : Nat => sumInt (r' + 1) (fun k => (choose (r' + 1) k : Int) * (y : Int) ^ k)) := by
            funext y; exact hexp y
          rw [hfun, iterDiff_sumInt]
          apply sumInt_congr
          intro k _
          exact iterDiff_const_mul s' (choose (r' + 1) k : Int) (fun y => (y : Int) ^ k) x
        constructor
        · intro hlt
          rw [hstep]
          apply sumInt_zero
          intro k hk
          have hzero := (ih k (by omega) s' x).1 (by omega)
          rw [hzero, Int.mul_zero]
        · intro heq
          have hrs : r' = s' := by omega
          subst hrs
          rw [hstep, sumInt_succ]
          have hlower : sumInt r' (fun k => (choose (r' + 1) k : Int) * iterDiff r' (fun y => (y : Int) ^ k) x) = 0 := by
            apply sumInt_zero
            intro k hk
            have hzero := (ih k (by omega) r' x).1 hk
            rw [hzero, Int.mul_zero]
          rw [hlower, Int.zero_add]
          have htop := (ih r' (Nat.lt_succ_self r') r' x).2 rfl
          rw [htop]
          have hch : choose (r' + 1) r' = r' + 1 := by
            clear ih hstep hlower htop hexp
            induction r' with
            | zero => rfl
            | succ m ihm =>
              rw [choose, ihm, choose_self]
              omega
          rw [hch, fact, Int.natCast_mul]

/-! ## 5. Monic Annihilator Polynomial `prodLinear` (For Necessity `⇒` of T1) -/

/-- Multiply by the monic linear polynomial with root `a` and add `prev` to the result. -/
def mulLinearGo (a prev : Int) : List Int → List Int
  | [] => [prev]
  | c :: rest => (prev - a * c) :: mulLinearGo a c rest

/-- Multiply an integer coefficient list by a monic linear polynomial. -/
def mulLinear (P : List Int) (a : Int) : List Int :=
  mulLinearGo a 0 P

/-- Evaluate an integer coefficient list in ascending degree order. -/
def evalIntPoly (P : List Int) (x : Int) : Int :=
  match P with
  | [] => 0
  | c :: rest => c + x * evalIntPoly rest x

private theorem evalIntPoly_mulLinearGo (prev a x : Int) (P : List Int) :
    evalIntPoly (mulLinearGo a prev P) x = prev + (x - a) * evalIntPoly P x := by
  induction P generalizing prev with
  | nil => simp [mulLinearGo, evalIntPoly]
  | cons c rest ih =>
    simp only [mulLinearGo, evalIntPoly, ih]
    calc
      prev - a * c + x * (c + (x - a) * evalIntPoly rest x)
          = prev + (-(a * c) + (x * c + x * ((x - a) * evalIntPoly rest x))) := by
            rw [Int.mul_add, Int.sub_eq_add_neg]; omega
      _   = prev + ((x - a) * c + (x - a) * (x * evalIntPoly rest x)) := by
            congr 1
            have h1 : (x - a) * c = x * c - a * c := Int.sub_mul x a c
            have h2 : (x - a) * (x * evalIntPoly rest x) = x * ((x - a) * evalIntPoly rest x) := by
              rw [← Int.mul_assoc, Int.mul_comm (x - a) x, Int.mul_assoc]
            rw [h1, h2]; omega
      _   = prev + (x - a) * (c + x * evalIntPoly rest x) := by rw [← Int.mul_add]

theorem evalIntPoly_mulLinear (P : List Int) (a x : Int) :
    evalIntPoly (mulLinear P a) x = (x - a) * evalIntPoly P x := by
  unfold mulLinear
  rw [evalIntPoly_mulLinearGo, Int.zero_add]

private theorem mulLinearGo_length (a prev : Int) (P : List Int) :
    (mulLinearGo a prev P).length = P.length + 1 := by
  induction P generalizing prev with
  | nil => rfl
  | cons c rest ih => simp [mulLinearGo, ih]

private theorem mulLinearGo_lead (a prev : Int) (P : List Int) (hP : P ≠ []) :
    (mulLinearGo a prev P).getD P.length 0 = P.getD (P.length - 1) 0 := by
  induction P generalizing prev with
  | nil => contradiction
  | cons c rest ih =>
    cases rest with
    | nil => rfl
    | cons c2 rest2 =>
      change (mulLinearGo a c (c2 :: rest2)).getD (c2 :: rest2).length 0 =
             (c :: c2 :: rest2).getD ((c2 :: rest2).length) 0
      rw [ih c (by simp)]
      simp

/-- Multiply the monic linear polynomials determined by the given integer roots. -/
def prodLinear : List Nat → List Int
  | [] => [1]
  | a :: rest => mulLinear (prodLinear rest) (a : Int)

theorem prodLinear_length (A : List Nat) : (prodLinear A).length = A.length + 1 := by
  induction A with
  | nil => rfl
  | cons a rest ih =>
    simp only [prodLinear, mulLinear, mulLinearGo_length, ih, List.length_cons]

theorem prodLinear_lead (A : List Nat) : (prodLinear A).getD A.length 0 = 1 := by
  induction A with
  | nil => rfl
  | cons a rest ih =>
    simp only [prodLinear, List.length_cons]
    have hlen : (prodLinear rest).length = rest.length + 1 := prodLinear_length rest
    have hne : prodLinear rest ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [← hlen]
    unfold mulLinear
    rw [mulLinearGo_lead (a : Int) 0 (prodLinear rest) hne, hlen]
    simpa using ih

theorem prodLinear_eval_mem (A : List Nat) {a : Nat} (ha : a ∈ A) :
    evalIntPoly (prodLinear A) (a : Int) = 0 := by
  induction A with
  | nil => cases ha
  | cons b rest ih =>
    simp only [prodLinear, evalIntPoly_mulLinear]
    simp only [List.mem_cons] at ha
    rcases ha with rfl | hmem
    · simp
    · rw [ih hmem, Int.mul_zero]

theorem evalIntPoly_eq_sumInt (P : List Int) (x : Int) :
    evalIntPoly P x = sumInt P.length (fun r => P.getD r 0 * x ^ r) := by
  induction P with
  | nil => rfl
  | cons c rest ih =>
    simp only [evalIntPoly, ih, List.length_cons]
    rw [sumInt_succ_shift]
    simp only [List.getD_cons_zero, Int.pow_zero, Int.mul_one, List.getD_cons_succ]
    congr 1
    rw [← sumInt_mul_left]
    apply sumInt_congr
    intro r _
    rw [Int.pow_succ, Int.mul_comm x (rest.getD r 0 * x ^ r), Int.mul_assoc]

end

end Catalytic
