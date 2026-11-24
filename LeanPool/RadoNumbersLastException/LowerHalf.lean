/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/

module

/-!
# The Boundary Colouring for Two-Colour Rado Numbers

Defines the lower bound `LB(c, k)` from Martinelli and Schaal (2007, Lemma 2)
and the exact last-exception formula `c*(k) = k(k^2 + k - 4)/2` (odd `k`) and `k(k^2 - 2)/2` (even `k`), and proves
that for every `k ≥ 3`, `[1, LB(c*(k), k)]` admits a 2-colouring with no monochromatic
solution of `x + y + c*(k) = k z` (`exists_good_col_cstar`).
-/

@[expose] public section

namespace RadoNu

namespace LowerHalf

/-! ## Definitions, as in the text -/

/-- LB(c, k) = ceil((2 ceil((c + 2)/k) + c)/k); `ceil(a/k)` is `(a + k - 1) / k`. -/
def LB (c k : Nat) : Nat := (2 * ((c + 2 + k - 1) / k) + c + k - 1) / k

/-- c*(k) = k(k^2 + k - 4)/2 for odd k, k(k^2 - 2)/2 for even k. -/
def cstar (k : Nat) : Nat :=
  if k % 2 = 1 then k * (k * k + k - 4) / 2 else k * (k * k - 2) / 2

/-- Odd k = 2j + 1, so j = (k - 1)/2: colour 1 if x mod k is in [1, j], or if
k | x and x >= k(floor(j/2) + 2); colour 0 otherwise. -/
def colOdd (k x : Nat) : Bool :=
  decide ((1 ≤ x % k ∧ x % k ≤ (k - 1) / 2) ∨
    (x % k = 0 ∧ k * ((k - 1) / 2 / 2 + 2) ≤ x))

/-- Even k, q = k(k - 2)/2: colour 0 on {q + 1} and [q + k, q + 2k - 2],
colour 1 elsewhere. -/
def colEven (k x : Nat) : Bool :=
  decide (¬ (x = k * (k - 2) / 2 + 1 ∨
    (k * (k - 2) / 2 + k ≤ x ∧ x ≤ k * (k - 2) / 2 + 2 * k - 2)))

/-- The proof's colouring for k. -/
def col (k x : Nat) : Bool := if k % 2 = 1 then colOdd k x else colEven k x

/-- The proof's N: k(j + 2) - 1 for odd k = 2j + 1; q + 2k - 1 for even k. -/
def N (k : Nat) : Nat :=
  if k % 2 = 1 then k * ((k - 1) / 2 + 2) - 1 else k * (k - 2) / 2 + 2 * k - 1

/-! ## Small arithmetic lemmas -/

theorem div_eq_of_decomp {a k q r : Nat} (h : a = k * q + r) (hr : r < k) :
    a / k = q := by
  subst h
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem mod_eq_of_decomp {a k q r : Nat} (h : a = k * q + r) (hr : r < k) :
    a % k = r := by
  subst h
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- If r + s = k w with r, s < k then w <= 1. -/
theorem sum_lt_two {k r s w : Nat} (hr : r < k) (hs : s < k)
    (h : r + s = k * w) : w = 0 ∨ w = 1 := by
  by_cases hw : 2 ≤ w
  · have h2 := Nat.mul_le_mul_left k hw
    omega
  · omega

/-- From x + y + k m = k z: z = m + t with x + y = k t. -/
theorem shift {k m x y z : Nat} (hk : 0 < k) (h : x + y + k * m = k * z) :
    ∃ t, z = m + t ∧ x + y = k * t := by
  have hzm : m ≤ z := by
    by_cases hc : m ≤ z
    · exact hc
    · have h1 := Nat.mul_le_mul_left k (show z + 1 ≤ m by omega)
      have h2 := Nat.mul_add k z 1
      omega
  refine ⟨z - m, by omega, ?_⟩
  have h3 := Nat.mul_add k m (z - m)
  rw [show m + (z - m) = z by omega] at h3
  omega

/-! ## Odd k = 2j + 1 -/

theorem sq_odd {k j : Nat} (hk : k = 2 * j + 1) : k * k = 2 * (k * j) + k := by
  have h1 : k * k = k * (2 * j + 1) := by rw [← hk]
  rw [h1, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

/-- c*(k) = k m with m = k j + 2j - 1 (= (k^2 + k - 4)/2). -/
theorem cstar_odd {k j : Nat} (hk : k = 2 * j + 1) (hj : 1 ≤ j) :
    cstar k = k * (k * j + 2 * j - 1) := by
  have hkk := sq_odd hk
  have hmod : k % 2 = 1 := by omega
  have h2 : k * k + k - 4 = 2 * (k * j + 2 * j - 1) := by omega
  unfold cstar
  simp only [hmod, ↓reduceIte]
  rw [h2, Nat.mul_left_comm k 2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- LB(c*(k), k) = k(j + 2) - 1 for odd k = 2j + 1. -/
theorem LB_odd {k j : Nat} (hk : k = 2 * j + 1) (hj : 1 ≤ j) :
    LB (cstar k) k = k * (j + 2) - 1 := by
  have hkk := sq_odd hk
  rw [cstar_odd hk hj]
  obtain ⟨m, hm⟩ : ∃ m, m = k * j + 2 * j - 1 := ⟨_, rfl⟩
  rw [← hm]
  have e1 := Nat.mul_add k m 1
  have e2 := Nat.mul_add k m (k + 1)
  have e3 := Nat.mul_add k k 1
  have e4 := Nat.mul_add k j 2
  have h1 : (k * m + 2 + k - 1) / k = m + 1 :=
    div_eq_of_decomp (r := 1) (by omega) (by omega)
  have h2 : (2 * (m + 1) + k * m + k - 1) / k = m + (k + 1) :=
    div_eq_of_decomp (r := k - 3) (by omega) (by omega)
  unfold LB
  rw [h1, h2]
  omega

/-- The odd colouring at x = k u + r, r < k. -/
theorem colOdd_eq {k j u r : Nat} (hk : k = 2 * j + 1) (hr : r < k) :
    colOdd k (k * u + r) =
      decide ((1 ≤ r ∧ r ≤ j) ∨ (r = 0 ∧ j / 2 + 2 ≤ u)) := by
  have hmod : (k * u + r) % k = r := mod_eq_of_decomp rfl hr
  have hj : (k - 1) / 2 = j := by omega
  unfold colOdd
  rw [hmod, hj]
  apply decide_eq_decide.mpr
  by_cases hu : j / 2 + 2 ≤ u
  · have h1 := Nat.mul_le_mul_left k hu
    omega
  · have h1 := Nat.mul_le_mul_left k (show u + 1 ≤ j / 2 + 2 by omega)
    have h2 := Nat.mul_add k u 1
    omega

/-- Odd case of the lower half, with `N` and `c*` in closed form. -/
theorem odd_case {k j : Nat} (hk : k = 2 * j + 1) (hj : 1 ≤ j) (x y z : Nat)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hzN : z ≤ k * (j + 2) - 1)
    (h : x + y + k * (k * j + 2 * j - 1) = k * z) :
    ¬ (colOdd k x = colOdd k y ∧ colOdd k y = colOdd k z) := by
  have hkpos : 0 < k := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = k * j + 2 * j - 1 := ⟨_, rfl⟩
  rw [← hm] at h
  obtain ⟨t, rfl, hxy⟩ := shift hkpos h
  have e1 := Nat.mul_add k j 2
  have e2 := Nat.mul_add k j 1
  have ht : t ≤ k + 1 := by omega
  -- x = k u + r, y = k v + s
  obtain ⟨u, r, hr, rfl⟩ : ∃ u r, r < k ∧ x = k * u + r :=
    ⟨x / k, x % k, Nat.mod_lt x hkpos, (Nat.div_add_mod x k).symm⟩
  obtain ⟨v, s, hs, rfl⟩ : ∃ v s, s < k ∧ y = k * v + s :=
    ⟨y / k, y % k, Nat.mod_lt y hkpos, (Nat.div_add_mod y k).symm⟩
  have e3 := Nat.mul_add k u v
  have huv : u + v ≤ t := by
    by_cases hc : u + v ≤ t
    · exact hc
    · have h1 := Nat.mul_le_mul_left k (show t + 1 ≤ u + v by omega)
      have h2 := Nat.mul_add k t 1
      omega
  obtain ⟨w, rfl⟩ : ∃ w, t = u + v + w := ⟨t - (u + v), by omega⟩
  have e4 := Nat.mul_add k (u + v) w
  have hrs : r + s = k * w := by omega
  intro ⟨h1, h2⟩
  rw [colOdd_eq hk hr, colOdd_eq hk hs] at h1
  have a := decide_eq_decide.mp h1
  rcases sum_lt_two hr hs hrs with hw | hw
  · -- r = s = 0: x = k u, y = k v, t = u + v
    subst hw
    have hr0 : r = 0 := by omega
    have hs0 : s = 0 := by omega
    have hu : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · subst h0; omega
      · exact h0
    have hv : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · subst h0; omega
      · exact h0
    -- z = m + t = k (j + 1) + (t - 2), residue t - 2 < k
    have hz : m + (u + v + 0) = k * (j + 1) + (u + v - 2) := by omega
    rw [colOdd_eq hk hs, hz, colOdd_eq hk (show u + v - 2 < k by omega)] at h2
    have b := decide_eq_decide.mp h2
    omega
  · -- r + s = k: residues r and k - r take different colours
    subst hw
    omega

/-! ## Even k = 2j, j >= 2 -/

theorem sq_even {k j : Nat} (hk : k = 2 * j) : k * k = 2 * (k * j) := by
  have h1 : k * k = k * (2 * j) := by rw [← hk]
  rw [h1, Nat.mul_left_comm]

theorem mul_pred {k j : Nat} (hj : 2 ≤ j) : k * j = k * (j - 1) + k := by
  have h := Nat.mul_add k (j - 1) 1
  rw [show j - 1 + 1 = j by omega, Nat.mul_one] at h
  exact h

/-- q = k(k - 2)/2 = k(j - 1). -/
theorem q_even {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) :
    k * (k - 2) / 2 = k * (j - 1) := by
  rw [show k - 2 = 2 * (j - 1) by omega, Nat.mul_left_comm k 2,
    Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- c*(k) = k m with m = k j - 1 (= (k^2 - 2)/2). -/
theorem cstar_even {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) :
    cstar k = k * (k * j - 1) := by
  have hkk := sq_even hk
  have hpos := Nat.mul_le_mul_left k hj
  have hmod : ¬ k % 2 = 1 := by omega
  have h2 : k * k - 2 = 2 * (k * j - 1) := by omega
  unfold cstar
  simp only [hmod, ↓reduceIte]
  rw [h2, Nat.mul_left_comm k 2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- LB(c*(k), k) = q + 2k - 1 for even k >= 4. -/
theorem LB_even {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) :
    LB (cstar k) k = k * (k - 2) / 2 + 2 * k - 1 := by
  have hq := q_even hk hj
  have hkj := mul_pred (k := k) hj
  have hkk := sq_even hk
  rw [cstar_even hk hj, hq]
  obtain ⟨m, hm⟩ : ∃ m, m = k * j - 1 := ⟨_, rfl⟩
  rw [← hm]
  have e1 := Nat.mul_add k m 1
  have e2 := Nat.mul_add k m k
  have h1 : (k * m + 2 + k - 1) / k = m + 1 :=
    div_eq_of_decomp (r := 1) (by omega) (by omega)
  have h2 : (2 * (m + 1) + k * m + k - 1) / k = m + k :=
    div_eq_of_decomp (r := k - 1) (by omega) (by omega)
  unfold LB
  rw [h1, h2]
  omega

/-- Even case of the lower half, with `N` and `c*` in closed form. -/
theorem even_case {k j : Nat} (hk : k = 2 * j) (hj : 2 ≤ j) (x y z : Nat)
    (hx1 : 1 ≤ x) (hxN : x ≤ k * (k - 2) / 2 + 2 * k - 1)
    (hy1 : 1 ≤ y) (hyN : y ≤ k * (k - 2) / 2 + 2 * k - 1)
    (hzN : z ≤ k * (k - 2) / 2 + 2 * k - 1)
    (h : x + y + k * (k * j - 1) = k * z) :
    ¬ (colEven k x = colEven k y ∧ colEven k y = colEven k z) := by
  have hkpos : 0 < k := by omega
  have hq := q_even hk hj
  have hkj := mul_pred (k := k) hj
  have hkk := sq_even hk
  have hc : ∀ n, colEven k n = decide (¬ (n = k * (j - 1) + 1 ∨
      (k * (j - 1) + k ≤ n ∧ n ≤ k * (j - 1) + 2 * k - 2))) := by
    intro n
    unfold colEven
    rw [hq]
  rw [hq] at hxN hyN hzN
  rw [hc x, hc y, hc z]
  obtain ⟨m, hm⟩ : ∃ m, m = k * j - 1 := ⟨_, rfl⟩
  rw [← hm] at h
  obtain ⟨t, rfl, hxy⟩ := shift hkpos h
  have ht : t ≤ k := by omega
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; omega
    · exact h0
  intro ⟨h1, h2⟩
  have a := decide_eq_decide.mp h1
  have b := decide_eq_decide.mp h2
  by_cases htk : t = k
  · -- z = N has colour 1; x + y = k^2
    rw [htk] at hxy
    omega
  · by_cases ht2 : t ≤ k - 2
    · -- x + y <= k(k - 2) = 2q
      have h3 := Nat.mul_le_mul_left k ht2
      have h4 : k * (k - 2) = 2 * (k * (j - 1)) := by
        rw [show k - 2 = 2 * (j - 1) by omega, Nat.mul_left_comm]
      omega
    · -- t = k - 1: x + y = k(k - 1) = 2q + k
      have h3 : t = k - 1 := by omega
      have h4 := Nat.mul_add k (k - 1) 1
      rw [show k - 1 + 1 = k by omega] at h4
      rw [h3] at hxy
      omega

/-! ## The claim -/

/-- LB(c*(k), k) equals the proof's N, for every k >= 3. -/
theorem LB_cstar (k : Nat) (hk : 3 ≤ k) : LB (cstar k) k = N k := by
  unfold N
  by_cases hodd : k % 2 = 1
  · simp only [hodd, ↓reduceIte]
    exact LB_odd (by omega) (by omega)
  · simp only [hodd, ↓reduceIte]
    exact LB_even (j := k / 2) (by omega) (by omega)

/-- The proof's colouring `col k` has no monochromatic solution on
[1, LB(c*(k), k)]. -/
theorem lower_col_valid (k : Nat) (hk : 3 ≤ k) (x y z : Nat)
    (hx1 : 1 ≤ x) (hxN : x ≤ LB (cstar k) k)
    (hy1 : 1 ≤ y) (hyN : y ≤ LB (cstar k) k)
    (_hz1 : 1 ≤ z) (hzN : z ≤ LB (cstar k) k)
    (h : x + y + cstar k = k * z) :
    ¬ (col k x = col k y ∧ col k y = col k z) := by
  by_cases hodd : k % 2 = 1
  · have hkj : k = 2 * (k / 2) + 1 := by omega
    have hj : 1 ≤ k / 2 := by omega
    rw [LB_odd hkj hj] at hzN
    rw [cstar_odd hkj hj] at h
    have hc : ∀ n, col k n = colOdd k n := fun n => by
      simp only [col, hodd, ↓reduceIte]
    rw [hc x, hc y, hc z]
    exact odd_case hkj hj x y z hx1 hy1 hzN h
  · have hkj : k = 2 * (k / 2) := by omega
    have hj : 2 ≤ k / 2 := by omega
    rw [LB_even hkj hj] at hxN hyN hzN
    rw [cstar_even hkj hj] at h
    have hc : ∀ n, col k n = colEven k n := fun n => by
      simp only [col, hodd, ↓reduceIte]
    rw [hc x, hc y, hc z]
    exact even_case hkj hj x y z hx1 hxN hy1 hyN hzN h

/-- For every `k ≥ 3`, some 2-colouring of
`[1, LB(c*(k), k)]` has no monochromatic solution of `x + y + c*(k) = k z`. -/
theorem exists_good_col_cstar (k : Nat) (hk : 3 ≤ k) :
    ∃ col : Nat → Bool, ∀ x y z : Nat,
      1 ≤ x → x ≤ LB (cstar k) k →
      1 ≤ y → y ≤ LB (cstar k) k →
      1 ≤ z → z ≤ LB (cstar k) k →
      x + y + cstar k = k * z →
      ¬ (col x = col y ∧ col y = col z) :=
  ⟨col k, fun x y z hx1 hxN hy1 hyN hz1 hzN h =>
    lower_col_valid k hk x y z hx1 hxN hy1 hyN hz1 hzN h⟩

end LowerHalf

end RadoNu
