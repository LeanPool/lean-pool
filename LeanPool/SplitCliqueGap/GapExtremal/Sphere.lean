/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.SCap
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Integer spheres are S-caps; the exponent of the gap is 2 (ledger §17, L17.2–L17.3, Theorem 17.0)

* `sphere_rel`: three distinct integer points with the same squared norm satisfy no relation
  `α (X - Z) + β (Y - Z) = 0` with `α ≠ 0` (strict convexity of the squared norm).
* `isSCap_seed`: a sphere `{x ∈ {0..K}^N : Σ x_i² = r}`, embedded in `F_p^N` with `10 K < p`, is an
S-cap for the
  colours `0, …, 5` (an `F_p` colour relation lifts to `ℤ`).
* `exists_large_sphere`: some sphere has `≥ (K+1)^N / (N R + 1)` points (`K² ≤ R`).
* **`exponent_two`**: `gap ≥ c · n^{2 - ε}` on split graphs with at most `n` vertices.
-/

@[expose] public section

namespace GapExtremal

open Finset

/-! ### Strict convexity over `ℤ` -/

/-- Three distinct integer points on a sphere satisfy no relation `α (X - Z) + β (Y - Z) = 0`, `α ≠
0`. -/
theorem sphere_rel {N : ℕ} (X Y Z : Fin N → ℤ) {α β : ℤ} (hα : α ≠ 0) (hXZ : X ≠ Z) (hXY : X ≠ Y)
    (hrel : ∀ i, α * (X i - Z i) + β * (Y i - Z i) = 0)
    (hX : ∑ i, X i ^ 2 = ∑ i, Z i ^ 2) (hY : ∑ i, Y i ^ 2 = ∑ i, Z i ^ 2) : False := by
  set A := ∑ i, (X i - Z i) ^ 2
  set B := ∑ i, (Y i - Z i) ^ 2
  set Pp := ∑ i, (X i - Z i) * Z i
  set Q := ∑ i, (Y i - Z i) * Z i
  have hb : ∀ i, β * (Y i - Z i) = -(α * (X i - Z i)) := fun i => by linear_combination hrel i
  have e1 : β * Q = -(α * Pp) := by
    simp only [Q, Pp, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, hb i]; ring
  have e2 : A + 2 * Pp = 0 := by
    have : A + 2 * Pp = ∑ i, X i ^ 2 - ∑ i, Z i ^ 2 := by
      simp only [A, Pp, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, hX, sub_self]
  have e3 : B + 2 * Q = 0 := by
    have : B + 2 * Q = ∑ i, Y i ^ 2 - ∑ i, Z i ^ 2 := by
      simp only [B, Q, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, hY, sub_self]
  have e4 : β ^ 2 * B = α ^ 2 * A := by
    change β ^ 2 * ∑ i, (Y i - Z i) ^ 2 = α ^ 2 * ∑ i, (X i - Z i) ^ 2
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (β * (Y i - Z i)) ^ 2 = (-(α * (X i - Z i))) ^ 2 := by rw [hb i]
    linear_combination this
  have hA : 0 < A := by
    obtain ⟨i, hi⟩ : ∃ i, X i ≠ Z i := by
      by_contra h; push Not at h; exact hXZ (funext h)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => sq_nonneg (X j - Z j))
      (Finset.mem_univ i))
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hi)))
  have key : α * (α + β) * A = 0 := by
    linear_combination (-1 : ℤ) * e4 + β ^ 2 * e3 - 2 * β * e1 + α * β * e2
  have hab : α + β = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hα
      · exact h'
    · exact absurd h hA.ne'
  apply hXY
  funext i
  have := hrel i
  have hb' : β = -α := by linear_combination hab
  rw [hb'] at this
  have : α * (X i - Y i) = 0 := by linear_combination this
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hα
  · exact sub_eq_zero.mp h

/-! ### Spheres in a box, embedded in `F_p^N` -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- Pin the additive group of `ZMod p` to the ring structure (avoids an exotic instance path). -/
instance (priority := 10000) addCommGroupZModP : AddCommGroup (ZMod p) := Ring.toAddCommGroup

/-- The colours `0, …, 5` in `ZMod p` (`p > 5`). -/
def colσ (hp5 : 5 < p) : Fin 6 ↪ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  inj' := by
    intro i j h
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext this

/-- Box points. -/
def emb (K N : ℕ) (x : Fin N → Fin (K + 1)) : Fin N → ZMod p := fun i => ((x i : ℕ) : ZMod p)

theorem emb_injective {K N : ℕ} (hK : K < p) : Function.Injective (emb (p := p) K N) := by
  intro x y h
  funext i
  have := congrArg ZMod.val (congrFun h i)
  simp only [emb, ZMod.val_natCast] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact Fin.ext this

/-- The sphere of squared radius `r` in the box `{0..K}^N`. -/
def sphere (K N r : ℕ) : Finset (Fin N → Fin (K + 1)) :=
  univ.filter fun x => ∑ i, ((x i : ℕ)) ^ 2 = r

/-- The seed: the sphere, embedded in `F_p^N`. -/
def seed (p K N r : ℕ) [Fact p.Prime] : Finset (Fin N → ZMod p) := (sphere K N r).image (emb K N)

theorem card_sphereSeed {K N r : ℕ} (hK : K < p) : (seed p K N r).card = (sphere K N r).card :=
  Finset.card_image_of_injective _ (emb_injective hK)

/-- An integer of absolute value `< p` divisible by `p` is `0`. -/
theorem int_eq_zero_of_cast {E : ℤ} (hE : (E : ZMod p) = 0) (hb : |E| < p) : E = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hE
  obtain ⟨k, hk⟩ := hE
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  rcases lt_trichotomy k 0 with h | h | h
  · exfalso
    have : (p : ℤ) ≤ |E| := by
      rw [hk, abs_mul, abs_of_pos hp0]
      have : 1 ≤ |k| := Int.one_le_abs h.ne
      nlinarith
    linarith
  · simp [hk, h]
  · exfalso
    have : (p : ℤ) ≤ |E| := by
      rw [hk, abs_mul, abs_of_pos hp0]
      have : 1 ≤ |k| := Int.one_le_abs h.ne'
      nlinarith
    linarith

/-- `|(m₂ - m₁)(x - z) + (m₃ - m₂)(y - z)| ≤ 10 K` for colours `≤ 5` and coordinates `≤ K`. -/
theorem lift_bound {K : ℕ} {m₁ m₂ m₃ x y z : ℕ} (h1 : m₁ < 6) (h2 : m₂ < 6) (h3 : m₃ < 6)
    (hx : x ≤ K) (hy : y ≤ K) (hz : z ≤ K) :
    |((m₂ : ℤ) - m₁) * ((x : ℤ) - z) + ((m₃ : ℤ) - m₂) * ((y : ℤ) - z)| ≤ 10 * K := by
  have a1 : |((m₂ : ℤ) - m₁)| ≤ 5 := by rw [abs_le]; constructor <;> omega
  have a2 : |((m₃ : ℤ) - m₂)| ≤ 5 := by rw [abs_le]; constructor <;> omega
  have b1 : |((x : ℤ) - z)| ≤ K := by rw [abs_le]; constructor <;> omega
  have b2 : |((y : ℤ) - z)| ≤ K := by rw [abs_le]; constructor <;> omega
  calc _ ≤ |((m₂ : ℤ) - m₁) * ((x : ℤ) - z)| + |((m₃ : ℤ) - m₂) * ((y : ℤ) - z)| := abs_add_le _ _
    _ = |((m₂ : ℤ) - m₁)| * |((x : ℤ) - z)| + |((m₃ : ℤ) - m₂)| * |((y : ℤ) - z)| := by
      rw [abs_mul, abs_mul]
    _ ≤ 5 * K + 5 * K := by
      gcongr
    _ = 10 * K := by ring

/-- **L17.2 + L17.3.** The embedded sphere is an S-cap for the colours `0, …, 5` when `10 K < p`. -/
theorem isSCap_seed {K N r : ℕ} (hK : 10 * K < p) (hp5 : 5 < p) :
    IsSCap (Set.range (colσ (p := p) hp5)) (seed p K N r : Set (Fin N → ZMod p)) := by
  intro a ha b hb c hc hab hac hbc s₁ h1 s₂ h2 s₃ h3 h12 hrel
  simp only [seed, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb hc
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  obtain ⟨z, hz, rfl⟩ := hc
  obtain ⟨i₁, rfl⟩ := h1
  obtain ⟨i₂, rfl⟩ := h2
  obtain ⟨i₃, rfl⟩ := h3
  simp only [sphere, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  set m₁ := (i₁ : ℕ)
  set m₂ := (i₂ : ℕ)
  set m₃ := (i₃ : ℕ)
  have hm12 : (m₁ : ℤ) ≠ m₂ := by
    intro h
    apply h12
    have h' : m₁ = m₂ := by exact_mod_cast h
    change ((m₁ : ℕ) : ZMod p) = ((m₂ : ℕ) : ZMod p)
    rw [h']
  set X : Fin N → ℤ := fun i => ((x i : ℕ) : ℤ)
  set Y : Fin N → ℤ := fun i => ((y i : ℕ) : ℤ)
  set Z : Fin N → ℤ := fun i => ((z i : ℕ) : ℤ)
  have hcoord : ∀ i, ((m₂ : ℤ) - m₁) * (X i - Z i) + ((m₃ : ℤ) - m₂) * (Y i - Z i) = 0 := by
    intro i
    apply int_eq_zero_of_cast (p := p)
    · have := congrFun hrel i
      simp only [colσ, Function.Embedding.coeFn_mk, emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at this
      push_cast [X, Y, Z]
      linear_combination this
    · have := lift_bound (K := K) (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) i₁.isLt i₂.isLt i₃.isLt
        (Nat.lt_succ_iff.mp (x i).isLt) (Nat.lt_succ_iff.mp (y i).isLt) (Nat.lt_succ_iff.mp (z
          i).isLt)
      have hK' : (10 * K : ℤ) < p := by exact_mod_cast hK
      exact lt_of_le_of_lt this hK'
  have hXr : ∑ i, X i ^ 2 = r := by simp only [X]; exact_mod_cast hx
  have hYr : ∑ i, Y i ^ 2 = r := by simp only [Y]; exact_mod_cast hy
  have hZr : ∑ i, Z i ^ 2 = r := by simp only [Z]; exact_mod_cast hz
  have hinj : ∀ u v : Fin N → Fin (K + 1), (fun i => ((u i : ℕ) : ℤ)) = (fun i => ((v i : ℕ) : ℤ))
    → u = v := by
    intro u v h; funext i
    have := congrFun h i
    simp only [Nat.cast_inj] at this
    exact Fin.ext this
  refine sphere_rel X Y Z (sub_ne_zero.mpr (Ne.symm hm12)) (fun h => hac ?_) (fun h =>
    hab ?_) hcoord
    (hXr.trans hZr.symm) (hYr.trans hZr.symm)
  · rw [hinj x z h]
  · rw [hinj x y h]

/-- **Pigeonhole.** Some sphere is large. -/
theorem exists_large_sphere (K N : ℕ) {R : ℕ} (hR : K ^ 2 ≤ R) :
    ∃ r, (K + 1) ^ N ≤ (N * R + 1) * (sphere K N r).card := by
  classical
  have hmaps : ∀ x ∈ (univ : Finset (Fin N → Fin (K + 1))), (∑ i, ((x i : ℕ)) ^ 2) ∈ range (N * R
    + 1) := by
    intro x _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc ∑ i, ((x i : ℕ)) ^ 2 ≤ ∑ _i : Fin N, R := Finset.sum_le_sum fun i _ =>
          le_trans (Nat.pow_le_pow_left (Nat.lt_succ_iff.mp (x i).isLt) 2) hR
      _ = N * R := by simp
  have hcard : (univ : Finset (Fin N → Fin (K + 1))).card =
      ∑ r ∈ range (N * R + 1), (sphere K N r).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    rfl
  obtain ⟨r, -, h⟩ := Finset.exists_le_of_sum_le (s := range (N * R + 1)) (by simp)
    (f := fun _ => (K + 1) ^ N) (g := fun r => (N * R + 1) * (sphere K N r).card) (by
      rw [← Finset.mul_sum, ← hcard, Finset.sum_const, Finset.card_range, smul_eq_mul,
        Finset.card_univ,
        Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fin])
  exact ⟨r, h⟩

end GapExtremal
