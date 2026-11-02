/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Minimization
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Conditional

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Arithmetic operations obtained by minimization

Truncated subtraction, integer square root, the two components of Cantor
unpairing, divisibility, remainder, and the Gödel beta function, each defined
by minimizing an arithmetic condition.

Each construction is accompanied by the theorem that it realizes the intended
function over the natural numbers.  Those `Computes` theorems are the input of
the standard-model bridge, which turns a computation over `ℕ` into evaluation at
standard numerals in an arbitrary model.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-- Truncated subtraction `d₀ - d₁`: the least `x` with `x + d₁ = d₀`, or
`0` when `d₀ < d₁`. -/
def codeSub {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeRfindPos
    (codeOr (codeEq (codeAdd codeHead (codeLift d₁)) (codeLift d₀))
      (codeAnd (codeLt (codeLift d₀) (codeLift d₁)) (codeEq codeHead (Code.zero _))))

/-- The integer square root of `d`: the least `x` with `x * x ≤ d < (x+1) * (x+1)`. -/
def codeSqrt {n : ℕ} (d : Code n) : Code n :=
  codeRfindPos
    (codeAnd
      (codeOr (codeLt (codeMul codeHead codeHead) (codeLift d))
        (codeEq (codeMul codeHead codeHead) (codeLift d)))
      (codeLt (codeLift d) (codeMul (codeSucc codeHead) (codeSucc codeHead))))

/-- The first component of Cantor unpairing. -/
def codeUnpair₁ {n : ℕ} (d : Code n) : Code n :=
  codeIfPos (codeLt (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d))
    (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d)

/-- The second component of Cantor unpairing. -/
def codeUnpair₂ {n : ℕ} (d : Code n) : Code n :=
  codeIfPos (codeLt (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d)) (codeSqrt d)
    (codeSub (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d))

/-- The characteristic value of `d₀ ∣ d₁`, decided by minimizing a quotient
bounded by `d₁`. -/
def codeDvd {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeBind
    (codeRfindPos
      (codeOr (codeEq (codeMul codeHead (codeLift d₀)) (codeLift d₁))
        (codeLt (codeLift d₁) codeHead)))
    (codeLe codeHead (codeLift d₁))

/-- The remainder of `d₀` on division by `d₁`. -/
def codeRem {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeRfindPos (codeDvd (codeLift d₁) (codeSub (codeLift d₀) codeHead))

/-- The Gödel beta function: the `di`-th entry of the sequence coded by `dn`. -/
def codeBeta {n : ℕ} (dn di : Code n) : Code n :=
  codeRem (codeUnpair₁ dn) (codeSucc (codeMul (codeSucc di) (codeUnpair₂ dn)))

/-!
### Standard computations over the natural numbers -/

theorem computes_codeSub {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeSub d₀ d₁) (fun v => g₀ v - g₁ v) :=
  by
  have hF :
    Computes
      (codeOr (codeEq (codeAdd codeHead (codeLift d₁)) (codeLift d₀))
        (codeAnd (codeLt (codeLift d₀) (codeLift d₁)) (codeEq codeHead (Code.zero _))))
      (fun w =>
        Nat.or (isEqNat (w.head + g₁ w.tail) (g₀ w.tail))
          (Nat.and (isLtNat (g₀ w.tail) (g₁ w.tail)) (isEqNat w.head 0))) :=
    computes_codeOr
      (computes_codeEq (computes_codeAdd computes_codeHead (computes_codeLift h₁))
        (computes_codeLift h₀))
      (computes_codeAnd (computes_codeLt (computes_codeLift h₀) (computes_codeLift h₁))
        (computes_codeEq computes_codeHead computes_zero))
  have h := eval_codeRfindPos hF
  refine eval_of_eq h ?_
  funext v
  have key :
    ∀ m : ℕ,
      (0 < Nat.or (isEqNat (m + g₁ v) (g₀ v)) (Nat.and (isLtNat (g₀ v) (g₁ v)) (isEqNat m 0))) ↔
        (m + g₁ v = g₀ v ∨ (g₀ v < g₁ v ∧ m = 0)) :=
    by
    intro m
    simp [Nat.orNat_pos_iff, Nat.and_pos_iff, isEqNat_pos_iff, isLtNat_pos_iff]
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ?_
  constructor
  · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq, key]
    omega
  · intro m hm
    rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not, key]
    omega

theorem computes_codeSqrt {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ} (hd : Computes d g) :
    Computes (codeSqrt d) (fun v => Nat.sqrt (g v)) :=
  by
  have hF :
    Computes
      (codeAnd
        (codeOr (codeLt (codeMul codeHead codeHead) (codeLift d))
          (codeEq (codeMul codeHead codeHead) (codeLift d)))
        (codeLt (codeLift d) (codeMul (codeSucc codeHead) (codeSucc codeHead))))
      (fun w =>
        Nat.and
          (Nat.or (isLtNat (w.head * w.head) (g w.tail)) (isEqNat (w.head * w.head) (g w.tail)))
          (isLtNat (g w.tail) ((w.head + 1) * (w.head + 1)))) :=
    computes_codeAnd
      (computes_codeOr
        (computes_codeLt (computes_codeMul computes_codeHead computes_codeHead)
          (computes_codeLift hd))
        (computes_codeEq (computes_codeMul computes_codeHead computes_codeHead)
          (computes_codeLift hd)))
      (computes_codeLt (computes_codeLift hd)
        (computes_codeMul (computes_codeSucc computes_codeHead)
          (computes_codeSucc computes_codeHead)))
  have h := eval_codeRfindPos hF
  refine eval_of_eq h ?_
  funext v
  have key :
    ∀ m : ℕ,
      (0 <
          Nat.and (Nat.or (isLtNat (m * m) (g v)) (isEqNat (m * m) (g v)))
            (isLtNat (g v) ((m + 1) * (m + 1)))) ↔
        (m * m ≤ g v ∧ g v < (m + 1) * (m + 1)) :=
    by
    intro m
    simp only [Nat.and_pos_iff, Nat.orNat_pos_iff, isLtNat_pos_iff, isEqNat_pos_iff]
    omega
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ?_
  constructor
  · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq, key]
    refine ⟨?_, ?_⟩
    · simpa [pow_two] using Nat.sqrt_le' (g v)
    · simpa [pow_two] using Nat.lt_succ_sqrt' (g v)
  · intro m hm
    rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not, key]
    rintro ⟨-, hlt⟩
    have : (m + 1) * (m + 1) ≤ g v := by simpa [pow_two] using Nat.le_sqrt'.mp hm
    omega

theorem computes_codeUnpair₁ {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ}
    (hd : Computes d g) : Computes (codeUnpair₁ d) (fun v => (g v).unpair.1) :=
  by
  have hs := computes_codeSqrt hd
  refine
    (computes_codeIfPos (computes_codeLt (computes_codeSub hd (computes_codeMul hs hs)) hs)
          (computes_codeSub hd (computes_codeMul hs hs)) hs).of_eq
      ?_
  intro v
  by_cases hlt : g v - (g v).sqrt * (g v).sqrt < (g v).sqrt <;> simp [Nat.unpair, isLtNat, hlt]

theorem computes_codeUnpair₂ {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ}
    (hd : Computes d g) : Computes (codeUnpair₂ d) (fun v => (g v).unpair.2) :=
  by
  have hs := computes_codeSqrt hd
  refine
    (computes_codeIfPos (computes_codeLt (computes_codeSub hd (computes_codeMul hs hs)) hs) hs
          (computes_codeSub (computes_codeSub hd (computes_codeMul hs hs)) hs)).of_eq
      ?_
  intro v
  by_cases hlt : g v - (g v).sqrt * (g v).sqrt < (g v).sqrt <;> simp [Nat.unpair, isLtNat, hlt]

theorem computes_codeDvd {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeDvd d₀ d₁) (fun v => isDvdNat (g₀ v) (g₁ v)) :=
  by
  have hF :
    Computes
      (codeOr (codeEq (codeMul codeHead (codeLift d₀)) (codeLift d₁))
        (codeLt (codeLift d₁) codeHead))
      (fun w =>
        Nat.or (isEqNat (w.head * g₀ w.tail) (g₁ w.tail)) (isLtNat (g₁ w.tail) w.head)) :=
    computes_codeOr
      (computes_codeEq (computes_codeMul computes_codeHead (computes_codeLift h₀))
        (computes_codeLift h₁))
      (computes_codeLt (computes_codeLift h₁) computes_codeHead)
  have hb :=
    eval_codeBind (eval_codeRfindPos hF)
      (computes_codeLe computes_codeHead (computes_codeLift h₁))
  refine eval_of_eq hb ?_
  funext v
  have key :
    ∀ m : ℕ,
      (0 < Nat.or (isEqNat (m * g₀ v) (g₁ v)) (isLtNat (g₁ v) m)) ↔
        (m * g₀ v = g₁ v ∨ g₁ v < m) :=
    by intro m; simp only [Nat.orNat_pos_iff, isEqNat_pos_iff, isLtNat_pos_iff]
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  by_cases hv : g₀ v ∣ g₁ v
  · obtain ⟨k, hk, hkm⟩ : ∃ k, k * g₀ v = g₁ v ∧ ∀ m, m < k → m * g₀ v ≠ g₁ v :=
      by
      obtain ⟨c, hc⟩ := hv
      have hex : ∃ k, k * g₀ v = g₁ v := ⟨c, by rw [hc, Nat.mul_comm]⟩
      exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hkle : k ≤ g₁ v := by
      rcases Nat.eq_zero_or_pos k with hz | hp
      · simp [hz]
      · rcases Nat.eq_zero_or_pos (g₀ v) with h0 | h0
        · exfalso
          have : g₁ v = 0 := by rw [← hk, h0, Nat.mul_zero]
          exact hkm 0 hp (by simp [this])
        · calc
            k = k * 1 := (Nat.mul_one k).symm
            _ ≤ k * g₀ v := (Nat.mul_le_mul_left k h0)
            _ = g₁ v := hk
    refine ⟨k, ?_, ?_⟩
    · refine Nat.mem_rfind.mpr ?_
      refine ⟨?_, ?_⟩
      · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq, key]; exact Or.inl hk
      · intro m hm
        rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not, key]
        rintro (he | hlt)
        · exact hkm m hm he
        · omega
    · simp [isDvdNat, hv, isLeNat, hkle]
  · refine ⟨g₁ v + 1, ?_, ?_⟩
    · refine Nat.mem_rfind.mpr ?_
      refine ⟨?_, ?_⟩
      · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq, key]; exact Or.inr (by omega)
      · intro m hm
        rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not, key]
        rintro (he | hlt)
        · exact hv ⟨m, by rw [← he, Nat.mul_comm]⟩
        · omega
    · simp [isDvdNat, hv, isLeNat]

theorem computes_codeRem {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeRem d₀ d₁) (fun v => g₀ v % g₁ v) :=
  by
  have hF :
    Computes (codeDvd (codeLift d₁) (codeSub (codeLift d₀) codeHead))
      (fun w => isDvdNat (g₁ w.tail) (g₀ w.tail - w.head)) :=
    computes_codeDvd (computes_codeLift h₁)
      (computes_codeSub (computes_codeLift h₀) computes_codeHead)
  have h := eval_codeRfindPos hF
  refine eval_of_eq h ?_
  funext v
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff]
  refine Nat.mem_rfind.mpr ?_
  constructor
  · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq, isDvdNat_pos_iff]
    exact Nat.dvd_sub_mod (g₀ v)
  · intro m hm
    rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not, isDvdNat_pos_iff]
    intro hdvd
    have hmlt : m < g₀ v % g₁ v := hm
    have hmod_le : g₀ v % g₁ v ≤ g₀ v := Nat.mod_le _ _
    rcases Nat.eq_zero_or_pos (g₁ v) with hz | hjpos
    · rw [hz] at hdvd
      rw [hz, Nat.mod_zero] at hmlt
      rw [Nat.zero_dvd] at hdvd
      omega
    · have hsub : g₁ v ∣ g₀ v % g₁ v - m :=
        by
        have heq : g₀ v - m - (g₀ v - g₀ v % g₁ v) = g₀ v % g₁ v - m := by omega
        rw [← heq]
        exact Nat.dvd_sub hdvd (Nat.dvd_sub_mod (g₀ v))
      have hpos : 0 < g₀ v % g₁ v - m := by omega
      have hmodlt : g₀ v % g₁ v < g₁ v := Nat.mod_lt _ hjpos
      exact absurd (Nat.le_of_dvd hpos hsub) (by omega)

theorem eval_codeBeta {n : ℕ} {dn di : Code n} {gn gi : List.Vector ℕ n → ℕ}
    (hn : Computes dn gn) (hi : Computes di gi) :
    Computes (codeBeta dn di) (fun v => Nat.beta (gn v) (gi v)) :=
  (computes_codeRem (computes_codeUnpair₁ hn)
        (computes_codeSucc
          (computes_codeMul (computes_codeSucc hi) (computes_codeUnpair₂ hn)))).of_eq
    (fun v => by simp [Nat.beta])

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
