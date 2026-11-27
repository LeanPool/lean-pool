/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.CommRing
public import LeanPool.CatalyticRegisters.PrimeFieldTools

/-!
# Theorem T1e: Sharpness of the Prime-Field Hypothesis over `𝔽_4`

Theorem `T1` (`Catalytic.DigitSumDichotomy`) proves that over every **prime field** `𝔽_p`
and for each access budget `t ≥ 1`, `f ∈ RP^{pass}_{𝔽_p}(2, t)` exactly when every monomial
degree `d ≥ 2` in `f` satisfies `s_p(d) ≤ min (p - 1) (t - 1)`. Over `𝔽_2`, `x^3` and `x^5`
are impossible as formal polynomial outputs at any budget.

This module constructs the finite extension field `𝔽_4 = 𝔽_2[ω] / (ω^2 + ω + 1)` as a
concrete four-element `Char2CRing`. It uses the passive-output instruction set of
Vinciguerra's Definition 2.2 with formal polynomial identities in `𝔽_4[O, R, x]`.
**Theorem T1e (Extension-Field Separation)** gives:
  1. `x^5 ∈ RP^{pass}_{𝔽_4}(2, 3)` AND `x^5 ∉ RP^{pass}_{𝔽_4}(2, 2)` (exact `t_min = 3`, via `ω^2 u^5 + ω (u + x)^5 + (u + ω x)^5 = x^5`),
  2. `x^3 ∈ RP^{pass}_{𝔽_4}(2, 4)` AND `x^3 ∉ RP^{pass}_{𝔽_4}(2, 3)` (exact `t_min = 4`, via `u^3 + (u + x)^3 + (u + ω x)^3 + (u + ω^2 x)^3 = x^3`),
  3. `∀ t : Nat, x^7 ∉ RP^{pass}_{𝔽_4}(2, t)` (because `α^7 = α` for every `α ∈ 𝔽_4`, so any clean
     program necessarily has `[x^7] ΔO = [R^6 x] ΔO = 0`).

The prime-field restriction in Theorem `T1` is sharp. The exclusion of `x^7` over `𝔽_4`
is about formal polynomials. As a function on `𝔽_4`, `x^7` agrees with `x`.
-/

namespace Catalytic

@[expose] public section

/-! ## 1. The Finite Extension Field `𝔽_4 = 𝔽_2[ω] / (ω^2 + ω + 1)` -/

/-- Elements of `𝔽_4`: `0`, `1`, `ω`, `ω^2 = ω + 1`. -/
inductive GF4 where
  | z   : GF4
  | one : GF4
  | w   : GF4
  | w2  : GF4
  deriving DecidableEq, Repr

/-- Add field elements in the basis consisting of one and a root of X² + X + 1. -/
def GF4.add : GF4 → GF4 → GF4
  | .z,   b    => b
  | a,    .z   => a
  | .one, .one => .z
  | .one, .w   => .w2
  | .one, .w2  => .w
  | .w,   .one => .w2
  | .w,   .w   => .z
  | .w,   .w2  => .one
  | .w2,  .one => .w
  | .w2,  .w   => .one
  | .w2,  .w2  => .z

/-- Multiply field elements modulo X² + X + 1 over the two-element field. -/
def GF4.mul : GF4 → GF4 → GF4
  | .z,   _    => .z
  | _,    .z   => .z
  | .one, b    => b
  | a,    .one => a
  | .w,   .w   => .w2
  | .w,   .w2  => .one
  | .w2,  .w   => .one
  | .w2,  .w2  => .w

/-- Raise an element of the four-element field to a natural power. -/
def GF4.pow : GF4 → Nat → GF4
  | _, 0     => .one
  | a, n + 1 => GF4.mul a (GF4.pow a n)

instance : CRing GF4 where
  zero := .z
  one  := .one
  add  := GF4.add
  neg  := fun a => a
  mul  := GF4.mul
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm  := by intro a b; cases a <;> cases b <;> rfl
  zero_add  := by intro a; cases a <;> rfl
  add_neg   := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm  := by intro a b; cases a <;> cases b <;> rfl
  one_mul   := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

instance : Char2CRing GF4 where
  add_self := by intro a; cases a <;> rfl

theorem GF4.one_ne_zero : (GF4.one : GF4) ≠ GF4.z := by
  intro h; cases h

theorem GF4.pow_zero (a : GF4) : GF4.pow a 0 = .one := rfl

theorem GF4.z_pow_succ (n : Nat) : GF4.pow .z (n + 1) = .z := rfl

theorem GF4.pow7_eq_self (a : GF4) : GF4.pow a 7 = a := by
  cases a <;> rfl

/-! ## 2. Formal 2-Register Passive-Output Model over `𝔽_4[O, R, x]` -/

/--
Passive-output 2-register instruction over `𝔽_4` from Vinciguerra's Definition 2.2
(identical instruction set to `Pass2Instr` in `Catalytic.DigitSumDichotomy`):
  * `addOut poly`:      `O ← O + ∑_k poly[k] * R^k`  (0 input accesses)
  * `addWorkConst c`:   `R ← R + c`                  (0 input accesses)
  * `addInputOut lam`:  `O ← O + lam * x`            (1 input access)
  * `addInputWork lam`: `R ← R + lam * x`            (1 input access)
-/
inductive Pass2GF4Instr where
  | addOut (poly : List GF4) : Pass2GF4Instr
  | addWorkConst (c : GF4) : Pass2GF4Instr
  | addInputOut (lam : GF4) : Pass2GF4Instr
  | addInputWork (lam : GF4) : Pass2GF4Instr
  deriving DecidableEq, Repr

/-- Count total input accesses in a 2-register passive program over `𝔽_4`. -/
def Pass2GF4Prog.accesses : List Pass2GF4Instr → Nat
  | [] => 0
  | .addOut _ :: rest => Pass2GF4Prog.accesses rest
  | .addWorkConst _ :: rest => Pass2GF4Prog.accesses rest
  | .addInputOut _ :: rest => 1 + Pass2GF4Prog.accesses rest
  | .addInputWork _ :: rest => 1 + Pass2GF4Prog.accesses rest

/-- Sum of `f 0 + f 1 + ... + f (n - 1)` in `𝔽_4`. -/
def sumGF4 : Nat → (Nat → GF4) → GF4
  | 0, _     => .z
  | n + 1, f => GF4.add (sumGF4 n f) (f n)

/-- Characteristic-2 binomial scalar in `𝔽_4`: `1` if `C(n, k)` is odd, `0` if even. -/
def binomGF4 (n k : Nat) : GF4 :=
  if choose n k % 2 = 1 then .one else .z

/--
Exact coefficient `[R^dR x^dx] (∑_k poly[k] * (R + b + a * x)^k)` in `𝔽_4[R, x]`.
By the trinomial expansion `(R + a*x + b)^k = ∑_{d=0}^k C(k, d) b^{k-d} (R + a*x)^d`,
setting `d = dR + dx`, the exact `𝔽_4`-coefficient of `R^dR x^dx` is
`(∑_k poly[k] * C(k, d) * b^{k - d}) * (C(d, dx) * a^{dx})`.
-/
def polyAtShiftCoeffGF4 (poly : List GF4) (b a : GF4) (dR dx : Nat) : GF4 :=
  let d := dR + dx
  let outer :=
    sumGF4 poly.length (fun k =>
      GF4.mul (poly.getD k .z) (GF4.mul (binomGF4 k d) (GF4.pow b (k - d))))
  GF4.mul outer (GF4.mul (binomGF4 d dx) (GF4.pow a dx))

/-- Formal symbolic state of a 2-register passive program in `𝔽_4[O, R, x]`. -/
structure State2GF4 where
  /-- Constant part of the affine expression stored in the work register. -/
  b : GF4
  /-- Input coefficient of the affine expression stored in the work register. -/
  a : GF4
  /-- Coefficients of the output increment over the four-element field. -/
  coeff : Nat → Nat → GF4

/-- Execute one `Pass2GF4Instr` on the formal polynomial state in `𝔽_4[O, R, x]`. -/
def Pass2GF4Instr.exec (st : State2GF4) : Pass2GF4Instr → State2GF4
  | .addOut poly =>
    { st with coeff := fun dR dx => GF4.add (st.coeff dR dx) (polyAtShiftCoeffGF4 poly st.b st.a dR dx) }
  | .addWorkConst c =>
    { st with b := GF4.add st.b c }
  | .addInputOut lam =>
    { st with coeff := fun dR dx => GF4.add (st.coeff dR dx) (if dR = 0 ∧ dx = 1 then lam else .z) }
  | .addInputWork lam =>
    { st with a := GF4.add st.a lam }

/-- Execute a `Pass2GF4Prog` from a given state. -/
def Pass2GF4Prog.execFrom : List Pass2GF4Instr → State2GF4 → State2GF4
  | [], st => st
  | i :: rest, st => Pass2GF4Prog.execFrom rest (i.exec st)

/-- Execute a `Pass2GF4Prog` from the clean initial state `R = R + 0 + 0*x`, `ΔO = 0`. -/
def Pass2GF4Prog.exec (prog : List Pass2GF4Instr) : State2GF4 :=
  Pass2GF4Prog.execFrom prog ⟨.z, .z, fun _ _ => .z⟩

/-- Clean formal-polynomial computation of `f(x) ∈ 𝔽_4[x]` in `𝔽_4[O, R, x]`. -/
def CleanlyComputes2GF4 (prog : List Pass2GF4Instr) (f : List GF4) : Prop :=
  let st := Pass2GF4Prog.exec prog
  st.b = .z ∧ st.a = .z ∧
  ∀ dR dx : Nat, st.coeff dR dx = if dR = 0 then f.getD dx .z else .z

/-- Membership `f ∈ RP^{pass}_{𝔽_4}(2, t)`. -/
def InRPPass2GF4 (t : Nat) (f : List GF4) : Prop :=
  ∃ prog : List Pass2GF4Instr, Pass2GF4Prog.accesses prog ≤ t ∧ CleanlyComputes2GF4 prog f

/-- Monic monomial `x^d ∈ 𝔽_4[x]`. -/
def monomialGF4 (d : Nat) : List GF4 :=
  List.replicate d .z ++ [.one]

private theorem monomialGF4_getD (d k : Nat) :
    (monomialGF4 d).getD k .z = if k = d then .one else .z := by
  simp only [monomialGF4]
  by_cases hlt : k < d
  · have hne : k ≠ d := by omega
    simp [List.getD, List.getElem?_append_left, hlt, hne]
  · by_cases heq : k = d
    · subst heq
      simp [List.getD]
    · have hgt : d < k := by omega
      have hne : k ≠ d := by omega
      have hge : d ≤ k := by omega
      simp [List.getD, List.getElem?_append_right, hge, hne, Nat.sub_ne_zero_of_lt hgt]

/-! ## 3. Explicit 3-Access Program for `x^5` and 4-Access Program for `x^3` over `𝔽_4` -/

/--
3-access program computing `x^5` cleanly over `𝔽_4`:
  `ω^2 * u^5 + ω * (u + x)^5 + (u + ω * x)^5 = x^5` in `𝔽_4[u, x]`.
Shift trajectory: `0 → 1 → ω → 0` (3 input accesses).
-/
def progGF4Power5 : List Pass2GF4Instr :=
  [ .addOut [.z, .z, .z, .z, .z, .w2],
    .addInputWork .one,
    .addOut [.z, .z, .z, .z, .z, .w],
    .addInputWork .w2,
    .addOut [.z, .z, .z, .z, .z, .one],
    .addInputWork .w ]

/--
4-access program computing `x^3` cleanly over `𝔽_4`:
  `u^3 + (u + x)^3 + (u + ω * x)^3 + (u + ω^2 * x)^3 = x^3` in `𝔽_4[u, x]`.
Shift trajectory: `0 → 1 → ω → ω^2 → 0` (4 input accesses).
-/
def progGF4Power3 : List Pass2GF4Instr :=
  [ .addOut [.z, .z, .z, .one],
    .addInputWork .one,
    .addOut [.z, .z, .z, .one],
    .addInputWork .w2,
    .addOut [.z, .z, .z, .one],
    .addInputWork .one,
    .addOut [.z, .z, .z, .one],
    .addInputWork .w2 ]

private theorem polyAtShiftCoeffGF4_mono5_ne (c a : GF4) (dR dx : Nat) (h : dR + dx ≠ 5) :
    polyAtShiftCoeffGF4 [.z, .z, .z, .z, .z, c] .z a dR dx = .z := by
  simp only [polyAtShiftCoeffGF4, List.length, sumGF4, List.getD]
  have h0 : GF4.mul .z (GF4.mul (binomGF4 0 (dR + dx)) (GF4.pow .z (0 - (dR + dx)))) = .z := rfl
  have h1 : GF4.mul .z (GF4.mul (binomGF4 1 (dR + dx)) (GF4.pow .z (1 - (dR + dx)))) = .z := rfl
  have h2 : GF4.mul .z (GF4.mul (binomGF4 2 (dR + dx)) (GF4.pow .z (2 - (dR + dx)))) = .z := rfl
  have h3 : GF4.mul .z (GF4.mul (binomGF4 3 (dR + dx)) (GF4.pow .z (3 - (dR + dx)))) = .z := rfl
  have h4 : GF4.mul .z (GF4.mul (binomGF4 4 (dR + dx)) (GF4.pow .z (4 - (dR + dx)))) = .z := rfl
  have h5 : GF4.mul (binomGF4 5 (dR + dx)) (GF4.pow .z (5 - (dR + dx))) = .z := by
    by_cases hlt : dR + dx < 5
    · obtain ⟨k, hk⟩ : ∃ k, 5 - (dR + dx) = k + 1 := ⟨5 - (dR + dx) - 1, by omega⟩
      rw [hk, GF4.z_pow_succ]
      cases binomGF4 5 (dR + dx) <;> rfl
    · have hgt : 5 < dR + dx := by omega
      have hch : choose 5 (dR + dx) = 0 := choose_eq_zero_of_lt hgt
      simp [binomGF4, hch, GF4.mul]
  change GF4.mul
    (GF4.add (GF4.add (GF4.add (GF4.add (GF4.add (GF4.add .z
      (GF4.mul .z (GF4.mul (binomGF4 0 (dR + dx)) (GF4.pow .z (0 - (dR + dx))))))
      (GF4.mul .z (GF4.mul (binomGF4 1 (dR + dx)) (GF4.pow .z (1 - (dR + dx))))))
      (GF4.mul .z (GF4.mul (binomGF4 2 (dR + dx)) (GF4.pow .z (2 - (dR + dx))))))
      (GF4.mul .z (GF4.mul (binomGF4 3 (dR + dx)) (GF4.pow .z (3 - (dR + dx))))))
      (GF4.mul .z (GF4.mul (binomGF4 4 (dR + dx)) (GF4.pow .z (4 - (dR + dx))))))
      (GF4.mul c (GF4.mul (binomGF4 5 (dR + dx)) (GF4.pow .z (5 - (dR + dx))))))
    (GF4.mul (binomGF4 (dR + dx) dx) (GF4.pow a dx)) = .z
  rw [h0, h1, h2, h3, h4, h5]
  cases c <;> rfl

private theorem polyAtShiftCoeffGF4_mono3_ne (a : GF4) (dR dx : Nat) (h : dR + dx ≠ 3) :
    polyAtShiftCoeffGF4 [.z, .z, .z, .one] .z a dR dx = .z := by
  have h0 : GF4.mul .z (GF4.mul (binomGF4 0 (dR + dx)) (GF4.pow .z (0 - (dR + dx)))) = .z := rfl
  have h1 : GF4.mul .z (GF4.mul (binomGF4 1 (dR + dx)) (GF4.pow .z (1 - (dR + dx)))) = .z := rfl
  have h2 : GF4.mul .z (GF4.mul (binomGF4 2 (dR + dx)) (GF4.pow .z (2 - (dR + dx)))) = .z := rfl
  have h3 : GF4.mul (binomGF4 3 (dR + dx)) (GF4.pow .z (3 - (dR + dx))) = .z := by
    by_cases hlt : dR + dx < 3
    · obtain ⟨k, hk⟩ : ∃ k, 3 - (dR + dx) = k + 1 := ⟨3 - (dR + dx) - 1, by omega⟩
      rw [hk, GF4.z_pow_succ]
      cases binomGF4 3 (dR + dx) <;> rfl
    · have hgt : 3 < dR + dx := by omega
      have hch : choose 3 (dR + dx) = 0 := choose_eq_zero_of_lt hgt
      simp [binomGF4, hch, GF4.mul]
  change GF4.mul
    (GF4.add (GF4.add (GF4.add (GF4.add .z
      (GF4.mul .z (GF4.mul (binomGF4 0 (dR + dx)) (GF4.pow .z (0 - (dR + dx))))))
      (GF4.mul .z (GF4.mul (binomGF4 1 (dR + dx)) (GF4.pow .z (1 - (dR + dx))))))
      (GF4.mul .z (GF4.mul (binomGF4 2 (dR + dx)) (GF4.pow .z (2 - (dR + dx))))))
      (GF4.mul .one (GF4.mul (binomGF4 3 (dR + dx)) (GF4.pow .z (3 - (dR + dx))))))
    (GF4.mul (binomGF4 (dR + dx) dx) (GF4.pow a dx)) = .z
  rw [h0, h1, h2, h3]
  rfl

/-- **`x^5 ∈ RP^{pass}_{𝔽_4}(2, 3)`:** beats `𝔽_2` saturation (where `x^5` is impossible for all `t`). -/
theorem gf4_x5_in_3_accesses : InRPPass2GF4 3 (monomialGF4 5) := by
  refine ⟨progGF4Power5, Nat.le_refl 3, rfl, rfl, ?_⟩
  intro dR dx
  rw [monomialGF4_getD]
  by_cases hsum : dR + dx = 5
  · have hcases :
        (dR = 5 ∧ dx = 0) ∨ (dR = 4 ∧ dx = 1) ∨ (dR = 3 ∧ dx = 2) ∨
        (dR = 2 ∧ dx = 3) ∨ (dR = 1 ∧ dx = 4) ∨ (dR = 0 ∧ dx = 5) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · have hrhs : (if dR = 0 then (if dx = 5 then GF4.one else GF4.z) else GF4.z) = .z := by
      split
      · rename_i h0
        have h5 : dx ≠ 5 := by omega
        simp [h5]
      · rfl
    rw [hrhs]
    change GF4.add (GF4.add (GF4.add .z
      (polyAtShiftCoeffGF4 [.z, .z, .z, .z, .z, .w2] .z .z dR dx))
      (polyAtShiftCoeffGF4 [.z, .z, .z, .z, .z, .w] .z .one dR dx))
      (polyAtShiftCoeffGF4 [.z, .z, .z, .z, .z, .one] .z .w dR dx) = .z
    rw [polyAtShiftCoeffGF4_mono5_ne .w2 .z dR dx hsum,
        polyAtShiftCoeffGF4_mono5_ne .w .one dR dx hsum,
        polyAtShiftCoeffGF4_mono5_ne .one .w dR dx hsum]
    rfl

/-- **`x^3 ∈ RP^{pass}_{𝔽_4}(2, 4)`:** beats `𝔽_2` saturation (where `x^3` is impossible for all `t`). -/
theorem gf4_x3_in_4_accesses : InRPPass2GF4 4 (monomialGF4 3) := by
  refine ⟨progGF4Power3, Nat.le_refl 4, rfl, rfl, ?_⟩
  intro dR dx
  rw [monomialGF4_getD]
  by_cases hsum : dR + dx = 3
  · have hcases :
        (dR = 3 ∧ dx = 0) ∨ (dR = 2 ∧ dx = 1) ∨ (dR = 1 ∧ dx = 2) ∨ (dR = 0 ∧ dx = 3) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · have hrhs : (if dR = 0 then (if dx = 3 then GF4.one else GF4.z) else GF4.z) = .z := by
      split
      · rename_i h0
        have h3 : dx ≠ 3 := by omega
        simp [h3]
      · rfl
    rw [hrhs]
    change GF4.add (GF4.add (GF4.add (GF4.add .z
      (polyAtShiftCoeffGF4 [.z, .z, .z, .one] .z .z dR dx))
      (polyAtShiftCoeffGF4 [.z, .z, .z, .one] .z .one dR dx))
      (polyAtShiftCoeffGF4 [.z, .z, .z, .one] .z .w dR dx))
      (polyAtShiftCoeffGF4 [.z, .z, .z, .one] .z .w2 dR dx) = .z
    rw [polyAtShiftCoeffGF4_mono3_ne .z dR dx hsum,
        polyAtShiftCoeffGF4_mono3_ne .one dR dx hsum,
        polyAtShiftCoeffGF4_mono3_ne .w dR dx hsum,
        polyAtShiftCoeffGF4_mono3_ne .w2 dR dx hsum]
    rfl

/-! ## 4. Universal Impossibility of `x^7` over `𝔽_4` for ALL `t` -/

/--
Because `C(7, 7) = 1 ≡ 1 (mod 2)`, `C(7, 1) = 7 ≡ 1 (mod 2)`, and `a^7 = a` for EVERY `a ∈ 𝔽_4`,
every single `addOut` step contributes identically to `[x^7] ΔO` and `[R^6 x] ΔO`.
-/
private theorem polyAtShiftCoeffGF4_07_eq_61 (poly : List GF4) (b a : GF4) :
    polyAtShiftCoeffGF4 poly b a 0 7 = polyAtShiftCoeffGF4 poly b a 6 1 := by
  simp only [polyAtShiftCoeffGF4]
  have hd : (0 : Nat) + 7 = 6 + 1 := rfl
  have hb7 : binomGF4 7 7 = .one := by decide
  have hb1 : binomGF4 7 1 = .one := by decide
  have hp7 : GF4.pow a 7 = GF4.pow a 1 := by cases a <;> rfl
  change GF4.mul _ (GF4.mul (binomGF4 7 7) (GF4.pow a 7)) =
         GF4.mul _ (GF4.mul (binomGF4 7 1) (GF4.pow a 1))
  rw [hb7, hb1, hp7]

private theorem execFrom_preserves_07_eq_61 (prog : List Pass2GF4Instr) (st : State2GF4)
    (h : st.coeff 0 7 = st.coeff 6 1) :
    (Pass2GF4Prog.execFrom prog st).coeff 0 7 = (Pass2GF4Prog.execFrom prog st).coeff 6 1 := by
  induction prog generalizing st with
  | nil => exact h
  | cons instr rest ih =>
    apply ih
    cases instr with
    | addOut poly =>
      simp only [Pass2GF4Instr.exec, h, polyAtShiftCoeffGF4_07_eq_61]
    | addWorkConst c =>
      exact h
    | addInputOut lam =>
      change GF4.add (st.coeff 0 7) (if (0 : Nat) = 0 ∧ (7 : Nat) = 1 then lam else .z) =
             GF4.add (st.coeff 6 1) (if (6 : Nat) = 0 ∧ (1 : Nat) = 1 then lam else .z)
      have h1 : (if (0 : Nat) = 0 ∧ (7 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      have h2 : (if (6 : Nat) = 0 ∧ (1 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      rw [h, h1, h2]
    | addInputWork lam =>
      exact h

/-- **`∀ t, x^7 ∉ RP^{pass}_{𝔽_4}(2, t)`:** unconditional impossibility for arbitrary access count `t`. -/
theorem gf4_x7_impossible_all_t (t : Nat) : ¬ InRPPass2GF4 t (monomialGF4 7) := by
  rintro ⟨prog, _, _, _, hclean⟩
  have hinv := execFrom_preserves_07_eq_61 prog ⟨.z, .z, fun _ _ => .z⟩ rfl
  have h07 := hclean 0 7
  have h61 := hclean 6 1
  rw [monomialGF4_getD] at h07
  simp only [↓reduceIte] at h07
  have h60 : (6 : Nat) ≠ 0 := by decide
  simp only [h60, ↓reduceIte] at h61
  have hcontra : GF4.one = GF4.z := by
    calc
      GF4.one = (Pass2GF4Prog.exec prog).coeff 0 7 := h07.symm
      _       = (Pass2GF4Prog.exec prog).coeff 6 1 := hinv
      _       = GF4.z := h61
  exact GF4.one_ne_zero hcontra

/-! ## 5. Sharp Lower Bounds over `𝔽_4`: `x^5 ∉ RP^{pass}_{𝔽_4}(2, 2)` and `x^3 ∉ RP^{pass}_{𝔽_4}(2, 3)` -/

/-- Count input accesses targeting the work register `R`. -/
def Pass2GF4Prog.workAccesses : List Pass2GF4Instr → Nat
  | [] => 0
  | .addInputWork _ :: rest => 1 + Pass2GF4Prog.workAccesses rest
  | _ :: rest => Pass2GF4Prog.workAccesses rest

private theorem Pass2GF4Prog.workAccesses_le_accesses (prog : List Pass2GF4Instr) :
    Pass2GF4Prog.workAccesses prog ≤ Pass2GF4Prog.accesses prog := by
  induction prog with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
    cases i <;> simp only [Pass2GF4Prog.workAccesses, Pass2GF4Prog.accesses] <;> omega

/-- Final `a`-shift depends only on the initial `a` and `addInputWork` instructions. -/
private def finalShiftGF4 : List Pass2GF4Instr → GF4 → GF4
  | [], a => a
  | .addInputWork lam :: rest, a => finalShiftGF4 rest (GF4.add a lam)
  | _ :: rest, a => finalShiftGF4 rest a

private theorem execFrom_a_eq_finalShift (prog : List Pass2GF4Instr) (st : State2GF4) :
    (Pass2GF4Prog.execFrom prog st).a = finalShiftGF4 prog st.a := by
  induction prog generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i <;> exact ih _

/-- Predicate asserting that every state visited during `prog` from shift `a` stays inside `S`. -/
private def ShiftsInGF4 (S : GF4 → Prop) : List Pass2GF4Instr → GF4 → Prop
  | [], a => S a
  | .addInputWork lam :: rest, a => S a ∧ ShiftsInGF4 S rest (GF4.add a lam)
  | _ :: rest, a => S a ∧ ShiftsInGF4 S rest a

private theorem workAccesses_zero_shifts (prog : List Pass2GF4Instr) (a : GF4)
    (hw : Pass2GF4Prog.workAccesses prog = 0) :
    ShiftsInGF4 (fun x => x = a) prog a := by
  induction prog with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | addInputWork _ => simp [Pass2GF4Prog.workAccesses] at hw
    | addOut _ => exact ⟨rfl, ih hw⟩
    | addWorkConst _ => exact ⟨rfl, ih hw⟩
    | addInputOut _ => exact ⟨rfl, ih hw⟩

private theorem shiftsIn_mono {S T : GF4 → Prop} (hST : ∀ x, S x → T x)
    (prog : List Pass2GF4Instr) (a : GF4) (h : ShiftsInGF4 S prog a) :
    ShiftsInGF4 T prog a := by
  induction prog generalizing a with
  | nil => exact hST a h
  | cons i rest ih =>
    cases i <;> exact ⟨hST a h.1, ih _ h.2⟩

private theorem workAccesses_eq_zero_final (prog : List Pass2GF4Instr) (a : GF4)
    (hw : Pass2GF4Prog.workAccesses prog = 0) :
    finalShiftGF4 prog a = a := by
  induction prog with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | addInputWork _ => simp [Pass2GF4Prog.workAccesses] at hw
    | addOut _ => exact ih hw
    | addWorkConst _ => exact ih hw
    | addInputOut _ => exact ih hw

/-- Any loop starting and ending at shift `0` with `≤ 2` work accesses stays inside `{0, α}` for some `α`. -/
private theorem closed_loop_le2_shifts (prog : List Pass2GF4Instr)
    (hw : Pass2GF4Prog.workAccesses prog ≤ 2) (hret : finalShiftGF4 prog .z = .z) :
    ∃ α : GF4, ShiftsInGF4 (fun x => x = .z ∨ x = α) prog .z := by
  induction prog with
  | nil => exact ⟨.z, Or.inl rfl⟩
  | cons i rest ih =>
    cases i with
    | addInputWork lam =>
      simp only [Pass2GF4Prog.workAccesses] at hw
      simp only [finalShiftGF4, GF4.add] at hret
      -- From `lam` with `workAccesses rest ≤ 1` and `finalShiftGF4 rest lam = .z`,
      -- `rest` visits only `{lam, .z}`!
      have hsub : ShiftsInGF4 (fun x => x = .z ∨ x = lam) rest lam := by
        have hrec : ∀ (p : List Pass2GF4Instr) (a : GF4),
            Pass2GF4Prog.workAccesses p ≤ 1 → finalShiftGF4 p a = .z →
            ShiftsInGF4 (fun x => x = .z ∨ x = a) p a := by
          intro p
          induction p with
          | nil => intro a _ hf; exact Or.inl hf
          | cons j tl ihtl =>
            intro a hwp hf
            cases j with
            | addInputWork lam2 =>
              simp only [Pass2GF4Prog.workAccesses] at hwp
              have h0 : Pass2GF4Prog.workAccesses tl = 0 := by omega
              simp only [finalShiftGF4] at hf
              have hfin := workAccesses_eq_zero_final tl (GF4.add a lam2) h0
              have hz : GF4.add a lam2 = .z := by rw [← hfin]; exact hf
              refine ⟨Or.inr rfl, ?_⟩
              rw [hz]
              exact shiftsIn_mono (fun x hx => Or.inl hx) tl .z (workAccesses_zero_shifts tl .z h0)
            | addOut _ => exact ⟨Or.inr rfl, ihtl a hwp hf⟩
            | addWorkConst _ => exact ⟨Or.inr rfl, ihtl a hwp hf⟩
            | addInputOut _ => exact ⟨Or.inr rfl, ihtl a hwp hf⟩
        exact hrec rest lam (by omega) hret
      exact ⟨lam, Or.inl rfl, hsub⟩
    | addOut _ =>
      rcases ih hw hret with ⟨α, hα⟩
      exact ⟨α, Or.inl rfl, hα⟩
    | addWorkConst _ =>
      rcases ih hw hret with ⟨α, hα⟩
      exact ⟨α, Or.inl rfl, hα⟩
    | addInputOut _ =>
      rcases ih hw hret with ⟨α, hα⟩
      exact ⟨α, Or.inl rfl, hα⟩

/-- Any loop starting and ending at shift `0` with `≤ 3` work accesses stays inside `{0, α, β}`. -/
private theorem closed_loop_le3_shifts (prog : List Pass2GF4Instr)
    (hw : Pass2GF4Prog.workAccesses prog ≤ 3) (hret : finalShiftGF4 prog .z = .z) :
    ∃ α β : GF4, ShiftsInGF4 (fun x => x = .z ∨ x = α ∨ x = β) prog .z := by
  induction prog with
  | nil => exact ⟨.z, .z, Or.inl rfl⟩
  | cons i rest ih =>
    cases i with
    | addInputWork lam =>
      simp only [Pass2GF4Prog.workAccesses] at hw
      simp only [finalShiftGF4, GF4.add] at hret
      -- From `lam` with `≤ 2` remaining work accesses returning to `.z`, we visit at most `{lam, β, .z}`!
      have hsub : ∀ (p : List Pass2GF4Instr) (a : GF4),
          Pass2GF4Prog.workAccesses p ≤ 2 → finalShiftGF4 p a = .z →
          ∃ β : GF4, ShiftsInGF4 (fun x => x = .z ∨ x = a ∨ x = β) p a := by
        intro p
        induction p with
        | nil => intro a _ hf; exact ⟨a, Or.inl hf⟩
        | cons j tl ihtl =>
          intro a hwp hf
          cases j with
          | addInputWork lam2 =>
            simp only [Pass2GF4Prog.workAccesses] at hwp
            simp only [finalShiftGF4] at hf
            have h1 : ∀ (q : List Pass2GF4Instr) (b : GF4),
                Pass2GF4Prog.workAccesses q ≤ 1 → finalShiftGF4 q b = .z →
                ShiftsInGF4 (fun x => x = .z ∨ x = a ∨ x = b) q b := by
              intro q
              induction q with
              | nil => intro b _ hfq; exact Or.inl hfq
              | cons k qtl ihq =>
                intro b hwq hfq
                cases k with
                | addInputWork lam3 =>
                  simp only [Pass2GF4Prog.workAccesses] at hwq
                  have h0 : Pass2GF4Prog.workAccesses qtl = 0 := by omega
                  simp only [finalShiftGF4] at hfq
                  have hfin := workAccesses_eq_zero_final qtl (GF4.add b lam3) h0
                  have hz : GF4.add b lam3 = .z := by rw [← hfin]; exact hfq
                  refine ⟨Or.inr (Or.inr rfl), ?_⟩
                  rw [hz]
                  exact shiftsIn_mono (fun x hx => Or.inl hx) qtl .z (workAccesses_zero_shifts qtl .z h0)
                | addOut _ => exact ⟨Or.inr (Or.inr rfl), ihq b hwq hfq⟩
                | addWorkConst _ => exact ⟨Or.inr (Or.inr rfl), ihq b hwq hfq⟩
                | addInputOut _ => exact ⟨Or.inr (Or.inr rfl), ihq b hwq hfq⟩
            exact ⟨GF4.add a lam2, Or.inr (Or.inl rfl), h1 tl (GF4.add a lam2) (by omega) hf⟩
          | addOut _ =>
            rcases ihtl a hwp hf with ⟨β, hβ⟩
            exact ⟨β, Or.inr (Or.inl rfl), hβ⟩
          | addWorkConst _ =>
            rcases ihtl a hwp hf with ⟨β, hβ⟩
            exact ⟨β, Or.inr (Or.inl rfl), hβ⟩
          | addInputOut _ =>
            rcases ihtl a hwp hf with ⟨β, hβ⟩
            exact ⟨β, Or.inr (Or.inl rfl), hβ⟩
      rcases hsub rest lam (by omega) hret with ⟨β, hβ⟩
      exact ⟨lam, β, Or.inl rfl, hβ⟩
    | addOut _ =>
      rcases ih hw hret with ⟨α, β, hαβ⟩
      exact ⟨α, β, Or.inl rfl, hαβ⟩
    | addWorkConst _ =>
      rcases ih hw hret with ⟨α, β, hαβ⟩
      exact ⟨α, β, Or.inl rfl, hαβ⟩
    | addInputOut _ =>
      rcases ih hw hret with ⟨α, β, hαβ⟩
      exact ⟨α, β, Or.inl rfl, hαβ⟩

private theorem polyAtShiftCoeffGF4_05_eq_alpha_14 (poly : List GF4) (b a α : GF4)
    (ha : a = .z ∨ a = α) :
    polyAtShiftCoeffGF4 poly b a 0 5 = GF4.mul α (polyAtShiftCoeffGF4 poly b a 1 4) := by
  simp only [polyAtShiftCoeffGF4]
  have hb5 : binomGF4 5 5 = .one := by decide
  have hb4 : binomGF4 5 4 = .one := by decide
  have hpow : GF4.pow a 5 = GF4.mul α (GF4.pow a 4) := by
    rcases ha with rfl | rfl
    · cases α <;> rfl
    · cases a <;> rfl
  change GF4.mul _ (GF4.mul (binomGF4 5 5) (GF4.pow a 5)) =
         GF4.mul α (GF4.mul _ (GF4.mul (binomGF4 5 4) (GF4.pow a 4)))
  rw [hb5, hb4, hpow]
  generalize sumGF4 poly.length (fun k =>
    GF4.mul (poly.getD k .z) (GF4.mul (binomGF4 k 5) (GF4.pow b (k - 5)))) = out
  cases out <;> cases α <;> cases a <;> rfl

private theorem execFrom_preserves_05_inv (α : GF4) (prog : List Pass2GF4Instr) (st : State2GF4)
    (hsh : ShiftsInGF4 (fun x => x = .z ∨ x = α) prog st.a)
    (hinv : st.coeff 0 5 = GF4.mul α (st.coeff 1 4)) :
    (Pass2GF4Prog.execFrom prog st).coeff 0 5 = GF4.mul α ((Pass2GF4Prog.execFrom prog st).coeff 1 4) := by
  induction prog generalizing st with
  | nil => exact hinv
  | cons instr rest ih =>
    cases instr with
    | addOut poly =>
      dsimp only [Pass2GF4Prog.execFrom]
      apply ih (Pass2GF4Instr.exec st (.addOut poly)) hsh.2
      change GF4.add (st.coeff 0 5) (polyAtShiftCoeffGF4 poly st.b st.a 0 5) =
             GF4.mul α (GF4.add (st.coeff 1 4) (polyAtShiftCoeffGF4 poly st.b st.a 1 4))
      rw [hinv, polyAtShiftCoeffGF4_05_eq_alpha_14 poly st.b st.a α hsh.1]
      generalize st.coeff 1 4 = u
      generalize polyAtShiftCoeffGF4 poly st.b st.a 1 4 = v
      cases α <;> cases u <;> cases v <;> rfl
    | addWorkConst c =>
      exact ih _ hsh.2 hinv
    | addInputOut lam =>
      dsimp only [Pass2GF4Prog.execFrom]
      apply ih (Pass2GF4Instr.exec st (.addInputOut lam)) hsh.2
      change GF4.add (st.coeff 0 5) (if (0 : Nat) = 0 ∧ (5 : Nat) = 1 then lam else .z) =
             GF4.mul α (GF4.add (st.coeff 1 4) (if (1 : Nat) = 0 ∧ (4 : Nat) = 1 then lam else .z))
      have h1 : (if (0 : Nat) = 0 ∧ (5 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      have h2 : (if (1 : Nat) = 0 ∧ (4 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      rw [hinv, h1, h2]
      generalize st.coeff 1 4 = u
      cases α <;> cases u <;> rfl
    | addInputWork lam =>
      exact ih _ hsh.2 hinv

/-- **Sharp lower bound: `x^5 ∉ RP^{pass}_{𝔽_4}(2, 2)`** (proving `t_min(5) = 3` is exact over `𝔽_4`). -/
theorem gf4_x5_not_in_2_accesses : ¬ InRPPass2GF4 2 (monomialGF4 5) := by
  rintro ⟨prog, hacc, _, ha0, hclean⟩
  have hw : Pass2GF4Prog.workAccesses prog ≤ 2 :=
    Nat.le_trans (Pass2GF4Prog.workAccesses_le_accesses prog) hacc
  have hret : finalShiftGF4 prog .z = .z := by
    rw [← execFrom_a_eq_finalShift prog ⟨.z, .z, fun _ _ => .z⟩]
    exact ha0
  rcases closed_loop_le2_shifts prog hw hret with ⟨α, hsh⟩
  have hinv := execFrom_preserves_05_inv α prog ⟨.z, .z, fun _ _ => .z⟩ hsh (by cases α <;> rfl)
  change (Pass2GF4Prog.exec prog).coeff 0 5 = GF4.mul α ((Pass2GF4Prog.exec prog).coeff 1 4) at hinv
  have h05 := hclean 0 5
  have h14 := hclean 1 4
  rw [monomialGF4_getD] at h05
  simp only [↓reduceIte] at h05
  have h10 : (1 : Nat) ≠ 0 := by decide
  simp only [h10, ↓reduceIte] at h14
  rw [h05, h14] at hinv
  have hz : GF4.mul α GF4.z = GF4.z := by cases α <;> rfl
  rw [hz] at hinv
  exact GF4.one_ne_zero hinv

private theorem polyAtShiftCoeffGF4_03_linrel (poly : List GF4) (b a α β : GF4)
    (ha : a = .z ∨ a = α ∨ a = β) :
    polyAtShiftCoeffGF4 poly b a 0 3 =
      GF4.add
        (GF4.mul (GF4.add α β) (polyAtShiftCoeffGF4 poly b a 1 2))
        (GF4.mul (GF4.mul α β) (polyAtShiftCoeffGF4 poly b a 2 1)) := by
  simp only [polyAtShiftCoeffGF4]
  have hb3 : binomGF4 3 3 = .one := by decide
  have hb2 : binomGF4 3 2 = .one := by decide
  have hb1 : binomGF4 3 1 = .one := by decide
  change GF4.mul _ (GF4.mul (binomGF4 3 3) (GF4.pow a 3)) =
         GF4.add
           (GF4.mul (GF4.add α β) (GF4.mul _ (GF4.mul (binomGF4 3 2) (GF4.pow a 2))))
           (GF4.mul (GF4.mul α β) (GF4.mul _ (GF4.mul (binomGF4 3 1) (GF4.pow a 1))))
  rw [hb3, hb2, hb1]
  generalize sumGF4 poly.length (fun k =>
    GF4.mul (poly.getD k .z) (GF4.mul (binomGF4 k 3) (GF4.pow b (k - 3)))) = out
  rcases ha with rfl | rfl | rfl
  · cases out <;> cases α <;> cases β <;> rfl
  · cases out <;> cases a <;> cases β <;> rfl
  · cases out <;> cases a <;> cases α <;> rfl

private theorem execFrom_preserves_03_inv (α β : GF4) (prog : List Pass2GF4Instr) (st : State2GF4)
    (hsh : ShiftsInGF4 (fun x => x = .z ∨ x = α ∨ x = β) prog st.a)
    (hinv : st.coeff 0 3 =
      GF4.add (GF4.mul (GF4.add α β) (st.coeff 1 2)) (GF4.mul (GF4.mul α β) (st.coeff 2 1))) :
    (Pass2GF4Prog.execFrom prog st).coeff 0 3 =
      GF4.add
        (GF4.mul (GF4.add α β) ((Pass2GF4Prog.execFrom prog st).coeff 1 2))
        (GF4.mul (GF4.mul α β) ((Pass2GF4Prog.execFrom prog st).coeff 2 1)) := by
  induction prog generalizing st with
  | nil => exact hinv
  | cons instr rest ih =>
    cases instr with
    | addOut poly =>
      dsimp only [Pass2GF4Prog.execFrom]
      apply ih (Pass2GF4Instr.exec st (.addOut poly)) hsh.2
      change GF4.add (st.coeff 0 3) (polyAtShiftCoeffGF4 poly st.b st.a 0 3) =
             GF4.add
               (GF4.mul (GF4.add α β) (GF4.add (st.coeff 1 2) (polyAtShiftCoeffGF4 poly st.b st.a 1 2)))
               (GF4.mul (GF4.mul α β) (GF4.add (st.coeff 2 1) (polyAtShiftCoeffGF4 poly st.b st.a 2 1)))
      rw [hinv, polyAtShiftCoeffGF4_03_linrel poly st.b st.a α β hsh.1]
      generalize GF4.add α β = s
      generalize GF4.mul α β = p
      generalize st.coeff 1 2 = u1
      generalize st.coeff 2 1 = u2
      generalize polyAtShiftCoeffGF4 poly st.b st.a 1 2 = v1
      generalize polyAtShiftCoeffGF4 poly st.b st.a 2 1 = v2
      change s * u1 + p * u2 + (s * v1 + p * v2) = s * (u1 + v1) + p * (u2 + v2)
      rw [CRing.left_distrib, CRing.left_distrib]
      calc
        s * u1 + p * u2 + (s * v1 + p * v2) = s * u1 + (p * u2 + (s * v1 + p * v2)) :=
          CRing.add_assoc _ _ _
        _ = s * u1 + (s * v1 + (p * u2 + p * v2)) := by
          rw [← CRing.add_assoc (p * u2), CRing.add_comm (p * u2) (s * v1), CRing.add_assoc (s * v1)]
        _ = s * u1 + s * v1 + (p * u2 + p * v2) := (CRing.add_assoc _ _ _).symm
    | addWorkConst c =>
      exact ih _ hsh.2 hinv
    | addInputOut lam =>
      dsimp only [Pass2GF4Prog.execFrom]
      apply ih (Pass2GF4Instr.exec st (.addInputOut lam)) hsh.2
      change GF4.add (st.coeff 0 3) (if (0 : Nat) = 0 ∧ (3 : Nat) = 1 then lam else .z) =
             GF4.add
               (GF4.mul (GF4.add α β) (GF4.add (st.coeff 1 2) (if (1 : Nat) = 0 ∧ (2 : Nat) = 1 then lam else .z)))
               (GF4.mul (GF4.mul α β) (GF4.add (st.coeff 2 1) (if (2 : Nat) = 0 ∧ (1 : Nat) = 1 then lam else .z)))
      have h1 : (if (0 : Nat) = 0 ∧ (3 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      have h2 : (if (1 : Nat) = 0 ∧ (2 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      have h3 : (if (2 : Nat) = 0 ∧ (1 : Nat) = 1 then lam else GF4.z) = GF4.z := by simp
      rw [hinv, h1, h2, h3]
      generalize GF4.add α β = s
      generalize GF4.mul α β = p
      generalize st.coeff 1 2 = u1
      generalize st.coeff 2 1 = u2
      change s * u1 + p * u2 + 0 = s * (u1 + 0) + p * (u2 + 0)
      simp only [CRing.add_zero]
    | addInputWork lam =>
      exact ih _ hsh.2 hinv

/-- **Sharp lower bound: `x^3 ∉ RP^{pass}_{𝔽_4}(2, 3)`** (proving `t_min(3) = 4` is exact over `𝔽_4`). -/
theorem gf4_x3_not_in_3_accesses : ¬ InRPPass2GF4 3 (monomialGF4 3) := by
  rintro ⟨prog, hacc, _, ha0, hclean⟩
  have hw : Pass2GF4Prog.workAccesses prog ≤ 3 :=
    Nat.le_trans (Pass2GF4Prog.workAccesses_le_accesses prog) hacc
  have hret : finalShiftGF4 prog .z = .z := by
    rw [← execFrom_a_eq_finalShift prog ⟨.z, .z, fun _ _ => .z⟩]
    exact ha0
  rcases closed_loop_le3_shifts prog hw hret with ⟨α, β, hsh⟩
  have hinit : GF4.z = GF4.add (GF4.mul (GF4.add α β) GF4.z) (GF4.mul (GF4.mul α β) GF4.z) := by
    cases α <;> cases β <;> rfl
  have hinv := execFrom_preserves_03_inv α β prog ⟨.z, .z, fun _ _ => .z⟩ hsh hinit
  change (Pass2GF4Prog.exec prog).coeff 0 3 =
    GF4.add
      (GF4.mul (GF4.add α β) ((Pass2GF4Prog.exec prog).coeff 1 2))
      (GF4.mul (GF4.mul α β) ((Pass2GF4Prog.exec prog).coeff 2 1)) at hinv
  have h03 := hclean 0 3
  have h12 := hclean 1 2
  have h21 := hclean 2 1
  rw [monomialGF4_getD] at h03
  simp only [↓reduceIte] at h03
  have h10 : (1 : Nat) ≠ 0 := by decide
  have h20 : (2 : Nat) ≠ 0 := by decide
  simp only [h10, ↓reduceIte] at h12
  simp only [h20, ↓reduceIte] at h21
  rw [h03, h12, h21] at hinv
  have hz : GF4.add (GF4.mul (GF4.add α β) GF4.z) (GF4.mul (GF4.mul α β) GF4.z) = GF4.z := by
    cases α <;> cases β <;> rfl
  rw [hz] at hinv
  exact GF4.one_ne_zero hinv

end

end Catalytic
