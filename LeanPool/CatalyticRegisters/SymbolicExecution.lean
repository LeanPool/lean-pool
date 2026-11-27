/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.CommRing

/-!
# Theorem T3: Strict Improvement Over Vinciguerra's 3-Register Powering Frontier

Vinciguerra (`arXiv:2609.18692`, Theorem 2.3) proved `x^5 ∈ RP^{pass}_K(3, 4)`, yielding
the recursive composition exponent `log_5 4 ≈ 0.861353` for 4-register powering, catalytic
streaming frequency moments (Corollary 5.1.1), and matrix powering (Theorem 5.2).

We construct five explicit passive-output 3-register catalytic programs (in Vinciguerra's
literal Definition 2.2 instruction set) with exact integer coefficients:
  * `prog5Power7`:  5 input accesses, computing `576 * x^7`                  (bad primes `{2, 3}`)
  * `prog6Power9`:  6 input accesses, computing `382500000 * x^9`            (bad primes `{2, 3, 5, 17}`)
  * `prog7Power11`: 7 input accesses, computing `68724637549388656012800 * x^11`
  * `prog8Power13`: 8 input accesses, computing `2656207148788801777680 * x^13`
  * `prog9Power15`: 9 input accesses, computing `876702103804656272895371895753963647960420947968000 * x^15`

Each integer program executes cleanly over **EVERY commutative ring `R`**, restoring work
registers `(u, v)` identically and adding `D * x^N` to the passive output register `O`.
Over any ring/field `R` in which `D` has a multiplicative inverse (in particular `ℚ`, `ℝ`, `ℂ`,
and `𝔽_p` avoiding the explicit finite set of bad primes), scaling `addOut` coefficients by `D⁻¹`
yields exact monic programs proving:
  * `x^7  ∈ RP^{pass}_K(3, 5)`  (`log_7  5 ≈ 0.827087`),
  * `x^9  ∈ RP^{pass}_K(3, 6)`  (`log_9  6 ≈ 0.815465`),
  * `x^11 ∈ RP^{pass}_K(3, 7)`  (`log_11 7 ≈ 0.811508`),
  * `x^13 ∈ RP^{pass}_K(3, 8)`  (`log_13 8 ≈ 0.810714`, the unique integer minimum of `log_{2t-3} t`),
  * `x^15 ∈ RP^{pass}_K(3, 9)`  (`log_15 9 ≈ 0.811368`, post-minimum ascent point).

We also formally certify the entire strictly decreasing exponent chain via exact `Nat`
power inequalities with rational separators (`30/37`, `13/16`, `9/11`, `5/6`).
-/

namespace Catalytic

@[expose] public section

universe u

/-! ## 1. Literal 3-Register Passive-Output Register Program Model (Vinciguerra Def. 2.2) -/

/--
A primitive instruction of a passive-output 3-register program over registers `(O, u, v)`
with coefficients in a ring `R`:
  * `addOut p`:   `O ← O + ∑_{(a, b, c) ∈ p} c * u^a * v^b`  (basic op, passive output, 0 accesses)
  * `addWorkV c d`: `v ← v + c * u^d`                        (basic op, reads only `u`, 0 accesses)
  * `addInputU α`:  `u ← u + α * x`                          (input access: **1 access to `x`**)
-/
inductive Pass3InstrR (R : Type u) where
  | addOut (terms : List (Nat × Nat × R)) : Pass3InstrR R
  | addWorkV (coeff : R) (deg : Nat) : Pass3InstrR R
  | addInputU (alpha : R) : Pass3InstrR R

/-- Integer-coefficient 3-register passive program instruction. -/
abbrev Pass3Instr := Pass3InstrR Int

/-- Count input accesses in a 3-register passive program. -/
def Pass3Prog.accesses {R : Type u} : List (Pass3InstrR R) → Nat
  | [] => 0
  | .addOut _ :: rest => Pass3Prog.accesses rest
  | .addWorkV _ _ :: rest => Pass3Prog.accesses rest
  | .addInputU _ :: rest => 1 + Pass3Prog.accesses rest

/-- Evaluate a bivariate polynomial `∑ (a, b, c) => c * u^a * v^b` in any `CRing R`. -/
def evalBivar {R : Type u} [CRing R] (u v : R) : List (Nat × Nat × R) → R
  | [] => 0
  | (a, b, c) :: rest => c * (CRing.pow u a * CRing.pow v b) + evalBivar u v rest

/-- Execute one 3-register instruction over any `CRing R`. -/
def Pass3InstrR.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) :
    Pass3InstrR R → R × R × R
  | .addOut terms => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
  | .addWorkV c d => (st.1, st.2.1, st.2.2 + c * CRing.pow st.2.1 d)
  | .addInputU α => (st.1, st.2.1 + α * x, st.2.2)

/-- Execute a 3-register program left-to-right over any `CRing R`. -/
def Pass3Prog.exec {R : Type u} [CRing R] (x : R) :
    List (Pass3InstrR R) → (R × R × R) → (R × R × R)
  | [], st => st
  | i :: rest, st => Pass3Prog.exec x rest (i.exec x st)

/-- Cast an integer 3-register program into any `CRing R`, scaling output updates by `s : R`. -/
def Pass3Instr.scaleOut {R : Type u} [CRing R] (s : R) : Pass3Instr → Pass3InstrR R
  | .addOut terms => .addOut (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c))
  | .addWorkV c d => .addWorkV (CRing.intCast c) d
  | .addInputU α => .addInputU (CRing.intCast α)

/-- Interpret the integer program over the ring and scale its output coefficients. -/
def Pass3Prog.scaleOut {R : Type u} [CRing R] (s : R) (p : List Pass3Instr) :
    List (Pass3InstrR R) :=
  p.map (Pass3Instr.scaleOut s)

theorem Pass3Prog.scaleOut_accesses {R : Type u} [CRing R] (s : R) (p : List Pass3Instr) :
    Pass3Prog.accesses (Pass3Prog.scaleOut s p) = Pass3Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    cases i <;>
      exact (by
        change Pass3Prog.accesses (Pass3Instr.scaleOut s _ :: Pass3Prog.scaleOut s rest) = _
        simp only [Pass3Instr.scaleOut, Pass3Prog.accesses, ih])

private theorem evalBivar_scale {R : Type u} [CRing R] (s u v : R)
    (terms : List (Nat × Nat × Int)) :
    evalBivar u v (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c)) =
      s * evalBivar u v (terms.map fun (a, b, c) => (a, b, CRing.intCast c)) := by
  induction terms with
  | nil => simp [evalBivar]
  | cons hd tl ih =>
    rcases hd with ⟨a, b, c⟩
    simp only [List.map, evalBivar, ih, CRing.left_distrib, CRing.mul_assoc]

/-- Scaling all `addOut` instructions by `s : R` leaves `(u, v)` unchanged and scales `ΔO` by `s`. -/
theorem Pass3Prog.exec_scaleOut {R : Type u} [CRing R] (s x o o' u v : R) (p : List Pass3Instr) :
    let res1 := Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p) (o, u, v)
    let resS := Pass3Prog.exec x (Pass3Prog.scaleOut s p) (o', u, v)
    resS.2 = res1.2 ∧
    ∀ Δ : R, res1.1 = o + Δ → resS.1 = o' + s * Δ := by
  induction p generalizing o o' u v with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro Δ hΔ
    change o = o + Δ at hΔ
    have h0 : Δ = 0 := by
      have := CRing.add_left_cancel (a := o) (b := 0) (c := Δ) (by rw [CRing.add_zero]; exact hΔ)
      exact this.symm
    change o' = o' + s * Δ
    rw [h0, CRing.mul_zero, CRing.add_zero]
  | cons instr rest ih =>
    cases instr with
    | addOut terms =>
      change let res1 := Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) rest)
               (o + evalBivar u v (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)), u, v)
             let resS := Pass3Prog.exec x (Pass3Prog.scaleOut s rest)
               (o' + evalBivar u v (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c)), u, v)
             resS.2 = res1.2 ∧ ∀ Δ : R, res1.1 = o + Δ → resS.1 = o' + s * Δ
      let raw := evalBivar u v (terms.map fun (a, b, c) => (a, b, CRing.intCast c))
      have h1 : evalBivar u v (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)) = raw := by
        rw [evalBivar_scale, CRing.one_mul]
      have hS : evalBivar u v (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c)) = s * raw :=
        evalBivar_scale s u v terms
      rw [h1, hS]
      have hrec := ih (o + raw) (o' + s * raw) u v
      refine ⟨hrec.1, ?_⟩
      intro Δ hΔ
      have hΔ' : (Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) rest) (o + raw, u, v)).1 =
          (o + raw) + (Δ + -raw) := by
        rw [hΔ]
        calc
          o + Δ = o + (0 + Δ) := by rw [CRing.zero_add]
          _     = o + ((raw + -raw) + Δ) := by rw [CRing.add_neg]
          _     = o + (raw + (Δ + -raw)) := by rw [CRing.add_assoc, CRing.add_comm (-raw) Δ]
          _     = (o + raw) + (Δ + -raw) := (CRing.add_assoc _ _ _).symm
      have hres := hrec.2 (Δ + -raw) hΔ'
      rw [hres, CRing.left_distrib, CRing.mul_neg]
      calc
        (o' + s * raw) + (s * Δ + -(s * raw))
            = o' + ((s * raw + -(s * raw)) + s * Δ) := by
              rw [CRing.add_assoc, CRing.add_comm (s * Δ) (-(s * raw)), ← CRing.add_assoc (s * raw)]
        _   = o' + (0 + s * Δ) := by rw [CRing.add_neg]
        _   = o' + s * Δ := by rw [CRing.zero_add]
    | addWorkV c d =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec, Pass3InstrR.exec]
      exact ih o o' u (v + CRing.intCast c * CRing.pow u d)
    | addInputU α =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec, Pass3InstrR.exec]
      exact ih o o' (u + CRing.intCast α * x) v

/-! ## 2. Verified Sparse Trivariate Integer Polynomial Reducer (Pure Kernel Sound Reflection) -/

/-- Monomial exponent triple `(deg_x, deg_u, deg_v)`. -/
abbrev Mon3 := Nat × Nat × Nat

/-- Lexicographic strict ordering on `Mon3`. -/
def Mon3.lt (a b : Mon3) : Bool :=
  if a.1 != b.1 then a.1 < b.1
  else if a.2.1 != b.2.1 then a.2.1 < b.2.1
  else a.2.2 < b.2.2

/-- Sparse trivariate integer polynomial in `(x, u, v)`. -/
abbrev Poly3 := List (Mon3 × Int)

/-- Evaluate a `Poly3` in any commutative ring `R`. -/
def Poly3.eval {R : Type u} [CRing R] (x u v : R) : Poly3 → R
  | [] => 0
  | ((dx, du, dv), c) :: rest =>
    CRing.intCast c * (CRing.pow x dx * (CRing.pow u du * CRing.pow v dv)) + Poly3.eval x u v rest

/-- Structurally recursive merge-add of two sorted sparse polynomials (instant kernel reduction!). -/
def Poly3.addAux (m1 : Mon3) (c1 : Int) (addR1 : Poly3 → Poly3) : Poly3 → Poly3
  | [] => (m1, c1) :: addR1 []
  | (m2, c2) :: r2 =>
    if m1 == m2 then
      let c := c1 + c2
      if c == 0 then addR1 r2
      else (m1, c) :: addR1 r2
    else if Mon3.lt m1 m2 then
      (m1, c1) :: addR1 ((m2, c2) :: r2)
    else
      (m2, c2) :: Poly3.addAux m1 c1 addR1 r2

/-- Merge two sorted polynomials and drop terms whose coefficients cancel. -/
def Poly3.add : Poly3 → Poly3 → Poly3
  | [], q => q
  | (m1, c1) :: r1, q => Poly3.addAux m1 c1 (Poly3.add r1) q

/-- Scale a `Poly3` by an integer scalar `k`. -/
def Poly3.scale (k : Int) (p : Poly3) : Poly3 :=
  if k == 0 then []
  else p.map fun (m, c) => (m, k * c)

/-- Multiply a `Poly3` by a single term `(m, c)`. -/
def Poly3.mulTerm (m : Mon3) (c : Int) (p : Poly3) : Poly3 :=
  if c == 0 then []
  else p.map fun (m', c') => ((m.1 + m'.1, m.2.1 + m'.2.1, m.2.2 + m'.2.2), c * c')

/-- Multiply two `Poly3` polynomials using merge-addition. -/
def Poly3.mul : Poly3 → Poly3 → Poly3
  | [], _ => []
  | (m, c) :: rest, q => Poly3.add (Poly3.mulTerm m c q) (Poly3.mul rest q)

/-- Raise a `Poly3` to a natural-number power. -/
def Poly3.pow (p : Poly3) : Nat → Poly3
  | 0 => [((0, 0, 0), 1)]
  | n + 1 => Poly3.mul (Poly3.pow p n) p

private theorem Poly3.eval_addAux {R : Type u} [CRing R] (x u v : R)
    (m1 : Mon3) (c1 : Int) (r1 : Poly3) (addR1 : Poly3 → Poly3)
    (hadd : ∀ q, Poly3.eval x u v (addR1 q) = Poly3.eval x u v r1 + Poly3.eval x u v q)
    (q : Poly3) :
    Poly3.eval x u v (Poly3.addAux m1 c1 addR1 q) =
      (CRing.intCast c1 * (CRing.pow x m1.1 * (CRing.pow u m1.2.1 * CRing.pow v m1.2.2)) +
        Poly3.eval x u v r1) + Poly3.eval x u v q := by
  induction q with
  | nil =>
    rcases m1 with ⟨dx1, du1, dv1⟩
    simp only [Poly3.addAux, Poly3.eval, hadd [], CRing.add_zero]
  | cons t2 r2 ih2 =>
    rcases m1 with ⟨dx1, du1, dv1⟩
    rcases t2 with ⟨⟨dx2, du2, dv2⟩, c2⟩
    simp only [Poly3.addAux]
    split
    · rename_i heq
      have hmeq : (dx1, du1, dv1) = (dx2, du2, dv2) := beq_iff_eq.mp heq
      cases hmeq
      split
      · rename_i hc0
        have hc : c1 + c2 = 0 := beq_iff_eq.mp hc0
        rw [hadd r2]
        simp only [Poly3.eval]
        let M := CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1)
        have hsum : (CRing.intCast c1 : R) * M + (CRing.intCast c2 : R) * M = 0 := by
          rw [← CRing.right_distrib, ← CRing.intCast_add, hc, CRing.intCast_zero, CRing.zero_mul]
        calc
          Poly3.eval x u v r1 + Poly3.eval x u v r2
              = 0 + (Poly3.eval x u v r1 + Poly3.eval x u v r2) := (CRing.zero_add _).symm
          _   = ((CRing.intCast c1 * M + CRing.intCast c2 * M) +
                 (Poly3.eval x u v r1 + Poly3.eval x u v r2)) := by rw [hsum]
          _   = (CRing.intCast c1 * M + Poly3.eval x u v r1) +
                (CRing.intCast c2 * M + Poly3.eval x u v r2) := by
                  rw [CRing.add_assoc, ← CRing.add_assoc (CRing.intCast c2 * M),
                      CRing.add_comm (CRing.intCast c2 * M) (Poly3.eval x u v r1),
                      CRing.add_assoc (Poly3.eval x u v r1), ← CRing.add_assoc]
      · rw [Poly3.eval, hadd r2, CRing.intCast_add, CRing.right_distrib]
        simp only [Poly3.eval]
        let A := CRing.intCast c1 * (CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1))
        let B := CRing.intCast c2 * (CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1))
        let E1 := Poly3.eval x u v r1
        let E2 := Poly3.eval x u v r2
        change (A + B) + (E1 + E2) = (A + E1) + (B + E2)
        rw [CRing.add_assoc, ← CRing.add_assoc B E1 E2, CRing.add_comm B E1,
            CRing.add_assoc E1 B E2, ← CRing.add_assoc]
    · split
      · rw [Poly3.eval, hadd (((dx2, du2, dv2), c2) :: r2)]
        simp only [Poly3.eval, CRing.add_assoc]
      · rw [Poly3.eval, ih2]
        simp only [Poly3.eval]
        let A := CRing.intCast c1 * (CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1))
        let B := CRing.intCast c2 * (CRing.pow x dx2 * (CRing.pow u du2 * CRing.pow v dv2))
        let E1 := Poly3.eval x u v r1
        let E2 := Poly3.eval x u v r2
        change B + ((A + E1) + E2) = (A + E1) + (B + E2)
        rw [← CRing.add_assoc, CRing.add_comm B (A + E1), CRing.add_assoc]

theorem Poly3.eval_add {R : Type u} [CRing R] (x u v : R) (p q : Poly3) :
    Poly3.eval x u v (Poly3.add p q) = Poly3.eval x u v p + Poly3.eval x u v q := by
  induction p generalizing q with
  | nil => simp [Poly3.add, Poly3.eval, CRing.zero_add]
  | cons t1 r1 ih1 =>
    rcases t1 with ⟨m1, c1⟩
    simp only [Poly3.add, Poly3.eval]
    exact Poly3.eval_addAux x u v m1 c1 r1 (Poly3.add r1) ih1 q

theorem Poly3.eval_scale {R : Type u} [CRing R] (x u v : R) (k : Int) (p : Poly3) :
    Poly3.eval x u v (Poly3.scale k p) = CRing.intCast k * Poly3.eval x u v p := by
  simp only [Poly3.scale]
  split
  · rename_i hk0
    have hk : k = 0 := beq_iff_eq.mp hk0
    subst hk; simp [Poly3.eval]
  · induction p with
    | nil => simp [Poly3.eval]
    | cons hd tl ih =>
      rcases hd with ⟨⟨dx, du, dv⟩, c⟩
      simp only [List.map, Poly3.eval, ih, CRing.intCast_mul, CRing.left_distrib, CRing.mul_assoc]

theorem Poly3.eval_mulTerm {R : Type u} [CRing R] (x u v : R) (m : Mon3) (c : Int) (p : Poly3) :
    Poly3.eval x u v (Poly3.mulTerm m c p) =
      CRing.intCast c * (CRing.pow x m.1 * (CRing.pow u m.2.1 * CRing.pow v m.2.2)) *
        Poly3.eval x u v p := by
  simp only [Poly3.mulTerm]
  split
  · rename_i hc0
    have hc : c = 0 := beq_iff_eq.mp hc0
    subst hc; simp [Poly3.eval]
  · induction p with
    | nil => simp [Poly3.eval]
    | cons hd tl ih =>
      rcases hd with ⟨⟨dx, du, dv⟩, c'⟩
      simp only [List.map, Poly3.eval, ih, CRing.intCast_mul, CRing.pow_add, CRing.left_distrib]
      congr 1
      let C1 : R := CRing.intCast c
      let C2 : R := CRing.intCast c'
      let X1 := CRing.pow x m.1; let X2 := CRing.pow x dx
      let U1 := CRing.pow u m.2.1; let U2 := CRing.pow u du
      let V1 := CRing.pow v m.2.2; let V2 := CRing.pow v dv
      change (C1 * C2) * ((X1 * X2) * ((U1 * U2) * (V1 * V2))) =
        C1 * (X1 * (U1 * V1)) * (C2 * (X2 * (U2 * V2)))
      have hUV : (U1 * U2) * (V1 * V2) = (U1 * V1) * (U2 * V2) := by
        rw [CRing.mul_assoc, ← CRing.mul_assoc U2 V1 V2, CRing.mul_comm U2 V1,
            CRing.mul_assoc V1 U2 V2, ← CRing.mul_assoc]
      have hXUV : (X1 * X2) * ((U1 * V1) * (U2 * V2)) = (X1 * (U1 * V1)) * (X2 * (U2 * V2)) := by
        rw [CRing.mul_assoc, ← CRing.mul_assoc X2 (U1 * V1), CRing.mul_comm X2 (U1 * V1),
            CRing.mul_assoc (U1 * V1) X2, ← CRing.mul_assoc]
      rw [hUV, hXUV]
      rw [CRing.mul_assoc, ← CRing.mul_assoc C2 (X1 * (U1 * V1)), CRing.mul_comm C2 (X1 * (U1 * V1)),
          CRing.mul_assoc (X1 * (U1 * V1)) C2, ← CRing.mul_assoc]

theorem Poly3.eval_mul {R : Type u} [CRing R] (x u v : R) (p q : Poly3) :
    Poly3.eval x u v (Poly3.mul p q) = Poly3.eval x u v p * Poly3.eval x u v q := by
  induction p with
  | nil => simp [Poly3.mul, Poly3.eval]
  | cons hd tl ih =>
    rcases hd with ⟨⟨dx, du, dv⟩, c⟩
    simp only [Poly3.mul, Poly3.eval_add, Poly3.eval_mulTerm, ih, Poly3.eval, CRing.right_distrib]

theorem Poly3.eval_pow {R : Type u} [CRing R] (x u v : R) (p : Poly3) (n : Nat) :
    Poly3.eval x u v (Poly3.pow p n) = CRing.pow (Poly3.eval x u v p) n := by
  induction n with
  | zero => simp [Poly3.pow, Poly3.eval]
  | succ k ih =>
    simp only [Poly3.pow, Poly3.eval_mul, ih, CRing.pow]

/-- Symbolic evaluation of a bivariate output polynomial at `(pu, pv)`. -/
def evalBivarPoly (pu pv : Poly3) : List (Nat × Nat × Int) → Poly3
  | [] => []
  | (a, b, c) :: rest =>
    Poly3.add (Poly3.scale c (Poly3.mul (Poly3.pow pu a) (Poly3.pow pv b)))
      (evalBivarPoly pu pv rest)

theorem evalBivarPoly_sound {R : Type u} [CRing R] (x u v : R)
    (pu pv : Poly3) (terms : List (Nat × Nat × Int)) :
    Poly3.eval x u v (evalBivarPoly pu pv terms) =
      evalBivar (Poly3.eval x u v pu) (Poly3.eval x u v pv)
        (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)) := by
  induction terms with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b, c⟩
    simp only [evalBivarPoly, List.map, evalBivar, Poly3.eval_add, Poly3.eval_scale,
      Poly3.eval_mul, Poly3.eval_pow, ih, CRing.one_mul]

/-- Symbolic execution of an integer 3-register program over `Poly3`. -/
def exec3PolyAux : List Pass3Instr → Poly3 × Poly3 × Poly3 → Poly3 × Poly3 × Poly3
  | [], st => st
  | .addOut terms :: rest, (po, pu, pv) =>
    exec3PolyAux rest (Poly3.add po (evalBivarPoly pu pv terms), pu, pv)
  | .addWorkV c d :: rest, (po, pu, pv) =>
    exec3PolyAux rest (po, pu, Poly3.add pv (Poly3.scale c (Poly3.pow pu d)))
  | .addInputU α :: rest, (po, pu, pv) =>
    exec3PolyAux rest (po, Poly3.add pu (Poly3.scale α [((1, 0, 0), 1)]), pv)

/-- Evaluate the program symbolically from independent work variables and zero output. -/
def exec3Poly (p : List Pass3Instr) : Poly3 × Poly3 × Poly3 :=
  exec3PolyAux p ([], [((0, 1, 0), 1)], [((0, 0, 1), 1)])

private theorem exec3PolyAux_sound {R : Type u} [CRing R] (x o u v : R)
    (p : List Pass3Instr) (po pu pv : Poly3) :
    Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p)
      (o + Poly3.eval x u v po, Poly3.eval x u v pu, Poly3.eval x u v pv) =
      let res := exec3PolyAux p (po, pu, pv)
      (o + Poly3.eval x u v res.1, Poly3.eval x u v res.2.1, Poly3.eval x u v res.2.2) := by
  induction p generalizing po pu pv with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | addOut terms =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec,
        Pass3InstrR.exec, exec3PolyAux]
      have h1 : o + Poly3.eval x u v po +
          evalBivar (Poly3.eval x u v pu) (Poly3.eval x u v pv)
            (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)) =
          o + Poly3.eval x u v (Poly3.add po (evalBivarPoly pu pv terms)) := by
        rw [Poly3.eval_add, evalBivarPoly_sound, CRing.add_assoc]
      rw [h1]
      exact ih (Poly3.add po (evalBivarPoly pu pv terms)) pu pv
    | addWorkV c d =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec,
        Pass3InstrR.exec, exec3PolyAux]
      have h1 : Poly3.eval x u v pv + CRing.intCast c * CRing.pow (Poly3.eval x u v pu) d =
          Poly3.eval x u v (Poly3.add pv (Poly3.scale c (Poly3.pow pu d))) := by
        rw [Poly3.eval_add, Poly3.eval_scale, Poly3.eval_pow]
      rw [h1]
      exact ih po pu (Poly3.add pv (Poly3.scale c (Poly3.pow pu d)))
    | addInputU α =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec,
        Pass3InstrR.exec, exec3PolyAux]
      have hx : Poly3.eval x u v (Poly3.scale α [((1, 0, 0), 1)]) = CRing.intCast α * x := by
        simp [Poly3.eval_scale, Poly3.eval, CRing.one_mul]
      have h1 : Poly3.eval x u v pu + CRing.intCast α * x =
          Poly3.eval x u v (Poly3.add pu (Poly3.scale α [((1, 0, 0), 1)])) := by
        rw [Poly3.eval_add, hx]
      rw [h1]
      exact ih po (Poly3.add pu (Poly3.scale α [((1, 0, 0), 1)])) pv

/--
Master soundness bridge: if `exec3Poly p = ([((N, 0, 0), D)], [((0, 1, 0), 1)], [((0, 0, 1), 1)])`,
then:
  1. Over EVERY commutative ring `R`, `Pass3Prog.scaleOut 1 p` cleanly computes `O ← O + D * x^N`.
  2. Over EVERY commutative ring `R` with an inverse `invD : R` (`invD * intCast D = 1`),
     `Pass3Prog.scaleOut invD p` cleanly computes `O ← O + x^N` with the exact same access count!
-/
theorem exec3Poly_certifies_monic {R : Type u} [CRing R]
    (p : List Pass3Instr) (N : Nat) (D : Int)
    (hcert : exec3Poly p = ([((N, 0, 0), D)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]))
    (invD : R) (hinv : invD * CRing.intCast D = 1) (x o u v : R) :
    Pass3Prog.exec x (Pass3Prog.scaleOut invD p) (o, u, v) =
      (o + CRing.pow x N, u, v) := by
  have h1 := exec3PolyAux_sound (R := R) x o u v p [] [((0, 1, 0), 1)] [((0, 0, 1), 1)]
  have he0 : Poly3.eval x u v [] = (0 : R) := rfl
  have heu : Poly3.eval x u v [((0, 1, 0), 1)] = u := by
    simp [Poly3.eval, CRing.one_mul]
  have hev : Poly3.eval x u v [((0, 0, 1), 1)] = v := by
    simp [Poly3.eval, CRing.one_mul]
  rw [he0, heu, hev, CRing.add_zero] at h1
  change Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p) (o, u, v) =
    let res := exec3Poly p
    (o + Poly3.eval x u v res.1, Poly3.eval x u v res.2.1, Poly3.eval x u v res.2.2) at h1
  rw [hcert] at h1
  simp only [Poly3.eval, CRing.pow_zero, CRing.pow_one, CRing.mul_one, CRing.add_zero,
    CRing.intCast_one, CRing.one_mul] at h1
  have hscale := Pass3Prog.exec_scaleOut (R := R) invD x o o u v p
  have h2 := hscale.1
  have h3 := hscale.2 (CRing.intCast D * CRing.pow x N) (by rw [h1])
  rw [h1] at h2
  have hprod : invD * (CRing.intCast D * CRing.pow x N) = CRing.pow x N := by
    rw [← CRing.mul_assoc, hinv, CRing.one_mul]
  rw [hprod] at h3
  exact Prod.ext h3 h2

end

end Catalytic
