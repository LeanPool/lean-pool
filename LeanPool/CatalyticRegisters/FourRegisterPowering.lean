/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.CommRing
public import LeanPool.CatalyticRegisters.PrimeFieldTools
public import LeanPool.CatalyticRegisters.Pass2Soundness
public import LeanPool.CatalyticRegisters.ThreeRegisterBreakthrough

/-!
# Theorem T3h: Machine-Checked Four-Register Passive Powering (`x^N` for All `N ≥ 1`)

Formalizes **Corollary 5.2** of Donahue's manuscript, which sharpens Corollary 4.3.1
of Vinciguerra (`arXiv:2609.18692v1`).

  1. **Concrete 3-work-register model (`Work3Instr R`)** on `(r0, r1, r2)` with concrete bivariate
     polynomial updates `r_dst ← r_dst + ∑ c * r_other1^a * r_other2^b` (never reading `r_dst`) and
     input accesses `r_dst ← r_dst + α * x`.
  2. **Clean non-passive 3-register composition (`Work3Prog.compose`):** a specialization of
     Alekseev et al., MFCS 2025, Lemma 8 (Lemma 2.1 of `arXiv:2504.17412v1`). Cyclic shift lets
     a clean passive block `Q` (such as `prog8Power13` or `prog5Power7`) be substituted into every
     input access of `P`, achieving
     `Work3Prog.exec x (compose P Q) st = Work3Prog.exec (g x) P st` and exact access product
     `accesses (compose P Q) = accesses P * tQ` within **3 work registers** (avoiding the extra
     register required by the passive composition in Vinciguerra's Lemma 2.2).
  3. **Exact 2-register forward-difference digit programs (`digitPowProg`):** using `iterDiff_pow`
     from `PrimeFieldTools` and `CRing.add_pow` from `Pass2Soundness`, computes `x^b` cleanly in
     `≤ b + 1` input accesses over any `CRing R` in which `b!` is invertible.
  4. **Literal 4-register passive model (`Pass4Instr R`)** on `(O, U, R1, R2)` where `O` is
     **strictly passive** (never appears on any RHS) and **Cook–Mertz finite-difference product
     accumulation (`accumProg`)**, proving `finDiffR (ys.length) ys u = (ys.length)! * prod(ys)`.
  5. **Complete 4-register powering for EVERY `N ≥ 1`:**
     * Via `prog8Power13`: `Pass4Prog.exec x prog (o, u, r1, r2) = (o + x^N, u, r1, r2)` with
       `13^ℓ ≤ N` and `3 * accesses prog < 104 * 8^ℓ` (i.e. `< (8/3) * 13 * N^{log_13 8}`),
       whenever `D_8`, `12!`, and `(ℓ + 1)!` are invertible in `R`.
     * Via `prog5Power7`: `Pass4Prog.exec x prog (o, u, r1, r2) = (o + x^N, u, r1, r2)` with
       `7^ℓ ≤ N` and `3 * accesses prog < 70 * 5^ℓ` (i.e. `< (10/3) * 7 * N^{log_7 5}`),
       whenever `6!` and `(ℓ + 1)!` are invertible in `R` (since `6! = 720` invertible already
       implies `2` and `3`, hence `576 = 2^6 * 3^2`, are invertible!).
  6. **Theorem T3i (Coordinatewise powering over `R^n`; no stream or bit-space model in statement):**
     Instantiates `T3h` over the pointwise product ring `CRing (Fin n → R)`, cleanly computing
     `(f_0^D, ..., f_{n-1}^D)` and `F_D(f) = ∑_{i<n} f_i^D` in `< (104/3) * 8^ℓ` passes.
-/

namespace Catalytic

@[expose] public section

universe u

/-! ## 1. Concrete 3-Work-Register Model, Cyclic Permutation, Inversion, and Composition -/

/--
A literal Definition 2.2 instruction on 3 work registers `(r0, r1, r2)` over a commutative ring `R`:
  * `addX dst c`:        `r_dst ← r_dst + c * x`                             (1 input access)
  * `addPoly dst terms`: `r_dst ← r_dst + evalBivar r_other1 r_other2 terms` (0 input accesses)
where `(other1, other2)` are the other two registers in cyclic order:
  `dst = 0 ↦ (r1, r2)`, `dst = 1 ↦ (r2, r0)`, `dst = 2 ↦ (r0, r1)`.
By construction, `r_dst` NEVER appears on the right-hand side of any instruction.
-/
inductive Work3Instr (R : Type u) where
  | addX (dst : Fin 3) (c : R) : Work3Instr R
  | addPoly (dst : Fin 3) (terms : List (Nat × Nat × R)) : Work3Instr R

/-- Count input accesses in a 3-work-register program. -/
def Work3Prog.accesses {R : Type u} : List (Work3Instr R) → Nat
  | [] => 0
  | .addX _ _ :: rest => 1 + Work3Prog.accesses rest
  | .addPoly _ _ :: rest => Work3Prog.accesses rest

theorem Work3Prog.accesses_append {R : Type u} (p q : List (Work3Instr R)) :
    Work3Prog.accesses (p ++ q) = Work3Prog.accesses p + Work3Prog.accesses q := by
  induction p with
  | nil => simp [Work3Prog.accesses]
  | cons i rest ih =>
    cases i <;> simp [Work3Prog.accesses, ih, Nat.add_assoc]

/-- Execute one `Work3Instr` on `(r0, r1, r2)`. -/
def Work3Instr.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) :
    Work3Instr R → R × R × R
  | .addX dst c =>
    match dst.val with
    | 0 => (st.1 + c * x, st.2.1, st.2.2)
    | 1 => (st.1, st.2.1 + c * x, st.2.2)
    | _ => (st.1, st.2.1, st.2.2 + c * x)
  | .addPoly dst terms =>
    match dst.val with
    | 0 => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
    | 1 => (st.1, st.2.1 + evalBivar st.2.2 st.1 terms, st.2.2)
    | _ => (st.1, st.2.1, st.2.2 + evalBivar st.1 st.2.1 terms)

/-- Execute a `Work3Prog` left-to-right on `(r0, r1, r2)`. -/
def Work3Prog.exec {R : Type u} [CRing R] (x : R) :
    List (Work3Instr R) → (R × R × R) → (R × R × R)
  | [], st => st
  | i :: rest, st => Work3Prog.exec x rest (i.exec x st)

theorem Work3Prog.exec_append {R : Type u} [CRing R] (x : R)
    (p q : List (Work3Instr R)) (st : R × R × R) :
    Work3Prog.exec x (p ++ q) st = Work3Prog.exec x q (Work3Prog.exec x p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih => exact ih (i.exec x st)

/-- Cyclically rotate register indices by `k` mod 3. -/
def rotFin3 (k : Nat) (d : Fin 3) : Fin 3 :=
  ⟨(d.val + k) % 3, Nat.mod_lt _ (by decide)⟩

/-- Cyclically shift all register targets of a `Work3Instr` by `k` mod 3. -/
def Work3Instr.shiftReg {R : Type u} (k : Nat) : Work3Instr R → Work3Instr R
  | .addX dst c => .addX (rotFin3 k dst) c
  | .addPoly dst terms => .addPoly (rotFin3 k dst) terms

/-- Build a program that adds the given shift to the designated working register. -/
def Work3Prog.shiftReg {R : Type u} (k : Nat) (p : List (Work3Instr R)) : List (Work3Instr R) :=
  p.map (Work3Instr.shiftReg k)

theorem Work3Prog.shiftReg_accesses {R : Type u} (k : Nat) (p : List (Work3Instr R)) :
    Work3Prog.accesses (Work3Prog.shiftReg k p) = Work3Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    cases i <;>
      exact (by
        change Work3Prog.accesses (Work3Instr.shiftReg k _ :: Work3Prog.shiftReg k rest) = _
        simp only [Work3Instr.shiftReg, Work3Prog.accesses, ih])

/-- Cyclic state rotation: moving `(r0, r1, r2)` to place `r0` into slot `k mod 3`. -/
def rotState {R : Type u} (k : Nat) (st : R × R × R) : R × R × R :=
  match k % 3 with
  | 0 => (st.1, st.2.1, st.2.2)
  | 1 => (st.2.2, st.1, st.2.1)
  | _ => (st.2.1, st.2.2, st.1)

theorem Work3Instr.exec_shiftReg {R : Type u} [CRing R] (k : Nat) (x : R)
    (i : Work3Instr R) (st : R × R × R) :
    (i.shiftReg k).exec x (rotState k st) = rotState k (i.exec x st) := by
  cases i with
  | addX dst c =>
    rcases dst with ⟨d, hd⟩
    have hdk : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    have hkm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hdk with rfl | rfl | rfl <;> rcases hkm with hk | hk | hk <;>
      simp [Work3Instr.shiftReg, rotFin3, Work3Instr.exec, rotState, Nat.add_mod, hk]
  | addPoly dst terms =>
    rcases dst with ⟨d, hd⟩
    have hdk : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    have hkm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hdk with rfl | rfl | rfl <;> rcases hkm with hk | hk | hk <;>
      simp [Work3Instr.shiftReg, rotFin3, Work3Instr.exec, rotState, Nat.add_mod, hk]

theorem Work3Prog.exec_shiftReg {R : Type u} [CRing R] (k : Nat) (x : R)
    (p : List (Work3Instr R)) (st : R × R × R) :
    Work3Prog.exec x (Work3Prog.shiftReg k p) (rotState k st) = rotState k (Work3Prog.exec x p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    change Work3Prog.exec x (Work3Prog.shiftReg k rest) ((i.shiftReg k).exec x (rotState k st)) = _
    rw [Work3Instr.exec_shiftReg, ih]
    rfl

/-- Shifted execution of a clean `r0`-targeting program targets `dst` while restoring the other two registers. -/
theorem Work3Prog.exec_shiftReg_clean {R : Type u} [CRing R] (dst : Fin 3) (x Δ : R)
    (q : List (Work3Instr R))
    (hq : ∀ a b c : R, Work3Prog.exec x q (a, b, c) = (a + Δ, b, c))
    (st : R × R × R) :
    Work3Prog.exec x (Work3Prog.shiftReg dst.val q) st =
      match dst.val with
      | 0 => (st.1 + Δ, st.2.1, st.2.2)
      | 1 => (st.1, st.2.1 + Δ, st.2.2)
      | _ => (st.1, st.2.1, st.2.2 + Δ) := by
  rcases st with ⟨r0, r1, r2⟩
  rcases dst with ⟨d, hd⟩
  have hdv : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hdv with rfl | rfl | rfl
  · have h := Work3Prog.exec_shiftReg 0 x q (r0, r1, r2)
    simpa [rotState, hq] using h
  · have h := Work3Prog.exec_shiftReg 1 x q (r1, r2, r0)
    simpa [rotState, hq] using h
  · have h := Work3Prog.exec_shiftReg 2 x q (r2, r0, r1)
    simpa [rotState, hq] using h

/-- Negate a single `Work3Instr` (exact two-sided inverse because `r_dst` is never on the RHS). -/
def Work3Instr.neg {R : Type u} [CRing R] : Work3Instr R → Work3Instr R
  | .addX dst c => .addX dst (-c)
  | .addPoly dst terms => .addPoly dst (terms.map fun (a, b, c) => (a, b, -c))

/-- Exact inverse of any `Work3Prog`. -/
def Work3Prog.invert {R : Type u} [CRing R] (p : List (Work3Instr R)) : List (Work3Instr R) :=
  (p.map Work3Instr.neg).reverse

private theorem evalBivar_neg {R : Type u} [CRing R] (u v : R) (terms : List (Nat × Nat × R)) :
    evalBivar u v (terms.map fun (a, b, c) => (a, b, -c)) = -(evalBivar u v terms) := by
  induction terms with
  | nil => simp [evalBivar]
  | cons hd tl ih =>
    rcases hd with ⟨a, b, c⟩
    simp only [List.map, evalBivar, ih, CRing.neg_mul, CRing.neg_add_rev]

theorem Work3Instr.exec_neg_cancel {R : Type u} [CRing R] (x : R)
    (i : Work3Instr R) (st : R × R × R) :
    i.neg.exec x (i.exec x st) = st := by
  rcases st with ⟨r0, r1, r2⟩
  cases i with
  | addX dst c =>
    rcases dst with ⟨d, hd⟩
    have hdv : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hdv with rfl | rfl | rfl <;>
      simp [Work3Instr.neg, Work3Instr.exec, CRing.neg_mul, CRing.add_assoc, CRing.add_neg]
  | addPoly dst terms =>
    rcases dst with ⟨d, hd⟩
    have hdv : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hdv with rfl | rfl | rfl <;>
      simp [Work3Instr.neg, Work3Instr.exec, evalBivar_neg, CRing.add_assoc, CRing.add_neg]

theorem Work3Prog.invert_accesses {R : Type u} [CRing R] (p : List (Work3Instr R)) :
    Work3Prog.accesses (Work3Prog.invert p) = Work3Prog.accesses p := by
  unfold Work3Prog.invert
  induction p with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.reverse_cons, Work3Prog.accesses_append, ih]
    cases i <;> simp [Work3Instr.neg, Work3Prog.accesses, Nat.add_comm]

theorem Work3Prog.exec_invert_cancel {R : Type u} [CRing R] (x : R)
    (p : List (Work3Instr R)) (st : R × R × R) :
    Work3Prog.exec x (Work3Prog.invert p) (Work3Prog.exec x p st) = st := by
  unfold Work3Prog.invert
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.reverse_cons, Work3Prog.exec, Work3Prog.exec_append]
    rw [ih (i.exec x st)]
    exact Work3Instr.exec_neg_cancel x i st

theorem Work3Prog.exec_invert_clean {R : Type u} [CRing R] (x Δ : R)
    (p : List (Work3Instr R))
    (hp : ∀ a b c : R, Work3Prog.exec x p (a, b, c) = (a + Δ, b, c))
    (a b c : R) :
    Work3Prog.exec x (Work3Prog.invert p) (a, b, c) = (a + (-Δ), b, c) := by
  have h1 : (a, b, c) = Work3Prog.exec x p (a + (-Δ), b, c) := by
    rw [hp]
    congr 1
    rw [CRing.add_assoc, CRing.neg_add, CRing.add_zero]
  conv => lhs; rw [h1]
  exact Work3Prog.exec_invert_cancel x p (a + (-Δ), b, c)

/-- Embed any `Pass3InstrR R` verbatim into `Work3Instr R` (`O = r0, u = r1, v = r2`). -/
def Pass3InstrR.toWork3 {R : Type u} : Pass3InstrR R → Work3Instr R
  | .addOut terms => .addPoly ⟨0, by decide⟩ terms
  | .addWorkV c d => .addPoly ⟨2, by decide⟩ [(0, d, c)]
  | .addInputU α => .addX ⟨1, by decide⟩ α

/-- Relabel the three-register program so that all of its registers are work registers. -/
def Pass3Prog.toWork3 {R : Type u} (p : List (Pass3InstrR R)) : List (Work3Instr R) :=
  p.map Pass3InstrR.toWork3

theorem Pass3Prog.toWork3_accesses {R : Type u} (p : List (Pass3InstrR R)) :
    Work3Prog.accesses (Pass3Prog.toWork3 p) = Pass3Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    cases i <;>
      exact (by
        change Work3Prog.accesses (Pass3InstrR.toWork3 _ :: Pass3Prog.toWork3 rest) = _
        simp only [Pass3InstrR.toWork3, Work3Prog.accesses, Pass3Prog.accesses, ih])

theorem Pass3Prog.toWork3_exec {R : Type u} [CRing R] (x : R)
    (p : List (Pass3InstrR R)) (st : R × R × R) :
    Work3Prog.exec x (Pass3Prog.toWork3 p) st = Pass3Prog.exec x p st := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | addOut terms => exact ih _
    | addInputU α => exact ih _
    | addWorkV c d =>
      have hstep :
          (Pass3InstrR.toWork3 (.addWorkV c d)).exec x st = (Pass3InstrR.addWorkV c d).exec x st := by
        simp [Pass3InstrR.toWork3, Work3Instr.exec, Pass3InstrR.exec, evalBivar, CRing.one_mul]
      change Work3Prog.exec x (Pass3Prog.toWork3 rest) ((Pass3InstrR.toWork3 (.addWorkV c d)).exec x st) = _
      rw [hstep]
      exact ih _

/--
**Clean Non-Passive 3-Register Composition (Alekseev et al., Composition Lemma / Lemma 2.1 in `arXiv:2504.17412v1`):**
Substitute a scalable clean 3-register block `Q : R → List (Work3Instr R)` into every input
access of `P`, reusing the other two registers catalytically.
-/
def Work3Prog.compose {R : Type u} (P : List (Work3Instr R)) (Q : R → List (Work3Instr R)) :
    List (Work3Instr R) :=
  P.flatMap fun
    | .addX dst c => Work3Prog.shiftReg dst.val (Q c)
    | .addPoly dst terms => [.addPoly dst terms]

theorem Work3Prog.compose_accesses {R : Type u} (P : List (Work3Instr R))
    (Q : R → List (Work3Instr R)) (tQ : Nat) (hQ : ∀ c, Work3Prog.accesses (Q c) = tQ) :
    Work3Prog.accesses (Work3Prog.compose P Q) = Work3Prog.accesses P * tQ := by
  induction P with
  | nil => simp [Work3Prog.compose, Work3Prog.accesses]
  | cons i rest ih =>
    cases i with
    | addX dst c =>
      change Work3Prog.accesses (Work3Prog.shiftReg dst.val (Q c) ++ Work3Prog.compose rest Q) = _
      rw [Work3Prog.accesses_append, Work3Prog.shiftReg_accesses, hQ c, ih]
      simp only [Work3Prog.accesses, Nat.add_mul, Nat.one_mul]
    | addPoly dst terms =>
      change Work3Prog.accesses ([Work3Instr.addPoly dst terms] ++ Work3Prog.compose rest Q) = _
      rw [Work3Prog.accesses_append, ih]
      simp [Work3Prog.accesses]

theorem Work3Prog.compose_exec {R : Type u} [CRing R] (x gx : R)
    (P : List (Work3Instr R)) (Q : R → List (Work3Instr R))
    (hQ : ∀ c a b d : R, Work3Prog.exec x (Q c) (a, b, d) = (a + c * gx, b, d))
    (st : R × R × R) :
    Work3Prog.exec x (Work3Prog.compose P Q) st = Work3Prog.exec gx P st := by
  induction P generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | addX dst c =>
      change Work3Prog.exec x (Work3Prog.shiftReg dst.val (Q c) ++ Work3Prog.compose rest Q) st = _
      rw [Work3Prog.exec_append, Work3Prog.exec_shiftReg_clean dst x (c * gx) (Q c) (hQ c) st]
      exact ih _
    | addPoly dst terms =>
      change Work3Prog.exec x ([Work3Instr.addPoly dst terms] ++ Work3Prog.compose rest Q) st = _
      rw [Work3Prog.exec_append]
      exact ih _

/-- Iterated `i`-fold non-passive 3-register composition `P ∘ Q^{∘ i}` staying strictly in 3 work registers. -/
def Work3Prog.composePow {R : Type u} : Nat → List (Work3Instr R) → (R → List (Work3Instr R)) → List (Work3Instr R)
  | 0, P, _ => P
  | i + 1, P, Q => Work3Prog.compose (Work3Prog.composePow i P Q) Q

theorem Work3Prog.composePow_accesses {R : Type u} (i : Nat) (P : List (Work3Instr R))
    (Q : R → List (Work3Instr R)) (tQ : Nat) (hQ : ∀ c, Work3Prog.accesses (Q c) = tQ) :
    Work3Prog.accesses (Work3Prog.composePow i P Q) = Work3Prog.accesses P * tQ ^ i := by
  induction i with
  | zero => simp [Work3Prog.composePow]
  | succ m ih =>
    simp only [Work3Prog.composePow, Work3Prog.compose_accesses _ Q tQ hQ, ih, Nat.pow_succ, Nat.mul_assoc]

theorem Work3Prog.composePow_exec {R : Type u} [CRing R] (δ i : Nat) (x : R)
    (P : List (Work3Instr R)) (Q : R → List (Work3Instr R))
    (hQ : ∀ c y a b d : R, Work3Prog.exec y (Q c) (a, b, d) = (a + c * CRing.pow y δ, b, d))
    (st : R × R × R) :
    Work3Prog.exec x (Work3Prog.composePow i P Q) st = Work3Prog.exec (CRing.pow x (δ ^ i)) P st := by
  induction i generalizing x st with
  | zero => simp [Work3Prog.composePow]
  | succ m ih =>
    simp only [Work3Prog.composePow]
    rw [Work3Prog.compose_exec x (CRing.pow x δ) _ Q (fun c a b d => hQ c x a b d) st]
    rw [ih (CRing.pow x δ) st, ← CRing.pow_mul, Nat.pow_succ, Nat.mul_comm]

/-! ## 2. Exact 2-Register Forward-Difference Digit Programs (`x^b` in `≤ b + 1` Accesses) -/

private theorem intCast_sumInt {R : Type u} [CRing R] (n : Nat) (f : Nat → Int) :
    (CRing.intCast (sumInt n f) : R) = sumR n (fun i => CRing.intCast (f i)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumInt_succ, CRing.intCast_add, ih, sumR_succ]

private theorem intCast_pow_nat {R : Type u} [CRing R] (a k : Nat) :
    (CRing.intCast ((a : Int) ^ k) : R) = CRing.pow (CRing.natCast a) k := by
  rw [← Int.natCast_pow, CRing.intCast_natCast, natCast_pow]

/-- Forward-difference loop for `a = 0, ..., m`: visits shifts `r1 + a * x` and adds `w(a) * r1^b` to `r0`. -/
def diffLoop {R : Type u} [CRing R] (b : Nat) (invFact : R) : Nat → List (Work3Instr R)
  | 0 =>
    [.addPoly ⟨0, by decide⟩ [(b, 0, invFact * CRing.intCast (altSign b * (choose b 0 : Int)))]]
  | m + 1 =>
    diffLoop b invFact m ++
    [.addX ⟨1, by decide⟩ 1,
     .addPoly ⟨0, by decide⟩
       [(b, 0, invFact * CRing.intCast (altSign (b - (m + 1)) * (choose b (m + 1) : Int)))]]

/-- 2-register clean program computing `r0 ← r0 + x^b` in at most `b + 1` accesses (`0` accesses if `b = 0`). -/
def digitPowProg {R : Type u} [CRing R] (b : Nat) (invFact : R) : List (Work3Instr R) :=
  if b = 0 then
    [.addPoly ⟨0, by decide⟩ [(0, 0, 1)]]
  else
    diffLoop b invFact b ++ [.addX ⟨1, by decide⟩ (-(CRing.natCast b))]

private theorem diffLoop_accesses {R : Type u} [CRing R] (b : Nat) (invFact : R) (m : Nat) :
    Work3Prog.accesses (diffLoop b invFact m) = m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp [diffLoop, Work3Prog.accesses_append, Work3Prog.accesses, ih]

theorem digitPowProg_accesses_le {R : Type u} [CRing R] (b : Nat) (invFact : R) :
    Work3Prog.accesses (digitPowProg b invFact) ≤ b + 1 := by
  unfold digitPowProg
  by_cases hb : b = 0
  · subst hb; simp [Work3Prog.accesses]
  · simp [hb, Work3Prog.accesses_append, diffLoop_accesses, Work3Prog.accesses]

private theorem diffLoop_exec {R : Type u} [CRing R] (b : Nat) (invFact x o u v : R) (m : Nat) :
    Work3Prog.exec x (diffLoop b invFact m) (o, u, v) =
      (o + sumR (m + 1) (fun a =>
             invFact * CRing.intCast (altSign (b - a) * (choose b a : Int)) *
               CRing.pow (u + CRing.natCast a * x) b),
       u + CRing.natCast m * x, v) := by
  induction m with
  | zero =>
    simp [diffLoop, Work3Prog.exec, Work3Instr.exec, evalBivar, sumR,
          CRing.zero_add, CRing.mul_one, CRing.zero_mul]
  | succ k ih =>
    simp only [diffLoop, Work3Prog.exec_append, ih, Work3Prog.exec, Work3Instr.exec, evalBivar]
    have hu : u + CRing.natCast k * x + 1 * x = u + CRing.natCast (k + 1) * x := by
      rw [CRing.one_mul, CRing.add_assoc]
      congr 1
      simp only [CRing.natCast, CRing.right_distrib, CRing.one_mul]
    rw [hu, sumR_succ (k + 1)]
    simp [CRing.mul_one, CRing.add_assoc]

theorem digitPowProg_clean {R : Type u} [CRing R] (b : Nat) (invFact : R)
    (hinv : invFact * CRing.natCast (fact b) = 1) (x o u v : R) :
    Work3Prog.exec x (digitPowProg b invFact) (o, u, v) = (o + CRing.pow x b, u, v) := by
  unfold digitPowProg
  by_cases hb : b = 0
  · subst hb
    simp [Work3Prog.exec, Work3Instr.exec, evalBivar, CRing.pow]
  · simp only [hb, ↓reduceIte, Work3Prog.exec_append, diffLoop_exec, Work3Prog.exec, Work3Instr.exec]
    have hr1 : u + CRing.natCast b * x + -(CRing.natCast b) * x = u := by
      rw [CRing.neg_mul, CRing.add_assoc, CRing.add_neg, CRing.add_zero]
    rw [hr1]
    have hsum :
        sumR (b + 1) (fun a =>
          invFact * CRing.intCast (altSign (b - a) * (choose b a : Int)) *
            CRing.pow (u + CRing.natCast a * x) b) =
        CRing.pow x b := by
      have hexp : ∀ a < b + 1,
          invFact * CRing.intCast (altSign (b - a) * (choose b a : Int)) *
            CRing.pow (u + CRing.natCast a * x) b =
          sumR (b + 1) (fun j =>
            invFact * CRing.natCast (choose b j) *
              (CRing.intCast (altSign (b - a) * (choose b a : Int) * (a : Int) ^ j)) *
              (CRing.pow x j * CRing.pow u (b - j))) := by
        intro a _
        rw [CRing.add_comm u (CRing.natCast a * x), CRing.add_pow (CRing.natCast a * x) u b]
        rw [← sumR_mul_left]
        refine sumR_congr (fun j _ => ?_)
        conv => rhs; rw [CRing.intCast_mul, intCast_pow_nat]
        rw [CRing.mul_pow]
        let W : R := CRing.intCast (altSign (b - a) * (choose b a : Int))
        let C : R := CRing.natCast (choose b j)
        let A : R := CRing.pow (CRing.natCast a) j
        let X : R := CRing.pow x j
        let U : R := CRing.pow u (b - j)
        change invFact * W * (C * (A * X * U)) = invFact * C * (W * A) * (X * U)
        calc
          invFact * W * (C * (A * X * U))
              = invFact * (W * (C * (A * (X * U)))) := by
                rw [CRing.mul_assoc invFact W, CRing.mul_assoc A X U]
          _   = invFact * (C * (W * (A * (X * U)))) := by
                rw [← CRing.mul_assoc W C, CRing.mul_comm W C, CRing.mul_assoc C W]
          _   = (invFact * C) * ((W * A) * (X * U)) := by
                rw [← CRing.mul_assoc invFact C, ← CRing.mul_assoc W A]
          _   = invFact * C * (W * A) * (X * U) := (CRing.mul_assoc _ _ _).symm
      rw [sumR_congr hexp, sumR_swap]
      have hinner : ∀ j < b + 1,
          sumR (b + 1) (fun a =>
            invFact * CRing.natCast (choose b j) *
              CRing.intCast (altSign (b - a) * (choose b a : Int) * (a : Int) ^ j) *
              (CRing.pow x j * CRing.pow u (b - j))) =
          if j = b then CRing.pow x b else 0 := by
        intro j hj
        rw [sumR_mul_right, sumR_mul_left, ← intCast_sumInt]
        have hid :
            sumInt (b + 1) (fun a => altSign (b - a) * (choose b a : Int) * (a : Int) ^ j) =
            iterDiff b (fun y => (y : Int) ^ j) 0 := by
          rw [iterDiff_eq_sum]
          refine sumInt_congr (fun a _ => ?_)
          simp
        rw [hid]
        by_cases hjb : j = b
        · subst hjb
          have htop := (iterDiff_pow j j 0).2 rfl
          rw [htop, choose_self, CRing.natCast_one, CRing.mul_one, CRing.intCast_natCast,
              hinv, CRing.one_mul, Nat.sub_self, CRing.pow_zero, CRing.mul_one]
          simp
        · have hlt : j < b := by omega
          have hzero := (iterDiff_pow j b 0).1 hlt
          rw [hzero]
          simp [hjb]
      rw [sumR_congr hinner]
      exact sumR_single (Nat.lt_succ_self b) (CRing.pow x b)
    rw [hsum]

/-! ## 3. Literal 4-Register Passive Model and Cook–Mertz Finite-Difference Product -/

/--
A literal Definition 2.2 passive-output 4-register instruction on `(O, U, R1, R2)` over `R`:
  * `work w`:             executes `w : Work3Instr R` on `(U, R1, R2)` (never touches or reads `O`)
  * `outAddPow coeff d`:  `O ← O + coeff * U^d` (passive output update; 0 accesses)
By construction, `O` NEVER appears on the right-hand side of any instruction.
-/
inductive Pass4Instr (R : Type u) where
  | work (w : Work3Instr R) : Pass4Instr R
  | outAddPow (coeff : R) (deg : Nat) : Pass4Instr R

/-- Count input accesses in a 4-register passive program. -/
def Pass4Prog.accesses {R : Type u} : List (Pass4Instr R) → Nat
  | [] => 0
  | .work w :: rest => Work3Prog.accesses [w] + Pass4Prog.accesses rest
  | .outAddPow _ _ :: rest => Pass4Prog.accesses rest

theorem Pass4Prog.accesses_append {R : Type u} (p q : List (Pass4Instr R)) :
    Pass4Prog.accesses (p ++ q) = Pass4Prog.accesses p + Pass4Prog.accesses q := by
  induction p with
  | nil => simp [Pass4Prog.accesses]
  | cons i rest ih =>
    cases i <;> simp [Pass4Prog.accesses, ih, Nat.add_assoc]

theorem Pass4Prog.accesses_map_work {R : Type u} (p : List (Work3Instr R)) :
    Pass4Prog.accesses (p.map Pass4Instr.work) = Work3Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons w rest ih =>
    cases w <;> simp [Pass4Prog.accesses, Work3Prog.accesses, ih]

/-- Execute one `Pass4Instr` on `(O, U, R1, R2)`. -/
def Pass4Instr.exec {R : Type u} [CRing R] (x : R) (st : R × R × R × R) :
    Pass4Instr R → R × R × R × R
  | .work w =>
    let w' := w.exec x st.2
    (st.1, w'.1, w'.2.1, w'.2.2)
  | .outAddPow coeff d =>
    (st.1 + coeff * CRing.pow st.2.1 d, st.2.1, st.2.2.1, st.2.2.2)

/-- Execute a `Pass4Prog` left-to-right on `(O, U, R1, R2)`. -/
def Pass4Prog.exec {R : Type u} [CRing R] (x : R) :
    List (Pass4Instr R) → (R × R × R × R) → (R × R × R × R)
  | [], st => st
  | i :: rest, st => Pass4Prog.exec x rest (i.exec x st)

theorem Pass4Prog.exec_append {R : Type u} [CRing R] (x : R)
    (p q : List (Pass4Instr R)) (st : R × R × R × R) :
    Pass4Prog.exec x (p ++ q) st = Pass4Prog.exec x q (Pass4Prog.exec x p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih => exact ih (i.exec x st)

theorem Pass4Prog.exec_map_work {R : Type u} [CRing R] (x : R)
    (p : List (Work3Instr R)) (o : R) (wst : R × R × R) :
    Pass4Prog.exec x (p.map Pass4Instr.work) (o, wst.1, wst.2.1, wst.2.2) =
      let w' := Work3Prog.exec x p wst
      (o, w'.1, w'.2.1, w'.2.2) := by
  induction p generalizing wst with
  | nil => rfl
  | cons w rest ih => exact ih (w.exec x wst)

/-- Product of a list of ring elements. -/
def listProdR {R : Type u} [CRing R] : List R → R
  | [] => 1
  | y :: rest => y * listProdR rest

/-- Iterated multivariate finite difference `Δ_{y_1} ⋯ Δ_{y_m} (u ↦ f u)` over any `CRing R`. -/
def multiDiff {R : Type u} [CRing R] : List R → (R → R) → R → R
  | [], f, u => f u
  | y :: rest, f, u => multiDiff rest f (u + y) + -(multiDiff rest f u)

theorem multiDiff_add {R : Type u} [CRing R] (ys : List R) (f g : R → R) (u : R) :
    multiDiff ys (fun z => f z + g z) u = multiDiff ys f u + multiDiff ys g u := by
  induction ys generalizing u with
  | nil => rfl
  | cons y rest ih =>
    simp only [multiDiff, ih, CRing.neg_add_rev]
    let A := multiDiff rest f (u + y)
    let B := multiDiff rest g (u + y)
    let C := -(multiDiff rest f u)
    let D := -(multiDiff rest g u)
    change (A + B) + (C + D) = (A + C) + (B + D)
    calc
      (A + B) + (C + D) = A + (B + (C + D)) := CRing.add_assoc _ _ _
      _ = A + ((B + C) + D) := by rw [← CRing.add_assoc B C D]
      _ = A + ((C + B) + D) := by rw [CRing.add_comm B C]
      _ = A + (C + (B + D)) := by rw [CRing.add_assoc C B D]
      _ = (A + C) + (B + D) := (CRing.add_assoc _ _ _).symm

theorem multiDiff_const_mul {R : Type u} [CRing R] (ys : List R) (c : R) (f : R → R) (u : R) :
    multiDiff ys (fun z => c * f z) u = c * multiDiff ys f u := by
  induction ys generalizing u with
  | nil => rfl
  | cons y rest ih =>
    simp only [multiDiff, ih, CRing.left_distrib, CRing.mul_neg]

theorem multiDiff_zero {R : Type u} [CRing R] (ys : List R) (u : R) :
    multiDiff ys (fun _ => (0 : R)) u = 0 := by
  induction ys generalizing u with
  | nil => rfl
  | cons y rest ih => simp [multiDiff, ih]

theorem multiDiff_sumR {R : Type u} [CRing R] (ys : List R) (n : Nat) (F : Nat → R → R) (u : R) :
    multiDiff ys (fun z => sumR n (fun j => F j z)) u =
      sumR n (fun j => multiDiff ys (fun z => F j z) u) := by
  induction n with
  | zero => exact multiDiff_zero ys u
  | succ m ih =>
    change multiDiff ys (fun z => sumR m (fun j => F j z) + F m z) u = _
    rw [multiDiff_add, ih, sumR_succ]

theorem multiDiff_comm_head {R : Type u} [CRing R] (y : R) (ys : List R) (f : R → R) (u : R) :
    multiDiff (y :: ys) f u = multiDiff ys (fun z => f (z + y) + -(f z)) u := by
  induction ys generalizing u with
  | nil => rfl
  | cons y' rest ih =>
    have h1 : multiDiff (y' :: rest) f (u + y) + -(multiDiff (y' :: rest) f u) =
        multiDiff (y :: rest) f (u + y') + -(multiDiff (y :: rest) f u) := by
      simp only [multiDiff]
      have hcomm : (u + y) + y' = (u + y') + y := by
        rw [CRing.add_assoc, CRing.add_comm y y', ← CRing.add_assoc]
      rw [hcomm]
      let A := multiDiff rest f ((u + y') + y)
      let B := multiDiff rest f (u + y)
      let C := multiDiff rest f (u + y')
      let D := multiDiff rest f u
      change (A + -B) + -(C + -D) = (A + -C) + -(B + -D)
      rw [CRing.neg_add_rev, CRing.neg_neg, CRing.neg_add_rev, CRing.neg_neg]
      calc
        (A + -B) + (-C + D)
            = A + ((-B + -C) + D) := by rw [CRing.add_assoc, ← CRing.add_assoc (-B)]
        _   = A + ((-C + -B) + D) := by rw [CRing.add_comm (-B) (-C)]
        _   = (A + -C) + (-B + D) := by rw [CRing.add_assoc (-C), ← CRing.add_assoc A]
    change multiDiff (y' :: rest) f (u + y) + -(multiDiff (y' :: rest) f u) =
      multiDiff rest (fun z => f (z + y) + -(f z)) (u + y') +
      -(multiDiff rest (fun z => f (z + y) + -(f z)) u)
    rw [h1, ih (u + y'), ih u]

private theorem choose_succ_self_pred (n : Nat) : choose (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [choose, ih, choose_self]

/--
**Cook–Mertz Multivariate Finite-Difference Product Identity over ANY `CRing R`:**
  * `k < ys.length  ⇒  multiDiff ys (u ↦ u^k) u = 0`
  * `k = ys.length  ⇒  multiDiff ys (u ↦ u^k) u = (k!) * ∏_{y ∈ ys} y`.
-/
theorem multiDiff_pow {R : Type u} [CRing R] (ys : List R) :
    ∀ (k : Nat) (u : R),
      (k < ys.length → multiDiff ys (fun z => CRing.pow z k) u = 0) ∧
      (k = ys.length → multiDiff ys (fun z => CRing.pow z k) u =
        CRing.natCast (fact k) * listProdR ys) := by
  induction ys with
  | nil =>
    intro k u
    constructor
    · intro h; simp at h
    · intro hk; simp at hk; subst hk; simp [multiDiff, fact, listProdR]
  | cons y rest ih =>
    intro k u
    cases k with
    | zero =>
      constructor
      · intro _
        rw [multiDiff_comm_head]
        have hfn : (fun z : R => CRing.pow (z + y) 0 + -(CRing.pow z 0)) = fun _ => 0 := by
          funext _; simp [CRing.pow, CRing.add_neg]
        rw [hfn]
        exact multiDiff_zero rest u
      · intro h; simp at h
    | succ k' =>
      have hdiff : ∀ z : R,
          CRing.pow (z + y) (k' + 1) + -(CRing.pow z (k' + 1)) =
          sumR (k' + 1) (fun j => (CRing.natCast (choose (k' + 1) j) * CRing.pow y (k' + 1 - j)) * CRing.pow z j) := by
        intro z
        rw [CRing.add_pow z y (k' + 1), sumR_succ (k' + 1)]
        have htop :
            CRing.natCast (choose (k' + 1) (k' + 1)) * (CRing.pow z (k' + 1) * CRing.pow y (k' + 1 - (k' + 1))) =
            CRing.pow z (k' + 1) := by
          simp [CRing.one_mul]
        rw [htop, CRing.add_assoc, CRing.add_neg, CRing.add_zero]
        refine sumR_congr (fun j _ => ?_)
        calc
          CRing.natCast (choose (k' + 1) j) * (CRing.pow z j * CRing.pow y (k' + 1 - j))
              = CRing.natCast (choose (k' + 1) j) * (CRing.pow y (k' + 1 - j) * CRing.pow z j) := by
                rw [CRing.mul_comm (CRing.pow z j)]
          _   = (CRing.natCast (choose (k' + 1) j) * CRing.pow y (k' + 1 - j)) * CRing.pow z j :=
                (CRing.mul_assoc _ _ _).symm
      have hstep :
          multiDiff (y :: rest) (fun z => CRing.pow z (k' + 1)) u =
          sumR (k' + 1) (fun j =>
            (CRing.natCast (choose (k' + 1) j) * CRing.pow y (k' + 1 - j)) *
              multiDiff rest (fun z => CRing.pow z j) u) := by
        rw [multiDiff_comm_head]
        have hfun : (fun z : R => CRing.pow (z + y) (k' + 1) + -(CRing.pow z (k' + 1))) =
            (fun z => sumR (k' + 1) (fun j =>
              (CRing.natCast (choose (k' + 1) j) * CRing.pow y (k' + 1 - j)) * CRing.pow z j)) := by
          funext z; exact hdiff z
        rw [hfun, multiDiff_sumR]
        refine sumR_congr (fun j _ => ?_)
        exact multiDiff_const_mul rest _ (fun z => CRing.pow z j) u
      constructor
      · intro hlt
        simp only [List.length_cons] at hlt
        rw [hstep]
        refine sumR_eq_zero (fun j hj => ?_)
        have hz := (ih j u).1 (by omega)
        rw [hz, CRing.mul_zero]
      · intro heq
        simp only [List.length_cons] at heq
        have hkr : k' = rest.length := by omega
        rw [hstep, sumR_succ k']
        have hlow :
            sumR k' (fun j =>
              (CRing.natCast (choose (k' + 1) j) * CRing.pow y (k' + 1 - j)) *
                multiDiff rest (fun z => CRing.pow z j) u) = 0 := by
          refine sumR_eq_zero (fun j hj => ?_)
          have hz := (ih j u).1 (by omega)
          rw [hz, CRing.mul_zero]
        rw [hlow, CRing.zero_add, (ih k' u).2 hkr]
        have hsub : k' + 1 - k' = 1 := by omega
        rw [hsub, choose_succ_self_pred, CRing.pow_one]
        simp only [fact, listProdR, CRing.natCast_mul]
        calc
          (CRing.natCast (k' + 1) * y) * (CRing.natCast (fact k') * listProdR rest)
              = CRing.natCast (k' + 1) * (y * (CRing.natCast (fact k') * listProdR rest)) :=
                CRing.mul_assoc _ _ _
          _   = CRing.natCast (k' + 1) * ((y * CRing.natCast (fact k')) * listProdR rest) := by
                rw [← CRing.mul_assoc y]
          _   = CRing.natCast (k' + 1) * ((CRing.natCast (fact k') * y) * listProdR rest) := by
                rw [CRing.mul_comm y]
          _   = CRing.natCast (k' + 1) * (CRing.natCast (fact k') * (y * listProdR rest)) := by
                rw [CRing.mul_assoc (CRing.natCast (fact k'))]
          _   = (CRing.natCast (k' + 1) * CRing.natCast (fact k')) * (y * listProdR rest) :=
                (CRing.mul_assoc _ _ _).symm

/--
4-register passive Cook–Mertz accumulation program computing `O ← O + scale * multiDiff ys (u ↦ u^m) U`
while restoring `(U, R1, R2)` identically.
-/
def accumProg {R : Type u} [CRing R] (m : Nat) (scale : R) :
    List (List (Work3Instr R)) → List (Pass4Instr R)
  | [] => [.outAddPow scale m]
  | C :: rest =>
    C.map Pass4Instr.work ++
    accumProg m scale rest ++
    (Work3Prog.invert C).map Pass4Instr.work ++
    accumProg m (-scale) rest

theorem accumProg_accesses {R : Type u} [CRing R] (m : Nat) (scale : R)
    (Cs : List (List (Work3Instr R))) :
    Pass4Prog.accesses (accumProg m scale Cs) =
      match Cs with
      | [] => 0
      | C :: rest => 2 * Work3Prog.accesses C + 2 * Pass4Prog.accesses (accumProg m scale rest) := by
  cases Cs with
  | nil => rfl
  | cons C rest =>
    have hneg : ∀ (k : Nat) (s : R) (L : List (List (Work3Instr R))),
        Pass4Prog.accesses (accumProg k (-s) L) = Pass4Prog.accesses (accumProg k s L) := by
      intro k s L
      induction L generalizing s with
      | nil => rfl
      | cons C' rest' ih =>
        simp only [accumProg, Pass4Prog.accesses_append, Pass4Prog.accesses_map_work,
                   Work3Prog.invert_accesses, ih s, ih (-s)]
    simp only [accumProg, Pass4Prog.accesses_append, Pass4Prog.accesses_map_work,
               Work3Prog.invert_accesses, hneg]
    omega

theorem accumProg_exec {R : Type u} [CRing R] (m : Nat) (x : R) :
    ∀ (Cs : List (List (Work3Instr R))) (ys : List R) (scale o u r1 r2 : R),
      Cs.length = ys.length →
      (∀ (idx : Nat) (h1 : idx < Cs.length) (h2 : idx < ys.length) (a b c : R),
        Work3Prog.exec x Cs[idx] (a, b, c) = (a + ys[idx], b, c)) →
      Pass4Prog.exec x (accumProg m scale Cs) (o, u, r1, r2) =
        (o + scale * multiDiff ys (fun z => CRing.pow z m) u, u, r1, r2) := by
  intro Cs
  induction Cs with
  | nil =>
    intro ys scale o u r1 r2 hlen _
    cases ys with
    | nil => simp [accumProg, Pass4Prog.exec, Pass4Instr.exec, multiDiff]
    | cons _ _ => simp at hlen
  | cons C rest ih =>
    intro ys scale o u r1 r2 hlen hclean
    cases ys with
    | nil => simp at hlen
    | cons y yrest =>
      have hlen' : rest.length = yrest.length := by simp at hlen; omega
      have hC : ∀ a b c : R, Work3Prog.exec x C (a, b, c) = (a + y, b, c) :=
        fun a b c => hclean 0 (by simp) (by simp) a b c
      have hrest : ∀ (idx : Nat) (h1 : idx < rest.length) (h2 : idx < yrest.length) (a b c : R),
          Work3Prog.exec x rest[idx] (a, b, c) = (a + yrest[idx], b, c) :=
        fun idx h1 h2 a b c => hclean (idx + 1) (by simp; omega) (by simp; omega) a b c
      simp only [accumProg, Pass4Prog.exec_append]
      rw [Pass4Prog.exec_map_work x C o (u, r1, r2), hC u r1 r2]
      rw [ih yrest scale o (u + y) r1 r2 hlen' hrest]
      rw [Pass4Prog.exec_map_work x (Work3Prog.invert C) _ (u + y, r1, r2),
          Work3Prog.exec_invert_clean x y C hC (u + y) r1 r2]
      have hu : u + y + -y = u := by rw [CRing.add_assoc, CRing.add_neg, CRing.add_zero]
      rw [hu]
      rw [ih yrest (-scale) _ u r1 r2 hlen' hrest]
      simp only [multiDiff, CRing.neg_mul, CRing.left_distrib, CRing.mul_neg, CRing.add_assoc]

/-! ## 4. Base-`δ` Expansion, Exact Access Recurrence, and Complete 4-Register Powering Theorems -/

/-- Base-`δ` digit expansion of `N` (LSB-first: `[b_0, b_1, ..., b_ℓ]` with `0 ≤ b_i < δ`). -/
def baseDigits (δ : Nat) (hδ : 2 ≤ δ) (N : Nat) : List Nat :=
  if _h : N < δ then
    [N]
  else
    (N % δ) :: baseDigits δ hδ (N / δ)
termination_by N
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

/-- Evaluate an LSB-first base-`δ` digit list. -/
def evalBase (δ : Nat) : List Nat → Nat
  | [] => 0
  | b :: rest => b + δ * evalBase δ rest

theorem baseDigits_eval (δ : Nat) (hδ : 2 ≤ δ) (N : Nat) :
    evalBase δ (baseDigits δ hδ N) = N := by
  induction N using nat_strong_ind with
  | _ N ih =>
    unfold baseDigits
    by_cases hlt : N < δ
    · simp [hlt, evalBase]
    · simp only [hlt, ↓reduceDIte, evalBase]
      have hdiv_lt : N / δ < N := Nat.div_lt_self (by omega) (by omega)
      rw [ih (N / δ) hdiv_lt, Nat.add_comm, Nat.div_add_mod]

theorem baseDigits_lt (δ : Nat) (hδ : 2 ≤ δ) (N : Nat) :
    ∀ b ∈ baseDigits δ hδ N, b < δ := by
  induction N using nat_strong_ind with
  | _ N ih =>
    unfold baseDigits
    by_cases hlt : N < δ
    · intro b hb
      simp only [hlt, ↓reduceDIte, List.mem_singleton] at hb
      omega
    · intro b hb
      simp only [hlt, ↓reduceDIte, List.mem_cons] at hb
      rcases hb with rfl | hmem
      · exact Nat.mod_lt N (by omega)
      · exact ih (N / δ) (Nat.div_lt_self (by omega) (by omega)) b hmem

theorem baseDigits_nonempty (δ : Nat) (hδ : 2 ≤ δ) (N : Nat) :
    0 < (baseDigits δ hδ N).length := by
  unfold baseDigits
  by_cases hlt : N < δ <;> simp [hlt]

theorem baseDigits_pow_le (δ : Nat) (hδ : 2 ≤ δ) (N : Nat) (hN : 1 ≤ N) :
    δ ^ ((baseDigits δ hδ N).length - 1) ≤ N := by
  induction N using nat_strong_ind with
  | _ N ih =>
    unfold baseDigits
    by_cases hlt : N < δ
    · simp [hlt]; omega
    · simp only [hlt, ↓reduceDIte, List.length_cons]
      have hq_pos : 1 ≤ N / δ := Nat.div_pos (by omega) (by omega)
      have hq_lt : N / δ < N := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih (N / δ) hq_lt hq_pos
      have hlen_pos := baseDigits_nonempty δ hδ (N / δ)
      have hsub : (baseDigits δ hδ (N / δ)).length + 1 - 1 =
                  ((baseDigits δ hδ (N / δ)).length - 1) + 1 := by omega
      rw [hsub, Nat.pow_succ, Nat.mul_comm]
      have hmul : δ * δ ^ ((baseDigits δ hδ (N / δ)).length - 1) ≤ δ * (N / δ) :=
        Nat.mul_le_mul_left δ hrec
      have hdiv := Nat.div_add_mod N δ
      omega

/-- Exact inverse of `fact b` derived from `invFactM * natCast (fact M) = 1` for any `b ≤ M`. -/
def subFactInv {R : Type u} [CRing R] (M b : Nat) (invFactM : R) : R :=
  invFactM * CRing.natCast (fact M / fact b)

private theorem fact_dvd_fact {b M : Nat} (h : b ≤ M) : fact b ∣ fact M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact Nat.dvd_refl _
  | succ k' ih =>
    have hstep : b + (k' + 1) = (b + k') + 1 := by omega
    rw [hstep, fact]
    exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left _ _)

theorem subFactInv_spec {R : Type u} [CRing R] {M b : Nat} (hb : b ≤ M)
    (invFactM : R) (hinv : invFactM * CRing.natCast (fact M) = 1) :
    subFactInv M b invFactM * CRing.natCast (fact b) = 1 := by
  unfold subFactInv
  rw [CRing.mul_assoc, ← CRing.natCast_mul]
  have hd : fact M / fact b * fact b = fact M := Nat.div_mul_cancel (fact_dvd_fact hb)
  rw [hd, hinv]

/-- Build MSB-first list of clean 3-work-register digit subprograms `[C_ℓ, ..., C_0]` for `N`. -/
def digitSubProgs {R : Type u} [CRing R] (δ : Nat) (invFactPrev : R)
    (baseBlock : R → List (Work3Instr R)) : Nat → List Nat → List (List (Work3Instr R))
  | _, [] => []
  | i, b :: rest =>
    digitSubProgs δ invFactPrev baseBlock (i + 1) rest ++
    [Work3Prog.composePow i (digitPowProg b (subFactInv (δ - 1) b invFactPrev)) baseBlock]

/-- Matching MSB-first list of power values `[x^{b_ℓ * δ^ℓ}, ..., x^{b_0 * δ^0}]`. -/
def digitPowVals {R : Type u} [CRing R] (δ : Nat) (x : R) : Nat → List Nat → List R
  | _, [] => []
  | i, b :: rest =>
    digitPowVals δ x (i + 1) rest ++ [CRing.pow x (b * δ ^ i)]

private theorem listProdR_append {R : Type u} [CRing R] (xs ys : List R) :
    listProdR (xs ++ ys) = listProdR xs * listProdR ys := by
  induction xs with
  | nil => simp [listProdR, CRing.one_mul]
  | cons a rest ih => simp [listProdR, ih, CRing.mul_assoc]

private theorem digitPowVals_prod {R : Type u} [CRing R] (δ : Nat) (x : R) :
    ∀ (i : Nat) (ds : List Nat),
      listProdR (digitPowVals δ x i ds) = CRing.pow x (evalBase δ ds * δ ^ i) := by
  intro i ds
  induction ds generalizing i with
  | nil => simp [digitPowVals, listProdR, evalBase]
  | cons b rest ih =>
    simp only [digitPowVals, listProdR_append, listProdR, CRing.mul_one, ih (i + 1), evalBase]
    rw [← CRing.pow_add]
    congr 1
    have hpow : δ ^ (i + 1) = δ * δ ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, Nat.add_mul, Nat.add_comm]
    congr 1
    rw [← Nat.mul_assoc, Nat.mul_comm (evalBase δ rest) δ, Nat.mul_assoc]

private theorem digitSubProgs_length {R : Type u} [CRing R] (δ : Nat) (invFactPrev : R)
    (baseBlock : R → List (Work3Instr R)) (i : Nat) (ds : List Nat) :
    (digitSubProgs δ invFactPrev baseBlock i ds).length = ds.length := by
  induction ds generalizing i with
  | nil => rfl
  | cons _ rest ih => simp [digitSubProgs, ih]

private theorem digitPowVals_length {R : Type u} [CRing R] (δ : Nat) (x : R) (i : Nat) (ds : List Nat) :
    (digitPowVals δ x i ds).length = ds.length := by
  induction ds generalizing i with
  | nil => rfl
  | cons _ rest ih => simp [digitPowVals, ih]

private theorem digitSubProgs_clean {R : Type u} [CRing R] (δ : Nat) (invFactPrev : R)
    (hinvPrev : invFactPrev * CRing.natCast (fact (δ - 1)) = 1)
    (baseBlock : R → List (Work3Instr R))
    (hBlock : ∀ c y a b d : R, Work3Prog.exec y (baseBlock c) (a, b, d) = (a + c * CRing.pow y δ, b, d))
    (x : R) :
    ∀ (i : Nat) (ds : List Nat), (∀ b ∈ ds, b < δ) →
      ∀ (idx : Nat)
        (h1 : idx < (digitSubProgs δ invFactPrev baseBlock i ds).length)
        (h2 : idx < (digitPowVals δ x i ds).length)
        (a b c : R),
        Work3Prog.exec x (digitSubProgs δ invFactPrev baseBlock i ds)[idx] (a, b, c) =
          (a + (digitPowVals δ x i ds)[idx], b, c) := by
  intro i ds hds
  induction ds generalizing i with
  | nil =>
    intro idx h1; simp [digitSubProgs] at h1
  | cons d rest ih =>
    intro idx h1 h2 a b c
    have hd_lt : d < δ := hds d (List.mem_cons_self ..)
    have hrest_lt : ∀ b' ∈ rest, b' < δ := fun b' hm => hds b' (List.mem_cons_of_mem _ hm)
    simp only [digitSubProgs, digitPowVals] at h1 h2 ⊢
    by_cases hlt : idx < (digitSubProgs δ invFactPrev baseBlock (i + 1) rest).length
    · have hlt2 : idx < (digitPowVals δ x (i + 1) rest).length := by
        rw [digitPowVals_length, ← digitSubProgs_length δ invFactPrev baseBlock (i + 1) rest]
        exact hlt
      rw [List.getElem_append_left hlt, List.getElem_append_left hlt2]
      exact ih (i + 1) hrest_lt idx hlt hlt2 a b c
    · have heq1 : idx = (digitSubProgs δ invFactPrev baseBlock (i + 1) rest).length := by
        simp only [List.length_append, List.length_singleton] at h1
        omega
      have hge1 : (digitSubProgs δ invFactPrev baseBlock (i + 1) rest).length ≤ idx := by omega
      have hge2 : (digitPowVals δ x (i + 1) rest).length ≤ idx := by
        rw [digitPowVals_length, ← digitSubProgs_length δ invFactPrev baseBlock (i + 1) rest]
        exact hge1
      rw [List.getElem_append_right hge1, List.getElem_append_right hge2]
      have hz1 : idx - (digitSubProgs δ invFactPrev baseBlock (i + 1) rest).length = 0 := by omega
      have hz2 : idx - (digitPowVals δ x (i + 1) rest).length = 0 := by
        rw [digitPowVals_length, ← digitSubProgs_length δ invFactPrev baseBlock (i + 1) rest]
        exact hz1
      simp only [hz1, hz2, List.getElem_singleton]
      rw [Work3Prog.composePow_exec δ i x _ baseBlock hBlock (a, b, c)]
      have hdig := digitPowProg_clean d (subFactInv (δ - 1) d invFactPrev)
        (subFactInv_spec (by omega) invFactPrev hinvPrev) (CRing.pow x (δ ^ i)) a b c
      rw [hdig, ← CRing.pow_mul, Nat.mul_comm]

/-- Exact integer geometric-series bound for `accumProg` over `digitSubProgs`. -/
private theorem accumProg_digitSubProgs_bound {R : Type u} [CRing R]
    (δ t m : Nat) (ht : 3 ≤ t) (invFactPrev scale : R)
    (baseBlock : R → List (Work3Instr R))
    (hAcc : ∀ c, Work3Prog.accesses (baseBlock c) = t) :
    ∀ (i : Nat) (ds : List Nat), 0 < ds.length → (∀ b ∈ ds, b < δ) →
      (t - 2) * Pass4Prog.accesses (accumProg m scale (digitSubProgs δ invFactPrev baseBlock i ds)) +
        2 * δ * 2 ^ ds.length * t ^ i ≤
      2 * δ * t * t ^ (i + ds.length - 1) := by
  intro i ds hpos hlt
  induction ds generalizing i with
  | nil => simp at hpos
  | cons d rest ih =>
    have hd_lt : d < δ := hlt d (List.mem_cons_self ..)
    have hrest_lt : ∀ b' ∈ rest, b' < δ := fun b' hm => hlt b' (List.mem_cons_of_mem _ hm)
    cases rest with
    | nil =>
      simp only [digitSubProgs, List.nil_append, accumProg_accesses, List.length_singleton]
      have hq : Work3Prog.accesses
          (Work3Prog.composePow i (digitPowProg d (subFactInv (δ - 1) d invFactPrev)) baseBlock) ≤
          δ * t ^ i := by
        rw [Work3Prog.composePow_accesses i _ baseBlock t hAcc]
        have h1 := digitPowProg_accesses_le d (subFactInv (δ - 1) d invFactPrev)
        exact Nat.mul_le_mul_right (t ^ i) (by omega)
      have hsub : i + 1 - 1 = i := by omega
      rw [hsub]
      have h1 : (t - 2) * (2 * Work3Prog.accesses
          (Work3Prog.composePow i (digitPowProg d (subFactInv (δ - 1) d invFactPrev)) baseBlock)) ≤
          (t - 2) * (2 * (δ * t ^ i)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hq)
      have h2 : (t - 2) * (2 * (δ * t ^ i)) + 2 * δ * 2 ^ 1 * t ^ i = 2 * δ * t * t ^ i := by
        have ht2 : (t - 2) + 2 = t := by omega
        calc
          (t - 2) * (2 * (δ * t ^ i)) + 2 * δ * 2 ^ 1 * t ^ i
              = (t - 2) * (2 * δ * t ^ i) + 2 * (2 * δ * t ^ i) := by
                have e1 : 2 * (δ * t ^ i) = 2 * δ * t ^ i := (Nat.mul_assoc 2 δ _).symm
                have e2 : 2 * δ * 2 ^ 1 * t ^ i = 2 * (2 * δ * t ^ i) := by
                  simp only [Nat.pow_one]
                  rw [Nat.mul_comm (2 * δ) 2, Nat.mul_assoc 2 (2 * δ)]
                rw [e1, e2]
          _   = ((t - 2) + 2) * (2 * δ * t ^ i) := (Nat.add_mul _ _ _).symm
          _   = t * (2 * δ * t ^ i) := by rw [ht2]
          _   = 2 * δ * t * t ^ i := by
                rw [← Nat.mul_assoc, Nat.mul_comm t (2 * δ), Nat.mul_assoc]
      rw [Nat.mul_zero, Nat.add_zero]
      omega
    | cons d2 rest2 =>
      -- Unroll the append of `[C_i]` at the tail of `digitSubProgs (i+1) (d2 :: rest2)`
      have htail_acc : ∀ (L : List (List (Work3Instr R))) (C : List (Work3Instr R)),
          Pass4Prog.accesses (accumProg m scale (L ++ [C])) =
            Pass4Prog.accesses (accumProg m scale L) + 2 ^ L.length * (2 * Work3Prog.accesses C) := by
        intro L C
        induction L with
        | nil => simp [accumProg_accesses]
        | cons hd tl ihL =>
          rw [List.cons_append, accumProg_accesses, accumProg_accesses]
          dsimp only
          rw [ihL, List.length_cons, Nat.pow_succ]
          have e : 2 * (2 ^ tl.length * (2 * Work3Prog.accesses C)) =
                   2 ^ tl.length * 2 * (2 * Work3Prog.accesses C) := by
            rw [Nat.mul_comm (2 ^ tl.length) 2, Nat.mul_assoc]
          rw [Nat.mul_add, e, Nat.add_assoc]
      change (t - 2) * Pass4Prog.accesses (accumProg m scale
          (digitSubProgs δ invFactPrev baseBlock (i + 1) (d2 :: rest2) ++
           [Work3Prog.composePow i (digitPowProg d (subFactInv (δ - 1) d invFactPrev)) baseBlock])) +
        2 * δ * 2 ^ (d :: d2 :: rest2).length * t ^ i ≤
        2 * δ * t * t ^ (i + (d :: d2 :: rest2).length - 1)
      rw [htail_acc, digitSubProgs_length]
      have hrec := ih (i + 1) (by simp) hrest_lt
      have hq : Work3Prog.accesses
          (Work3Prog.composePow i (digitPowProg d (subFactInv (δ - 1) d invFactPrev)) baseBlock) ≤
          δ * t ^ i := by
        rw [Work3Prog.composePow_accesses i _ baseBlock t hAcc]
        have h1 := digitPowProg_accesses_le d (subFactInv (δ - 1) d invFactPrev)
        exact Nat.mul_le_mul_right (t ^ i) (by omega)
      let k := (d2 :: rest2).length
      have hstep1 : i + 1 + k - 1 = i + (k + 1) - 1 := by omega
      rw [hstep1] at hrec
      have hmul_q : (t - 2) * (2 ^ k * (2 * Work3Prog.accesses
          (Work3Prog.composePow i (digitPowProg d (subFactInv (δ - 1) d invFactPrev)) baseBlock))) ≤
          (t - 2) * (2 ^ k * (2 * (δ * t ^ i))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hq))
      have hcancel :
          (t - 2) * (2 ^ k * (2 * (δ * t ^ i))) + 2 * δ * 2 ^ (k + 1) * t ^ i =
          2 * δ * 2 ^ k * t ^ (i + 1) := by
        have ht2 : (t - 2) + 2 = t := by omega
        have e1 : 2 ^ k * (2 * (δ * t ^ i)) = 2 * δ * 2 ^ k * t ^ i := by
          calc
            2 ^ k * (2 * (δ * t ^ i))
                = 2 ^ k * ((2 * δ) * t ^ i) := by rw [Nat.mul_assoc 2 δ]
            _   = (2 ^ k * (2 * δ)) * t ^ i := (Nat.mul_assoc _ _ _).symm
            _   = (2 * δ * 2 ^ k) * t ^ i := by rw [Nat.mul_comm (2 ^ k) (2 * δ)]
        have e2 : 2 * δ * 2 ^ (k + 1) * t ^ i = 2 * (2 * δ * 2 ^ k * t ^ i) := by
          rw [Nat.pow_succ]
          calc
            2 * δ * (2 ^ k * 2) * t ^ i
                = 2 * δ * (2 * 2 ^ k) * t ^ i := by rw [Nat.mul_comm (2 ^ k) 2]
            _   = ((2 * δ) * 2 * 2 ^ k) * t ^ i := by rw [← Nat.mul_assoc (2 * δ) 2]
            _   = (2 * (2 * δ) * 2 ^ k) * t ^ i := by rw [Nat.mul_comm (2 * δ) 2]
            _   = 2 * (2 * δ * 2 ^ k * t ^ i) := by rw [Nat.mul_assoc 2 (2 * δ), Nat.mul_assoc 2]
        have e3 : t * (2 * δ * 2 ^ k * t ^ i) = 2 * δ * 2 ^ k * t ^ (i + 1) := by
          rw [Nat.pow_succ]
          calc
            t * (2 * δ * 2 ^ k * t ^ i)
                = (2 * δ * 2 ^ k * t ^ i) * t := Nat.mul_comm _ _
            _   = 2 * δ * 2 ^ k * (t ^ i * t) := Nat.mul_assoc _ _ _
        rw [e1, e2, ← Nat.add_mul, ht2, e3]
      have hlen_d : (d :: d2 :: rest2).length = k + 1 := rfl
      rw [hlen_d, Nat.mul_add]
      dsimp only [k] at hrec hmul_q hcancel ⊢
      omega

/-- Master 4-register passive powering program for arbitrary `N ≥ 1` built from any `(δ, t)` base block. -/
def fourRegPowerProg {R : Type u} [CRing R] (δ : Nat) (hδ : 2 ≤ δ) (N : Nat)
    (invFactPrev invFactLen : R) (baseBlock : R → List (Work3Instr R)) : List (Pass4Instr R) :=
  let ds := baseDigits δ hδ N
  accumProg ds.length invFactLen (digitSubProgs δ invFactPrev baseBlock 0 ds)

theorem fourRegPowerProg_spec {R : Type u} [CRing R] (δ t : Nat) (hδ : 2 ≤ δ) (ht : 3 ≤ t)
    (N : Nat) (hN : 1 ≤ N)
    (invFactPrev invFactLen : R)
    (hinvPrev : invFactPrev * CRing.natCast (fact (δ - 1)) = 1)
    (hinvLen : invFactLen * CRing.natCast (fact (baseDigits δ hδ N).length) = 1)
    (baseBlock : R → List (Work3Instr R))
    (hAcc : ∀ c, Work3Prog.accesses (baseBlock c) = t)
    (hBlock : ∀ c y a b d : R, Work3Prog.exec y (baseBlock c) (a, b, d) = (a + c * CRing.pow y δ, b, d)) :
    let prog := fourRegPowerProg δ hδ N invFactPrev invFactLen baseBlock
    let ℓ := (baseDigits δ hδ N).length - 1
    δ ^ ℓ ≤ N ∧
    (t - 2) * Pass4Prog.accesses prog < 2 * δ * t * t ^ ℓ ∧
    ∀ x o u r1 r2 : R,
      Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2) := by
  let ds := baseDigits δ hδ N
  have hpos : 0 < ds.length := baseDigits_nonempty δ hδ N
  have hlt : ∀ b ∈ ds, b < δ := baseDigits_lt δ hδ N
  refine ⟨baseDigits_pow_le δ hδ N hN, ?_, ?_⟩
  · have hbnd := accumProg_digitSubProgs_bound δ t ds.length ht invFactPrev invFactLen
      baseBlock hAcc 0 ds hpos hlt
    have hslack : 0 < 2 * δ * 2 ^ ds.length * t ^ 0 := by
      have h1 : 0 < 2 ^ ds.length := Nat.pow_pos (by decide)
      have h2 : 0 < 2 * δ := by omega
      simp only [Nat.pow_zero, Nat.mul_one]
      exact Nat.mul_pos h2 h1
    simp only [Nat.zero_add] at hbnd
    change (t - 2) * Pass4Prog.accesses
        (accumProg ds.length invFactLen (digitSubProgs δ invFactPrev baseBlock 0 ds)) <
      2 * δ * t * t ^ (ds.length - 1)
    omega
  · intro x o u r1 r2
    unfold fourRegPowerProg
    have hlen : (digitSubProgs δ invFactPrev baseBlock 0 ds).length = (digitPowVals δ x 0 ds).length := by
      rw [digitSubProgs_length, digitPowVals_length]
    have hclean := digitSubProgs_clean δ invFactPrev hinvPrev baseBlock hBlock x 0 ds hlt
    rw [accumProg_exec ds.length x _ (digitPowVals δ x 0 ds) invFactLen o u r1 r2 hlen hclean]
    have hmlen : ds.length = (digitPowVals δ x 0 ds).length := (digitPowVals_length δ x 0 ds).symm
    rw [(multiDiff_pow (digitPowVals δ x 0 ds) ds.length u).2 hmlen]
    rw [← CRing.mul_assoc, hinvLen, CRing.one_mul]
    rw [digitPowVals_prod δ x 0 ds, Nat.pow_zero, Nat.mul_one, baseDigits_eval δ hδ N]

/-- Rescaling a clean `Pass3Prog.scaleOut s p` program by `c : R` multiplies its output delta by `c`. -/
private theorem Pass3Prog.exec_scaleOut_mul {R : Type u} [CRing R] (c s x a b d Δ : R)
    (p : List Pass3Instr)
    (hs : Pass3Prog.exec x (Pass3Prog.scaleOut s p) (a, b, d) = (a + Δ, b, d)) :
    Pass3Prog.exec x (Pass3Prog.scaleOut (c * s) p) (a, b, d) = (a + c * Δ, b, d) := by
  let res1 := Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p) (a, b, d)
  let δ1 : R := res1.1 + -a
  have hδ1 : res1.1 = a + δ1 := by
    change res1.1 = a + (res1.1 + -a)
    rw [CRing.add_comm res1.1 (-a), ← CRing.add_assoc, CRing.add_neg, CRing.zero_add]
  have hS := Pass3Prog.exec_scaleOut s x a a b d p
  have hCS := Pass3Prog.exec_scaleOut (c * s) x a a b d p
  have hs1 : (Pass3Prog.exec x (Pass3Prog.scaleOut s p) (a, b, d)).1 = a + s * δ1 := hS.2 δ1 hδ1
  have hsΔ : a + s * δ1 = a + Δ := by rw [← hs1, hs]
  have hs_eq : s * δ1 = Δ := CRing.add_left_cancel hsΔ
  have hcs1 : (Pass3Prog.exec x (Pass3Prog.scaleOut (c * s) p) (a, b, d)).1 = a + c * Δ := by
    rw [hCS.2 δ1 hδ1, CRing.mul_assoc, hs_eq]
  have hcs2 : (Pass3Prog.exec x (Pass3Prog.scaleOut (c * s) p) (a, b, d)).2 = (b, d) := by
    have h1 : (Pass3Prog.exec x (Pass3Prog.scaleOut s p) (a, b, d)).2 = (b, d) := by rw [hs]
    rw [hCS.1, ← hS.1, h1]
  exact Prod.ext hcs1 hcs2

/--
**Theorem `T3h` (Part 1 — `prog8Power13` 4-Register Passive Powering for All `N ≥ 1` under Stated Invertibility):**
For EVERY commutative ring `R` and EVERY `N ≥ 1` with `ℓ = (baseDigits 13 N).length - 1`,
whenever `D_8`, `12!`, and `(ℓ + 1)!` are invertible in `R`, there is an explicit passive
4-register program computing `O ← O + x^N` cleanly with `13^ℓ ≤ N` and
`3 * accesses < 104 * 8^ℓ` (i.e. `< (8/3) * 13 * N^{log_13 8} = O(N^{0.81072})`).
-/
theorem four_reg_powering_x13 {R : Type u} [CRing R] (N : Nat) (hN : 1 ≤ N)
    (invD8 invFact12 invFactLen : R)
    (hD8 : invD8 * CRing.intCast 2656207148788801777680 = 1)
    (hF12 : invFact12 * CRing.natCast (fact 12) = 1)
    (hFL : invFactLen * CRing.natCast (fact (baseDigits 13 (by decide) N).length) = 1) :
    ∃ prog : List (Pass4Instr R),
      let ℓ := (baseDigits 13 (by decide) N).length - 1
      13 ^ ℓ ≤ N ∧
      3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
      ∀ x o u r1 r2 : R,
        Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2) := by
  let block : R → List (Work3Instr R) :=
    fun c => Pass3Prog.toWork3 (Pass3Prog.scaleOut (c * invD8) prog8Power13)
  have hAcc : ∀ c, Work3Prog.accesses (block c) = 8 := by
    intro c
    simp only [block, Pass3Prog.toWork3_accesses, Pass3Prog.scaleOut_accesses]
    exact prog8_x13_accesses
  have hBlock : ∀ c y a b d : R, Work3Prog.exec y (block c) (a, b, d) = (a + c * CRing.pow y 13, b, d) := by
    intro c y a b d
    simp only [block, Pass3Prog.toWork3_exec]
    exact Pass3Prog.exec_scaleOut_mul c invD8 y a b d (CRing.pow y 13) prog8Power13
      ((three_reg_8call_x13 invD8 hD8).2 y a b d)
  have hspec := fourRegPowerProg_spec 13 8 (by decide) (by decide) N hN
    invFact12 invFactLen hF12 hFL block hAcc hBlock
  refine ⟨fourRegPowerProg 13 (by decide) N invFact12 invFactLen block, hspec.1, ?_, hspec.2.2⟩
  have hb := hspec.2.1
  omega

/--
**Theorem `T3h` (Part 2 — Low-Characteristic `prog5Power7` 4-Register Passive Powering for All `N ≥ 1`):**
For EVERY commutative ring `R` and EVERY `N ≥ 1` with `ℓ = (baseDigits 7 N).length - 1`,
whenever `6!` and `(ℓ + 1)!` are invertible in `R` (e.g. `char = 0` or `p > max(6, ℓ + 1)` —
note `6! = 720` invertible automatically makes `576 = 2^6 * 3^2` invertible!), there is an explicit
passive 4-register program computing `O ← O + x^N` cleanly with `7^ℓ ≤ N` and
`3 * accesses < 70 * 5^ℓ` (i.e. `< (10/3) * 7 * N^{log_7 5} = O(N^{0.82709})`).
-/
theorem four_reg_powering_x7 {R : Type u} [CRing R] (N : Nat) (hN : 1 ≤ N)
    (invFact6 invFactLen : R)
    (hF6 : invFact6 * CRing.natCast (fact 6) = 1)
    (hFL : invFactLen * CRing.natCast (fact (baseDigits 7 (by decide) N).length) = 1) :
    ∃ prog : List (Pass4Instr R),
      let ℓ := (baseDigits 7 (by decide) N).length - 1
      7 ^ ℓ ≤ N ∧
      3 * Pass4Prog.accesses prog < 70 * 5 ^ ℓ ∧
      ∀ x o u r1 r2 : R,
        Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2) := by
  -- Derive `576⁻¹` directly from `(6!)⁻¹ = 720⁻¹`: `720 * 720 = 576 * 900`!
  let inv576 : R := invFact6 * invFact6 * CRing.natCast 900
  have h576 : inv576 * CRing.intCast 576 = 1 := by
    have h720 : fact 6 = 720 := by decide
    have hF6' : invFact6 * CRing.natCast 720 = 1 := by rw [← h720]; exact hF6
    change invFact6 * invFact6 * CRing.natCast 900 * CRing.natCast 576 = 1
    calc
      invFact6 * invFact6 * CRing.natCast 900 * CRing.natCast 576
          = (invFact6 * invFact6) * (CRing.natCast 900 * CRing.natCast 576) := CRing.mul_assoc _ _ _
      _   = (invFact6 * invFact6) * CRing.natCast (900 * 576) := by rw [← CRing.natCast_mul]
      _   = (invFact6 * invFact6) * CRing.natCast (720 * 720) := rfl
      _   = (invFact6 * invFact6) * (CRing.natCast 720 * CRing.natCast 720) := by rw [CRing.natCast_mul]
      _   = invFact6 * (invFact6 * (CRing.natCast 720 * CRing.natCast 720)) := CRing.mul_assoc _ _ _
      _   = invFact6 * ((CRing.natCast 720 * invFact6) * CRing.natCast 720) := by
            rw [← CRing.mul_assoc invFact6 (CRing.natCast 720), CRing.mul_comm invFact6 (CRing.natCast 720)]
      _   = (invFact6 * CRing.natCast 720) * (invFact6 * CRing.natCast 720) := by
            rw [CRing.mul_assoc (CRing.natCast 720), ← CRing.mul_assoc invFact6 (CRing.natCast 720)]
      _   = 1 * 1 := by rw [hF6']
      _   = 1 := CRing.one_mul 1
  let block : R → List (Work3Instr R) :=
    fun c => Pass3Prog.toWork3 (Pass3Prog.scaleOut (c * inv576) prog5Power7)
  have hAcc : ∀ c, Work3Prog.accesses (block c) = 5 := by
    intro c
    simp only [block, Pass3Prog.toWork3_accesses, Pass3Prog.scaleOut_accesses]
    exact prog5_x7_accesses
  have hBlock : ∀ c y a b d : R, Work3Prog.exec y (block c) (a, b, d) = (a + c * CRing.pow y 7, b, d) := by
    intro c y a b d
    simp only [block, Pass3Prog.toWork3_exec]
    exact Pass3Prog.exec_scaleOut_mul c inv576 y a b d (CRing.pow y 7) prog5Power7
      ((three_reg_5call_x7 inv576 h576).2 y a b d)
  have hspec := fourRegPowerProg_spec 7 5 (by decide) (by decide) N hN
    invFact6 invFactLen hF6 hFL block hAcc hBlock
  refine ⟨fourRegPowerProg 7 (by decide) N invFact6 invFactLen block, hspec.1, ?_, hspec.2.2⟩
  have hb := hspec.2.1
  omega

/-! ## 5. Pointwise Product-Ring Instantiation (`Fin n → R`) for Catalytic Streaming Frequency Moments (`T3i`) -/

/-- Pointwise commutative ring structure on `Fin n → R` (modelling the frequency-vector algebra `𝔽_p^n`). -/
instance instCRingFinFun {n : Nat} {R : Type u} [CRing R] : CRing (Fin n → R) where
  zero := fun _ => 0
  one := fun _ => 1
  add f g := fun i => f i + g i
  mul f g := fun i => f i * g i
  neg f := fun i => -(f i)
  add_assoc a b c := funext fun i => CRing.add_assoc (a i) (b i) (c i)
  add_comm a b := funext fun i => CRing.add_comm (a i) (b i)
  zero_add a := funext fun i => CRing.zero_add (a i)
  add_neg a := funext fun i => CRing.add_neg (a i)
  mul_assoc a b c := funext fun i => CRing.mul_assoc (a i) (b i) (c i)
  mul_comm a b := funext fun i => CRing.mul_comm (a i) (b i)
  one_mul a := funext fun i => CRing.one_mul (a i)
  left_distrib a b c := funext fun i => CRing.left_distrib (a i) (b i) (c i)

private theorem natCast_finFun {n : Nat} {R : Type u} [CRing R] (k : Nat) (i : Fin n) :
    (CRing.natCast k : Fin n → R) i = CRing.natCast k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    change (CRing.natCast m : Fin n → R) i + (1 : R) = CRing.natCast m + 1
    rw [ih]

private theorem intCast_finFun {n : Nat} {R : Type u} [CRing R] (z : Int) (i : Fin n) :
    (CRing.intCast z : Fin n → R) i = CRing.intCast z := by
  cases z with
  | ofNat k => exact natCast_finFun k i
  | negSucc k =>
    change -((CRing.natCast (k + 1) : Fin n → R) i) = -(CRing.natCast (k + 1))
    rw [natCast_finFun]

private theorem pow_finFun {n : Nat} {R : Type u} [CRing R] (f : Fin n → R) (D : Nat) (i : Fin n) :
    CRing.pow f D i = CRing.pow (f i) D := by
  induction D with
  | zero => rfl
  | succ m ih =>
    change CRing.pow f m i * f i = CRing.pow (f i) m * f i
    rw [ih]

/-- Coordinate sum `∑_{i < n} v i` of a vector `v : Fin n → R`. -/
def sumFin {n : Nat} {R : Type u} [CRing R] (v : Fin n → R) : R :=
  sumR n (fun j => if h : j < n then v ⟨j, h⟩ else 0)

theorem sumFin_add {n : Nat} {R : Type u} [CRing R] (u v : Fin n → R) :
    sumFin (fun i => u i + v i) = sumFin u + sumFin v := by
  unfold sumFin
  have hcongr :
      sumR n (fun j => if h : j < n then u ⟨j, h⟩ + v ⟨j, h⟩ else 0) =
      sumR n (fun j => (if h : j < n then u ⟨j, h⟩ else 0) + (if h : j < n then v ⟨j, h⟩ else 0)) := by
    refine sumR_congr (fun j hj => ?_)
    simp [hj]
  rw [hcongr, sumR_add]

/--
**Theorem `T3i` (Algebraic Catalytic Streaming Frequency-Moment Pass Bound over `R^n`):**
For EVERY universe size `n : Nat`, EVERY commutative ring `R` (e.g., `𝔽_p`), and EVERY moment
order `D ≥ 1` with `ℓ = (baseDigits 13 D).length - 1`, whenever `D_8`, `12!`, and `(ℓ + 1)!`
are invertible in `R`, there is an explicit 4-vector-register passive catalytic program over
`Fin n → R` performing strictly fewer than `(104/3) * 8^ℓ ≤ (8/3) * 13 * D^{log_13 8}` passes
over the stream frequency vector `f : Fin n → R` that cleanly updates every coordinate
`O_i ← O_i + f_i^D`, restores all three catalytic vectors `(U, R1, R2)` identically, and
cleanly accumulates the `D`-th frequency moment `F_D(f) = ∑_{i < n} f_i^D` in `sumFin O`.
-/
theorem four_reg_streaming_moment_x13 {R : Type u} [CRing R] (n D : Nat) (hD : 1 ≤ D)
    (invD8 invFact12 invFactLen : R)
    (hD8 : invD8 * CRing.intCast 2656207148788801777680 = 1)
    (hF12 : invFact12 * CRing.natCast (fact 12) = 1)
    (hFL : invFactLen * CRing.natCast (fact (baseDigits 13 (by decide) D).length) = 1) :
    ∃ prog : List (Pass4Instr (Fin n → R)),
      let ℓ := (baseDigits 13 (by decide) D).length - 1
      13 ^ ℓ ≤ D ∧
      3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
      ∀ f o u r1 r2 : Fin n → R,
        let res := Pass4Prog.exec f prog (o, u, r1, r2)
        (∀ i : Fin n, res.1 i = o i + CRing.pow (f i) D) ∧
        res.2 = (u, r1, r2) ∧
        sumFin res.1 = sumFin o + sumFin (fun i => CRing.pow (f i) D) := by
  have hD8' : (fun _ : Fin n => invD8) * CRing.intCast 2656207148788801777680 = (1 : Fin n → R) := by
    funext i
    change invD8 * (CRing.intCast 2656207148788801777680 : Fin n → R) i = 1
    rw [intCast_finFun, hD8]
  have hF12' : (fun _ : Fin n => invFact12) * CRing.natCast (fact 12) = (1 : Fin n → R) := by
    funext i
    change invFact12 * (CRing.natCast (fact 12) : Fin n → R) i = 1
    rw [natCast_finFun, hF12]
  have hFL' :
      (fun _ : Fin n => invFactLen) * CRing.natCast (fact (baseDigits 13 (by decide) D).length) =
        (1 : Fin n → R) := by
    funext i
    change invFactLen * (CRing.natCast (fact (baseDigits 13 (by decide) D).length) : Fin n → R) i = 1
    rw [natCast_finFun, hFL]
  obtain ⟨prog, hpow, hacc, hexec⟩ :=
    four_reg_powering_x13 (R := Fin n → R) D hD
      (fun _ => invD8) (fun _ => invFact12) (fun _ => invFactLen) hD8' hF12' hFL'
  refine ⟨prog, hpow, hacc, ?_⟩
  intro f o u r1 r2
  have he := hexec f o u r1 r2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h1 : (Pass4Prog.exec f prog (o, u, r1, r2)).1 = o + CRing.pow f D := congrArg Prod.fst he
    rw [h1]
    change o i + CRing.pow f D i = o i + CRing.pow (f i) D
    rw [pow_finFun]
  · exact congrArg Prod.snd he
  · have h1 : (Pass4Prog.exec f prog (o, u, r1, r2)).1 = fun i => o i + CRing.pow (f i) D := by
      have hf := congrArg Prod.fst he
      rw [hf]
      funext i
      change o i + CRing.pow f D i = o i + CRing.pow (f i) D
      rw [pow_finFun]
    rw [h1, sumFin_add]

end

end Catalytic
